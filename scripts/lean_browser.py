#!/usr/bin/env python3
"""Build `browser/` — the formal statement browser, from the compiled environment.

Every declaration of the library with the type the *kernel* elaborated, its docstring, the
axioms it rests on, and both directions of its dependency edges. The forward direction comes
from `docs/lean-facts.json`; the reverse is computed here, and it is the thing neither
`docs/REPO-INDEX.md` nor a doc-gen4 site gives you — when you are deciding whether a lemma is
safe to change, *used by* is the question.

Nothing here parses Lean source. `scripts/repo_map.py` does, and its two parser bugs are why
this reads `lean-facts.json` instead: that file is written by `scripts/lean_facts.lean` walking
the environment, so a name is in it exactly when the compiler agrees it exists.

Output (git-ignored, staged like `blueprint/web/`):

    browser/
      index.html      search over every declaration; the index is INLINED, not fetched
      lean-browser.{css,js}
      m/<Module>.html one page per module, `<article id="<FullName>">` per declaration
      find/index.html the doc-gen4 URL contract: {dochome}/find/#doc/<Name>
      leanref.js      turns the blueprint's plain `[[Name]]` citations into links
      facts.json      the machine twin

Inlined rather than fetched on purpose: `fetch()` fails under `file://`, and this is a tool you
want when the deploy is the thing that is broken.

    python3 scripts/lean_browser.py             build
    python3 scripts/lean_browser.py --verify    build, then assert the site is self-consistent
    python3 scripts/lean_browser.py --allow-stale
"""
import argparse, html, json, os, re, subprocess, sys, datetime

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "browser")
GITHUB = "https://github.com/LBrunswic/GFNBoundsLean"
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs"

# Companions the elaborator emits beside a real declaration. They are declarations to the
# kernel and noise to a reader, so they are counted separately and hidden by default —
# otherwise this page reports 2041 where the dashboard reports 1776 and neither looks right.
GENERATED_SUFFIXES = (
    ".injEq", ".noConfusionType", ".noConfusion", ".sizeOf_spec", ".ctorIdx",
    ".congr_simp", ".below", ".brecOn", ".binductionOn", ".rec", ".recOn",
    ".casesOn", ".ndrec", ".ndrecOn", ".mk", ".eq_def", ".eq_1", ".ofNat",
)


def sh(*cmd):
    return subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT)


def git(*args):
    r = sh("git", *args)
    return r.stdout.strip() if r.returncode == 0 else ""


def esc(s):
    return html.escape(str(s), quote=True)


def is_generated(name, kind):
    return kind in ("ctor", "rec") or name.endswith(GENERATED_SUFFIXES)


def is_named_result(doc):
    """The house marker, same rule as `scripts/appendix.py`: a result the library names
    announces itself with a bold lead in its docstring. See kb/0018."""
    return doc.lstrip().startswith("**")


# ---------------------------------------------------------------- load

def load():
    with open(os.path.join(ROOT, "docs", "lean-facts.json"), encoding="utf-8") as fh:
        decls = json.load(fh)["declarations"]

    # Statements of the paper that name a declaration, inverted: declaration -> its label.
    paper = {}
    pm = os.path.join(ROOT, "paper-map.json")
    if os.path.exists(pm):
        with open(pm, encoding="utf-8") as fh:
            m = json.load(fh)
        app_of = {k: v["appendix"] for k, v in m.get("sources", {}).items()}
        for st in m["statements"]:
            for d in st.get("decls", []):
                paper.setdefault(d, []).append({
                    "label": st["label"], "status": st["status"],
                    "bucket": st.get("bucket") or "",
                    "appendix": app_of.get(st.get("source", ""), "?"),
                })

    # Declarations the blueprint carries a `\lean{}` anchor for.
    blueprint = set()
    ld = os.path.join(ROOT, "blueprint", "lean_decls")
    if os.path.exists(ld):
        with open(ld, encoding="utf-8") as fh:
            blueprint = {ln.strip() for ln in fh if ln.strip()}

    # Externals, if scripts/lean_facts.lean has been extended to record them.
    externals = {}
    ex = os.path.join(ROOT, "docs", "lean-externals.json")
    if os.path.exists(ex):
        with open(ex, encoding="utf-8") as fh:
            externals = json.load(fh).get("declarations", {})

    return decls, paper, blueprint, externals


def reverse_edges(decls):
    """The reverse of `uses_type` and `uses_value`. The forward direction is in the JSON; this
    direction is not, and is the reason the browser exists."""
    by_type, by_value = {}, {}
    for name, d in decls.items():
        for t in d.get("uses_type", []):
            by_type.setdefault(t, []).append(name)
        for t in d.get("uses_value", []):
            by_value.setdefault(t, []).append(name)
    for m in (by_type, by_value):
        for k in m:
            m[k].sort()
    return by_type, by_value


def closure_sizes(decls):
    """How many declarations each one transitively rests on, over `uses_value` — the quantity
    `appendix.py`'s `closure()` reports, so the browser and the blueprint's closing table
    corroborate each other rather than merely coexisting.

    Memoised and iterative: the graph has cycles only through `partial`/mutual blocks, and a
    recursive walk would both blow the stack and recompute `Setting`'s closure 500 times."""
    memo, sizes = {}, {}
    for start in decls:
        if start in memo:
            continue
        # Iterative DFS with an explicit stack; a node is resolved once every child is.
        stack = [(start, False)]
        while stack:
            node, expanded = stack.pop()
            if node in memo:
                continue
            kids = [k for k in decls.get(node, {}).get("uses_value", []) if k in decls]
            if expanded:
                acc = set()
                for k in kids:
                    acc.add(k)
                    acc |= memo.get(k, set())
                acc.discard(node)
                memo[node] = acc
            else:
                stack.append((node, True))
                for k in kids:
                    if k not in memo:
                        stack.append((k, False))
    for n in decls:
        sizes[n] = len(memo.get(n, set()))
    return sizes


# ---------------------------------------------------------------- rendering

def link_names_in_type(type_str, names, mod_of):
    """Escape the type, then link every project constant it mentions. Project names appear
    verbatim in `ppExpr` output, so this needs no span information. Longest-first so
    `...Stat` cannot be clobbered by `...St`, and one pass so a replacement is never rescanned."""
    body = esc(type_str)
    targets = sorted({n for n in names if n in mod_of}, key=len, reverse=True)
    if not targets:
        return body
    pat = re.compile("(?:" + "|".join(re.escape(n) for n in targets) + r")(?![A-Za-z0-9_.'])")

    def repl(m):
        n = m.group(0)
        return ('<a class="cst" href="%s.html#%s">%s</a>'
                % (esc(mod_of[n]), esc(n), esc(n)))
    return pat.sub(repl, body)


DOC_CODE = re.compile(r"`([^`]+)`")
# Non-greedy and *permitting* a star inside: these docstrings are mathematics, so a bold lead
# like `**p_*(c) packaged.**` carries a multiplication star and `[^*]+` silently refuses it.
DOC_BOLD = re.compile(r"\*\*(.+?)\*\*", re.S)
# Emphasis only when the stars hug non-space, so `a * b * c` is arithmetic and stays arithmetic.
DOC_ITAL = re.compile(r"(?<!\*)\*(?=\S)([^*\n]+?)(?<=\S)\*(?!\*)")


def render_doc(doc, mod_of):
    """The docstrings here use exactly three constructs. A markdown library would be a
    dependency and 2041 pandoc subprocesses would dominate the build, so this renders those
    three and leaves everything else as text."""
    if not doc:
        return ""
    out = esc(doc.strip())

    def code(m):
        inner = html.unescape(m.group(1))
        if inner in mod_of:
            return ('<a class="cst" href="%s.html#%s"><code>%s</code></a>'
                    % (esc(mod_of[inner]), esc(inner), esc(inner)))
        return "<code>%s</code>" % m.group(1)
    out = DOC_CODE.sub(code, out)
    out = DOC_BOLD.sub(r"<b>\1</b>", out)
    out = DOC_ITAL.sub(r"<i>\1</i>", out)
    return "".join("<p>%s</p>" % p.replace("\n", " ")
                   for p in re.split(r"\n\s*\n", out) if p.strip())


def chip_list(names, mod_of, limit=40, cls="cst"):
    if not names:
        return '<span class="none">none</span>'
    shown = names[:limit]
    items = "".join('<a class="%s" href="%s.html#%s">%s</a>'
                    % (cls, esc(mod_of[n]), esc(n), esc(n.split(".")[-1]))
                    for n in shown if n in mod_of)
    if len(names) > limit:
        rest = "".join('<a class="%s" href="%s.html#%s">%s</a>'
                       % (cls, esc(mod_of[n]), esc(n), esc(n.split(".")[-1]))
                       for n in names[limit:] if n in mod_of)
        items += ('<details class="more"><summary>%d more</summary>%s</details>'
                  % (len(names) - limit, rest))
    return items


def declaration_html(name, d, ctx):
    mod_of, by_type, by_value, paper, blueprint, externals, sha, rests = ctx
    short = name.split(".")[-1]
    kind = d["kind"]
    badges = ['<span class="kind k-%s">%s</span>' % (esc(kind), esc(kind))]
    if kind in ("axiom", "opaque"):
        badges.append('<span class="warn">unproved primitive</span>')
    if is_named_result(d["doc"]):
        badges.append('<span class="named">named result</span>')
    if name in blueprint:
        badges.append('<span class="bp">in the blueprint</span>')

    src = "%s/blob/%s/%s.lean" % (GITHUB, sha, d["module"].replace(".", "/"))
    if d["line"]:
        src += "#L%d" % d["line"]

    parts = ['<article id="%s" class="decl%s">' % (esc(name), " gen" if is_generated(name, kind) else "")]
    parts.append('<h3><a class="self" href="#%s">%s</a> %s</h3>'
                 % (esc(name), esc(short), "".join(badges)))
    parts.append('<p class="fq"><code>%s</code></p>' % esc(name))

    if d["nonstandard_axioms"]:
        parts.append('<p class="alarm">Rests on non-standard axioms: %s</p>'
                     % esc(", ".join(d["nonstandard_axioms"])))

    parts.append('<pre class="type">%s</pre>'
                 % link_names_in_type(d["type"], d.get("uses_type", []), mod_of))

    if d["doc"]:
        parts.append('<div class="doc">%s</div>' % render_doc(d["doc"], mod_of))

    for lab in paper.get(name, []):
        parts.append('<p class="paper">Appendix %s &middot; <code>%s</code> '
                     '<span class="st st-%s">%s</span>%s</p>'
                     % (esc(lab["appendix"]), esc(lab["label"]), esc(lab["status"]),
                        esc(lab["status"]),
                        (" &middot; bucket %s" % esc(lab["bucket"])) if lab["bucket"] else ""))

    work = [n for n in d.get("uses_value", []) if n not in set(d.get("uses_type", []))]
    rows = [("Statement uses", chip_list(sorted(d.get("uses_type", [])), mod_of)),
            ("Proof also uses", chip_list(sorted(work), mod_of)),
            ("Used by (statement)", chip_list(by_type.get(name, []), mod_of)),
            ("Used by (proof)", chip_list(by_value.get(name, []), mod_of))]
    ext = externals.get(name) or []
    if ext:
        rows.append(("Mathlib and core", "".join(
            '<a class="ext" href="%s/find/#doc/%s" rel="noreferrer">%s</a>'
            % (MATHLIB_DOCS, esc(n), esc(n)) for n in ext[:60])))
    parts.append('<dl class="edges">%s</dl>' % "".join(
        "<dt>%s</dt><dd>%s</dd>" % (k, v) for k, v in rows))

    parts.append('<p class="meta">'
                 '<a href="%s" rel="noreferrer">source (GitHub &middot; private)</a>'
                 ' &middot; %s:%s &middot; rests on %d declarations &middot; axioms %s</p>'
                 % (esc(src), esc(d["module"]), d["line"] or "?", rests.get(name, 0),
                    esc(", ".join(d["axioms"]) or "none")))
    parts.append("</article>")
    return "".join(parts)


# ---------------------------------------------------------------- assets

CSS = """/* Generated by scripts/lean_browser.py. Same roles as the dashboard's stylesheet so the
   two read as one site; self-contained so browser/ also works opened off disk. */
:root{color-scheme:light;--surface-1:#fcfcfb;--plane:#f9f9f7;--ink-1:#0b0b0b;--ink-2:#52514e;
--ink-muted:#898781;--grid:#e1e0d9;--baseline:#c3c2b7;--border:rgba(11,11,11,.10);
--good:#0ca30c;--warning:#fab219;--critical:#d03b3b;--link:#2a78d6;
--sans:system-ui,-apple-system,"Segoe UI",sans-serif;
--mono:ui-monospace,SFMono-Regular,"SF Mono",Menlo,monospace}
@media(prefers-color-scheme:dark){:root:where(:not([data-theme=light])){color-scheme:dark;
--surface-1:#1a1a19;--plane:#0d0d0d;--ink-1:#fff;--ink-2:#c3c2b7;--grid:#2c2c2a;
--baseline:#383835;--border:rgba(255,255,255,.10);--link:#3987e5}}
:root[data-theme=dark]{color-scheme:dark;--surface-1:#1a1a19;--plane:#0d0d0d;--ink-1:#fff;
--ink-2:#c3c2b7;--grid:#2c2c2a;--baseline:#383835;--border:rgba(255,255,255,.10);--link:#3987e5}
*{box-sizing:border-box}
body{margin:0;padding:0 1.25rem 5rem;background:var(--plane);color:var(--ink-1);
font-family:var(--sans);font-size:16px;line-height:1.55;-webkit-font-smoothing:antialiased}
.wrap{max-width:64rem;margin:0 auto}
a{color:var(--link);text-decoration-thickness:1px;text-underline-offset:2px}
header.masthead{padding:2rem 0 1rem;border-bottom:1px solid var(--grid)}
.eyebrow{font-size:.8125rem;letter-spacing:.08em;text-transform:uppercase;color:var(--ink-muted);margin:0 0 .4rem}
.eyebrow a{color:var(--ink-muted)}
h1{font-size:1.5rem;font-weight:650;margin:0 0 .3rem;letter-spacing:-.01em}
.masthead p{color:var(--ink-2);margin:0;max-width:48rem}
#q{width:100%;padding:.7rem .9rem;font:inherit;border:1px solid var(--baseline);
border-radius:.5rem;background:var(--surface-1);color:var(--ink-1);margin:1.25rem 0 .6rem}
.filters{display:flex;gap:.4rem;flex-wrap:wrap;margin-bottom:1rem}
.filters button{border:1px solid var(--border);background:var(--surface-1);color:var(--ink-2);
border-radius:999px;padding:.25rem .7rem;font:inherit;font-size:.8125rem;cursor:pointer}
.filters button[aria-pressed=true]{border-color:var(--link);color:var(--link)}
#count{color:var(--ink-muted);font-size:.8125rem;margin:0 0 .5rem}
#results{list-style:none;padding:0;margin:0}
#results li{padding:.5rem .1rem;border-bottom:1px solid var(--grid)}
#results .nm{font-family:var(--mono);font-size:.9rem}
#results .md{color:var(--ink-muted);font-size:.75rem;margin-left:.5rem}
#results .ty{color:var(--ink-2);font-size:.8125rem;font-family:var(--mono);
display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.modlist{columns:3;column-gap:1.5rem;list-style:none;padding:0;font-size:.875rem}
@media(max-width:52rem){.modlist{columns:1}}
.decl{background:var(--surface-1);border:1px solid var(--border);border-radius:.5rem;
padding:1rem 1.15rem;margin:1rem 0}
.decl.gen{opacity:.75}
.decl h3{margin:0 0 .2rem;font-size:1.0625rem;font-family:var(--mono);font-weight:650}
.decl h3 a.self{color:inherit;text-decoration:none}
.decl h3 a.self:hover{color:var(--link)}
.fq{margin:0 0 .6rem;font-size:.75rem;color:var(--ink-muted)}
.kind,.warn,.named,.bp{font-family:var(--sans);font-size:.6875rem;font-weight:600;
border-radius:999px;padding:.1rem .5rem;margin-left:.4rem;vertical-align:middle;
border:1px solid var(--border);color:var(--ink-2)}
.warn{background:var(--warning);color:#0b0b0b;border-color:transparent}
.named{border-color:var(--link);color:var(--link)}
.alarm{background:var(--critical);color:#fff;padding:.5rem .7rem;border-radius:.375rem;font-weight:600}
pre.type{background:var(--plane);border:1px solid var(--border);border-radius:.375rem;
padding:.7rem .8rem;overflow-x:auto;font-family:var(--mono);font-size:.8125rem;
line-height:1.5;white-space:pre-wrap;word-break:break-word;margin:.5rem 0}
.doc{color:var(--ink-2);font-size:.9375rem}
.doc p{margin:.5rem 0}
.paper{font-size:.8125rem;color:var(--ink-2);margin:.5rem 0}
.st{font-weight:600}.st-closed{color:var(--good)}.st-partial{color:var(--warning)}
.st-open{color:var(--ink-muted)}.st-stale{color:var(--critical)}
dl.edges{display:grid;grid-template-columns:11rem 1fr;gap:.3rem .9rem;margin:.8rem 0 .4rem;
font-size:.8125rem;align-items:baseline}
@media(max-width:44rem){dl.edges{grid-template-columns:1fr}dl.edges dt{margin-top:.5rem}}
dl.edges dt{color:var(--ink-muted)}
dl.edges dd{margin:0}
a.cst,a.ext{font-family:var(--mono);font-size:.78rem;display:inline-block;margin:0 .35rem .2rem 0}
pre.type a.cst{margin:0;font-size:inherit}
.none{color:var(--ink-muted)}
details.more{display:inline}
details.more summary{display:inline;cursor:pointer;color:var(--ink-muted);font-size:.78rem}
.meta{font-size:.75rem;color:var(--ink-muted);margin:.5rem 0 0}
footer{margin-top:3rem;padding-top:1rem;border-top:1px solid var(--grid);
font-size:.8125rem;color:var(--ink-muted)}
footer a{color:var(--ink-2)}
.dirty{color:var(--warning)}
#theme{position:fixed;top:.9rem;right:.9rem;z-index:30;border:1px solid var(--border);
background:var(--surface-1);color:var(--ink-2);border-radius:999px;padding:.35rem .8rem;
font:inherit;font-size:.8125rem;cursor:pointer}
"""

THEME_JS = """<button id="theme" type="button" aria-label="Switch colour theme">Theme</button>
<script>(function(){var r=document.documentElement,k='gfnbounds-theme',s=null;
try{s=localStorage.getItem(k)}catch(e){}
if(s)r.setAttribute('data-theme',s);
document.getElementById('theme').addEventListener('click',function(){
var d=getComputedStyle(r).colorScheme.indexOf('dark')>=0,n=d?'light':'dark';
r.setAttribute('data-theme',n);try{localStorage.setItem(k,n)}catch(e){}});})();</script>"""

SEARCH_JS = """// Generated by scripts/lean_browser.py. IDX is inlined by index.html.
(function () {
  var q = document.getElementById('q'), out = document.getElementById('results'),
      cnt = document.getElementById('count'), t = null;
  var kinds = {}, opts = { named: false, generated: false };

  function score(e, s) {
    if (e.s === s) return 0;
    if (e.s.toLowerCase().indexOf(s) === 0) return 1;
    if (e.l.indexOf(s) >= 0) return 2;
    if (e.d && e.d.indexOf(s) >= 0) return 3;
    if (e.t && e.t.indexOf(s) >= 0) return 4;
    return -1;
  }
  function run() {
    var s = q.value.trim().toLowerCase();
    var active = Object.keys(kinds).filter(function (k) { return kinds[k]; });
    var hits = [];
    for (var i = 0; i < IDX.length; i++) {
      var e = IDX[i];
      if (!opts.generated && e.g) continue;
      if (opts.named && !e.n) continue;
      if (active.length && active.indexOf(e.k) < 0) continue;
      var r = s ? score(e, s) : 5;
      if (r < 0) continue;
      hits.push([r, e]);
    }
    hits.sort(function (a, b) { return a[0] - b[0] || (a[1].s < b[1].s ? -1 : 1); });
    cnt.textContent = hits.length + ' of ' + IDX.length + ' declarations';
    var frag = document.createDocumentFragment();
    for (var j = 0; j < Math.min(hits.length, 300); j++) {
      var e = hits[j][1], li = document.createElement('li');
      li.innerHTML = '<a class="nm" href="m/' + e.m + '.html#' + encodeURIComponent(e.f) +
        '">' + e.s + '</a><span class="md">' + e.k + ' &middot; ' + e.m + '</span>' +
        '<span class="ty">' + e.t0 + '</span>';
      frag.appendChild(li);
    }
    out.innerHTML = '';
    out.appendChild(frag);
    if (hits.length > 300) {
      var li = document.createElement('li');
      li.className = 'md';
      li.textContent = 'showing the first 300 — narrow the search';
      out.appendChild(li);
    }
  }
  q.addEventListener('input', function () { clearTimeout(t); t = setTimeout(run, 60); });
  document.querySelectorAll('.filters button').forEach(function (b) {
    b.addEventListener('click', function () {
      var on = b.getAttribute('aria-pressed') !== 'true';
      b.setAttribute('aria-pressed', on ? 'true' : 'false');
      if (b.dataset.kind) kinds[b.dataset.kind] = on; else opts[b.dataset.opt] = on;
      run();
    });
  });
  // #?q=... lets `find/` hand an unresolved name straight to the search box.
  var m = /[#?&]q=([^&]*)/.exec(location.hash + location.search);
  if (m) q.value = decodeURIComponent(m[1]);
  run();
  q.focus();
})();
"""


def page(title, body, depth=0, extra=""):
    up = "../" * depth
    return ("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            "<meta name=\"robots\" content=\"noindex, nofollow\">\n"
            "<title>%s</title>\n<link rel=\"stylesheet\" href=\"%slean-browser.css\">\n"
            "</head>\n<body>\n<div class=\"wrap\">\n%s\n</div>\n%s\n</body>\n</html>\n"
            % (esc(title), up, body, extra))


def footer(meta):
    warn = ""
    if meta["dirty"]:
        warn = (' <span class="dirty">The working tree is dirty, so the source links point at '
                'a commit that does not contain everything shown here.</span>')
    elif not meta["pushed"]:
        warn = (' <span class="dirty">HEAD is not on origin/main, so the source links may 404 '
                'until it is pushed.</span>')
    return ('<footer>%d declarations across %d modules, from the compiled environment at '
            '<code>%s</code>. Built %s.%s '
            '<a href="../">Back to the dashboard</a> &middot; '
            '<a href="facts.json">facts.json</a></footer>'
            % (meta["shown"], meta["modules"], esc(meta["sha"]), esc(meta["built"]), warn))


# ---------------------------------------------------------------- build

def build(allow_stale=False):
    facts_path = os.path.join(ROOT, "docs", "lean-facts.json")
    if not os.path.exists(facts_path):
        sys.exit("lean_browser: docs/lean-facts.json missing — run `make facts`")
    if not allow_stale:
        r = sh("find", "GFNBounds", "scaffold", "-name", "*.lean",
               "-newer", "docs/lean-facts.json", "-print", "-quit")
        if r.stdout.strip():
            sys.exit("lean_browser: %s is newer than docs/lean-facts.json — run `make facts` "
                     "(or --allow-stale)" % r.stdout.strip())

    decls, paper, blueprint, externals = load()
    mod_of = {n: d["module"] for n, d in decls.items()}
    by_type, by_value = reverse_edges(decls)
    sha = git("rev-parse", "HEAD") or "HEAD"
    meta = {
        "sha": (sha[:10] if sha != "HEAD" else "HEAD"),
        "full_sha": sha,
        "dirty": git("status", "--porcelain") != "",
        "pushed": "origin/main" in git("branch", "-r", "--contains", "HEAD"),
        "built": datetime.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %Z"),
        "modules": len({d["module"] for d in decls.values()}),
        "shown": sum(1 for n, d in decls.items() if not is_generated(n, d["kind"])),
        "total": len(decls),
    }
    ctx = (mod_of, by_type, by_value, paper, blueprint, externals, sha, closure_sizes(decls))

    if os.path.isdir(OUT):
        import shutil
        shutil.rmtree(OUT)
    os.makedirs(os.path.join(OUT, "m"))
    os.makedirs(os.path.join(OUT, "find"))

    with open(os.path.join(OUT, "lean-browser.css"), "w", encoding="utf-8") as fh:
        fh.write(CSS)
    with open(os.path.join(OUT, "lean-browser.js"), "w", encoding="utf-8") as fh:
        fh.write(SEARCH_JS)

    # ---- module pages
    by_module = {}
    for n, d in decls.items():
        by_module.setdefault(d["module"], []).append(n)

    for mod, names in sorted(by_module.items()):
        real = sorted(n for n in names if not is_generated(n, decls[n]["kind"]))
        gen = sorted(n for n in names if is_generated(n, decls[n]["kind"]))
        body = ['<header class="masthead"><p class="eyebrow">'
                '<a href="../">Statement browser</a> / module</p>'
                '<h1><code>%s</code></h1><p>%d declarations'
                '%s.</p></header>' % (esc(mod), len(real),
                                      (", and %d generated by the elaborator" % len(gen)) if gen else "")]
        for n in real:
            body.append(declaration_html(n, decls[n], ctx))
        if gen:
            body.append('<details><summary>%d declarations generated by the elaborator</summary>%s</details>'
                        % (len(gen), "".join(declaration_html(n, decls[n], ctx) for n in gen)))
        body.append(footer(meta))
        with open(os.path.join(OUT, "m", mod + ".html"), "w", encoding="utf-8") as fh:
            fh.write(page("%s — GFNBoundsLean" % mod, "".join(body), depth=1, extra=THEME_JS))

    # ---- the search index, inlined
    idx = []
    for n, d in sorted(decls.items()):
        # Not the first *line*: ppExpr wraps, so line one of a long type is often just the
        # binder prefix (`{V : Type u_1} →`) and says nothing. Collapse and take the head.
        t0 = " ".join(d["type"].split())
        idx.append({
            "f": n, "s": n.split(".")[-1], "l": n.lower(), "k": d["kind"],
            "m": d["module"], "t0": esc(t0[:160]), "t": d["type"][:240].lower(),
            "d": d["doc"][:200].lower(), "n": 1 if is_named_result(d["doc"]) else 0,
            "g": 1 if is_generated(n, d["kind"]) else 0,
        })

    mods_html = "".join('<li><a href="m/%s.html"><code>%s</code></a> <span class="md">%d</span></li>'
                        % (esc(m), esc(m), len([x for x in ns if not is_generated(x, decls[x]["kind"])]))
                        for m, ns in sorted(by_module.items()))
    kinds = sorted({d["kind"] for d in decls.values()})
    filt = "".join('<button type="button" aria-pressed="false" data-kind="%s">%s</button>'
                   % (esc(k), esc(k)) for k in kinds)
    filt += ('<button type="button" aria-pressed="false" data-opt="named">named results</button>'
             '<button type="button" aria-pressed="false" data-opt="generated">show generated</button>')

    index_body = (
        '<header class="masthead"><p class="eyebrow">GFNBoundsLean</p>'
        '<h1>The formal statements</h1>'
        '<p>Every declaration of the library as the compiler elaborated it — its type, its '
        'docstring, the axioms it rests on, what it invokes and what invokes it. Read from the '
        'compiled environment, not from the source text.</p></header>'
        '<input id="q" type="search" placeholder="Search names, statements and docstrings…" '
        'autocomplete="off" spellcheck="false">'
        '<div class="filters">%s</div><p id="count"></p><ul id="results"></ul>'
        '<h2>Modules</h2><ul class="modlist">%s</ul>%s' % (filt, mods_html, footer(meta)))

    with open(os.path.join(OUT, "index.html"), "w", encoding="utf-8") as fh:
        fh.write(page("Statement browser — GFNBoundsLean", index_body, depth=0,
                      extra=('<script>var IDX=%s;</script><script src="lean-browser.js"></script>%s'
                             % (json.dumps(idx, ensure_ascii=False, separators=(",", ":")), THEME_JS))))

    # ---- find/ : the doc-gen4 URL contract. The fragment never reaches the server, so the
    # whole server-side requirement is that this file exists and returns 200.
    modmap = json.dumps({n: d["module"] for n, d in sorted(decls.items())},
                        ensure_ascii=False, separators=(",", ":"))
    find_body = ('<header class="masthead"><p class="eyebrow">'
                 '<a href="../">Statement browser</a></p><h1 id="msg">Resolving…</h1></header>')
    find_extra = ("""<script>
var MOD=%s;
(function(){
  var h=decodeURIComponent(location.hash.replace(/^#(doc\\/)?/,''));
  if(!h){location.replace('../');return;}
  var m=MOD[h];
  if(m){location.replace('../m/'+m+'.html#'+encodeURIComponent(h));return;}
  document.getElementById('msg').innerHTML='No declaration named <code>'+
    h.replace(/[&<>]/g,'')+'</code>';
  document.querySelector('.masthead').insertAdjacentHTML('beforeend',
    '<p>It may have been renamed. <a href="../#?q='+encodeURIComponent(h)+
    '">Search for it</a>.</p>');
})();
</script>
<noscript><p>Enable JavaScript, or go to <a href="../">the browser</a>.</p></noscript>""" % modmap)
    with open(os.path.join(OUT, "find", "index.html"), "w", encoding="utf-8") as fh:
        fh.write(page("find — GFNBoundsLean", find_body, depth=1, extra=find_extra))

    # ---- leanref.js : the blueprint prints `[[Name]]` citations as plain monospace. This turns
    # them into links at read time, which keeps `content.tex` and its six lint gates out of the
    # blast radius of a cosmetic change.
    short_map = {}
    for n, d in decls.items():
        for prefix in ("GFNBounds.Doubling.", "GFNBounds."):
            if n.startswith(prefix):
                short_map.setdefault(n[len(prefix):], [n, d["module"]])
    with open(os.path.join(OUT, "leanref.js"), "w", encoding="utf-8") as fh:
        fh.write("// Generated by scripts/lean_browser.py.\n"
                 "var SHORT=%s;\n" % json.dumps(short_map, ensure_ascii=False,
                                                separators=(",", ":")))
        fh.write("""
// The tag is `defer`, so the document is already parsed when this runs. Do NOT wait for
// DOMContentLoaded: the blueprint pages pull MathJax from a CDN with a parser-blocking
// script tag, and when that stalls the event can arrive far too late or not at all.
(function ready(fn) {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', fn);
  else fn();
})(function () {
  document.querySelectorAll('span.ttfamily > small.small').forEach(function (el) {
    var hit = SHORT[el.textContent.trim()];
    if (!hit) return;
    var a = document.createElement('a');
    a.href = '../lean/m/' + hit[1] + '.html#' + encodeURIComponent(hit[0]);
    a.className = 'lean_decl';
    a.title = hit[0];
    var p = el.parentNode;
    p.parentNode.insertBefore(a, p);
    a.appendChild(p);
  });
});
""")

    # ---- machine twin
    with open(os.path.join(OUT, "facts.json"), "w", encoding="utf-8") as fh:
        json.dump({"meta": meta, "declarations": decls}, fh,
                  ensure_ascii=False, separators=(",", ":"))

    print("lean_browser: %d declarations (%d shown, %d generated) in %d modules -> browser/"
          % (meta["total"], meta["shown"], meta["total"] - meta["shown"], meta["modules"]))
    return decls, mod_of, blueprint, meta


def verify(decls, mod_of, blueprint, meta):
    bad = []
    pages = {f[:-5] for f in os.listdir(os.path.join(OUT, "m")) if f.endswith(".html")}
    mods = {d["module"] for d in decls.values()}
    if pages != mods:
        bad.append("module pages %d != modules %d" % (len(pages), len(mods)))

    seen = {}
    for f in sorted(os.listdir(os.path.join(OUT, "m"))):
        with open(os.path.join(OUT, "m", f), encoding="utf-8") as fh:
            for m in re.finditer(r'<article id="([^"]+)"', fh.read()):
                seen[html.unescape(m.group(1))] = seen.get(html.unescape(m.group(1)), 0) + 1
    dup = [k for k, v in seen.items() if v > 1]
    if dup:
        bad.append("%d declarations rendered more than once (e.g. %s)" % (len(dup), dup[0]))
    missing = set(decls) - set(seen)
    if missing:
        bad.append("%d declarations never rendered (e.g. %s)" % (len(missing), sorted(missing)[0]))

    dangling = set()
    for n, d in decls.items():
        for t in d.get("uses_type", []) + d.get("uses_value", []):
            if t not in mod_of:
                dangling.add(t)
    if dangling:
        bad.append("%d dangling dependency targets (e.g. %s)"
                   % (len(dangling), sorted(dangling)[0]))

    if blueprint:
        absent = sorted(blueprint - set(decls))
        if absent:
            bad.append("%d blueprint \\lean{} names have no declaration: %s"
                       % (len(absent), ", ".join(absent[:5])))
        else:
            print("verify: all %d blueprint \\lean{} names resolve" % len(blueprint))

    for f in ("index.html", "find/index.html", "leanref.js", "lean-browser.css",
              "lean-browser.js", "facts.json"):
        if not os.path.exists(os.path.join(OUT, f)):
            bad.append("missing %s" % f)

    if bad:
        for b in bad:
            print("verify: FAIL " + b, file=sys.stderr)
        return 1
    print("verify: %d declarations, %d module pages, 0 duplicates, 0 dangling targets"
          % (len(decls), len(pages)))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--allow-stale", action="store_true")
    a = ap.parse_args()
    decls, mod_of, blueprint, meta = build(allow_stale=a.allow_stale)
    return verify(decls, mod_of, blueprint, meta) if a.verify else 0


if __name__ == "__main__":
    sys.exit(main())
