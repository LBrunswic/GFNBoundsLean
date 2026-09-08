#!/usr/bin/env python3
"""Render the map of the Lean library that a sub-session reads before it touches anything.

Three generated files, do not edit them by hand:

  * `docs/REPO-MAP.md`   — the orientation map. Small enough to read whole before starting.
  * `docs/REPO-INDEX.md` — every declaration with its statement, plus the name index. Grep this;
                           do not read it whole.
  * `docs/repo-map.json` — the same data for tooling.

For every `.lean` file in `GFNBounds/` and `scaffold/` this extracts:

  * the title line of the module docstring, and whether the file carries a `SCOPE` disclosure
  * the paper labels the file certifies (from the bolded header line and the `#print axioms`
    comments), cross-checked against `paper-map.json` for status and bucket
  * the internal imports, hence the layering
  * every declaration: kind, fully-qualified name, the statement up to `:=`, its doc first line

and then renders what a prover actually needs:

  1. **Loose ends** — files the build compiles that are untracked or unimported. This tree is
     worked in concurrently, so that list is rarely empty.
  2. **Layer order** — what may import what.
  3. **The general-purpose shelf** — declarations whose statement mentions none of the doubling
     types (`St`, `Setting`, `Stat`, `pstar`). These are ordinary real analysis proved here
     because Mathlib lacked them in this shape; they are the first place to look before proving
     an analysis fact from scratch, and the first candidates to migrate to `~/LeanAI/library`.
  4. **Per file** — what each file is for, in `REPO-MAP.md`; its full declaration inventory, in
     `REPO-INDEX.md`.
"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIBS = (("GFNBounds", "GFNBounds", "strict"), ("scaffold", "GFNBoundsScaffold", "scaffold"))

KINDS = "theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|example"
DECL_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*)"
    r"(?P<kind>" + KINDS + r")(?![\w'])"
    r"(?:\s+(?P<name>[A-Za-z_α-ωΑ-Ω][\w.'α-ωΑ-Ω₀-₉]*))?")
LABEL_RE = re.compile(r"(?:theo|lem|prop|cor|def|rem):doubling[a-z_0-9]*")
DOUBLING_TYPES = ("St", "Setting", "Stat", "pstar", "OnChain", "PreStat", "CutBalanceSeq",
                  "HasDouble", "window", "epsCS", "Decay", "CutBal")
# `D` is the standing `variable (D : Decay)`: a statement mentioning `D.p` is decay-specific too.
DECAY_VAR_RE = re.compile(r"(?<![\w.])D\.")

OPENERS, CLOSERS = "([{⟨", ")]}⟩"


def comment_depth(line, depth):
    """Block-comment nesting after this line, given the depth before it.

    Lean block comments nest, and `/--` and `/-!` are block comments, so this cannot be done
    by stripping `--` first: that would eat the `-` of `/--` and leave a stray `/`. Walks the
    line instead. String literals are not tracked -- a `/-` inside a string would fool it, and
    there is none in this library."""
    j = 0
    while j < len(line):
        if depth > 0:
            if line.startswith("-/", j):
                depth -= 1
                j += 2
                continue
            if line.startswith("/-", j):
                depth += 1
                j += 2
                continue
        else:
            if line.startswith("/-", j):
                depth += 1
                j += 2
                continue
            if line.startswith("--", j):
                break          # a line comment: nothing after it can open a block
        j += 1
    return depth


def depth_delta(s):
    """Bracket balance of a line, ignoring `--` comments and string literals (good enough here)."""
    s = re.sub(r"--.*$", "", s)
    return sum(1 for c in s if c in OPENERS) - sum(1 for c in s if c in CLOSERS)


def statement_of(lines, i, kind):
    """The declaration at line `i`, from its keyword up to the `:=` (or `where`) that opens the
    body. Returns (text, line_after)."""
    buf, depth = [], 0
    for k in range(i, min(i + 30, len(lines))):
        raw = lines[k]
        # A signature never spans another declaration. This guard alone makes a mis-detected
        # declaration harmless instead of destructive: it stops at the real one rather than
        # consuming it.
        if k > i and DECL_RE.match(raw):
            return " ".join(" ".join(buf).split()), k
        line = re.sub(r"--.*$", "", raw).rstrip()
        cut = None
        d = depth
        j = 0
        while j < len(line):
            c = line[j]
            if c in OPENERS:
                d += 1
            elif c in CLOSERS:
                d -= 1
            elif d == 0 and line.startswith(":=", j):
                cut = j
                break
            elif d == 0 and re.match(r"\bwhere\b", line[j:]) and (j == 0 or not line[j-1].isalnum()):
                cut = j
                break
            j += 1
        if cut is not None:
            buf.append(line[:cut])
            return " ".join(" ".join(buf).split()), k + 1
        buf.append(line)
        depth += depth_delta(raw)
        # an `inductive` body starts with `|` on the next line. Only `inductive`: a `|` at the
        # head of a continuation line is far more often the opening bar of an `|x|`.
        # `inductive`, and equation-style `def`/`abbrev`, put the body's first `|` on the next
        # line with no `:=` anywhere. Restricted to those kinds and to depth 0, because a `|`
        # heading a continuation line is otherwise far more often the opening bar of `|x|`.
        if (kind in ("inductive", "def", "abbrev") and k + 1 < len(lines) and depth <= 0
                and ":" in " ".join(buf)
                and re.match(r"^\s*\|", lines[k + 1])):
            return " ".join(" ".join(buf).split()), k + 1
    return " ".join(" ".join(buf).split()), i + 1


def doc_above(lines, i):
    """The first sentence of the `/-- ... -/` doc comment attached above line `i`, if any."""
    k = i - 1
    while k >= 0 and re.match(r"^\s*@\[", lines[k]):
        k -= 1
    if k < 0 or "-/" not in lines[k]:
        return ""
    end = k
    while k >= 0 and not lines[k].lstrip().startswith("/--"):
        k -= 1
        if k < 0 or end - k > 40:
            return ""
    body = " ".join(lines[k:end + 1])
    body = body[body.index("/--") + 3:]
    body = body[:body.rindex("-/")] if "-/" in body else body
    body = " ".join(body.split())
    m = re.search(r"(?<![A-Z])\.(\s|$)", body)
    return (body[:m.start() + 1] if m else body).strip()


def module_header(text):
    """Title, paper labels and SCOPE flag from the `/-! ... -/` module docstring."""
    m = re.search(r"/-!(.*?)-/", text, re.S)
    if not m:
        return "", [], False
    doc = m.group(1)
    title = ""
    for ln in doc.splitlines():
        if ln.strip().startswith("# "):
            title = ln.strip()[2:].strip()
            break
    head = doc[:doc.find("\n\n", doc.find(title) if title else 0) + 400]
    return title, list(dict.fromkeys(LABEL_RE.findall(head))), "SCOPE" in doc


def scan(path, rel):
    text = open(path, encoding="utf-8").read()
    lines = text.splitlines()
    title, labels, scoped = module_header(text)
    imports = [ln.split()[1] for ln in lines if ln.startswith("import ")]
    variables = [" ".join(ln.split()) for ln in lines if ln.startswith("variable")]
    # Which lines *begin* inside a block comment. Without this, a prose line that happens to
    # start with a declaration keyword -- `theorem about the derivative. -/` -- is read as a
    # declaration named `about`, and `statement_of` then swallows the real one after it.
    in_comment, _d = [], 0
    for ln in lines:
        in_comment.append(_d > 0)
        _d = comment_depth(ln, _d)

    ns, decls, i = [], [], 0
    while i < len(lines):
        ln = lines[i]
        if in_comment[i]:
            i += 1
            continue
        if ln.startswith("namespace "):
            ns.append(ln.split()[1])
        elif ln.startswith("end ") or ln.rstrip() == "end":
            if ns:
                ns.pop()
        elif ln.startswith("section"):
            ns.append(None)
        m = DECL_RE.match(ln)
        if m and not ln.startswith("import"):
            stmt, nxt = statement_of(lines, i, m.group("kind"))
            name = m.group("name") or "_"
            prefix = ".".join(p for p in ns if p)
            decls.append({
                "name": name,
                "full": (prefix + "." + name) if prefix and name != "_" else name,
                "kind": m.group("kind"),
                "line": i + 1,
                "attrs": " ".join(m.group("attrs").split()),
                "private": "private" in (m.group("mods") or ""),
                "statement": stmt,
                "doc": doc_above(lines, i),
            })
            i = max(nxt, i + 1)
            continue
        i += 1
    return {"file": rel, "title": title, "labels": labels, "scope_disclosed": scoped,
            "imports": imports, "variables": variables, "lines": len(lines), "decls": decls}


def is_general(d):
    """A statement mentioning none of the doubling types: ordinary analysis, reusable elsewhere."""
    if d["kind"] in ("structure", "inductive", "class", "instance") or d["private"]:
        return False
    if d["name"] in ("_", "example"):
        return False
    # a declaration living inside `Decay`, `Stat`, `Setting`, … is about that object whatever its
    # signature says: `Decay.tau : ℝ` mentions nothing, and is not reusable outside the appendix.
    if any(("." + t + ".") in ("." + d["full"]) for t in DOUBLING_TYPES):
        return False
    body = d["statement"]
    if DECAY_VAR_RE.search(body):
        return False
    return not any(re.search(r"(?<![\w.])%s(?![\w'])" % t, body) for t in DOUBLING_TYPES)


def git_tracked():
    try:
        out = subprocess.check_output(["git", "-C", ROOT, "ls-files", "*.lean"], text=True,
                                      stderr=subprocess.DEVNULL)
        return set(out.split())
    except Exception:
        return None


def reachable(files):
    """Modules reachable by `import` from the two root modules."""
    by_mod = {f["file"][:-5].replace("/", ".").replace("scaffold.", ""): f for f in files}
    seen, stack = set(), ["GFNBounds", "GFNBoundsScaffold"]
    while stack:
        m = stack.pop()
        if m in seen or m not in by_mod:
            continue
        seen.add(m)
        stack.extend(by_mod[m]["imports"])
    return seen


def build():
    files = []
    for sub, _mod, kind in LIBS:
        for dirpath, _, names in os.walk(os.path.join(ROOT, sub)):
            for n in sorted(names):
                if n.endswith(".lean"):
                    p = os.path.join(dirpath, n)
                    rec = scan(p, os.path.relpath(p, ROOT))
                    rec["library"] = kind
                    files.append(rec)
    for extra in ("GFNBounds.lean",):
        p = os.path.join(ROOT, extra)
        if os.path.exists(p) and not any(f["file"] == extra for f in files):
            rec = scan(p, extra)
            rec["library"] = "strict"
            files.append(rec)
    files.sort(key=lambda f: (f["library"] != "strict", f["file"]))
    tracked = git_tracked()
    reach = reachable(files)
    for f in files:
        f["tracked"] = None if tracked is None else f["file"] in tracked
        f["root_reachable"] = f["file"][:-5].replace("/", ".").replace("scaffold.", "") in reach
    return files


def status_by_file():
    try:
        m = json.load(open(os.path.join(ROOT, "paper-map.json"), encoding="utf-8"))
    except Exception:
        return {}, {}
    by_file, by_label = {}, {}
    for st in m["statements"]:
        by_label[st["label"]] = st
        for f in st["lean_files"]:
            by_file.setdefault(f, []).append(st)
    return by_file, by_label


MARK = {"closed": "✅", "partial": "\U0001f7e1", "open": "⬜", "stale": "⚠️"}


def render(files):
    by_file, by_label = status_by_file()
    modname = {f["file"]: f["file"][:-5].replace("/", ".").replace("scaffold.", "") for f in files}
    out = []
    w = out.append
    ndecl = sum(len(f["decls"]) for f in files)
    w("# Map of the Lean library\n")
    w("Generated by `scripts/repo_map.py`; do not edit by hand. "
      "Machine-readable twin: `docs/repo-map.json`.\n")
    w("**%d files · %d declarations · %d lines.** Statement coverage is a different question and "
      "lives in [`COVERAGE.md`](COVERAGE.md); this file answers *where is the lemma I need*.\n"
      % (len(files), ndecl, sum(f["lines"] for f in files)))

    w("\n## How to read this\n")
    w("- The **strict** library `GFNBounds/` is `sorry`-free by compiler enforcement. Anything "
      "listed under it is available to build on with no caveat.\n"
      "- The **scaffold** library `scaffold/GFNBoundsScaffold/` may contain tagged `sorry`s. "
      "`GFNBounds` never imports it. Building on a scaffold declaration means your result "
      "inherits that `sorry`, and it must stay in the scaffold too.\n"
      "- A file's **labels** are the `app_doubling.tex` statements it certifies, with the status "
      "`paper-map.json` records for them.\n"
      "- Build one module while iterating: `lake build GFNBounds.Doubling.Tail`.\n"
      "- Looking for a specific lemma? `grep -n '<name>' docs/REPO-INDEX.md` — that file has every "
      "declaration with its statement, and is too big to read whole.\n")

    loose = [f for f in files if f["tracked"] is False or not f["root_reachable"]]
    if loose:
        w("\n## Loose ends\n")
        w("Files the build compiles (the lakefile globs `GFNBounds.*`, so **every** `.lean` under "
          "the directory is built and is therefore `sorry`-free) but which are not yet committed, "
          "or are not imported by the root module. Treat them as work in progress by another "
          "session: **read before extending, and do not assume the master session knows they "
          "exist.**\n")
        w("\n| file | in git | imported by root | what it is |\n|---|---|---|---|")
        for f in loose:
            w("| `%s` | %s | %s | %s |" % (
                f["file"], "yes" if f["tracked"] else "**no**",
                "yes" if f["root_reachable"] else "**no**", f["title"] or "—"))
        w("")

    w("\n## Layer order\n")
    w("Imports inside the project, in dependency order. A file may only use what its imports "
      "reach; adding an import is a real decision, so check here first.\n")
    w("\n| module | imports (internal) |\n|---|---|")
    for f in files:
        if f["file"] in ("GFNBounds.lean", "scaffold/GFNBoundsScaffold.lean"):
            continue
        inner = [i for i in f["imports"] if i.startswith(("GFNBounds.", "GFNBoundsScaffold."))]
        w("| `%s` | %s |" % (modname[f["file"]],
                             ", ".join("`%s`" % i.split(".")[-1] for i in inner) or "*(Mathlib only)*"))

    w("\n## The general-purpose shelf\n")
    w("Declarations whose statement mentions none of `St`, `Setting`, `Stat`, `pstar` — ordinary "
      "real analysis, proved here because Mathlib v4.31.0 lacked it in this shape. **Look here "
      "before proving an analysis fact from scratch.** These are also the migration candidates "
      "for `~/LeanAI/library`, which is pinned to the same Mathlib commit.\n")
    shelf = [(f, d) for f in files for d in f["decls"] if is_general(d)]
    w("Names only here, grouped by file, so this stays scannable — the statements are in "
      "[`REPO-INDEX.md`](REPO-INDEX.md) under the same heading.\n")
    byf = {}
    for f, d in shelf:
        byf.setdefault(f["file"], []).append(d["name"])
    w("\n| file | declarations |\n|---|---|")
    for fn, names in byf.items():
        w("| `%s` | %s |" % (fn.split("/")[-1], ", ".join("`%s`" % n for n in names)))
    w("\n*%d of %d declarations.*\n" % (len(shelf), ndecl))

    w("\n## Files\n")
    w("What each file is for. The declaration inventory is in "
      "[`REPO-INDEX.md`](REPO-INDEX.md) — grep that one.\n")
    w("\n| file | what it is | certifies | decls |\n|---|---|---|---|")
    for f in files:
        if not f["decls"] and not f["title"]:
            continue
        labs = f["labels"] or [s["label"] for s in by_file.get(f["file"], [])]
        cert = ", ".join(
            "%s `%s`%s" % (MARK.get(by_label.get(l, {}).get("status", ""), ""), l,
                           (" %s" % by_label[l]["bucket"]) if by_label.get(l, {}).get("bucket") else "")
            for l in labs) or "—"
        title = f["title"] or "—"
        if f["scope_disclosed"]:
            title += " **[SCOPE]**"
        w("| `%s` | %s | %s | %d |" % (f["file"].replace("GFNBounds/Doubling/", "")
                                       .replace("scaffold/GFNBoundsScaffold/Doubling/", "scaffold:"),
                                       title, cert, len(f["decls"])))
    w("\n**[SCOPE]** marks a file carrying a `SCOPE (disclosed)` section: it proves less than its "
      "label, and says so. Read that section before extending the file.\n")
    return "\n".join(out)


def render_index(files):
    by_file, by_label = status_by_file()
    modname = {f["file"]: f["file"][:-5].replace("/", ".").replace("scaffold.", "") for f in files}
    out = []
    w = out.append
    w("# Declaration index\n")
    w("Generated by `scripts/repo_map.py`; do not edit by hand. **Grep this file — do not read it "
      "whole.** Orientation lives in [`REPO-MAP.md`](REPO-MAP.md).\n")
    w("```\ngrep -n 'powerTail' docs/REPO-INDEX.md\n```\n")

    shelf = [(f, d) for f in files for d in f["decls"] if is_general(d)]
    w("\n## The general-purpose shelf\n")
    w("Declarations whose statement mentions none of `St`, `Setting`, `Stat`, `pstar` — ordinary "
      "real analysis, proved here because Mathlib v4.31.0 lacked it in this shape. **Look here "
      "before proving an analysis fact from scratch.**\n")
    w("\n| declaration | file | statement |\n|---|---|---|")
    for f, d in shelf:
        w("| `%s` | `%s` | `%s` |" % (d["name"], f["file"].split("/")[-1],
                                      d["statement"].replace("|", "\\|")))
    w("")

    w("\n## Every declaration, by file\n")
    for f in files:
        if not f["decls"]:
            continue
        w("\n### `%s`\n" % f["file"])
        if f["title"]:
            w("**%s**  \n" % f["title"])
        bits = ["%s library" % f["library"], "%d lines" % f["lines"],
                "%d declarations" % len(f["decls"])]
        if f["scope_disclosed"]:
            bits.append("carries a **SCOPE** disclosure — read it before extending")
        w("*%s.*\n" % "; ".join(bits))
        labs = f["labels"] or [s["label"] for s in by_file.get(f["file"], [])]
        if labs:
            w("\nCertifies: " + ", ".join(
                "%s `%s`%s" % (MARK.get(by_label.get(l, {}).get("status", ""), ""), l,
                               (" (bucket %s)" % by_label[l]["bucket"])
                               if by_label.get(l, {}).get("bucket") else "")
                for l in labs) + "\n")
        if f["variables"]:
            w("\nIn scope: " + ", ".join("`%s`" % v for v in f["variables"]) + "\n")
        w("\n| ln | kind | name | statement |\n|---|---|---|---|")
        for d in f["decls"]:
            w("| %d | %s%s | `%s` | `%s` |" % (
                d["line"], d["kind"], " " + d["attrs"] if d["attrs"] else "",
                d["name"], d["statement"].replace("|", "\\|")))
    w("\n## Name index\n")
    w("| name | module |\n|---|---|")
    for name, mod in sorted({d["name"]: modname[f["file"]] for f in files for d in f["decls"]}.items()):
        w("| `%s` | `%s` |" % (name, mod))
    w("")
    return "\n".join(out)


def main():
    files = build()
    with open(os.path.join(ROOT, "docs", "repo-map.json"), "w", encoding="utf-8") as fh:
        json.dump({"files": files}, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
    with open(os.path.join(ROOT, "docs", "REPO-MAP.md"), "w", encoding="utf-8") as fh:
        fh.write(render(files))
    with open(os.path.join(ROOT, "docs", "REPO-INDEX.md"), "w", encoding="utf-8") as fh:
        fh.write(render_index(files))
    print("repo_map: %d files, %d declarations"
          % (len(files), sum(len(f["decls"]) for f in files)))


if __name__ == "__main__":
    main()
