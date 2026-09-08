#!/usr/bin/env python3
"""Keep `paper-map.json` honest against the paper's sources and the Lean sources.

Since 2026-09-08 the library covers **Appendices A, B and H**, so the map is multi-source: every
statement carries a `source` field naming one of `scripts/paper.py`'s `SOURCES`, defaulting to
`app_doubling.tex` for rows written before the widening.

Four invariants:
  (a) every mapped label still exists in its source .tex; if its lines moved, rewrite `tex_span`
  (b) every listed Lean declaration exists in its listed file
  (c) no orphan certificates: a Lean file citing a label DEFINED IN ONE OF THE SOURCES must be
      in the map. Before the widening this test matched only `…:doubling…`, which meant a file
      citing `theo:universality_L2_full` passed unchecked; it now covers every in-scope label.
  (d) per-statement digests: a changed LaTeX block flips `status` to "stale"

  --init [SOURCE] create/extend the map from a source (all labels, status "open");
                  SOURCE defaults to app_doubling.tex
  --reaffirm LBL  accept the current LaTeX block for LBL and clear "stale"
"""
import json, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAP = os.path.join(ROOT, "paper-map.json")


def load():
    with open(MAP, encoding="utf-8") as fh:
        return json.load(fh)


def save(m):
    with open(MAP, "w", encoding="utf-8") as fh:
        json.dump(m, fh, indent=2, ensure_ascii=False)
        fh.write("\n")


def lean_sources():
    out = {}
    for sub in ("GFNBounds", "scaffold"):
        for dirpath, _, names in os.walk(os.path.join(ROOT, sub)):
            for n in names:
                if n.endswith(".lean"):
                    p = os.path.join(dirpath, n)
                    out[os.path.relpath(p, ROOT)] = open(p, encoding="utf-8").read()
    return out


STATEMENT_LABEL = re.compile(r"\\label\{((?:theo|lem|prop|cor|def|rem|assum):[A-Za-z_0-9]+)\}")


def labels_of(source):
    """Every theorem-like label defined in one source file, in document order."""
    lines, out = paper.read_tex(source), []
    for ln in lines:
        for m in STATEMENT_LABEL.finditer(ln):
            if m.group(1) not in out:
                out.append(m.group(1))
    return out


def in_scope_labels():
    """Every label the library is chartered to certify — the union over `paper.SOURCES`."""
    out = {}
    for src in paper.SOURCES:
        for lab in labels_of(src):
            out[lab] = src
    return out


def do_init(source=paper.DEFAULT_SOURCE):
    """Extend the map with every statement of `source` that is not already mapped."""
    m = load() if os.path.exists(MAP) else {"statements": []}
    m.setdefault("paper", {"path": paper.tex_path(), "git_commit": git_commit(), "appendix": "H"})
    m["sources"] = {s: {"path": paper.tex_path(s), "appendix": a}
                    for s, a in paper.SOURCES.items()}
    known = {st["label"] for st in m["statements"]}
    lines, added = paper.read_tex(source), 0
    for lab in labels_of(source):
        if lab in known:
            continue
        span = paper.find_block(lines, lab)
        if span is None:
            continue
        m["statements"].append({
            "label": lab, "source": source, "tex_span": list(span),
            "block_sha256": paper.digest(lines, span),
            "lean_files": [], "decls": [], "status": "open", "bucket": "", "scope_notes": ""})
        added += 1
    save(m)
    print("%s: added %d statements from %s (%d total)"
          % (MAP, added, source, len(m["statements"])))


def git_commit():
    try:
        return subprocess.check_output(
            ["git", "-C", os.path.dirname(paper.tex_path()), "rev-parse", "--short", "HEAD"],
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown"


def main():
    if "--init" in sys.argv:
        i = sys.argv.index("--init")
        source = sys.argv[i + 1] if len(sys.argv) > i + 1 else paper.DEFAULT_SOURCE
        return do_init(source)
    m, src = load(), lean_sources()
    reaffirm = sys.argv[sys.argv.index("--reaffirm") + 1] if "--reaffirm" in sys.argv else None
    fail, moved, stale = [], [], []
    mapped_labels = {s["label"] for s in m["statements"]}

    for st in m["statements"]:
        lab = st["label"]
        source = st.setdefault("source", paper.DEFAULT_SOURCE)
        lines = paper.read_tex(source)
        span = paper.find_block(lines, lab)
        if span is None:                                            # (a)
            fail.append("label %s no longer exists in %s" % (lab, source))
            continue
        if list(span) != st["tex_span"]:
            st["tex_span"] = list(span)
            moved.append(lab)
        dig = paper.digest(lines, span)                             # (d)
        if dig != st["block_sha256"]:
            if reaffirm == lab:
                st["block_sha256"], st["status"] = dig, st.get("prev_status", st["status"])
                st.pop("prev_status", None)
            else:
                if st["status"] != "stale":
                    st["prev_status"] = st["status"]
                st["status"] = "stale"
                stale.append(lab)
        elif st["status"] == "stale":
            # the block came back — a reverted edit, or a run against a different .tex
            st["status"] = st.pop("prev_status", "open")
            print("note: %s is no longer stale; status restored to %s" % (lab, st["status"]))
        for f in st["lean_files"]:                                  # (b)
            if f not in src:
                fail.append("%s: listed Lean file %s does not exist" % (lab, f))
        for d in st["decls"]:
            short = d.split(".")[-1]
            # `(?![\w'])` rather than `\b`: Lean names may end in a prime, after which
            # `\b` would demand a word character.
            pat = (r"\b(theorem|lemma|def|structure|inductive|abbrev|instance)\s+"
                   r"(?:[A-Za-z_][\w.']*\.)?%s(?![\w'])" % re.escape(short))
            if not any(re.search(pat, src[f]) for f in st["lean_files"] if f in src):
                fail.append("%s: declaration %s not found in its listed files" % (lab, d))

    scoped = in_scope_labels()                                      # (c)
    for f, text in src.items():
        cited = set(re.findall(r"((?:theo|lem|prop|cor|def|rem|assum):[A-Za-z_0-9]+)", text))
        for lab in sorted(cited & set(scoped)):
            if lab not in mapped_labels:
                fail.append("%s cites %s (%s), which has no paper-map.json row"
                            % (f, lab, scoped[lab]))

    m["paper"]["git_commit"] = git_commit()
    m["sources"] = {s0: {"path": paper.tex_path(s0), "appendix": a}
                    for s0, a in paper.SOURCES.items()}
    save(m)
    for lab in moved:
        print("note: %s moved in the .tex; tex_span rewritten" % lab)
    for lab in stale:
        print("STALE: %s — its LaTeX block changed. Re-read it, then "
              "`python3 scripts/trace_check.py --reaffirm %s`" % (lab, lab))
    for e in fail:
        print("FAIL: %s" % e)
    if fail or stale:
        sys.exit(1)
    by_source = {}
    for st in m["statements"]:
        by_source[st.get("source", paper.DEFAULT_SOURCE)] = \
            by_source.get(st.get("source", paper.DEFAULT_SOURCE), 0) + 1
    print("trace_check: %d statements mapped (%s), all digests current"
          % (len(m["statements"]),
             ", ".join("%s %d" % (paper.SOURCES.get(k, k), v)
                       for k, v in sorted(by_source.items()))))


if __name__ == "__main__":
    main()
