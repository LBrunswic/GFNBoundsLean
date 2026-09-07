#!/usr/bin/env python3
"""Keep `paper-map.json` honest against `app_doubling.tex` and the Lean sources.

Four invariants:
  (a) every mapped label still exists in the .tex; if its lines moved, rewrite `tex_span`
  (b) every listed Lean declaration exists in its listed file
  (c) no orphan certificates: a Lean file citing a doubling label must be in the map
  (d) per-statement digests: a changed LaTeX block flips `status` to "stale"

  --init          create/extend the map from the .tex (all labels, status "open")
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


def do_init():
    lines = paper.read_tex()
    labels = []
    for ln in lines:
        for m in re.finditer(r"\\label\{((?:theo|lem|prop|cor|def|rem):doubling[^}]*)\}", ln):
            if m.group(1) not in labels:
                labels.append(m.group(1))
    m = {"paper": {"path": paper.tex_path(), "git_commit": git_commit(), "appendix": "H"},
         "statements": []}
    for lab in labels:
        span = paper.find_block(lines, lab)
        if span is None:
            continue
        m["statements"].append({
            "label": lab, "tex_span": list(span), "block_sha256": paper.digest(lines, span),
            "lean_files": [], "decls": [], "status": "open", "bucket": "", "scope_notes": ""})
    save(m)
    print("wrote %s with %d statements" % (MAP, len(m["statements"])))


def git_commit():
    try:
        return subprocess.check_output(
            ["git", "-C", os.path.dirname(paper.tex_path()), "rev-parse", "--short", "HEAD"],
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown"


def main():
    if "--init" in sys.argv:
        return do_init()
    m, lines, src = load(), paper.read_tex(), lean_sources()
    reaffirm = sys.argv[sys.argv.index("--reaffirm") + 1] if "--reaffirm" in sys.argv else None
    fail, moved, stale = [], [], []
    mapped_labels = {s["label"] for s in m["statements"]}

    for st in m["statements"]:
        lab = st["label"]
        span = paper.find_block(lines, lab)
        if span is None:                                            # (a)
            fail.append("label %s no longer exists in the .tex" % lab)
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

    for f, text in src.items():                                     # (c)
        for lab in set(re.findall(r"((?:theo|lem|prop|cor|def|rem):doubling[a-z_0-9]*)", text)):
            if lab not in mapped_labels:
                fail.append("%s cites unmapped label %s" % (f, lab))

    m["paper"]["git_commit"] = git_commit()
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
    print("trace_check: %d statements mapped, all digests current" % len(m["statements"]))


if __name__ == "__main__":
    main()
