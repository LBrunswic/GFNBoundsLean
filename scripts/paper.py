"""Shared LaTeX extraction for the GFN Bounds Lean library.

Locates a theorem-like environment by its `\\label{...}` in `app_doubling.tex`, returns the
statement block together with the proof that follows it, and digests it. Per-*statement* digests
rather than a whole-file digest is the point: an edit to `lem:doubling_doeblin` must not mark
`lem:doubling_percut` stale.
"""
import hashlib, os, re

DEFAULT_TEX = os.path.expanduser("~/Dropbox/GFN Bounds/app_doubling.tex")
ENVS = ("definition", "lemma", "proposition", "theorem", "corollary", "remark")


def tex_path() -> str:
    return os.environ.get("GFNBOUNDS_TEX", DEFAULT_TEX)


def read_tex(path=None):
    with open(path or tex_path(), encoding="utf-8") as fh:
        return fh.read().split("\n")


def _match_end(lines, start, env):
    """Index of the `\\end{env}` closing the `\\begin{env}` at `start`, honouring nesting."""
    depth = 0
    for i in range(start, len(lines)):
        depth += lines[i].count("\\begin{%s}" % env)
        depth -= lines[i].count("\\end{%s}" % env)
        if depth == 0:
            return i
    return len(lines) - 1


def find_block(lines, label):
    """Return `(first_line, last_line)`, 1-indexed inclusive, of the statement carrying `label`
    together with the `proof` environment that immediately follows it, if any."""
    lab = "\\label{%s}" % label
    idx = next((i for i, ln in enumerate(lines) if lab in ln), None)
    if idx is None:
        return None
    start = None
    for i in range(idx, -1, -1):
        m = re.search(r"\\begin\{(%s)\}" % "|".join(ENVS), lines[i])
        if m:
            start, env = i, m.group(1)
            break
    if start is None:
        return None
    end = _match_end(lines, start, env)
    # absorb a following proof block, skipping blank lines
    j = end + 1
    while j < len(lines) and not lines[j].strip():
        j += 1
    if j < len(lines) and "\\begin{proof}" in lines[j]:
        end = _match_end(lines, j, "proof")
    return start + 1, end + 1


def digest(lines, span):
    """sha256 of the block, whitespace-normalised so that a reflow is not a content change."""
    body = " ".join(" ".join(lines[span[0] - 1: span[1]]).split())
    return hashlib.sha256(body.encode("utf-8")).hexdigest()
