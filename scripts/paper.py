"""Shared LaTeX extraction for the GFN Bounds Lean library.

Locates a theorem-like environment by its `\\label{...}` in one of the paper's source files,
returns the statement block together with the proof that follows it, and digests it.
Per-*statement* digests rather than a whole-file digest is the point: an edit to
`lem:doubling_doeblin` must not mark `lem:doubling_percut` stale.

**Multi-source since 2026-09-08.** The library's charter widened from Appendix H alone to
Appendices A, B and H, so a statement carries the file it comes from. `SOURCES` maps a source
filename to its appendix letter; `paper-map.json` rows carry a `source` field, defaulting to
`app_doubling.tex` for the Appendix-H rows written before the widening.
"""
import hashlib, os, re

PAPER_DIR = os.path.expanduser("~/Dropbox/GFN Bounds")

#: source filename -> appendix letter. The library covers these and only these.
SOURCES = {
    "proofs.tex": "A",
    "silva_comparison.tex": "B",
    "app_doubling.tex": "H",
}

DEFAULT_SOURCE = "app_doubling.tex"
DEFAULT_TEX = os.path.join(PAPER_DIR, DEFAULT_SOURCE)
ENVS = ("definition", "lemma", "proposition", "theorem", "corollary", "remark")


def paper_dir() -> str:
    return os.environ.get("GFNBOUNDS_PAPER_DIR", PAPER_DIR)


def tex_path(source: str = DEFAULT_SOURCE) -> str:
    """Absolute path of one source file. `GFNBOUNDS_TEX` still overrides, for the
    Appendix-H-only callers that predate the widening."""
    override = os.environ.get("GFNBOUNDS_TEX")
    if override and source == DEFAULT_SOURCE:
        return override
    return os.path.join(paper_dir(), source)


_CACHE = {}


def read_tex(source: str = DEFAULT_SOURCE, path=None):
    """Lines of one source file, cached — `trace_check` reads each of them once per statement."""
    key = path or tex_path(source)
    if key not in _CACHE:
        with open(key, encoding="utf-8") as fh:
            _CACHE[key] = fh.read().split("\n")
    return _CACHE[key]


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
