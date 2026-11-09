#!/usr/bin/env python3
"""seed_tentative.py: the statement records of FATE-X, in the shape scripts/setup-source.mjs seeds its queue from.

setup-source.mjs reads tengoku's data/tentative/<key>.jsonl (one record per harvested declaration). FATE-X is not harvested
into tengoku and must not be, so this writes the same records, for the upstream checkout at its pinned commit, to a file
that exists only on the runner (EMISSARY_TENTATIVE_DIR). Nothing here is written to the tree or to a bank.

  seed_tentative.py --repo infra/fate-x/repo --commit <sha> --repo-url https://github.com/frenzymath/FATE-X --out tentative/fate-x.jsonl

One record per FATEX/<n>.lean: the file's single theorem or lemma, its statement up to `:=`, and its proof text (`sorry`).
A file with no theorem, or with a second one, is an error: the attestation pairs one original with one translation.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable)[ \t]+)*(?:theorem|lemma)[ \t]+([^\s({\[:]+)", re.M)


def strip_comments(text: str) -> str:
    """The text with block comments (nested) and line comments blanked out, line structure and offsets kept (spaces for every character but a newline)."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if two == "/-":
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth:
            if text[i] != "\n":
                out[i] = " "
            i += 1
        elif two == "--":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


def record(path: Path, index: int, commit: str, repo_url: str) -> dict:
    text = path.read_text()
    bare = strip_comments(text)
    hits = list(DECL.finditer(bare))
    if len(hits) != 1:
        raise SystemExit(f"{path}: {len(hits)} theorem/lemma declarations, expected exactly 1")
    m = hits[0]
    line = bare.count("\n", 0, m.start()) + 1
    assign = bare.find(":=", m.end())
    if assign < 0:
        raise SystemExit(f"{path}: no `:=` after the declaration")
    return {
        "name": m.group(1),
        "library": "fate-x",
        "statement": text[m.start() : assign].strip(),
        "proof": text[assign:].split("end Problem", 1)[0].strip(),
        "source_url": f"{repo_url}/blob/{commit}/FATEX/{index}.lean#L{line}",
    }


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--commit", required=True)
    ap.add_argument("--repo-url", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--count", type=int, default=100)
    a = ap.parse_args(argv)
    repo = Path(a.repo)
    rows = [record(repo / "FATEX" / f"{i}.lean", i, a.commit, a.repo_url) for i in range(1, a.count + 1)]
    out = Path(a.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    print(f"seed_tentative: {len(rows)} records -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
