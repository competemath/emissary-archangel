#!/usr/bin/env python3
"""The tentative record files of a library: ONE rule for every job that reads tengoku's data/tentative.

sources.json lists a library's files under `tentative` (flt-anthropic: flt-anthropic-001.jsonl .. -003.jsonl; lean-pool, tauceti, formal-math, navier-stokes-euler, openai-math and
others do too); a library without the field has <key>.jsonl. The directory data/tentative/<key>/ is read in every case. The setup workflows have always read this list; the bump
workflows read <key>.jsonl and <key>/*.jsonl only, so the bump of flt-anthropic (5 Nov 2026) found 0 entries in 30,961 modules and stopped in compose.

  python3 scripts/bump/tentative_files.py sparse sources.json KEY          the paths for `git sparse-checkout set --no-cone` (one line, space separated)
  python3 scripts/bump/tentative_files.py globs  sources.json KEY ROOT     the comma list of globs for --tentative, under ROOT (the tengoku checkout)
"""
import glob
import json
import sys


def names(sources: dict, key: str) -> list[str]:
    """The files of data/tentative that hold the library's records (as sources.json lists them; <key>.jsonl when it lists none)."""
    return list(sources["sources"][key].get("tentative", [key + ".jsonl"]))


def sparse_paths(sources: dict, key: str) -> list[str]:
    return [f"/data/tentative/{n}" for n in names(sources, key)] + [f"/data/tentative/{key}/"]


def covered_by_directory(key: str, name: str) -> bool:
    """A listed file inside the library's own directory (lean-pool/records-001.jsonl) is read by the directory's glob: not twice (Gate 2 expands each pattern on its own)."""
    return name.startswith(key + "/") and name.endswith(".jsonl") and "/" not in name[len(key) + 1 :]


def globs(sources: dict, key: str, root: str) -> list[str]:
    return [f"{root}/data/tentative/{n}" for n in names(sources, key) if not covered_by_directory(key, n)] + [f"{root}/data/tentative/{key}/*.jsonl"]


def files(sources: dict, key: str, root: str) -> list[str]:
    out: list[str] = []
    for pattern in globs(sources, key, root):
        out += [p for p in sorted(glob.glob(pattern)) if p not in out]  # a library may list a file inside its directory (lean-pool): once
    return out


def main(argv: list[str]) -> int:
    if len(argv) < 4 or argv[1] not in ("sparse", "globs") or (argv[1] == "globs" and len(argv) < 5):
        print(__doc__, file=sys.stderr)
        return 2
    sources = json.load(open(argv[2]))
    key = argv[3]
    if key not in sources["sources"]:
        print(f"tentative_files: {key} is not in {argv[2]}", file=sys.stderr)
        return 1
    if argv[1] == "sparse":
        print(" ".join(sparse_paths(sources, key)))
    else:
        print(",".join(globs(sources, key, argv[4])))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
