#!/usr/bin/env python3
"""canonicalise_bundle.py --bundle DIR [--bundle DIR ...] — every `.lean` module of the bundle directories, rewritten in place in the canonical form of tengoku's
scripts/isnad_tag.py (`canonical_text`: the isnad tags out, the whitespace before every docstring's closing `-/` normalised).

Why: once tengoku's intake lane is born tagged (tengoku docs/isnad.md, "Born tagged"; the repository variable TENGOKU_ISNAD_REQUIRED is 1 in both repositories), a PR
carries its modules with their isnad tags, and tengoku's gate rebuilds the attested archive from them by taking each module through `canonical_text`. That function is
not the identity on a module with a one-line docstring (`/-- Words. -/` is `/-- Words.-/`), so the factory's archive must hold the same form, or the attestation would not
match the gate's bytes. The step runs in the attest job, before the archive is packed, and only when the variable is 1; without it nothing here runs and the archive is the
bytes the factory wrote, as before.

`isnad_tag.py` beside this file is a VERBATIM copy of tengoku's scripts/isnad_tag.py, as `bundle_tar.py` is of tengoku's scripts/ci/bundle_tar.py: the attest job holds the
OIDC token and the attestation permission, so it runs no code that was fetched while it ran, and it does not execute tengoku's main as it happens to be. Both copies are pinned by
the same sha256 (test_canonicalise_bundle.py here, test_isnad_copy.py in tengoku) and by the same golden cases, so a change on one side fails a test until it is made on the other.
A file that is not UTF-8 is left alone (tengoku's gate leaves it alone too and fails it on its own account), and so is anything but a regular `.lean` file inside a bundle
directory."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))  # the copy of tengoku's isnad_tag.py beside this file
from isnad_tag import canonical_text  # noqa: E402


def canonicalise_dir(d: str, canonical=canonical_text) -> tuple[int, int, int]:
    """(modules seen, modules rewritten, modules left alone because they are not UTF-8)"""
    root = Path(d).resolve()
    seen = changed = skipped = 0
    for p in sorted(root.rglob("*.lean")):
        if not p.is_file() or p.is_symlink() or root not in p.resolve().parents:
            continue
        seen += 1
        raw = p.read_bytes()
        try:
            new = canonical(raw.decode("utf-8")).encode("utf-8")
        except UnicodeDecodeError:
            skipped += 1
            continue
        if new != raw:
            p.write_bytes(new)
            changed += 1
    return seen, changed, skipped


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", default=[], required=True)
    a = ap.parse_args(argv)
    for d in a.bundle:
        if not Path(d).is_dir():
            print(f"{d}: no such bundle in this run, skipped")
            continue
        seen, changed, skipped = canonicalise_dir(d)
        print(f"{d}: {seen} modules, {changed} rewritten in the canonical form, {skipped} not UTF-8 (left as they are)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
