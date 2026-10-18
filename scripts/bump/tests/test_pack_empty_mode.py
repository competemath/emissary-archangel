"""A mode with no new module must not fail the pack step of bump-sharded.yml.

2026-10-18: the Navier-Stokes-Euler resume run (shard 1) spent 5 h 21 min on its shard, then compose and verify, and died in `finish` at "Pack and attest": the strict bundle had no
module the tree lacked, `bundle_layers.py` cut 0 parts, and `cp "parts-strict"/part-*.tar` was called with the glob unexpanded. The run's artifact, attestation and parts were lost with it.
"""

from __future__ import annotations

import re
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

PATH = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "bump-sharded.yml"
STEP = next(s for s in yaml.safe_load(PATH.read_text(encoding="utf-8"))["jobs"]["finish"]["steps"] if s.get("name") == "Pack and attest")["run"]
LOOP = re.search(r'^( *)for t in "parts-\$mode"/part-\*\.tar; do .*?; done$', STEP, re.M).group(0).strip()


def run_loop(parts: list[str]) -> subprocess.CompletedProcess:
    d = Path(tempfile.mkdtemp())
    (d / "parts-strict").mkdir()
    for p in parts:
        (d / "parts-strict" / p).write_text("tar")
    return subprocess.run(["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", "-c", f'mode=strict; KEY=k; {LOOP}; ls'], cwd=d, capture_output=True, text=True)


class PackEmptyMode(unittest.TestCase):
    def test_a_mode_with_no_part_is_skipped_not_a_failure(self):
        r = run_loop([])
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertNotIn("bundle-k-strict-", r.stdout)

    def test_the_parts_a_mode_has_are_copied_under_the_modes_name(self):
        r = run_loop(["part-010.tar", "part-011.tar"])
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("bundle-k-strict-part-010.tar", r.stdout)
        self.assertIn("bundle-k-strict-part-011.tar", r.stdout)


if __name__ == "__main__":
    unittest.main()
