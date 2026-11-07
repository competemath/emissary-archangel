"""A bump cuts parts unless told not to: the opener opens part archives only.

The real case: formal-conjectures (recut run 42392708632, 7 Nov) was dispatched without `parts`, the input's default was 0, no part archive was cut, and the opener failed with
"run 42392708632 has no archive bundle-formal-conjectures-proposed-part-001.tar (was it dispatched with `parts`?)": 311 verified theorems waited for a second recut by hand.
Invariants: both bump workflows default `parts` to a positive number; the opener asks every run for a numbered part (intake_open passes --part, open_intake_pr names the archive
`-part-NNN` for it), so a run without parts is never openable; the pack step cuts parts exactly when `parts` is not 0.
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]


def inputs(wf: str) -> dict:
    import yaml

    doc = yaml.safe_load((ROOT / ".github" / "workflows" / wf).read_text())
    on = doc.get("on", doc.get(True))
    return on["workflow_dispatch"]["inputs"]


class PartsDefault(unittest.TestCase):
    def test_both_bumps_cut_parts_by_default(self):
        for wf in ("bump-sharded.yml", "bump-library.yml"):
            d = inputs(wf)["parts"]["default"]
            self.assertRegex(d, r"^[1-9][0-9]*$", wf)
            self.assertEqual(int(d), 300, wf)  # the size the queue builds in its 40 minutes (~3 s a module)

    def test_the_opener_only_opens_numbered_parts(self):
        opener = (HERE / "intake_open.py").read_text()
        self.assertIn('"--part", str(act["part"])', opener)  # every open names a part
        pr = (HERE / "open_intake_pr.py").read_text()
        self.assertIn('suffix = "" if a.part is None else f"-part-{a.part:03d}"', pr)  # a named part is a -part-NNN archive

    def test_the_pack_step_cuts_parts_unless_parts_is_0(self):
        for wf in ("bump-sharded.yml", "bump-library.yml"):
            text = (ROOT / ".github" / "workflows" / wf).read_text()
            self.assertIn('if [ "${PARTS:-0}" != 0 ]; then', text, wf)
            self.assertIn('--max-modules "$PARTS"', text, wf)


if __name__ == "__main__":
    unittest.main()
