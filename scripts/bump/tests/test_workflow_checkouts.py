"""Every workflow job that runs a script of scripts/ from a sparse checkout checks out what the script imports from outside scripts/.

2026-09-29 to 2026-10-09: bank-flush.mjs began to import ../lib/stage-record.mjs, the flush job of translate-all.yml checked out `scripts`, `data/bank` and
`data/translate` only, and every scheduled run (about four a day) died on ERR_MODULE_NOT_FOUND: nothing banked was sent to tengoku for ten days.
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = ROOT / ".github" / "workflows"
OUTSIDE = re.compile(r"""from\s+["']\.\./([A-Za-z0-9_-]+)/""")


def sparse_dirs(step: dict) -> set[str]:
    raw = str((step.get("with") or {}).get("sparse-checkout", ""))
    return {
        ln.strip().strip("/").split("/")[0]
        for ln in raw.replace("\\n", "\n").splitlines()
        if ln.strip()
    }


class SparseCheckoutsHoldWhatTheScriptsImport(unittest.TestCase):
    def test_every_job_that_runs_a_node_script_checks_out_the_directories_it_imports_from(
        self,
    ):
        problems = []
        for wf in sorted(WORKFLOWS.glob("*.yml")):
            doc = yaml.safe_load(wf.read_text(encoding="utf-8"))
            for name, job in (doc.get("jobs") or {}).items():
                steps = job.get("steps") or []
                sparse = [
                    s
                    for s in steps
                    if "actions/checkout" in str(s.get("uses", "")) and sparse_dirs(s)
                ]
                if not sparse:
                    continue  # a full checkout has everything
                dirs = set().union(*(sparse_dirs(s) for s in sparse))
                for s in steps:
                    for script in re.findall(
                        r"node\s+(scripts/[A-Za-z0-9_./-]+\.mjs)", str(s.get("run", ""))
                    ):
                        src = ROOT / script
                        if not src.exists():
                            continue
                        needed = set(OUTSIDE.findall(src.read_text(encoding="utf-8")))
                        missing = sorted(needed - dirs)
                        if missing:
                            problems.append(
                                f"{wf.name} job {name}: {script} imports from {missing}, the checkout has {sorted(dirs)}"
                            )
        self.assertEqual(problems, [])

    def test_the_flush_job_of_translate_all_has_lib(self):
        doc = yaml.safe_load(
            (WORKFLOWS / "translate-all.yml").read_text(encoding="utf-8")
        )
        steps = doc["jobs"]["flush"]["steps"]
        self.assertIn(
            "lib",
            set().union(
                *(
                    sparse_dirs(s)
                    for s in steps
                    if "actions/checkout" in str(s.get("uses", ""))
                )
            ),
        )


if __name__ == "__main__":
    unittest.main()
