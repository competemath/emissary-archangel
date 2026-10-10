"""2026-10-10: the organisation has 20 concurrent runners and competemath/tengoku's gate and merge queue need about a dozen of them. A 12-shard translate run (10 of its jobs ran for hours),
a 6-way flt-anthropic setup and a 6-way lean-pool bump were running at once: 24 jobs wanted 20 runners, tengoku got 3-5, queue entries timed out and were rebuilt, and nothing merged for
three hours. translate-all had a JOB_BUDGET of 16 that it checked once, when it dispatched, and that the setup dispatch ignored. What is pinned here: every heavy workflow runs at most 6 jobs at once,
translate-all's budget is 8 (so tengoku always has 12), and the setup dispatch waits for the budget as the translate dispatch does."""

from __future__ import annotations

import re
import unittest
from pathlib import Path

import yaml

WORKFLOWS = Path(__file__).resolve().parents[3] / ".github" / "workflows"
CAP, BUDGET = 6, 8


def load(name: str) -> dict:
    return yaml.safe_load((WORKFLOWS / name).read_text(encoding="utf-8"))


def text(name: str) -> str:
    return (WORKFLOWS / name).read_text(encoding="utf-8")


def step(doc: dict, job: str, name_start: str) -> dict:
    return next(s for s in doc["jobs"][job]["steps"] if s.get("name", "").startswith(name_start))


class JobBudget(unittest.TestCase):
    def test_translate_all_keeps_the_heavy_jobs_under_eight_so_tengoku_has_twelve(self):
        d = load("translate-all.yml")
        self.assertLessEqual(int(step(d, "dispatch", "Plan and dispatch")["env"]["JOB_BUDGET"]), BUDGET)
        self.assertLessEqual(int(step(d, "dispatch", "The big setups")["env"]["JOB_BUDGET"]), BUDGET)

    def test_the_setup_dispatch_waits_for_the_budget_like_the_translate_dispatch(self):
        run = step(load("translate-all.yml"), "dispatch", "The big setups")["run"]
        self.assertRegex(run, r'-gt "\$JOB_BUDGET"')
        self.assertLess(run.index('-gt "$JOB_BUDGET"'), run.index("gh workflow run setup-sharded.yml"))  # asked before it dispatches, not after

    def test_every_queued_setup_fits_the_budget_by_itself(self):
        queue = step(load("translate-all.yml"), "dispatch", "The big setups")["env"]["SETUP_QUEUE"].split()
        self.assertTrue(queue)
        for spec in queue:
            self.assertLessEqual(int(spec.split(":")[4]), CAP, spec)

    def test_a_translate_run_holds_at_most_six_runners(self):
        self.assertLessEqual(load("translate.yml")["jobs"]["translate"]["strategy"]["max-parallel"], CAP)
        self.assertIn("shards = min(shards, 6)", text("translate-all.yml"))

    def test_setup_and_bump_default_to_six_at_a_time(self):
        ss = text("setup-sharded.yml")
        self.assertIn("inputs.parallel || '6'", ss)
        self.assertEqual(load("setup-sharded.yml")[True]["workflow_dispatch"]["inputs"]["parallel"]["default"], "6")
        self.assertEqual(load("bump-sharded.yml")[True]["workflow_dispatch"]["inputs"]["parallel"]["default"], "6")

    def test_no_workflow_asks_for_more_parallel_jobs_than_the_cap_by_default(self):
        for f in sorted(WORKFLOWS.glob("*.yml")):
            for m in re.finditer(r"max-parallel:\s*(\d+)", f.read_text(encoding="utf-8")):
                self.assertLessEqual(int(m.group(1)), CAP, f"{f.name}: max-parallel {m.group(1)}")


if __name__ == "__main__":
    unittest.main()
