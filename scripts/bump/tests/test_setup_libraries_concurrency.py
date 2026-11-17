"""setup-libraries.yml: runs for different libraries must not cancel each other.

The real case (16 Nov 2026, batch 8): setup-pickup started 2-4 small libraries per run through setup-auto, which dispatches setup-libraries.yml once per library. The workflow had
`concurrency: group: setup-libraries, cancel-in-progress: false`: GitHub keeps ONE running and ONE pending run per group and a newer pending run replaces the older pending one. 8 of the
15 setups ended "cancelled" within seconds of being dispatched (fixtures/real-setup-libraries-runs-2026-11-16.json: the 19 real dispatches of that day), a running one held the group for
1 h 45 min, and setup-pickup counted every setup-auto run as an attempt, so none was retried.

The model below is GitHub's rule for one group. Invariants: with one group for the workflow the real dispatch times cancel at least as many runs as the real day shows replaced within a
minute; with the group per key list the dispatches of different libraries cancel none, and a second dispatch of the SAME keys replaces only the older pending one. Mutant: the old group
string brings the cancellations back.
"""
import json
import re
import unittest
from datetime import datetime, timedelta
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
WORKFLOW = HERE.parents[2] / ".github" / "workflows" / "setup-libraries.yml"
DOC = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
RUNS = json.loads((HERE / "fixtures" / "real-setup-libraries-runs-2026-11-16.json").read_text())
OLD_GROUP = "setup-libraries"


def _t(iso: str) -> datetime:
    return datetime.fromisoformat(iso.replace("Z", "+00:00"))


def group_of(template: str, keys: str) -> str:
    return template.replace("${{ inputs.keys }}", keys)


def simulate(template: str, dispatches: list[tuple[datetime, str]], run_minutes: float = 20.0) -> list[int]:
    """indices of the dispatches that are replaced while pending: GitHub's rule for one concurrency group (one running, one pending, newer pending cancels older pending)"""
    running: dict[str, datetime] = {}  # group -> end of the running run
    pending: dict[str, int] = {}
    cancelled: list[int] = []
    order = sorted(range(len(dispatches)), key=lambda i: dispatches[i][0])
    for i in order:
        when, keys = dispatches[i]
        g = group_of(template, keys)
        # runs that ended before this dispatch free their group: the pending one (if any) starts
        for gg in list(running):
            while gg in running and running[gg] <= when:
                if gg in pending:
                    running[gg] = running[gg] + timedelta(minutes=run_minutes)
                    del pending[gg]
                else:
                    del running[gg]
        if g not in running:
            running[g] = when + timedelta(minutes=run_minutes)
        else:
            if g in pending:
                cancelled.append(pending[g])
            pending[g] = i
    return cancelled


def real_dispatches() -> list[tuple[datetime, str]]:
    return [(_t(r["created"]), f"lib-{i}") for i, r in enumerate(RUNS)]  # every real dispatch was for its own library (one key each)


class TheWorkflow(unittest.TestCase):
    def test_the_group_is_per_key_list_and_never_cancels_a_running_setup(self):
        c = DOC["concurrency"]
        self.assertIn("inputs.keys", c["group"])
        self.assertIs(c["cancel-in-progress"], False)

    def test_the_exports_commit_retries_so_runs_of_different_keys_may_push_side_by_side(self):
        text = WORKFLOW.read_text(encoding="utf-8")
        self.assertRegex(text, r"for i in \$\(seq 1 30\); do\s*\n\s*if git pull -q --rebase --autostash origin main && git push")


    def test_a_second_run_of_the_same_library_banks_nothing_and_does_not_fail(self):
        """cubic on #211 (P2): overlapping key lists (translate-all's bulk list, setup-auto's single key) can run one library twice: the second finds nothing new to commit and exits 0"""
        text = WORKFLOW.read_text(encoding="utf-8")
        i = text.index("git diff --cached --quiet")
        self.assertLess(i, text.index('git commit -q -m "exports: $KEY (runner)"'))
        self.assertIn("exit 0", text[i : i + 120])


class TheModel(unittest.TestCase):
    def real_replaced(self):
        return [i for i, r in enumerate(RUNS) if r["conclusion"] == "cancelled" and (_t(r["updated"]) - _t(r["created"])).total_seconds() < 60]

    def test_the_real_day_has_eight_runs_replaced_within_a_minute(self):
        self.assertEqual(len(self.real_replaced()), 8)

    def test_the_old_group_reproduces_the_cancellations_of_the_real_dispatch_times(self):
        got = simulate(OLD_GROUP, real_dispatches())
        self.assertGreaterEqual(len(got), 8)

    def test_the_group_of_the_workflow_cancels_none_of_the_real_dispatches(self):
        self.assertEqual(simulate(DOC["concurrency"]["group"], real_dispatches()), [])

    def test_the_same_keys_twice_replace_only_the_older_pending_run(self):
        t0 = _t(RUNS[0]["created"])
        d = [(t0, "a"), (t0 + timedelta(seconds=5), "a"), (t0 + timedelta(seconds=10), "a")]
        self.assertEqual(simulate(DOC["concurrency"]["group"], d), [1])  # run 0 runs, run 1 pends, run 2 replaces it
        d = [(t0, "a"), (t0 + timedelta(seconds=5), "b"), (t0 + timedelta(seconds=10), "c")]
        self.assertEqual(simulate(DOC["concurrency"]["group"], d), [])

    def test_a_thousand_random_dispatch_sets(self):
        """distinct keys: the workflow's group cancels none; the old group cancels at least one whenever three dispatches fall inside one run's length (20 min)"""
        import random
        rnd = random.Random(16112026)
        t0 = _t(RUNS[0]["created"])
        old_cancelled_some = 0
        for _ in range(1000):
            n = rnd.randrange(3, 25)
            d = [(t0 + timedelta(seconds=rnd.randrange(0, 600)), f"k{i}") for i in range(n)]  # all inside 10 minutes, distinct keys
            self.assertEqual(simulate(DOC["concurrency"]["group"], d), [])
            if simulate(OLD_GROUP, d):
                old_cancelled_some += 1
        self.assertEqual(old_cancelled_some, 1000)  # with 3 or more dispatches inside one run, the old group always loses at least one

    def test_mutant_the_old_group_string_in_the_workflow_text(self):
        self.assertNotRegex(WORKFLOW.read_text(encoding="utf-8"), r"group: setup-libraries\s*\n")


if __name__ == "__main__":
    unittest.main()
