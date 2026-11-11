"""The opener again as soon as an intake pull request merges (scripts/bump/intake_next.py, .github/workflows/intake-next.yml, the `next` job of intake-open.yml).

Real cases: every pull request competemath/tengoku had on 11 Nov 2026 (fixtures/tengoku_prs_2026-11-11.json.gz: 688, of them 306 of the intake lane, 199 merged), replayed
against the wait with a clock that moves through their real open, merge and close times; and the 70 real gaps between a part's merge and the next part's opening
(median 17 minutes, longest 6.4 days), each of which the wait closes to one poll.

Invariants:
  I1  nothing of the lane open: the wait ends at once and starts nothing;
  I2  the wait starts the opener only after a pull request it saw open is no longer open, and at most one poll after that happened;
  I3  pull requests outside the lane (dependabot, people) are never waited for;
  I4  a wait that sees no change before its deadline starts itself again instead of the opener; a GitHub that cannot be read ends it without starting anything;
  I5  the workflows: lane switch, main only, no App key, pinned actions, only actions: write beyond reading, the job outlives the wait's deadline, the opener starts the wait
      only after a real run on tengoku.
Mutants (each fails a test): every open pull request counted; the opener started when a new pull request appears; no deadline check; no retry of a failed read.
"""

from __future__ import annotations

import gzip
import importlib.util
import json
import sys
import unittest
from datetime import datetime
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
BUMP = HERE.parent
ROOT = BUMP.parents[1]
sys.path.insert(0, str(BUMP))
spec = importlib.util.spec_from_file_location("intake_next", BUMP / "intake_next.py")
nx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(nx)

PRS = json.loads(gzip.open(HERE / "fixtures" / "tengoku_prs_2026-11-11.json.gz", "rt").read())["prs"]


def ts(s: str | None) -> float | None:
    return datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp() if s else None


def ended(p: dict) -> float | None:
    return ts(p["mergedAt"]) or ts(p["closedAt"])


def open_at(t: float) -> list[dict]:
    return [{"number": p["number"], "headRefName": p["headRefName"]} for p in PRS if ts(p["createdAt"]) <= t and (ended(p) is None or ended(p) > t)]


class Clock:
    """a clock that moves only when the wait sleeps; a wait that sleeps past 30 days has ignored its deadline (a mutant without one fails here instead of hanging)"""

    def __init__(self, t: float):
        self.t = self.t0 = t

    def now(self) -> float:
        return self.t

    def sleep(self, s: float) -> None:
        self.t += s
        if self.t - self.t0 > 30 * 24 * 3600:
            raise AssertionError("the wait ran past every deadline")


LANE = [p for p in PRS if nx.BRANCH.match(p["headRefName"])]


class Replay(unittest.TestCase):
    def test_the_fixture_is_the_real_history(self):
        self.assertEqual(len(PRS), 688)
        self.assertEqual(len(LANE), 306)
        self.assertEqual(sum(p["state"] == "MERGED" for p in LANE), 199)

    def test_every_start_against_the_real_history(self):
        cases = 0
        for p in LANE:
            for poll in (60, 120, 300):
                for deadline_min in (30, 330):
                    start = ts(p["createdAt"]) + 30
                    c = Clock(start)
                    what, nums = nx.wait(lambda: open_at(c.t), c.sleep, c.now, deadline_min * 60, poll)
                    first = {q["number"] for q in open_at(start) if nx.BRANCH.match(q["headRefName"])}
                    cases += 1
                    if not first:
                        self.assertEqual((what, nums), ("none", []))  # I1
                        continue
                    by = {q["number"]: q for q in LANE}
                    gone_at = min((ended(by[n]) for n in first if ended(by[n])), default=None)
                    if what == "changed":
                        for n in nums:  # I2: really ended, and seen at most one poll late
                            self.assertIn(n, first)
                            self.assertLessEqual(ended(by[n]), c.t)
                        self.assertGreaterEqual(c.t, gone_at)
                        self.assertLessEqual(c.t - gone_at, poll)
                    else:
                        self.assertEqual(what, "deadline")  # I4
                        self.assertTrue(gone_at is None or gone_at > c.t, (p["number"], poll, deadline_min))
                        self.assertLessEqual(c.t, start + deadline_min * 60)
        self.assertEqual(cases, 306 * 3 * 2)

    def test_the_real_gaps_between_a_merge_and_the_next_part_close_to_one_poll(self):
        by_key: dict[str, list[tuple[int, dict]]] = {}
        for p in LANE:
            m = nx.BRANCH.match(p["headRefName"])
            by_key.setdefault(m["key"], []).append((int(m["part"] or 1), p))
        gaps, closed = [], 0
        for parts in by_key.values():
            parts.sort(key=lambda x: x[1]["createdAt"])
            for (a_n, a), (b_n, b) in zip(parts, parts[1:]):
                if a["mergedAt"] and b_n == a_n + 1 and b["createdAt"] > a["mergedAt"]:
                    gaps.append((ts(b["createdAt"]) - ts(a["mergedAt"])) / 60)
                    c = Clock(ts(a["createdAt"]) + 30)  # the opener that opened part N started the wait
                    what, nums = nx.wait(lambda: open_at(c.t), c.sleep, c.now, 7 * 24 * 3600, nx.POLL)
                    self.assertEqual(what, "changed")
                    started = c.t
                    if a["number"] in nums:  # this part's merge, not another library's, ended the wait: the next part is started within a poll
                        self.assertLessEqual(started - ts(a["mergedAt"]), nx.POLL)
                        closed += 1
        self.assertEqual(len(gaps), 70)
        gaps.sort()
        self.assertEqual(round(gaps[len(gaps) // 2]), 17)  # the median real wait, minutes
        self.assertGreater(gaps[-1], 9000)  # openai-math part 10: 6.4 days
        self.assertGreater(closed, 10)

    def test_pull_requests_outside_the_lane_are_never_waited_for(self):  # I3
        rows = [{"number": 1, "headRefName": "dependabot/pip/x"}, {"number": 2, "headRefName": "fix/thing"}, {"number": 3, "headRefName": "intake/aintlib-42873180722-part-002"}]
        self.assertEqual(nx.lane_open(rows), {3})
        others = [p for p in PRS if not nx.BRANCH.match(p["headRefName"])]
        self.assertGreater(len(others), 300)
        self.assertEqual(nx.lane_open([{"number": p["number"], "headRefName": p["headRefName"]} for p in others]), set())

    def test_a_new_pull_request_alone_does_not_start_the_opener(self):
        seq = iter([[{"number": 5, "headRefName": "intake/a-123456789-part-002"}]] + [[{"number": 5, "headRefName": "intake/a-123456789-part-002"}, {"number": 6, "headRefName": "intake/b-123456789"}]] * 10)
        c = Clock(0)
        self.assertEqual(nx.wait(lambda: next(seq), c.sleep, c.now, 600, 60), ("deadline", [5]))

    def test_a_read_that_fails_is_tried_again_and_one_that_keeps_failing_starts_nothing(self):
        calls = {"n": 0}

        def flaky():
            calls["n"] += 1
            if calls["n"] in (2, 3):
                raise RuntimeError("HTTP 502")
            return [] if calls["n"] > 4 else [{"number": 9, "headRefName": "intake/a-123456789"}]

        c = Clock(0)
        self.assertEqual(nx.wait(flaky, c.sleep, c.now, 3600, 60), ("changed", [9]))

        def dead():
            raise RuntimeError("HTTP 502")

        c = Clock(0)
        self.assertEqual(nx.wait(dead, c.sleep, c.now, 3600, 60), ("blind", []))
        self.assertLessEqual(c.t, 3600)


class Workflows(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        wf = ROOT / ".github" / "workflows"
        cls.next_text = (wf / "intake-next.yml").read_text()
        cls.next = yaml.safe_load(cls.next_text)
        cls.open = yaml.safe_load((wf / "intake-open.yml").read_text())

    def test_the_wait_runs_on_main_with_the_lane_on_and_holds_no_app_key(self):
        job = self.next["jobs"]["wait"]
        self.assertIn("vars.LANE_ENABLED == 'true'", job["if"])
        self.assertIn("github.ref == 'refs/heads/main'", job["if"])
        self.assertEqual(self.next["permissions"], {})
        self.assertEqual(job["permissions"], {"contents": "read", "actions": "write"})
        self.assertNotIn("secrets.", self.next_text)
        self.assertNotIn("create-github-app-token", self.next_text)
        for s in job["steps"]:
            if "uses" in s:
                self.assertRegex(s["uses"], r"@[0-9a-f]{40}$")
            if "run" in s:
                self.assertNotIn("${{", s["run"])

    def test_the_job_outlives_the_wait(self):
        job = self.next["jobs"]["wait"]
        run = job["steps"][-1]["run"]
        deadline = float(run.split("--deadline-min")[1].split()[0])
        self.assertGreater(job["timeout-minutes"], deadline + 10)

    def test_the_opener_starts_the_wait_only_after_a_real_run_on_tengoku(self):
        nxt = self.open["jobs"]["next"]
        self.assertEqual(nxt["needs"], "open")
        for clause in ("needs.open.result == 'success'", "(inputs.dry_run || 'false') == 'false'", "(inputs.target || 'competemath/tengoku') == 'competemath/tengoku'", "github.ref == 'refs/heads/main'"):
            self.assertIn(clause, nxt["if"])
        self.assertEqual(nxt["permissions"], {"actions": "write"})
        self.assertNotIn("secrets", json.dumps(nxt))
        self.assertIn("gh workflow run intake-next.yml", nxt["steps"][0]["run"])
        self.assertEqual(self.open["jobs"]["open"]["permissions"], {"contents": "read", "actions": "read", "attestations": "read"})  # the App's job gains nothing

    def test_one_wait_at_a_time(self):
        self.assertEqual(self.next["concurrency"], {"group": "intake-next", "cancel-in-progress": False})


if __name__ == "__main__":
    unittest.main()
