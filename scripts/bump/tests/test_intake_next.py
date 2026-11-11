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
from datetime import datetime, timezone
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
    """what `gh pr list --state all` says at time t: every pull request created by then, open or (with its closing time) merged or closed"""
    out = []
    for p in PRS:
        if ts(p["createdAt"]) > t:
            continue
        e = ended(p)
        if e is None or e > t:
            out.append({"number": p["number"], "headRefName": p["headRefName"], "state": "OPEN", "closedAt": None})
        else:
            out.append({"number": p["number"], "headRefName": p["headRefName"], "state": "MERGED" if p["mergedAt"] else "CLOSED", "closedAt": p["mergedAt"] or p["closedAt"]})
    return out


def at(t: float) -> datetime:
    return datetime.fromtimestamp(t, tz=timezone.utc)


class Clock:
    """a clock that moves only when the wait sleeps; a wait that sleeps past 30 days has ignored its deadline (a mutant without one fails here instead of hanging)"""

    def __init__(self, t: float):
        self.t = self.t0 = t

    def now(self) -> float:
        return self.t

    def sleep(self, s: float) -> None:
        if s < 0:
            raise AssertionError(f"a sleep of {s} s: the wait went past its deadline")
        self.sleeps = getattr(self, "sleeps", 0) + 1
        if self.sleeps > 20_000:  # the longest wait here is 330 minutes at 1 minute (330 sleeps): this many is a wait that never ends (a sleep of 0 at the deadline, forever)
            raise AssertionError("the wait never ends")
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
                    first = nx.lane_open(open_at(start))
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
        """Each of the 70 real gaps, replayed as the chain runs: the opener that opened part N starts a wait; a wait that another library's merge ends starts the opener, which
        starts the next wait (with `since` = that opener's start); a wait that reaches its deadline starts itself again. Every one of the 70 merges is seen within one poll."""
        by_key: dict[str, list[tuple[int, dict]]] = {}
        for p in LANE:
            m = nx.BRANCH.match(p["headRefName"])
            by_key.setdefault(m["key"], []).append((int(m["part"] or 1), p))
        gaps, seen, hops = [], 0, 0
        for parts in by_key.values():
            parts.sort(key=lambda x: x[1]["createdAt"])
            for (a_n, a), (b_n, b) in zip(parts, parts[1:]):
                if not (a["mergedAt"] and b_n == a_n + 1 and b["createdAt"] > a["mergedAt"]):
                    continue
                gaps.append((ts(b["createdAt"]) - ts(a["mergedAt"])) / 60)
                c = Clock(ts(a["createdAt"]) + 30)
                since = None
                while True:
                    hops += 1
                    run_start = c.t
                    what, nums = nx.wait(lambda: open_at(c.t), c.sleep, c.now, 330 * 60, nx.POLL, since=since)
                    if what == "changed" and a["number"] in nums:
                        self.assertLessEqual(c.t - ts(a["mergedAt"]), nx.POLL, a["number"])
                        seen += 1
                        break
                    self.assertIn(what, ("changed", "deadline"), (a["number"], what))  # part N is open until it merges: the chain never ends with 'none' before that
                    since = at(c.t if what == "deadline" else run_start)
                    c.t += 1  # the next run starts a second later
        self.assertEqual(len(gaps), 70)
        self.assertEqual(seen, 70)
        gaps.sort()
        self.assertEqual(round(gaps[len(gaps) // 2]), 17)  # the median real wait, minutes
        self.assertGreater(gaps[-1], 9000)  # openai-math part 10: 6.4 days
        self.assertGreater(hops, 70)

    def test_a_merge_before_the_first_look_is_not_missed(self):
        """the opener ran, found part N open and started the wait; part N merged before the wait's first look (cubic, #172)"""
        merged = [{"number": 7, "headRefName": "intake/a-123456789-part-002", "state": "MERGED", "closedAt": "2026-11-11T10:00:30Z"}]
        c = Clock(0)
        self.assertEqual(nx.wait(lambda: merged, c.sleep, c.now, 600, 60, since=nx.parse_time("2026-11-11T10:00:00Z")), ("changed", [7]))
        self.assertEqual(nx.wait(lambda: merged, c.sleep, c.now, 600, 60, since=nx.parse_time("2026-11-11T10:01:00Z")), ("none", []))  # merged before the opener looked: it saw it
        self.assertEqual(nx.wait(lambda: merged, c.sleep, c.now, 600, 60), ("none", []))
        with self.assertRaises(ValueError):
            nx.parse_time("2026-11-11T10:00:00")  # no zone: refused, not read as local time

    def test_the_reads_are_complete_or_refused_never_cut(self):
        """the wait reads every open pull request and every one closed since `since`, not the newest N of all; a list as long as its limit may be cut and is refused (a failed
        read: retried, then the schedule takes over), never read as complete (cubic, #172). Checked against the real history: the open list and the closed-since list at every
        lane pull request's opening are exactly what the replay's full view says."""
        since = nx.parse_time("2026-11-11T08:00:00Z")
        asked = []

        def gh(args):
            asked.append(args)
            return [{"number": i, "headRefName": "x", "state": "OPEN"} for i in range(nx.OPEN_LIMIT)] if "open" in args else []

        with self.assertRaises(RuntimeError):
            nx.fetch_rows(gh, "competemath/tengoku", since)

        def gh2(args):
            return [] if "open" in args else [{"number": i, "headRefName": "x", "state": "MERGED", "closedAt": "2026-11-11T09:00:00Z"} for i in range(nx.CLOSED_LIMIT)]

        with self.assertRaises(RuntimeError):
            nx.fetch_rows(gh2, "competemath/tengoku", since)
        seen = []
        nx.fetch_rows(lambda args: seen.append(args) or [], "competemath/tengoku", since)
        self.assertEqual(seen[0][:6], ["pr", "list", "-R", "competemath/tengoku", "--state", "open"])
        self.assertIn("closed:>=2026-11-11T08:00:00Z", seen[1])
        self.assertNotIn("-L", seen[0][:6])
        self.assertEqual(len(nx.fetch_rows(lambda a: [], "t", None)), 0)
        # the two queries against the real history give the replay's full view
        for p in LANE[::5]:
            t = ts(p["createdAt"]) + 30
            full = open_at(t)
            s_ = at(t - 3600)

            def real(args, t=t, s_=s_, full=full):
                if "open" in args:
                    return [r for r in full if r["state"] == "OPEN"]
                return [r for r in full if r["state"] != "OPEN" and nx.parse_time(r["closedAt"]) >= s_]

            got = nx.fetch_rows(real, "t", s_)
            self.assertEqual(nx.lane_open(got), nx.lane_open(full))
            self.assertEqual(nx.closed_since(got, s_), nx.closed_since(full, s_))

    def test_the_last_look_is_at_the_deadline(self):
        looks = []
        c = Clock(0)
        nx.wait(lambda: looks.append(c.t) or [{"number": 5, "headRefName": "intake/a-123456789-part-002", "state": "OPEN"}], c.sleep, c.now, 330 * 60, 120)
        self.assertEqual(looks[-1], 330 * 60)

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
        self.assertIn('-f since="$since"', nxt["steps"][0]["run"])

    def test_an_automatic_start_of_the_opener_obeys_the_lane_switch(self):
        """intake-next starts the opener with automatic=true; such a run needs LANE_ENABLED like the schedule; a person's dispatch does not (cubic, #172)"""
        cond = self.open["jobs"]["open"]["if"]
        self.assertIn("(github.event_name == 'workflow_dispatch' && inputs.automatic != 'true') || vars.LANE_ENABLED == 'true'", cond)
        src = (BUMP / "intake_next.py").read_text()
        self.assertIn('"-f", "automatic=true"', src)
        self.assertEqual(self.open[True]["workflow_dispatch"]["inputs"]["automatic"]["default"], "false")
        self.assertEqual(self.open["jobs"]["open"]["permissions"], {"contents": "read", "actions": "read", "attestations": "read"})  # the App's job gains nothing

    def test_one_wait_at_a_time(self):
        self.assertEqual(self.next["concurrency"], {"group": "intake-next", "cancel-in-progress": False})


if __name__ == "__main__":
    unittest.main()
