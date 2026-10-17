import argparse
import json
import subprocess
import sys
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import intake_open as io  # noqa: E402

NOW = datetime(2026, 10, 10, 12, 0, tzinfo=timezone.utc)


def pr(number, state, key="lib", run=100000000, part=1, title=""):
    return io.Pr(number, state, key, run, part, title)


def rows(*specs):
    return [{"number": n, "state": s, "headRefName": b, "title": t} for n, s, b, t in specs]


class ParsePrs(unittest.TestCase):
    def test_the_key_the_run_and_the_part_come_from_the_branch(self):
        got = io.parse_prs(rows((1, "OPEN", "intake/erdos-unit-distance-1-38055889087-part-001", "x"), (2, "MERGED", "intake/prismriver-37978594492", "y"), (3, "OPEN", "feature/other", "z")))
        self.assertEqual(sorted(got), ["erdos-unit-distance-1", "prismriver"])
        self.assertEqual((got["erdos-unit-distance-1"][0].run, got["erdos-unit-distance-1"][0].part), (38055889087, 1))
        self.assertEqual(got["prismriver"][0].part, 1)  # an unparted bundle is part 1
        self.assertEqual((got["prismriver"][0].parted, got["erdos-unit-distance-1"][0].parted), (False, True))

    def test_a_branch_that_is_not_an_intake_branch_is_ignored(self):
        self.assertEqual(io.parse_prs(rows((1, "OPEN", "isnad/tags", ""), (2, "OPEN", "intake/short-1", ""))), {})


class NewestBundles(unittest.TestCase):
    def run_row(self, run, title, concl="success", hours_ago=1):
        return {"databaseId": run, "displayTitle": title, "conclusion": concl, "createdAt": (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")}

    def test_the_newest_successful_run_of_each_library_from_either_workflow(self):
        got = io.newest_bundles([self.run_row(1, "bump a", hours_ago=5), self.run_row(2, "bump-sharded a", hours_ago=2), self.run_row(3, "bump b")], NOW)
        self.assertEqual({k: v[0] for k, v in got.items()}, {"a": 2, "b": 3})

    def test_a_failed_run_an_expired_one_and_another_title_do_not_count(self):
        got = io.newest_bundles([self.run_row(1, "bump a", concl="failure"), self.run_row(2, "bump b", hours_ago=73), self.run_row(3, "translate-all"), self.run_row(4, "bump c", hours_ago=71)], NOW)
        self.assertEqual(list(got), ["c"])


class Decide(unittest.TestCase):
    def test_a_new_library_opens_part_one(self):
        self.assertEqual(io.decide([], 5, False), ("open", {"part": 1, "run": 5, "depends_on": None}))

    def test_one_open_pr_per_library(self):
        self.assertEqual(io.decide([pr(1, "OPEN")], 5, False)[0], "skip")

    def test_the_next_part_follows_the_merged_one_and_depends_on_it(self):
        merged = pr(7, "MERGED", run=5, part=2, title="intake: lib part 2 of 9 (1 verified theorems in 1 modules)")
        self.assertEqual(io.decide([pr(6, "MERGED", run=5, part=1), merged], 5, False), ("open", {"part": 3, "run": 5, "depends_on": "#7"}))

    def test_the_last_part_merged_ends_the_library(self):
        self.assertEqual(io.decide([pr(7, "MERGED", run=5, part=9, title="extend: lib part 9 of 9 (3 verified theorems in 1 modules)")], 5, False), ("skip", "every part is in the tree"))

    def test_a_later_run_needs_a_recut_not_a_new_part(self):
        verdict, why = io.decide([pr(7, "MERGED", run=5, part=1, title="intake: lib part 1 of 3 (2 verified theorems in 1 modules)")], 6, False)
        self.assertEqual(verdict, "skip")
        self.assertIn("recut", why)

    def test_no_bundle_and_a_library_in_the_tree_without_an_intake_are_left_alone(self):
        self.assertEqual(io.decide([], None, False)[0], "skip")
        self.assertEqual(io.decide([], 5, True), ("skip", "in the tree without an intake"))

    def test_a_library_that_came_as_one_unparted_bundle_has_no_next_part(self):
        # 2026-10-10: leaninfotheory merged from `intake/leaninfotheory-<run>` (no `-part-`, no 'part N of M' in the title); the opener tried 'part 2' of that run every 10 minutes and failed: no archive
        merged = io.Pr(348, "MERGED", "lib", 5, 1, "intake: lib (12 verified theorems in 3 modules)", False)
        verdict, why = io.decide([merged], 5, False)
        self.assertEqual(verdict, "skip")
        self.assertIn("one bundle", why)
        self.assertEqual(io.decide([io.Pr(348, "MERGED", "lib", 5, 1, "intake: lib part 1 of 3 (1 verified theorems in 1 modules)", True)], 5, False)[0], "open")  # a parted one continues
        self.assertEqual(io.decide([io.Pr(348, "MERGED", "lib", 5, 1, "intake: lib part 1 of 3 (1 verified theorems in 1 modules)", False)], 5, False)[0], "open")  # so does one whose title says it is part 1 of 3

    def test_a_pr_closed_without_merging_for_this_run_is_not_opened_again_but_a_newer_run_is(self):
        closed = pr(3, "CLOSED", run=5, part=1)
        self.assertEqual(io.decide([closed], 5, False)[0], "skip")  # else the lane would reopen what a person closed, every tick
        self.assertEqual(io.decide([closed], 6, False)[0], "open")


class Budget(unittest.TestCase):
    def test_the_smallest_of_the_three_limits_and_never_below_zero(self):
        self.assertEqual(io.budget(10, 0, 80, 400, 12), 12)
        self.assertEqual(io.budget(75, 0, 80, 400, 12), 5)
        self.assertEqual(io.budget(0, 395, 80, 400, 12), 5)
        self.assertEqual(io.budget(90, 0, 80, 400, 12), 0)
        self.assertEqual(io.budget(0, 500, 80, 400, 12), 0)


class FakeGh:
    def __init__(self, prs=(), runs=(), opened=0, in_tree=(), absent=(), razes=None):
        self._prs, self._runs, self._opened, self._in_tree, self._absent = list(prs), list(runs), opened, set(in_tree), set(absent)
        self._razes = razes or {}  # key -> when the whole-library raze marker merged

    def prs(self):
        return self._prs

    def runs(self):
        return self._runs

    def opened_since(self, since):
        return self._opened

    def unmanaged_in_tree(self, key):
        return key in self._in_tree

    def absent_from_tree(self, key):
        return key in self._absent

    def whole_raze_time(self, key):
        return self._razes.get(key)


def run_row(run, key, hours_ago):
    return {"databaseId": run, "displayTitle": f"bump {key}", "conclusion": "success", "createdAt": (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")}


def args(**kw):
    base = dict(target="o/t", max_open=80, daily_cap=400, per_tick=12, pace=90, keys="", auto_merge=False, auto_merge_first=False, dry_run=False)
    return argparse.Namespace(**{**base, **kw})


class Tick(unittest.TestCase):
    def go(self, gh, a=None, results=None):
        calls, sleeps = [], []

        def opener(target, key, act, auto_merge, auto_first=False):
            calls.append((key, act["part"], auto_merge))
            r = (results or {}).get(key, (0, "", "https://github.com/o/t/pull/1"))
            return subprocess.CompletedProcess([], r[0], stdout=r[2], stderr=r[1])

        out = io.tick(a or args(), gh, opener=opener, sleep=sleeps.append, now=NOW)
        return out, calls, sleeps

    def test_oldest_bundle_first_up_to_the_room_and_paced_between_prs(self):
        gh = FakeGh(runs=[run_row(1, "newer", 1), run_row(2, "older", 9), run_row(3, "middle", 5)])
        out, calls, sleeps = self.go(gh, args(per_tick=2))
        self.assertEqual([c[0] for c in calls], ["older", "middle"])
        self.assertEqual(sleeps, [90])  # between the two, not after the last

    def test_nothing_opens_when_the_open_limit_or_the_daily_cap_is_reached(self):
        gh = FakeGh(prs=rows(*[(i, "OPEN", f"intake/k{i}-10000000{i}", "") for i in range(3)]), runs=[run_row(1, "fresh", 1)])
        self.assertEqual(self.go(gh, args(max_open=3))[1], [])
        self.assertEqual(self.go(FakeGh(runs=[run_row(1, "fresh", 1)], opened=400))[1], [])

    def test_dry_run_calls_nothing(self):
        out, calls, sleeps = self.go(FakeGh(runs=[run_row(1, "a", 1)]), args(dry_run=True))
        self.assertEqual((calls, sleeps, out["opened"]), ([], [], ["a"]))

    def test_keys_restricts_the_libraries(self):
        out, calls, _ = self.go(FakeGh(runs=[run_row(1, "a", 1), run_row(2, "b", 2)]), args(keys="b"))
        self.assertEqual([c[0] for c in calls], ["b"])

    def test_one_failure_does_not_stop_the_others_and_an_empty_bundle_is_not_a_failure(self):
        gh = FakeGh(runs=[run_row(1, "bad", 9), run_row(2, "empty", 8), run_row(3, "good", 7)])
        out, calls, _ = self.go(gh, results={"bad": (1, "boom", ""), "empty": (1, "EMPTY BUNDLE: no verified theorem", "")})
        self.assertEqual((out["failed"], out["opened"]), (["bad"], ["good"]))
        self.assertEqual(out["skipped"]["empty"], "no verified theorem in the bundle")

    def test_auto_merge_is_only_asked_for_when_the_lane_is_on(self):
        gh = FakeGh(prs=rows((7, "MERGED", "intake/lib-100000000", "intake: lib part 1 of 3 (1 verified theorems in 1 modules)")), runs=[run_row(100000000, "lib", 1)])
        self.assertEqual(self.go(gh)[1], [("lib", 2, False)])
        self.assertEqual(self.go(gh, args(auto_merge=True))[1], [("lib", 2, True)])

    OLD_PART = rows((7, "MERGED", "intake/lib-100000000-part-005", "intake: lib part 5 of 5 (3 verified theorems in 1 modules)"))

    def test_a_library_razed_whole_starts_again_at_part_one_of_a_bundle_built_after_the_raze(self):
        # 2026-10-16: navier-stokes-euler was razed whole (tengoku#579) and re-cut; its old part 5 of 5 was MERGED, so the opener said 'every part is in the tree' for a library whose folder was gone
        razed = {"lib": NOW - timedelta(hours=3)}  # the bundle is 1 hour old
        out, calls, _ = self.go(FakeGh(prs=self.OLD_PART, runs=[run_row(200000000, "lib", 1)], absent=["lib"], razes=razed))
        self.assertEqual((out["opened"], out["skipped"], calls), (["lib"], {}, [("lib", 1, False)]))

    def test_the_history_is_forgotten_only_with_the_marker_the_library_missing_from_the_tree_and_a_newer_bundle(self):
        runs = [run_row(200000000, "lib", 1)]

        def refused(gh, why):
            out, calls, _ = self.go(gh)
            self.assertEqual((out["opened"], calls), ([], []))
            self.assertIn(why, out["skipped"]["lib"])

        # still in the tree (a marker from an earlier raze is history): nothing follows its last part
        refused(FakeGh(prs=self.OLD_PART, runs=runs, razes={"lib": NOW - timedelta(hours=3)}), "every part is in the tree")
        # missing from the tree but no marker (deregistered, moved, an API that answered 404 for another reason): nothing is shipped again
        refused(FakeGh(prs=self.OLD_PART, runs=runs, absent=["lib"]), "every part is in the tree")
        # missing, razed, but the newest bundle is older than the raze: it is the very bundle that was razed
        refused(FakeGh(prs=self.OLD_PART, runs=runs, absent=["lib"], razes={"lib": NOW - timedelta(minutes=30)}), "needs a recut")

    def test_a_razed_library_keeps_its_open_and_closed_pull_requests(self):
        # only the MERGED ones are history: an open part still blocks the library, and one closed for this run is still not reopened
        merged = (7, "MERGED", "intake/lib-100000000-part-005", "intake: lib part 5 of 5 (3 verified theorems in 1 modules)")
        razed = {"lib": NOW - timedelta(hours=3)}
        out, calls, _ = self.go(FakeGh(prs=rows(merged, (8, "OPEN", "intake/lib-200000000-part-001", "")), runs=[run_row(200000000, "lib", 1)], absent=["lib"], razes=razed))
        self.assertEqual((out["opened"], out["skipped"]), ([], {"lib": "a pull request of this library is open"}))
        out, calls, _ = self.go(FakeGh(prs=rows(merged, (9, "CLOSED", "intake/lib-200000000-part-001", "")), runs=[run_row(200000000, "lib", 1)], absent=["lib"], razes=razed))
        self.assertEqual(out["opened"], [])
        self.assertIn("closed without merging", out["skipped"]["lib"])

    def test_a_library_with_no_merged_part_costs_no_lookup(self):
        class Strict(FakeGh):
            def absent_from_tree(self, key):
                raise AssertionError("looked at the tree of a library with no merged part")

        out, calls, _ = self.go(Strict(runs=[run_row(1, "fresh", 1)]))
        self.assertEqual(out["opened"], ["fresh"])

    def test_a_library_in_the_tree_without_an_intake_is_skipped(self):
        out, calls, _ = self.go(FakeGh(runs=[run_row(1, "seeded", 1)], in_tree=["seeded"]))
        self.assertEqual((calls, out["skipped"]), ([], {"seeded": "in the tree without an intake"}))


class WholeRazeTime(unittest.TestCase):
    """Gh.whole_raze_time against canned answers of the GitHub API"""

    def gh(self, listing, files, commits, listing_rc=0, listing_err=""):
        g = io.Gh("o/t", "o/f", "app/x")

        def run(*a):
            path = a[1]
            if path.endswith("contents/data/raze?ref=main"):
                return subprocess.CompletedProcess([], listing_rc, stdout=json.dumps(listing), stderr=listing_err)
            for name, marker in files.items():
                if f"contents/data/raze/{name}" in path:
                    return subprocess.CompletedProcess([], 0, stdout=json.dumps(marker), stderr="")
            for name, when in commits.items():
                if f"path=data/raze/{name}" in path:
                    return subprocess.CompletedProcess([], 0, stdout=json.dumps([{"commit": {"committer": {"date": when}}}]), stderr="")
            raise AssertionError(path)

        g.run = run
        return g

    def test_the_newest_whole_library_marker_of_the_key_counts_and_nothing_else(self):
        listing = [{"name": n} for n in ("lib-2026-10-01.json", "lib-2026-10-16.json", "lib-leaks-2026-10-16.json", "library-2026-10-16.json", "other-2026-10-16.json", "README.md")]
        files = {
            "lib-2026-10-01.json": {"library": "lib", "all": True},
            "lib-2026-10-16.json": {"library": "lib", "all": True},
            "lib-leaks-2026-10-16.json": {"library": "lib", "modules": ["Tengoku.Lib.A"]},  # a partial raze: the library stays in the tree
            "library-2026-10-16.json": {"library": "library", "all": True},  # another key that starts with the same letters
        }
        commits = {"lib-2026-10-01.json": "2026-10-01T10:00:00Z", "lib-2026-10-16.json": "2026-10-16T18:07:00Z"}
        self.assertEqual(self.gh(listing, files, commits).whole_raze_time("lib"), datetime(2026, 10, 16, 18, 7, tzinfo=timezone.utc))

    def test_no_marker_and_no_folder_are_none_but_any_other_error_is_raised(self):
        self.assertIsNone(self.gh([], {}, {}).whole_raze_time("lib"))
        self.assertIsNone(self.gh([], {}, {}, listing_rc=1, listing_err="gh: Not Found (HTTP 404)").whole_raze_time("lib"))
        with self.assertRaises(RuntimeError):
            self.gh([], {}, {}, listing_rc=1, listing_err="gh: API rate limit exceeded (HTTP 403)").whole_raze_time("lib")


class FromTreeRecuts(unittest.TestCase):
    """2026-10-10: openai-math part 2 failed in the queue, was recut from the tree (parts 2-9 cut again from a new run) and the opener skipped it ('needs a recut'): a person opened the
    replacement and queued it by hand. A recut that says so in its title continues by itself."""

    def test_the_title_of_a_from_tree_recut_is_read(self):
        rows = [
            {"databaseId": 1, "displayTitle": "bump-sharded openai-math (from tree)", "conclusion": "success", "createdAt": "2026-10-10T12:00:00Z"},
            {"databaseId": 2, "displayTitle": "bump-sharded lean-pool", "conclusion": "success", "createdAt": "2026-10-10T11:00:00Z"},
            {"databaseId": 3, "displayTitle": "bump complexitylib (from tree)", "conclusion": "success", "createdAt": "2026-10-10T10:00:00Z"},
        ]
        got = io.newest_bundles(rows, NOW)
        self.assertEqual({k: (v[0], v[2]) for k, v in got.items()}, {"openai-math": (1, True), "lean-pool": (2, False), "complexitylib": (3, True)})

    def test_a_from_tree_recut_opens_the_next_part_after_the_merged_one_and_a_plain_newer_run_still_waits(self):
        merged = io.Pr(413, "MERGED", "lib", 5, 1, "intake: lib part 1 of 9 (1 verified theorems in 1 modules)", True)
        self.assertEqual(io.decide([merged], 6, False, from_tree=True), ("open", {"part": 2, "run": 6, "depends_on": "#413"}))
        self.assertEqual(io.decide([merged], 6, False)[0], "skip")  # an ordinary newer run is not a recut from the tree: its part 2 would not match the tree
        self.assertEqual(io.decide([merged, io.Pr(433, "OPEN", "lib", 6, 2, "", True)], 6, False, from_tree=True)[0], "skip")  # one open PR per library still

    def test_a_from_tree_recut_that_was_closed_without_merging_is_not_reopened(self):
        merged = io.Pr(413, "MERGED", "lib", 5, 1, "intake: lib part 1 of 9 (1 verified theorems in 1 modules)", True)
        closed = io.Pr(433, "CLOSED", "lib", 6, 2, "", True)
        self.assertEqual(io.decide([merged, closed], 6, False, from_tree=True)[0], "skip")


class FirstPartsAutomatic(unittest.TestCase):
    """2026-10-10: 'automate it all': with Tengoku/All.lean unowned a first part needs no person, so the opener may arm auto-merge on it too, when LANE_AUTOMERGE_FIRST says so."""

    def cmd_env(self, act, auto_merge, auto_first):
        with mock.patch.object(io.subprocess, "run") as run:
            io.open_pr("o/t", "lib", act, auto_merge, auto_first)
            return run.call_args[0][0], run.call_args[1].get("env")

    def test_a_first_part_is_armed_only_when_both_switches_are_on(self):
        first = {"part": 1, "run": 5, "depends_on": None}
        cmd, env = self.cmd_env(first, True, True)
        self.assertIn("--auto-merge", cmd)
        self.assertEqual(env["LANE_AUTOMERGE_FIRST"], "true")
        self.assertNotIn("--auto-merge", self.cmd_env(first, True, False)[0])  # LANE_AUTOMERGE alone: extend parts only
        self.assertNotIn("--auto-merge", self.cmd_env(first, False, True)[0])  # the lane's main switch is off

    def test_an_extend_part_is_armed_with_the_main_switch_alone(self):
        ext = {"part": 2, "run": 5, "depends_on": "#7"}
        cmd, env = self.cmd_env(ext, True, False)
        self.assertIn("--auto-merge", cmd)
        self.assertIsNone(env)

    def test_the_tick_hands_the_second_switch_to_the_opener(self):
        seen = []

        def opener(target, key, act, auto_merge, auto_first=False):
            seen.append((auto_merge, auto_first))
            return subprocess.CompletedProcess([], 0, stdout="https://x/pull/1", stderr="")

        io.tick(args(auto_merge=True, auto_merge_first=True), FakeGh(runs=[run_row(1, "a", 1)]), opener=opener, sleep=lambda s: None, now=NOW)
        self.assertEqual(seen, [(True, True)])


class OpenPrCommand(unittest.TestCase):
    def cmd(self, act, auto_merge):
        with mock.patch.object(io.subprocess, "run") as run:
            io.open_pr("o/t", "lib", act, auto_merge)
            return run.call_args[0][0]

    def test_a_first_part_never_gets_auto_merge_and_an_extend_part_gets_it_on_request(self):
        first = self.cmd({"part": 1, "run": 5, "depends_on": None}, True)
        self.assertNotIn("--auto-merge", first)
        ext = self.cmd({"part": 2, "run": 5, "depends_on": "#7"}, True)
        self.assertIn("--auto-merge", ext)
        self.assertEqual(ext[ext.index("--depends-on") + 1], "#7")
        self.assertNotIn("--auto-merge", self.cmd({"part": 2, "run": 5, "depends_on": "#7"}, False))


if __name__ == "__main__":
    unittest.main()
