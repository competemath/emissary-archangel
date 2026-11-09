"""Which library the hourly pickup bumps (bump_pickup.py), on the repository's real history (fixtures/real-bump-pickup.json.gz: 154 real setup commits of 143 libraries, 359 real bump runs, 170 real part
titles) and on 5,000 random states.

Invariants: at most one library starts; never a setup from before FIRST_SETUP; never a library that has a bump started after its setup; never one with a part open; never one that exported nothing or is
over MAX_MODULES; nothing starts with too few free runners; the smallest ready library goes first; only a commit a setup job writes counts as a setup."""

import gzip
import json
import random
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import bump_pickup as bp  # noqa: E402
import yaml  # noqa: E402

R = json.loads(gzip.open(HERE / "fixtures" / "real-bump-pickup.json.gz").read())
AFTER = bp.FIRST_SETUP + 3600


class RealHistory(unittest.TestCase):
    def setUp(self):
        self.published = bp.setups(R["log"])
        self.bumps = bp.last_bumps(R["runs"])

    def test_the_case_is_the_real_one(self):
        self.assertGreaterEqual(len(self.published), 140)
        self.assertIn("flt-anthropic", self.published)
        self.assertIn("leanbridge", self.bumps)
        self.assertGreater(len(bp.open_parts(R["part_titles"])), 50)

    def test_the_real_past_starts_nothing(self):
        """the day this is switched on, no old setup may start a bump"""
        key, notes = bp.decide(self.published, R["records"], self.bumps, set(), 20)
        self.assertIsNone(key)
        self.assertEqual(notes, [])

    def test_every_real_library_set_up_again_today_is_picked_or_explained(self):
        for k, rec in R["records"].items():
            if k not in self.published:
                continue
            key, notes = bp.decide({k: AFTER}, R["records"], {}, set(), 20)
            if rec["exported"] < 1 or rec["modules"] > bp.MAX_MODULES:
                self.assertIsNone(key, k)
                self.assertEqual(len(notes), 1, k)
            else:
                self.assertEqual(key, k)

    def test_flt_is_left_to_its_own_lane(self):
        key, notes = bp.decide({"flt-anthropic": AFTER}, R["records"], {}, set(), 20)
        self.assertIsNone(key)
        self.assertIn("too big", notes[0])

    def test_the_real_titles_with_a_from_tree_suffix_name_the_library(self):
        self.assertEqual(bp.last_bumps([{"displayTitle": "bump-sharded foundation (from tree)", "createdAt": "2026-11-09T08:00:00Z"}]), {"foundation": bp.FIRST_SETUP})

    def test_real_part_titles(self):
        self.assertEqual(bp.open_parts(["intake: tnlean part 1 of 1 (959 verified theorems in 119 modules)", "extend: lean-pool part 11 of 40 (1 verified)", "build(deps): bump the actions group"]), {"tnlean", "lean-pool"})


class Reading(unittest.TestCase):
    """what GitHub answers, however many pages it takes"""

    def test_every_page_of_runs_and_jobs_counts(self):
        calls = []

        def gh(*args):
            calls.append(args)
            path = args[2]
            if "/jobs" in path:
                return [100, 3]  # two pages of one run
            if "tengoku?" in path or "repos/competemath/tengoku/actions/runs?status=in_progress" in path:
                return [1, 2]
            return []

        self.assertEqual(bp.runners_in_use(gh), 206)
        self.assertTrue(all("--paginate" in c for c in calls))

    def test_both_bump_workflows_are_read_since_the_window(self):
        calls = []

        def gh(*args):
            calls.append(args)
            answers = {
                "repos/o/r/actions/workflows/bump-sharded.yml/runs?per_page=100&created=>=2026-11-09T08:00:00Z": "bump-sharded j",
                "repos/o/r/actions/workflows/bump-library.yml/runs?per_page=100&created=>=2026-11-09T08:00:00Z": "bump k",
            }
            return [{"displayTitle": answers[args[2]], "createdAt": "2026-11-09T09:00:00Z"}]

        runs = bp.bump_runs("o/r", bp.FIRST_SETUP, gh)
        self.assertEqual(set(bp.last_bumps(runs)), {"j", "k"})
        self.assertEqual(len(calls), 2)
        self.assertTrue(all("--paginate" in c for c in calls))

    def test_a_list_that_may_be_cut_short_stops_the_pickup(self):
        full = [{"displayTitle": "bump-sharded j", "createdAt": "2026-11-09T09:00:00Z"}] * bp.LIST_LIMIT
        with self.assertRaisesRegex(RuntimeError, "cut short"):
            bp.bump_runs("o/r", bp.FIRST_SETUP, lambda *a: full)
        with self.assertRaisesRegex(RuntimeError, "cut short"):
            bp.open_titles("o/t", lambda *a: ["x"] * bp.LIST_LIMIT)

    def test_a_bump_of_a_small_library_counts_as_its_bump(self):
        """bump-library.yml names its runs `bump KEY`, as on the real stafford38-formal"""
        runs = [{"displayTitle": "bump stafford38-formal", "createdAt": "2026-11-09T09:00:00Z"}]
        bumps = bp.last_bumps(runs)
        self.assertEqual(list(bumps), ["stafford38-formal"])
        self.assertIsNone(bp.decide({"stafford38-formal": AFTER - 60}, {"stafford38-formal": {"exported": 3, "modules": 3}}, bumps, set(), 20)[0])

    def test_a_setup_older_than_the_window_waits_no_longer(self):
        rec = {"a": {"exported": 5, "modules": 5}}
        now = AFTER + 30 * 86400
        self.assertEqual(bp.window_start(now), now - bp.WINDOW_DAYS * 86400)
        self.assertEqual(bp.window_start(bp.FIRST_SETUP + 5), bp.FIRST_SETUP)
        self.assertIsNone(bp.decide({"a": AFTER}, rec, {}, set(), 20, bp.window_start(now))[0])
        self.assertEqual(bp.decide({"a": now - 60}, rec, {}, set(), 20, bp.window_start(now))[0], "a")


class Commits(unittest.TestCase):
    def log(self, subject, key="k"):
        return f"@{AFTER}\t{subject}\n\ndata/exports/{key}/setup.ci.json\n"

    def test_both_kinds_of_setup_commit_count(self):
        self.assertEqual(bp.setups(self.log("exports: k (runner)")), {"k": AFTER})
        self.assertEqual(bp.setups(self.log("exports: k (sharded runner)")), {"k": AFTER})

    def test_any_other_commit_over_the_records_is_not_a_setup(self):
        for s in ["sweep: every setup record gains a field", "exports: k", "exports: k (runner) again", "Merge pull request #9: exports: k (runner)", "exports: k;x (runner)"]:
            self.assertEqual(bp.setups(self.log(s)), {}, s)

    def test_a_commit_that_names_another_library_counts_for_nothing(self):
        self.assertEqual(bp.setups(self.log("exports: other (runner)", "k")), {})

    def test_the_newest_setup_wins(self):
        log = f"@{AFTER + 9}\texports: k (runner)\n\ndata/exports/k/setup.ci.json\n@{AFTER}\texports: k (runner)\n\ndata/exports/k/setup.ci.json\n"
        self.assertEqual(bp.setups(log), {"k": AFTER + 9})


class Decide(unittest.TestCase):
    rec = {"a": {"exported": 5, "modules": 50}, "b": {"exported": 5, "modules": 10}}

    def test_the_smallest_goes_first_and_only_one(self):
        key, notes = bp.decide({"a": AFTER, "b": AFTER}, self.rec, {}, set(), 20)
        self.assertEqual(key, "b")
        self.assertEqual(notes, ["a: waits for the next run"])

    def test_a_bump_started_after_the_setup_is_its_bump_even_a_failed_one(self):
        self.assertIsNone(bp.decide({"a": AFTER}, self.rec, {"a": AFTER + 1}, set(), 20)[0])

    def test_a_bump_older_than_the_setup_does_not_count(self):
        self.assertEqual(bp.decide({"a": AFTER}, self.rec, {"a": AFTER - 1}, set(), 20)[0], "a")

    def test_a_part_open_on_the_tree_holds_it_back(self):
        key, notes = bp.decide({"a": AFTER}, self.rec, {}, {"a"}, 20)
        self.assertIsNone(key)
        self.assertIn("part is open", notes[0])

    def test_too_few_free_runners(self):
        self.assertIsNone(bp.decide({"a": AFTER}, self.rec, {}, set(), bp.NEED_FREE - 1)[0])
        self.assertEqual(bp.decide({"a": AFTER}, self.rec, {}, set(), bp.NEED_FREE)[0], "a")

    def test_parallel_follows_the_free_runners(self):
        self.assertEqual([bp.parallel_for(f) for f in (10, 12, 14, 16, 20)], [3, 4, 5, 6, 6])

    def test_the_dispatch_is_the_standard_bump(self):
        a = bp.dispatch_args("aintlib", 20, "o/r")
        self.assertEqual(a[:8], ["gh", "workflow", "run", "bump-sharded.yml", "-R", "o/r", "--ref", "main"])
        got = dict(x.split("=", 1) for x in a[a.index("-f") + 1 :: 2])
        self.assertEqual(got, {"key": "aintlib", "parallel": "6", "shards": "0", "max_targets": "400", "parts": "300", "imports": "faithful", "verify": "true", "verify_partial": "true", "verify_modes": "proposed"})

    def test_property(self):
        rnd = random.Random(11)
        names = [f"L{i}" for i in range(12)]
        started = 0
        for case in range(5000):
            pub = {k: bp.FIRST_SETUP + rnd.randint(-50, 50) for k in rnd.sample(names, rnd.randint(0, 12))}
            rec = {k: {"exported": rnd.choice([0, 1, 9]), "modules": rnd.choice([1, 40, bp.MAX_MODULES, bp.MAX_MODULES + 1])} for k in names if rnd.random() < 0.9}
            bumps = {k: bp.FIRST_SETUP + rnd.randint(-80, 80) for k in names if rnd.random() < 0.4}
            parts = {k for k in names if rnd.random() < 0.2}
            free = rnd.randint(0, 20)
            key, _ = bp.decide(pub, rec, bumps, parts, free)
            eligible = [k for k in pub if pub[k] >= bp.FIRST_SETUP and bumps.get(k, 0) < pub[k] and k in rec and rec[k]["exported"] >= 1 and rec[k]["modules"] <= bp.MAX_MODULES and k not in parts]
            if key is None:
                self.assertTrue(free < bp.NEED_FREE or not eligible, case)
            else:
                started += 1
                self.assertIn(key, eligible, case)
                self.assertGreaterEqual(free, bp.NEED_FREE, case)
                self.assertEqual(rec[key]["modules"], min(rec[k]["modules"] for k in eligible), case)
        self.assertGreater(started, 500)


class Workflow(unittest.TestCase):
    def test_it_can_dispatch_and_nothing_else(self):
        w = yaml.safe_load((HERE.parents[2] / ".github" / "workflows" / "bump-pickup.yml").read_text())
        self.assertEqual(w["permissions"], {})
        job = w["jobs"]["pickup"]
        self.assertEqual(job["permissions"], {"actions": "write", "contents": "read"})
        self.assertIn("LANE_ENABLED", job["if"])
        self.assertIn("refs/heads/main", job["if"])
        text = json.dumps(job["steps"])
        self.assertNotIn("${{", text)
        self.assertNotIn("lake", text)
        self.assertIn("python3 scripts/bump/bump_pickup.py", job["steps"][-1]["run"])


if __name__ == "__main__":
    unittest.main()
