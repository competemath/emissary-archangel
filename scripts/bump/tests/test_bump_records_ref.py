"""A bump reads the library's records from where the tree holds them, and a bump that finds none stops at its plan, saying so.

The real case: rankamplificationtotient (batch 6), 13 Nov 2026. Its setup finished at 02:47:37 and bump-pickup started its bump at 02:48 (run 43354641538) with no tengoku_ref. Its records were on
content/fatex-libraries-batch-6 (competemath/tengoku#789, not merged), so the plan read main, found `entries: 0 modules with entries: 0`, planned no shard, and the run failed only at compose with
"merge: no shard pack in ../shards ... the run named by recut_from has none", which says nothing of the cause. A person re-ran it with tengoku_ref (run 43355094704).

Invariants:
  1. bump_pickup gives the bump the branch tree_records finds (the real #789 and the real setup record), '' (no tengoku_ref) when the records are on main, and starts nothing when they are nowhere.
  2. The plan step of bump-sharded.yml, its real text run with the real readers (gate2_batch, tentative_files, plan_shards, tolerant_build) over a library whose records the tree checkout does not hold,
     fails, naming the library and the branch read; with 303 real records of the library in the checkout it plans shards.
  3. Mutants: the dispatch without the branch (the real bug) has no tengoku_ref; the plan step without the guard passes with `shards=[]` (what the real run did)."""

import gzip
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import bump_pickup as bp  # noqa: E402
import tree_records as tr  # noqa: E402

ROOT = HERE.parents[2]
KEY = "rankamplificationtotient"
BRANCH = "content/fatex-libraries-batch-6"
SETUP_AT = 1794538057  # 2026-11-13T02:47:37Z, the record's finishedAt
REC = {KEY: {"exported": 160, "modules": 160}}  # data/exports/rankamplificationtotient/setup.ci.json on main, 13 Nov 2026
PR789 = {"number": 789, "branch": BRANCH, "repo": "competemath/tengoku", "files": [
    "data/tentative/ck-hopf-formalization.jsonl", "data/tentative/lean-eval-pi-succ-sphere-n-mulequiv-zmod-two.jsonl", "data/tentative/nlalib.jsonl",
    "data/tentative/rankamplificationtotient.jsonl", "schemas/sources.json"]}
FILES = set(tr.tentative_files(KEY, {}))


class PickupGivesTheBranch(unittest.TestCase):
    def refs(self, on_main, prs):
        return {KEY: tr.records_ref(KEY, {}, FILES if on_main else set(), prs, "competemath/tengoku")}

    def test_the_real_case_gets_its_branch(self):
        refs = self.refs(False, [PR789])
        key, notes = bp.decide({KEY: SETUP_AT}, REC, {}, set(), 20, refs=refs)
        self.assertEqual((key, notes), (KEY, []))
        args = bp.dispatch_args(KEY, 20, "competemath/emissary-archangel", refs[KEY][0])
        self.assertEqual(args[-2:], ["-f", f"tengoku_ref={BRANCH}"])

    def test_records_on_main_need_no_branch(self):
        refs = self.refs(True, [PR789])
        self.assertEqual(bp.decide({KEY: SETUP_AT}, REC, {}, set(), 20, refs=refs)[0], KEY)
        self.assertNotIn("tengoku_ref", " ".join(bp.dispatch_args(KEY, 20, "o/r", refs[KEY][0])))

    def test_records_nowhere_start_nothing(self):
        for prs in ([], [dict(PR789, repo="someone/tengoku")], [PR789, dict(PR789, number=790)]):
            key, notes = bp.decide({KEY: SETUP_AT}, REC, {}, set(), 20, refs=self.refs(False, prs))
            self.assertIsNone(key, prs)
            self.assertTrue(notes[0].startswith(f"{KEY}: records"), notes)

    def test_without_refs_the_old_callers_are_unchanged(self):
        self.assertEqual(bp.decide({KEY: SETUP_AT}, REC, {}, set(), 20)[0], KEY)

    def test_mutant_the_dispatch_as_it_was_reads_main(self):
        self.assertNotIn("tengoku_ref", " ".join(bp.dispatch_args(KEY, 20, "o/r")))  # what run 43354641538 got

    def test_a_bad_branch_is_refused(self):
        for bad in ("a b", "$(id)", "x;y"):
            with self.assertRaises(ValueError):
                bp.dispatch_args(KEY, 20, "o/r", bad)

    def test_the_pickup_reads_the_registry(self):
        steps = yaml.safe_load((ROOT / ".github" / "workflows" / "bump-pickup.yml").read_text())["jobs"]["pickup"]["steps"]
        self.assertIn('"/sources.json"', steps[0]["run"])


def plan_text() -> str:
    steps = yaml.safe_load((ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text())["jobs"]["plan"]["steps"]
    run = next(s["run"] for s in steps if s.get("id") == "p")
    return run[run.index("python3 - <<'PY'\n") + len("python3 - <<'PY'\n") : run.rindex("PY")]


def run_plan(code: str, records: str | None, ref: str = ""):
    """the step's Python in a directory laid out as the job lays it out: emissary/ (scripts, sources.json, the setup record, lib/) and tengoku/ (the sparse checkout)"""
    with tempfile.TemporaryDirectory() as d:
        e = Path(d) / "emissary"
        e.mkdir()
        (e / "scripts").symlink_to(ROOT / "scripts")
        (e / "sources.json").symlink_to(ROOT / "sources.json")
        (e / "data" / "exports" / KEY).mkdir(parents=True)
        (e / "data" / "exports" / KEY / "setup.ci.json").write_text(json.dumps({"roots": ["RankAmplification"]}))
        lib = e / "lib" / "RankAmplification"
        lib.mkdir(parents=True)
        (lib / "SupplierEncodingUnconditional.lean").write_text("import Mathlib\n\ntheorem a : True := trivial\n")
        (lib / "SUnitQuantitative.lean").write_text("import RankAmplification.SupplierEncodingUnconditional\n\ntheorem b : True := trivial\n")
        t = Path(d) / "tengoku" / "data" / "tentative"
        t.mkdir(parents=True)
        if records is not None:
            (t / f"{KEY}.jsonl").write_text(records)
        out = Path(d) / "out"
        out.write_text("")
        env = {**os.environ, "KEY": KEY, "SHARDS": "0", "MAX_TARGETS": "400", "TENGOKU_REF": ref, "ONLY_MODULES": "", "GITHUB_OUTPUT": str(out)}
        r = subprocess.run([sys.executable, "-c", code], cwd=e, env=env, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr, out.read_text()


class PlanStopsWithoutRecords(unittest.TestCase):
    CODE = plan_text()
    REAL = gzip.open(HERE / "fixtures" / "real-rank-records-2026-11-13.jsonl.gz", "rt").read()

    def test_the_fixture_is_the_real_one(self):
        lines = self.REAL.splitlines()
        self.assertEqual(len(lines), 303)
        self.assertTrue(all(json.loads(x)["library"] == KEY for x in lines))

    def test_no_records_stops_the_plan_and_says_why(self):
        for ref, said in (("", "main"), (BRANCH, BRANCH)):
            code, out, gh_out = run_plan(self.CODE, None, ref)
            self.assertNotEqual(code, 0, out)
            self.assertIn(f"::error::no tentative records of {KEY} on the tree's {said}", out)
            self.assertNotIn("shards=", gh_out)

    def test_real_records_are_planned(self):
        code, out, gh_out = run_plan(self.CODE, self.REAL)
        self.assertEqual(code, 0, out)
        self.assertIn("entries: 303 modules with entries: 2", out)
        shards = json.loads(gh_out.split("shards=", 1)[1])
        self.assertGreaterEqual(len(shards), 1)

    def test_mutant_without_the_guard_passes_with_no_shard(self):
        lines = self.CODE.splitlines(keepends=True)
        i = next(n for n, ln in enumerate(lines) if ln.lstrip().startswith("if not ents:"))
        without = "".join(lines[:i] + lines[i + 2 :])
        self.assertNotEqual(without, self.CODE)
        code, out, gh_out = run_plan(without, None)
        self.assertEqual(code, 0, out)
        self.assertIn("entries: 0 modules with entries: 0", out)  # the real run's line
        self.assertEqual(gh_out.strip(), "shards=[]")


if __name__ == "__main__":
    unittest.main()
