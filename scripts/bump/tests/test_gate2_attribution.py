"""A pass is credited only to a module Gate 2 judged in that shard (scripts/bump/gate2_batch.py parse --only, attribute()).

The real case (fixtures/aintlib_shard19_attribution.json): aintlib has two copies of one file, LutzNagell/EllipticDivisibilitySequence and
HasseWeil/Foundation/Auxiliary/EllipticDivisibilitySequence, declaring the same root names; tengoku's records hold one line per copy (956 names of aintlib have records in
two files). Shard 19 judged the HasseWeil copy (a target) and passed 18 of those names; parse looked each name up by name, found the LutzNagell record first and credited
the passes to LutzNagell.EllipticDivisibilitySequence, a module shard 19 never built. The keep step then imported it, died on "unknown module prefix 'LutzNagell'" and kept
nothing, and 7 of shard 19's theorems that no other shard kept were cut from aintlib part 2 while its manifest listed them (tengoku #770).

The fixture: shard 19's real Gate 2 log, its 46 targets, the ranges its build left (75 modules), and every tengoku record of a name in the log.

Invariants:
  I1  every module of passed.json is one the shard judged (a target);
  I2  a name judged in a target is credited to the target that declares it, however the records order the copies;
  I3  a pass no target declares, or more than one does, is credited to none and listed under pass_unattributed;
  I4  without --only (bump-library.yml: one job judges every module) nothing changes.
Mutant: crediting the record's module unchecked (the old parse) puts LutzNagell back (fails I1).
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
FX = json.loads((HERE / "tests" / "fixtures" / "aintlib_shard19_attribution.json").read_text())
EDS_H = "HasseWeil.Foundation.Auxiliary.EllipticDivisibilitySequence"
EDS_L = "LutzNagell.EllipticDivisibilitySequence"


def run_parse(only: list[str] | None, ranges: dict | None = None, killed: list[str] | None = None) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        return _run_parse(Path(tmp), only, ranges, killed)


def _run_parse(d: Path, only: list[str] | None, ranges: dict | None, killed: list[str] | None) -> dict:
    (d / "gate2.log").write_text(FX["gate2_log"])
    (d / "tent.jsonl").write_text("".join(FX["tentative"]))
    for mod, rows in (FX["ranges"] if ranges is None else ranges).items():
        f = d / "lib" / ".lake" / "build" / "lib" / "lean" / (mod.replace(".", "/") + ".olean.ranges.json")
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(json.dumps(rows))
    cmd = [sys.executable, str(HERE / "gate2_batch.py"), "parse", "--log", str(d / "gate2.log"), "--ledger", str(d / "none.jsonl"), "--out", str(d / "results.json"),
           "--lib", str(d / "lib"), "--tentative", str(d / "tent.jsonl")]
    if only is not None:
        cmd += ["--only", ",".join(only)]
    if killed is not None:
        (d / "killed.json").write_text(json.dumps(killed))
        cmd += ["--killed", str(d / "killed.json")]
    subprocess.run(cmd, check=True, capture_output=True, text=True)
    return {"passed": json.loads((d / "passed.json").read_text()), "results": json.loads((d / "results.json").read_text())}


class RealShard19(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixed = run_parse(FX["targets"])
        cls.unscoped = run_parse(None)

    def test_the_fixture_is_the_real_case(self):
        self.assertEqual(len(FX["targets"]), 46)
        self.assertIn(EDS_H, FX["targets"])
        self.assertNotIn(EDS_L, FX["targets"])
        self.assertEqual(len(FX["passed_before_the_fix"][EDS_L]), 18)  # what the shard's real passed.json credited to the copy it never built

    def test_every_credited_module_was_judged_here(self):  # I1
        self.assertTrue(self.fixed["passed"])
        self.assertLessEqual(set(self.fixed["passed"]), set(FX["targets"]))

    def test_the_eighteen_go_to_the_copy_that_was_judged(self):  # I2
        wrong = set(FX["passed_before_the_fix"][EDS_L])
        self.assertNotIn(EDS_L, self.fixed["passed"])
        self.assertLessEqual(wrong & set(sum(self.unscoped["passed"].values(), [])), set(self.fixed["passed"].get(EDS_H, [])))
        declared = {row[0] for row in FX["ranges"][EDS_H]}
        for n in self.fixed["passed"].get(EDS_H, []):
            self.assertIn(n, declared)

    def test_the_old_reading_is_the_bug(self):  # the mutant: credit the record's module unchecked
        self.assertIn(EDS_L, self.unscoped["passed"])
        self.assertFalse(set(self.unscoped["passed"]) <= set(FX["targets"]))

    def test_a_pass_no_target_declares_is_credited_to_none(self):  # I3
        ranges = {m: rows for m, rows in FX["ranges"].items() if m != EDS_H}
        r = run_parse(FX["targets"], ranges)  # the HasseWeil copy's ranges are gone: nothing judged here declares the 18 that the records put in the LutzNagell copy
        wrong = set(FX["passed_before_the_fix"][EDS_L]) & set(sum(self.unscoped["passed"].values(), []))
        self.assertTrue(wrong)
        self.assertNotIn(EDS_L, r["passed"])
        self.assertFalse(wrong & set(r["passed"].get(EDS_H, [])))  # names whose record names the HasseWeil copy stay there: that copy was judged
        self.assertLessEqual(wrong, set(r["results"]["pass_unattributed"]))
        self.assertLessEqual(set(r["passed"]), set(FX["targets"]))

    def test_without_the_judged_list_nothing_changes(self):  # I4
        self.assertEqual(self.unscoped["results"]["pass_unattributed"], [])
        total = sum(len(v) for v in self.unscoped["passed"].values())
        self.assertEqual(total, sum(len(v) for v in self.fixed["passed"].values()) + len(self.fixed["results"]["pass_unattributed"]))


class NoVerdictAndNames(unittest.TestCase):
    def test_a_target_with_no_verdict_is_not_judged(self):
        """gate2-killed.json lists the targets Gate 2 skipped or that killed Lean: a pass is not credited to one of them (cubic, #173)"""
        r = run_parse(FX["targets"], killed=[EDS_H])
        self.assertNotIn(EDS_H, r["passed"])
        self.assertNotIn(EDS_L, r["passed"])
        self.assertTrue(set(r["results"]["pass_unattributed"]))
        self.assertLessEqual(set(r["passed"]), set(FX["targets"]) - {EDS_H})

    def test_a_dotted_last_component_finds_its_sidecar(self):
        sys.path.insert(0, str(HERE))
        import gate2_batch as g

        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)
            f = lib / ".lake" / "build" / "lib" / "lean" / "Foo" / "1102.4662.olean.ranges.json"
            f.parent.mkdir(parents=True)
            f.write_text(json.dumps([["Foo.bar", 1, 2]]))
            self.assertEqual(g.declared_in(lib, "Foo.«1102.4662»"), {"Foo.bar"})
            self.assertEqual(g.declared_in(lib, "Foo.Missing"), set())

    def test_the_merge_keeps_the_unattributed_names(self):
        """shard_pack.py merge adds every shard's pass_unattributed to the run's results (cubic, #173)"""
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            for i, names in enumerate((["a.x", "a.y"], ["a.y", "b.z"])):
                d = t / "shards" / f"shard-k-{i}"
                (d / "src").mkdir(parents=True)
                (d / "gate2-killed.json").write_text("[]")
                (d / "gate2-results.json").write_text(json.dumps({"checked": 1, "pass": 1, "pass_unattributed": names}))
            (t / "logs").mkdir()  # the workflow makes it (mkdir -p ../merged ../logs)
            subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "merge", "--shards", str(t / "shards"), "--out", str(t / "merged"), "--logs", str(t / "logs")],
                           check=True, capture_output=True, text=True)
            got = json.loads((t / "logs" / "gate2-results.json").read_text())
            self.assertEqual(got["pass_unattributed"], ["a.x", "a.y", "b.z"])


class Workflow(unittest.TestCase):
    def test_the_shard_parses_with_its_targets(self):
        text = (HERE.parents[1] / ".github" / "workflows" / "bump-shard.yml").read_text()
        line = next(ln for ln in text.splitlines() if "gate2_batch.py parse" in ln)
        self.assertIn('--only "$mine" --killed gate2-killed.json', line)
        self.assertIn('mine=$(paste -sd, targets.txt)', text)


if __name__ == "__main__":
    unittest.main()
