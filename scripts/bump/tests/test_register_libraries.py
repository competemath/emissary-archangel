import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("rl", Path(__file__).resolve().parents[2] / "register_libraries.py")
rl = importlib.util.module_from_spec(spec)
sys.modules["rl"] = rl
spec.loader.exec_module(rl)


class Roots(unittest.TestCase):
    def test_lean_lakefile(self):
        self.assertEqual(rl.roots_of("lean_lib RiemannRoch where\n  x := 1\nlean_lib «GRR»\n"), ["GRR", "RiemannRoch"])

    def test_toml_lakefile_with_name_after_other_keys(self):
        t = '[[lean_lib]]\nname = "A"\n\n[[lean_lib]]\nglobs = ["B.+"]\nname = "B"\n'
        self.assertEqual(rl.roots_of(t), ["A", "B"])

    def test_no_lib_no_roots(self):
        self.assertEqual(rl.roots_of("package x\nrequire mathlib from git \"u\"\n"), [])


class Apply(unittest.TestCase):
    def test_entries_land_in_both_registries_and_a_refused_one_does_not(self):
        d = Path(tempfile.mkdtemp())
        (d / "t/schemas").mkdir(parents=True); (d / "t/data/tentative").mkdir(parents=True); (d / "e").mkdir(); (d / "rec").mkdir()
        (d / "t/schemas/sources.json").write_text(json.dumps({"allowed": [], "licences": {}, "corpora": {}}))
        (d / "e/sources.json").write_text(json.dumps({"sources": {}}))
        (d / "rec/good.jsonl").write_text("{}\n")
        ok = {"repo": "o/good", "key": "good", "commit": "c" * 40, "licence": "MIT", "toolchain": "leanprover/lean4:v4.35.0", "roots": ["Good"], "verdict": "ok"}
        bad = {"repo": "o/bad", "key": "bad", "verdict": "archived"}
        (d / "meta.json").write_text(json.dumps([ok, bad]))
        rl.apply(["apply", "--tengoku", str(d / "t"), "--emissary", str(d / "e"), "--meta", str(d / "meta.json"), "--records", str(d / "rec")])
        t = json.loads((d / "t/schemas/sources.json").read_text())
        e = json.loads((d / "e/sources.json").read_text())
        self.assertEqual(t["allowed"], ["https://github.com/o/good"])
        self.assertEqual(t["licences"], {"https://github.com/o/good": "MIT"})
        self.assertEqual(t["corpora"], {"good": {"repo": "https://github.com/o/good", "commit": "c" * 40, "roots": ["Good"]}})
        self.assertEqual(list(e["sources"]), ["good"])
        self.assertTrue((d / "t/data/tentative/good.jsonl").exists())
        self.assertFalse((d / "t/data/tentative/bad.jsonl").exists())

    def _setup(self, registered=None):
        d = Path(tempfile.mkdtemp())
        (d / "t/schemas").mkdir(parents=True); (d / "t/data/tentative").mkdir(parents=True); (d / "e").mkdir(); (d / "rec").mkdir()
        corpora = {"foo": {"repo": "https://github.com/" + registered, "commit": "x", "roots": ["F"]}} if registered else {}
        (d / "t/schemas/sources.json").write_text(json.dumps({"allowed": [], "licences": {}, "corpora": corpora}))
        (d / "e/sources.json").write_text(json.dumps({"sources": {}}))
        (d / "rec/foo.jsonl").write_text("{}\n")
        return d

    def _run(self, d, metas):
        (d / "meta.json").write_text(json.dumps(metas))
        rl.apply(["apply", "--tengoku", str(d / "t"), "--emissary", str(d / "e"), "--meta", str(d / "meta.json"), "--records", str(d / "rec")])

    def test_a_key_registered_for_another_repository_is_refused(self):
        d = self._setup(registered="a/foo")
        m = {"repo": "b/foo", "key": "foo", "commit": "c" * 40, "licence": "MIT", "toolchain": "t", "roots": ["F"], "verdict": "ok"}
        with self.assertRaises(SystemExit):
            self._run(d, [m])

    def test_two_repositories_with_one_key_are_refused(self):
        d = self._setup()
        m = {"repo": "a/foo", "key": "foo", "commit": "c" * 40, "licence": "MIT", "toolchain": "t", "roots": ["F"], "verdict": "ok"}
        with self.assertRaises(SystemExit):
            self._run(d, [m, {**m, "repo": "b/foo"}])


class Requires(unittest.TestCase):
    def test_lean_and_toml_spellings(self):
        self.assertEqual(rl.requires_of('require mathlib from git "u"\nrequire «foo-bar» from git "v"\n'), ["foo-bar", "mathlib"])
        self.assertEqual(rl.requires_of('[[require]]\nname = "mathlib"\nscope = "x"\n\n[[require]]\nname = "other"\n'), ["mathlib", "other"])

    def test_none(self):
        self.assertEqual(rl.requires_of("package x\n"), [])


class Twins(unittest.TestCase):
    def test_a_copy_is_found_and_a_small_overlap_is_not(self):
        names = {"grr": {f"a{i}" for i in range(100)}, "copy": {f"a{i}" for i in range(100)}, "vendors": {f"a{i}" for i in range(60)} | {f"b{i}" for i in range(40)},
                 "own": {f"c{i}" for i in range(100)} | {f"a{i}" for i in range(40)}}  # 40% shared with grr: below the 0.5 cutoff
        got = rl.mostly_overlapping(names, ["copy", "vendors", "own"])
        self.assertIn(("copy", "grr", 1.0), got)
        self.assertIn(("vendors", "grr", 0.6), got)
        self.assertFalse([g for g in got if g[0] == "own"])

    def test_two_new_libraries_that_are_twins_are_reported_once(self):
        names = {"a": {"x", "y"}, "b": {"x", "y"}}
        self.assertEqual(rl.mostly_overlapping(names, ["a", "b"]), [("b", "a", 1.0)])


if __name__ == "__main__":
    unittest.main()


class RefusedLines(unittest.TestCase):
    """refine reads the record lines both record rules refuse. The real case: batch 7 (13 Nov 2026), the first registration whose records met
    lint_banked.py: it prints `data/x.jsonl:N (Name): reason` and refine read only `data/x.jsonl:N: reason`, so it stopped as if the lint had
    failed without naming a record (fixtures/real-record-rules-2026-11-13.json: both rules' real output on that commit)."""

    REAL = json.loads((Path(__file__).resolve().parent / "fixtures" / "real-record-rules-2026-11-13.json").read_text())

    @staticmethod
    def listed(text):
        return [ln for ln in text.splitlines() if ln.startswith("  data/")]

    def test_every_line_of_the_real_lint_is_read(self):
        text = self.REAL["lint_banked"]
        got = rl.refused_lines(text)
        self.assertEqual(len(got), len(self.listed(text)))
        self.assertGreaterEqual(len(got), 10)
        self.assertEqual(got[0], ("data/tentative/palomar-qseries-row-factorization.jsonl", 1084, "native_decide (trusts the compiler)"))

    def test_every_line_of_the_real_validator_is_read(self):
        text = self.REAL["validate_records"]
        got = rl.refused_lines(text)
        self.assertEqual(len(got), len(self.listed(text)))
        self.assertGreaterEqual(len(got), 3)
        self.assertIn(("data/tentative/sandrones-library.jsonl", 110, "duplicate name in this PR: SandronesLibrary.Topology.dist_convexComb_left_le"), got)

    def test_names_with_brackets_and_reasons_with_colons(self):
        got = rl.refused_lines("  data/tentative/a.jsonl:3 (A.«f (x)».g): banned: #eval\n  data/tentative/a.jsonl:4: x: y (z): w\n")
        self.assertEqual(got, [("data/tentative/a.jsonl", 3, "banned: #eval"), ("data/tentative/a.jsonl", 4, "x: y (z): w")])

    def test_other_lines_are_not_records(self):
        self.assertEqual(rl.refused_lines("FAIL: banked content lint:\n  Tengoku/X.lean:3: native_decide\ncontent lint OK\n"), [])

    def test_mutant_the_pattern_as_it_was_reads_no_lint_line(self):
        import re

        old = re.compile(r"^\s*(data/\S+\.jsonl):(\d+): (.*)$", re.M)
        self.assertEqual(len(old.findall(self.REAL["lint_banked"])), 0)  # what stopped batch 7's refine
        self.assertEqual(len(old.findall(self.REAL["validate_records"])), len(self.listed(self.REAL["validate_records"])))
