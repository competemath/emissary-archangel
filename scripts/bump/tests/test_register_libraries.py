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

class TrustedNames(unittest.TestCase):
    """15 Nov 2026, batch 8: refine ran in a sparse checkout without data/trusted, so it could not see that symmmoncoherence's `exchange` (theorem exchange : (Fin.preCoxeterSystem n).ExchangeProperty')
    is the name of a trusted record (the whiskering lemma of mathlib-categorytheory); gitar found it on the records PR. The names are now read from origin/main with `git show`."""

    def repo(self, trusted, tentative_old=None, tentative_new=None):
        import subprocess
        d = Path(tempfile.mkdtemp())
        run = lambda *a: subprocess.run(["git", "-C", str(d), "-c", "user.name=t", "-c", "user.email=t@t", *a], check=True, capture_output=True)
        run("init", "-q", "-b", "main")
        (d / "data/trusted").mkdir(parents=True); (d / "data/tentative").mkdir(parents=True)
        (d / "data/trusted/mathlib-categorytheory.jsonl").write_text("".join(json.dumps({"name": n}) + "\n" for n in trusted))
        for k, names in (tentative_old or {}).items():
            (d / f"data/tentative/{k}.jsonl").write_text("".join(json.dumps({"name": n}) + "\n" for n in names))
        run("add", "-A"); run("commit", "-q", "-m", "base"); run("update-ref", "refs/remotes/origin/main", "HEAD")
        for k, names in (tentative_new or {}).items():
            (d / f"data/tentative/{k}.jsonl").write_text("".join(json.dumps({"name": n}) + "\n" for n in names))
        run("add", "-A"); run("commit", "-q", "-m", "records")
        return d

    def test_nested_trusted_files_are_read_too(self):
        """cubic on #209 (P1, P2): ls-tree without -r listed only the top level of data/trusted; today every file is at the top, a subfolder would have been skipped silently"""
        import subprocess
        d = self.repo(["top_name"], tentative_new={"lib": ["nested_name", "top_name", "free_name"]})
        run = lambda *a: subprocess.run(["git", "-C", str(d), "-c", "user.name=t", "-c", "user.email=t@t", *a], check=True, capture_output=True)
        (d / "data/trusted/sub/deeper").mkdir(parents=True)
        (d / "data/trusted/sub/deeper/more.jsonl").write_text(json.dumps({"name": "nested_name"}) + "\n")
        run("add", "-A"); run("commit", "-q", "-m", "nested trusted"); run("update-ref", "refs/remotes/origin/main", "HEAD")
        t = rl.trusted_names(str(d))
        self.assertEqual(t, {"top_name", "nested_name"})
        # the records are on main already, so none is new: add a new file with the nested name and judge it
        (d / "data/tentative/lib2.jsonl").write_text(json.dumps({"name": "nested_name"}) + "\n" + json.dumps({"name": "free_name"}) + "\n")
        run("add", "-A"); run("commit", "-q", "-m", "new records")
        self.assertEqual(rl.trusted_clashes(str(d), t), {"data/tentative/lib2.jsonl": {1}})

    def test_the_real_case_exchange_is_found_by_line_without_data_trusted_in_the_checkout(self):
        d = self.repo(["exchange", "CategoryTheory.whiskerLeft_id"], tentative_new={"symmmoncoherence": ["SymmMonCoherence.foo", "exchange", "SymmMonCoherence.bar"]})
        import shutil; shutil.rmtree(d / "data/trusted")  # a sparse checkout has none
        t = rl.trusted_names(str(d))
        self.assertEqual(t, {"exchange", "CategoryTheory.whiskerLeft_id"})
        self.assertEqual(rl.trusted_clashes(str(d), t), {"data/tentative/symmmoncoherence.jsonl": {2}})

    def test_a_record_already_on_main_is_not_new_and_a_qualified_name_is_not_a_clash(self):
        d = self.repo(["exchange"], tentative_old={"lib": ["exchange"]}, tentative_new={"lib": ["exchange", "Lib.exchange"]})
        self.assertEqual(rl.trusted_clashes(str(d), rl.trusted_names(str(d))), {})

    def test_two_thousand_records_every_clash_and_only_those(self):
        import random
        rnd = random.Random(15112026)
        trusted = [f"t{i}" for i in range(500)]
        names = [rnd.choice([f"t{rnd.randrange(900)}", f"x{rnd.randrange(10**6)}"]) for _ in range(2000)]
        d = self.repo(trusted, tentative_new={"big": names})
        want = {i for i, n in enumerate(names, 1) if n in set(trusted)}
        got = rl.trusted_clashes(str(d), rl.trusted_names(str(d)))
        self.assertEqual(got.get("data/tentative/big.jsonl", set()), want)
        self.assertGreater(len(want), 200)  # the draw really has clashes

    def test_refine_applies_it_and_counts_the_reason(self):
        import inspect
        src = inspect.getsource(rl.refine)
        self.assertIn("trusted_clashes(T, trusted)", src)
        self.assertIn('reasons["already trusted name"]', src)
        self.assertLess(src.index("trusted = trusted_names(T)"), src.index("for _ in range(REFINE_ROUNDS)"))

    def test_mutant_without_the_trusted_names_nothing_is_found(self):
        d = self.repo(["exchange"], tentative_new={"lib": ["exchange"]})
        self.assertEqual(rl.trusted_clashes(str(d), set()), {})  # the old refine: no trusted names, no clash: this is what let `exchange` through
        self.assertEqual(rl.trusted_clashes(str(d), rl.trusted_names(str(d))), {"data/tentative/lib.jsonl": {1}})



class RefineSparse(unittest.TestCase):
    """17 Nov 2026, batch 10: `refine` ran against a sparse tengoku checkout (data/ left out). A plain `git add -A` skips paths outside the sparse set, so the lines the record
    rules had cut never reached the commit, the same lines were refused again, and refine stopped after 40 rounds (and again after 3,000)."""

    @staticmethod
    def git(T, *a):
        import subprocess
        return subprocess.run(["git", "-C", str(T), "-c", "user.name=t", "-c", "user.email=t@example.com", *a], check=True, capture_output=True, text=True).stdout

    def repo(self, tmp):
        T = Path(tmp)
        self.git(T, "init", "-q", "-b", "main")
        (T / "scripts").mkdir()
        (T / "scripts" / "a.py").write_text("x = 1\n")
        (T / "data" / "tentative").mkdir(parents=True)
        (T / "data" / "tentative" / "lib.jsonl").write_text("".join(json.dumps({"name": f"A.t{i}"}) + "\n" for i in range(5)))
        self.git(T, "add", "-A")
        self.git(T, "commit", "-q", "-m", "base")
        self.git(T, "sparse-checkout", "set", "--no-cone", "/scripts/")  # the real clone: scripts/ and a few more, data/ left out
        (T / "data" / "tentative").mkdir(parents=True, exist_ok=True)  # `apply` writes records there all the same
        (T / "data" / "tentative" / "lib.jsonl").write_text("".join(json.dumps({"name": f"A.t{i}"}) + "\n" for i in range(5)))
        return T

    def head_lines(self, T):
        return len(self.git(T, "show", "HEAD:data/tentative/lib.jsonl").splitlines())

    def cut_two_lines(self, T):
        f = T / "data" / "tentative" / "lib.jsonl"
        f.write_text("".join(l for i, l in enumerate(f.read_text().splitlines(True), 1) if i not in (2, 4)))

    def test_lines_cut_outside_the_sparse_set_reach_the_commit(self):
        with tempfile.TemporaryDirectory() as tmp:
            T = self.repo(tmp)
            self.assertEqual(self.head_lines(T), 5)
            self.cut_two_lines(T)
            rl.stage_and_amend(str(T))
            self.assertEqual(self.head_lines(T), 3)

    def test_mutant_a_plain_add_leaves_the_cut_lines_in_the_commit(self):
        import subprocess
        with tempfile.TemporaryDirectory() as tmp:
            T = self.repo(tmp)
            self.cut_two_lines(T)
            subprocess.run(["git", "-C", str(T), "add", "-A"], check=True, capture_output=True)  # what refine did
            self.git(T, "commit", "-q", "--amend", "--no-edit", "--allow-empty")
            self.assertEqual(self.head_lines(T), 5)  # still five: this is the bug

    def test_the_round_cap_covers_a_real_batch(self):
        refused_per_run = 18  # the smaller of the two real runs of 17 Nov 2026 (validator 27 lines, lint 18)
        self.assertGreaterEqual(rl.REFINE_ROUNDS * refused_per_run, 4 * 1993)

    def test_refine_stages_through_the_helper(self):
        src = (Path(__file__).resolve().parents[2] / "register_libraries.py").read_text()
        body = src[src.index("def refine(") : src.index("def names_of(")]
        self.assertIn("stage_and_amend(T)", body)
        self.assertNotIn('"add", "-A"', body)


if __name__ == "__main__":
    unittest.main()
