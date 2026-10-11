import base64
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import open_intake_pr as op  # noqa: E402


def write(root: Path, rel: str, text: str) -> None:
    (root / rel).parent.mkdir(parents=True, exist_ok=True)
    (root / rel).write_text(text, encoding="utf-8")


class Place(unittest.TestCase):
    """How a bundle or a part is laid into a checkout of the tree: an intake is new files and one line in All.lean; an extend part appends to the manifest."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.stage, self.repo = Path(self.tmp.name) / "stage", Path(self.tmp.name) / "repo"
        write(self.repo, "Tengoku/All.lean", "import Tengoku.Lib\n")

    def tearDown(self):
        self.tmp.cleanup()

    def bundle(self, manifest: str, report: dict):
        write(self.stage, "Tengoku/FxLib/A.lean", "module A\n")
        write(self.stage, "Tengoku/FxLib.lean", "import Tengoku.FxLib.A\n")
        write(self.stage, "manifest.jsonl", manifest)
        write(self.stage, "report.json", json.dumps(report))

    def test_an_intake_is_new_files_and_one_all_lean_line(self):
        self.bundle('{"name": "a"}\n', {"part": 1})
        op.place(self.stage, self.repo, "fx-lib", "FxLib", None)
        self.assertEqual((self.repo / "data/intake/fx-lib/manifest.jsonl").read_text(), '{"name": "a"}\n')
        self.assertEqual(json.loads((self.repo / "data/intake/fx-lib/report.json").read_text()), {"part": 1})
        self.assertEqual(sorted((self.repo / "Tengoku/All.lean").read_text().split("\n")), ["", "import Tengoku.FxLib", "import Tengoku.Lib"])  # one line added, in the library's own gap
        self.assertTrue((self.repo / "Tengoku/FxLib/A.lean").is_file())

    def test_the_first_part_is_an_intake(self):
        self.bundle('{"name": "a"}\n', {"part": 1})
        op.place(self.stage, self.repo, "fx-lib", "FxLib", 1)
        self.assertTrue((self.repo / "data/intake/fx-lib/report.json").is_file())
        self.assertFalse((self.repo / "data/intake/fx-lib/parts").exists())
        self.assertIn("import Tengoku.FxLib", (self.repo / "Tengoku/All.lean").read_text())

    def test_a_later_part_appends_the_manifest_keeps_its_report_under_parts_and_leaves_all_lean(self):
        write(self.repo, "data/intake/fx-lib/manifest.jsonl", '{"name": "old"}\n')
        write(self.repo, "data/intake/fx-lib/report.json", '{"part": 1}')
        write(self.repo, "Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        self.bundle('{"name": "new"}\n', {"part": 2})
        op.place(self.stage, self.repo, "fx-lib", "FxLib", 2)
        self.assertEqual((self.repo / "data/intake/fx-lib/manifest.jsonl").read_text(), '{"name": "old"}\n{"name": "new"}\n')
        self.assertEqual(json.loads((self.repo / "data/intake/fx-lib/parts/002.json").read_text()), {"part": 2})
        self.assertEqual(json.loads((self.repo / "data/intake/fx-lib/report.json").read_text()), {"part": 1})  # part 1's report is not touched
        self.assertEqual((self.repo / "Tengoku/All.lean").read_text(), "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        self.assertEqual((self.repo / "Tengoku/FxLib.lean").read_text(), "import Tengoku.FxLib.A\n")

    def test_the_part_number_is_three_digits(self):
        write(self.repo, "data/intake/fx-lib/manifest.jsonl", "")
        self.bundle("", {"part": 14})
        op.place(self.stage, self.repo, "fx-lib", "FxLib", 14)
        self.assertTrue((self.repo / "data/intake/fx-lib/parts/014.json").is_file())

    def test_all_lean_without_a_final_newline_still_gets_its_line_on_its_own(self):
        for text in ("import Tengoku.Lib", "import Tengoku.Abc"):  # the gap is the library's own, so check the shape for both
            write(self.repo, "Tengoku/All.lean", text)
            self.bundle("", {})
            op.place(self.stage, self.repo, "fx-lib", "FxLib", None)
            got = (self.repo / "Tengoku/All.lean").read_text()
            self.assertEqual(sorted(got.split()), sorted(text.split() + ["import", "Tengoku.FxLib"]), got)
            self.assertEqual(sorted(l for l in got.split("\n") if l), sorted([text, "import Tengoku.FxLib"]), got)  # each import on its own line
            self.assertTrue(got.endswith("\n") or got.endswith(text), got)  # inserted before the last line (untouched, still without a newline) or appended on its own line


class PartsTotal(unittest.TestCase):
    def test_a_cut_from_part_one_has_as_many_parts_as_the_plan_lists(self):
        self.assertEqual(op.parts_total({"parts": [{"part": 1}, {"part": 2}, {"part": 3}]}), 3)

    def test_a_cut_from_the_tree_counts_the_parts_before_it_too(self):
        self.assertEqual(op.parts_total({"parts": [{"part": 2}, {"part": 3}, {"part": 4}, {"part": 5}]}), 5)


class WithImport(unittest.TestCase):
    ALL = "import Tengoku.Apap\nimport Tengoku.Carleson\nimport Tengoku.Flt\nimport Tengoku.Pfr\n"
    # the head of the real Tengoku/All.lean on 2026-10-11: NOT sorted (22 descents in 59 imports)
    REAL_HEAD = ["MerelyTrue", "Algolean", "AndersonConjecture", "InfinityCosmos", "ArchonFirstproofResults", "Carleson", "Zflean", "Degiorgi", "Expdb", "FltRegular", "GibbsMeasure", "Leanforcontrol"]

    def real_all(self, n: int = 59) -> str:
        return "-- Everything in the tree\n" + "".join(f"import Tengoku.{x}\n" for x in [*self.REAL_HEAD, *[f"Lib{i:02d}" for i in range(n - len(self.REAL_HEAD))]])

    def test_one_line_is_added_everything_else_stays_in_order(self):
        got = op.with_import(self.ALL, "import Tengoku.Complexitylib").split("\n")
        want = self.ALL.split("\n")
        self.assertEqual(len(got), len(want) + 1)
        self.assertEqual([l for l in got if l != "import Tengoku.Complexitylib"], want)

    def test_a_library_always_lands_in_the_same_gap(self):
        line = "import Tengoku.LeanPool"
        self.assertEqual(op.with_import(self.real_all(), line), op.with_import(self.real_all(), line))
        self.assertEqual(op.with_import(self.real_all(), line).split("\n").index(line), 1 + op.gap_of(line, 59))

    def test_a_file_without_a_final_newline_and_a_line_already_there(self):
        for last, line in (("import Tengoku.A", "import Tengoku.B"), ("import Tengoku.Z", "import Tengoku.B")):
            got = op.with_import(last, line)
            self.assertEqual(sorted(got.split("\n")), sorted(["", last, line]) if got.endswith("\n") else sorted([last, line]), got)
            self.assertIn(got, (f"{line}\n{last}", f"{last}\n{line}\n"))
        self.assertEqual(op.with_import(self.ALL, "import Tengoku.Flt"), self.ALL)

    def test_the_real_file_does_not_send_a_whole_alphabet_to_one_gap(self):
        """2026-10-11: 'before the first import that sorts after it' put chebotarev-density, groebner-proj, lean-pool, causalean and complexitylib all before `MerelyTrue` (the first line is
        not sorted, so every name A-M sorts before it): they conflicted with each other in the merge queue, one rebase and one re-approval after another."""
        names = ["ChebotarevDensity", "GroebnerProj", "LeanPool", "Causalean", "Complexitylib", "Aaa", "Mmm", "Fx", "Gibbs", "Erdos"]
        gaps = [op.gap_of(f"import Tengoku.{n}", 59) for n in names]
        self.assertGreaterEqual(len(set(gaps)), 8, gaps)  # the old rule gave 1 for the first seven names
        self.assertEqual(len({op.gap_of(f"import Tengoku.{n}", 59) for n in ("ChebotarevDensity", "GroebnerProj", "LeanPool")}), 3)

    def test_gap_is_in_range(self):
        for n in range(0, 80):
            self.assertTrue(0 <= op.gap_of(f"import Tengoku.X{n}", n) <= n)

    def test_two_libraries_added_apart_from_each_other_do_not_conflict_in_git(self):
        """Both PRs branch from the same All.lean: in the same gap they conflict, in different gaps they merge. Libraries whose gaps are not neighbours are chosen by the gap function itself."""
        import subprocess
        import tempfile

        d = Path(tempfile.mkdtemp())

        def git(*a):
            return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@e", *a], cwd=d, check=True, capture_output=True, text=True).stdout

        base = "".join(f"import Tengoku.{x}\n" for x in ("Apap", "Carleson", "Flt", "Pfr", "Statsmllib", "Vcvio", "Wxyz", "Yz"))
        libs = [f"Lib{i}" for i in range(40)]
        one = libs[0]
        two = next(x for x in libs if abs(op.gap_of(f"import Tengoku.{x}", 8) - op.gap_of(f"import Tengoku.{one}", 8)) >= 2)
        git("init", "-q", "-b", "main")
        (d / "All.lean").write_text(base)
        git("add", "-A")
        git("commit", "-q", "-m", "base")
        for branch, lib in (("one", one), ("two", two)):
            git("checkout", "-q", "-b", branch, "main")
            (d / "All.lean").write_text(op.with_import(base, f"import Tengoku.{lib}"))
            git("commit", "-qam", branch)
        git("checkout", "-q", "one")
        git("merge", "-q", "--no-edit", "two")  # raises on a conflict
        self.assertEqual((d / "All.lean").read_text().count("import Tengoku."), 10)


class RefuseEmpty(unittest.TestCase):
    def test_a_bundle_with_no_verified_theorem_is_refused_and_says_so(self):
        for report in ({"theorems": 0}, {}, {"theorems": None}):
            with self.assertRaises(SystemExit) as cm:
                op.refuse_empty(report, "bundle-x-proposed-part-001.tar")
            self.assertIn("EMPTY BUNDLE", str(cm.exception))

    def test_a_bundle_with_theorems_is_not(self):
        op.refuse_empty({"theorems": 1}, "x")


class AsTheApp(unittest.TestCase):
    """The scheduled opener (intake-open.yml) acts on the target repository as the intake App: its token for git and gh, its name on the commit and the sign-off."""

    def test_the_target_calls_use_the_app_token_and_it_is_in_no_argument(self):
        env = op.target_env({"TENGOKU_TOKEN": "tok-123", "GH_TOKEN": "factory-token", "PATH": "/bin"})
        self.assertEqual(env["GH_TOKEN"], "tok-123")  # not the factory's: the pull request and the push are the App's
        self.assertEqual(env["GIT_CONFIG_KEY_0"], "http.https://github.com/.extraheader")
        self.assertEqual(env["GIT_CONFIG_VALUE_0"], "AUTHORIZATION: basic " + base64.b64encode(b"x-access-token:tok-123").decode())
        self.assertEqual(env["PATH"], "/bin")

    def test_without_the_token_nothing_changes(self):
        base = {"GH_TOKEN": "mine", "PATH": "/bin"}
        self.assertEqual(op.target_env(base), base)

    def test_the_commit_is_the_apps_and_the_signoff_says_so(self):
        ident = op.commit_identity({"BOT_NAME": "tengoku-intake[bot]", "BOT_EMAIL": "1+tengoku-intake[bot]@users.noreply.github.com"})
        self.assertEqual(op.commit_identity({"BOT_NAME": "only-a-name"}), {})  # half an identity is none
        with tempfile.TemporaryDirectory() as t:
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")} | {"HOME": t, "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_SYSTEM": "/dev/null"}
            subprocess.run(["git", "init", "-q", t], check=True, env=env)
            (Path(t) / "f").write_text("x")
            subprocess.run(["git", "add", "f"], cwd=t, check=True, env=env)
            op.sh("git", "commit", "-q", "-s", "-m", "m", cwd=t, env={**env, **ident})
            msg = subprocess.run(["git", "log", "-1", "--format=%B%an <%ae>"], cwd=t, capture_output=True, text=True, env=env).stdout
            self.assertIn("Signed-off-by: tengoku-intake[bot] <1+tengoku-intake[bot]@users.noreply.github.com>", msg)
            self.assertIn("tengoku-intake[bot] <1+tengoku-intake[bot]@users.noreply.github.com>", msg.splitlines()[-1])

    def test_auto_merge_belongs_to_an_extend_part_unless_the_lane_allows_first_parts(self):
        script = str(Path(op.__file__))
        env = {k: v for k, v in os.environ.items() if k != "LANE_AUTOMERGE_FIRST"}
        for extra in ([], ["--part", "1"]):
            r = subprocess.run([sys.executable, script, "--key", "k", "--run", "1", "--repo", "o/r", "--auto-merge", *extra], capture_output=True, text=True, env=env)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("extend PR", r.stderr)
        # LANE_AUTOMERGE_FIRST=true lets a first part through the guard (it then stops at the download: the run does not exist)
        r = subprocess.run([sys.executable, script, "--key", "k", "--run", "1", "--repo", "o/r", "--auto-merge", "--part", "1"], capture_output=True, text=True, env={**env, "LANE_AUTOMERGE_FIRST": "true", "GH_TOKEN": "x"})
        self.assertNotIn("extend PR", r.stderr)


if __name__ == "__main__":
    unittest.main()
