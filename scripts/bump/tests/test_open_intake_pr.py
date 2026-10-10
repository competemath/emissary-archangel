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
        self.assertEqual((self.repo / "Tengoku/All.lean").read_text(), "import Tengoku.FxLib\nimport Tengoku.Lib\n")  # at its sorted place
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
        write(self.repo, "Tengoku/All.lean", "import Tengoku.Lib")
        self.bundle("", {})
        op.place(self.stage, self.repo, "fx-lib", "FxLib", None)
        self.assertEqual((self.repo / "Tengoku/All.lean").read_text(), "import Tengoku.FxLib\nimport Tengoku.Lib")  # inserted before it: the last line is not touched
        write(self.repo, "Tengoku/All.lean", "import Tengoku.Abc")
        op.place(self.stage, self.repo, "fx-lib", "FxLib", None)
        self.assertEqual((self.repo / "Tengoku/All.lean").read_text(), "import Tengoku.Abc\nimport Tengoku.FxLib\n")  # appended: on its own line


class PartsTotal(unittest.TestCase):
    def test_a_cut_from_part_one_has_as_many_parts_as_the_plan_lists(self):
        self.assertEqual(op.parts_total({"parts": [{"part": 1}, {"part": 2}, {"part": 3}]}), 3)

    def test_a_cut_from_the_tree_counts_the_parts_before_it_too(self):
        self.assertEqual(op.parts_total({"parts": [{"part": 2}, {"part": 3}, {"part": 4}, {"part": 5}]}), 5)


class WithImport(unittest.TestCase):
    ALL = "import Tengoku.Apap\nimport Tengoku.Carleson\nimport Tengoku.Flt\nimport Tengoku.Pfr\n"

    def test_a_library_goes_to_its_own_place_in_the_sorted_imports(self):
        got = op.with_import(self.ALL, "import Tengoku.Complexitylib")
        self.assertEqual(got, "import Tengoku.Apap\nimport Tengoku.Carleson\nimport Tengoku.Complexitylib\nimport Tengoku.Flt\nimport Tengoku.Pfr\n")

    def test_the_last_in_order_is_appended_and_the_first_is_prepended(self):
        self.assertTrue(op.with_import(self.ALL, "import Tengoku.Zzz").endswith("import Tengoku.Pfr\nimport Tengoku.Zzz\n"))
        self.assertTrue(op.with_import(self.ALL, "import Tengoku.Aaa").startswith("import Tengoku.Aaa\nimport Tengoku.Apap\n"))

    def test_a_file_without_a_final_newline_and_a_line_already_there(self):
        self.assertEqual(op.with_import("import Tengoku.A", "import Tengoku.B"), "import Tengoku.A\nimport Tengoku.B\n")
        self.assertEqual(op.with_import(self.ALL, "import Tengoku.Flt"), self.ALL)

    def test_two_libraries_added_apart_from_each_other_do_not_conflict_in_git(self):
        """The reason for the change: both PRs branch from the same All.lean; appended at the end they conflict, at their own places they merge."""
        import subprocess
        import tempfile

        d = Path(tempfile.mkdtemp())

        def git(*a):
            return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@e", *a], cwd=d, check=True, capture_output=True, text=True).stdout

        base = "".join(f"import Tengoku.{x}\n" for x in ("Apap", "Carleson", "Flt", "Pfr", "Statsmllib", "Vcvio"))
        git("init", "-q", "-b", "main")
        (d / "All.lean").write_text(base)
        git("add", "-A")
        git("commit", "-q", "-m", "base")
        for branch, lib in (("one", "Complexitylib"), ("two", "Tauceti")):
            git("checkout", "-q", "-b", branch, "main")
            (d / "All.lean").write_text(op.with_import(base, f"import Tengoku.{lib}"))
            git("commit", "-qam", branch)
        git("checkout", "-q", "one")
        git("merge", "-q", "--no-edit", "two")  # raises on a conflict
        self.assertEqual((d / "All.lean").read_text().count("import Tengoku."), 8)


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

    def test_auto_merge_belongs_to_an_extend_part_only(self):
        script = str(Path(op.__file__))
        for extra in ([], ["--part", "1"]):
            r = subprocess.run([sys.executable, script, "--key", "k", "--run", "1", "--repo", "o/r", "--auto-merge", *extra], capture_output=True, text=True)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("extend PR", r.stderr)


if __name__ == "__main__":
    unittest.main()
