import json
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
        self.assertEqual((self.repo / "Tengoku/All.lean").read_text(), "import Tengoku.Lib\nimport Tengoku.FxLib\n")
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
        self.assertEqual((self.repo / "Tengoku/All.lean").read_text(), "import Tengoku.Lib\nimport Tengoku.FxLib\n")


class PartsTotal(unittest.TestCase):
    def test_a_cut_from_part_one_has_as_many_parts_as_the_plan_lists(self):
        self.assertEqual(op.parts_total({"parts": [{"part": 1}, {"part": 2}, {"part": 3}]}), 3)

    def test_a_cut_from_the_tree_counts_the_parts_before_it_too(self):
        self.assertEqual(op.parts_total({"parts": [{"part": 2}, {"part": 3}, {"part": 4}, {"part": 5}]}), 5)


if __name__ == "__main__":
    unittest.main()
