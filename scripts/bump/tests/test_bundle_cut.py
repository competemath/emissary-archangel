import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bundle_cut as bc  # noqa: E402


def make(d: Path):
    root = d / "Tengoku" / "Lib"
    (root / "A").mkdir(parents=True)
    (root / "A" / "Base.lean").write_text("import Tengoku\n\ntheorem a : True := trivial\n")
    (root / "A" / "Cadlag.lean").write_text("import Tengoku\n\ntheorem c : True := trivial\n")
    (root / "A" / "Uses.lean").write_text("import Tengoku\nimport Tengoku.Lib.A.Cadlag\n\ntheorem u : True := trivial\n")
    (root / "A" / "Other.lean").write_text("import Tengoku.Lib.A.Base\n\ntheorem o : True := trivial\n")
    (root / "Deps.lean").write_text("-- Lib: marker\n")
    (d / "Tengoku" / "Lib.lean").write_text("".join(f"import Tengoku.Lib.A.{m}\n" for m in ("Base", "Cadlag", "Uses", "Other")))
    rows = [{"name": n, "module": f"Tengoku.Lib.A.{m}"} for n, m in (("a", "Base"), ("c", "Cadlag"), ("u", "Uses"), ("o", "Other"))]
    (d / "manifest.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    (d / "report.json").write_text(json.dumps({"theorems": 4, "modules_in_bundle": 4}))


class Cut(unittest.TestCase):
    def test_a_module_and_its_importers_go_and_the_rest_follows(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t) / "bundle"
            make(d)
            r = bc.cut_dir(d, "lib", {"A.Cadlag"})
            self.assertEqual((r["modules"], r["theorems"], r["dropped_modules"], r["dropped_theorems"]), (2, 2, 2, 2))
            self.assertFalse((d / "Tengoku/Lib/A/Cadlag.lean").exists())
            self.assertFalse((d / "Tengoku/Lib/A/Uses.lean").exists())
            self.assertTrue((d / "Tengoku/Lib/Deps.lean").exists())
            self.assertEqual((d / "Tengoku/Lib.lean").read_text(), "import Tengoku.Lib.A.Base\nimport Tengoku.Lib.A.Other\n")
            self.assertEqual([json.loads(x)["name"] for x in (d / "manifest.jsonl").read_text().splitlines()], ["a", "o"])
            rep = json.loads((d / "report.json").read_text())
            self.assertEqual((rep["theorems"], rep["modules_in_bundle"]), (2, 2))
            self.assertEqual(sorted(rep["queue_dropped"]), ["A.Cadlag", "A.Uses"])

    def test_a_name_that_is_not_in_the_bundle_is_reported(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t) / "bundle"
            make(d)
            self.assertEqual(bc.cut_dir(d, "lib", {"Nope"})["not_in_bundle"], ["Nope"])

    def test_both_modes_are_cut(self):
        with tempfile.TemporaryDirectory() as t:
            for n in ("bundle", "bundle-proposed"):
                make(Path(t) / n)
            for n in ("bundle", "bundle-proposed"):
                self.assertEqual(bc.cut_dir(Path(t) / n, "lib", {"A.Uses"})["theorems"], 3)


class Cli(unittest.TestCase):
    def run_cut(self, drop: str) -> subprocess.CompletedProcess:
        d = Path(tempfile.mkdtemp()) / "bundle"
        make(d)
        return subprocess.run([sys.executable, str(Path(bc.__file__)), "--bundle", str(d), "--key", "lib", "--drop", drop], capture_output=True, text=True)

    def test_a_list_that_names_no_module_fails(self):
        r = self.run_cut("Nope.Missing")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("names no module of the bundle", r.stderr)

    def test_a_stale_name_among_real_ones_is_tolerated(self):
        self.assertEqual(self.run_cut("A.Cadlag,Nope.Missing").returncode, 0)


if __name__ == "__main__":
    unittest.main()
