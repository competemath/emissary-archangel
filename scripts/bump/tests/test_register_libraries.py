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
        self.assertEqual(t["corpora"]["good"]["roots"], ["Good"])
        self.assertEqual(list(e["sources"]), ["good"])
        self.assertTrue((d / "t/data/tentative/good.jsonl").exists())
        self.assertFalse((d / "t/data/tentative/bad.jsonl").exists())


if __name__ == "__main__":
    unittest.main()
