import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "tests"))
import test_records as T  # the toy library


class Bundle(unittest.TestCase):
    def test_bundle_keeps_only_what_passed_and_maps_imports(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        A = T.A + "\ntheorem broken_header (x : Nat) : foo x = x := by\n  simp\n"
        (lib / "Toy" / "A.lean").write_text(A)
        (lib / "Toy" / "B.lean").write_text(T.B)
        la, lb = A.split("\n"), T.B.split("\n")
        ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
        one = (ln(la, "/-- the number one"), ln(la, "def one"))
        unused = (ln(la, "/-- never used"), ln(la, "theorem unused"))
        one_pos = (ln(la, "theorem one_pos"),) * 2
        unrelated = (ln(lb, "theorem unrelated"),) * 2
        uses = (ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos"))
        bad = ln(la, "theorem broken_header")
        sidecars = {"Toy/A": [["Toy.one", *one], ["Toy.unused", *unused], ["Toy.one_pos", *one_pos]], "Toy/B": [["Toy.unrelated", *unrelated], ["Toy.uses_one_pos", *uses]]}
        for m, rows in sidecars.items():
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(rows))
        keep = [["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one"]]
        (d / "deps.log").write_text(f"x:1:0: info: BUNDLE_KEEP {json.dumps(keep)} BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps({"Toy.B": ["Toy.uses_one_pos"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
        (d / "build.log").write_text(f"error: Toy/A.lean:{bad}:30: Unknown identifier `foo`\n")
        (d / "gate2.log").write_text("GATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n")
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
                        "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src")], check=True)
        a = (d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "A.lean").read_text()
        b = (d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "B.lean").read_text()
        self.assertIn("def one : Nat := 1", a)
        self.assertIn("theorem one_pos", a)
        self.assertNotIn("theorem unused", a)  # nothing passed uses it
        self.assertNotIn("broken_header", a)  # Lean's error: no constant, no range, still gone
        self.assertIn("import Tengoku.Data.Nat.Basic", a)  # Mathlib -> the tree's root
        self.assertIn("import Tengoku.ToyLib.Toy.A", b)  # the library's own module -> its place in the tree
        self.assertNotIn("theorem unrelated", b)
        self.assertIn("theorem uses_one_pos", b)
        self.assertEqual((d / "bundle-proposed" / "Tengoku" / "ToyLib.lean").read_text(), "import Tengoku.ToyLib.Toy.A\nimport Tengoku.ToyLib.Toy.B\n")
        man = [json.loads(x) for x in (d / "bundle-proposed" / "manifest.jsonl").read_text().splitlines()]
        self.assertEqual([m["name"] for m in man], ["Toy.uses_one_pos"])
        self.assertEqual(man[0]["via"], "equal")
        self.assertTrue(man[0]["statement"].startswith("theorem uses_one_pos"))
        # the source that gets BUILT keeps the original layout and imports
        self.assertIn("import Mathlib.Data.Nat.Basic", (d / "src-proposed" / "Toy" / "A.lean").read_text())
        # the strict lint (tengoku's allow-list) rejects the `notation` module A, and B with it: the strict bundle is empty, and says why
        strict = json.loads((d / "bundle" / "report.json").read_text())
        self.assertEqual(strict["theorems"], 0)
        self.assertTrue(any("notation" in k for k in strict["lint_cost"]), strict["lint_cost"])
        self.assertEqual(json.loads((d / "bundle-proposed" / "report.json").read_text())["theorems"], 1)

    def test_a_module_importing_a_package_the_tree_lacks_takes_its_theorems_with_it(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "A.lean").write_text("import Cslib.Foo\n\ntheorem a : True := trivial\n")
        (lib / "Toy" / "B.lean").write_text("import Toy.A\n\ntheorem b : True := a\n")
        for m in ("Toy/A", "Toy/B"):
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps([[f"Toy.{m[-1].lower()}", 3, 3]]))
        (d / "deps.log").write_text('BUNDLE_KEEP [["Toy.A","Toy.a"],["Toy.B","Toy.b"]] BUNDLE_END\n')
        (d / "passed.json").write_text(json.dumps({"Toy.A": ["Toy.a"], "Toy.B": ["Toy.b"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy", "commit": "c"}))
        (d / "build.log").write_text("")
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
                        "--key", "toy", "--toolchain", "tc", "--errors", str(d / "build.log"), "--out", str(d / "bundle"), "--src", str(d / "src")], check=True)
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(rep["theorems"], 0)
        self.assertEqual(rep["modules_dropped"], 2)


    def test_a_module_that_declares_a_name_the_tree_has_is_left_out_with_its_importers(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        A = T.A + "\ntheorem broken_header (x : Nat) : foo x = x := by\n  simp\n"
        (lib / "Toy" / "A.lean").write_text(A)
        (lib / "Toy" / "B.lean").write_text(T.B)
        la, lb = A.split("\n"), T.B.split("\n")
        ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
        one = (ln(la, "/-- the number one"), ln(la, "def one"))
        unused = (ln(la, "/-- never used"), ln(la, "theorem unused"))
        one_pos = (ln(la, "theorem one_pos"),) * 2
        unrelated = (ln(lb, "theorem unrelated"),) * 2
        uses = (ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos"))
        bad = ln(la, "theorem broken_header")
        sidecars = {"Toy/A": [["Toy.one", *one], ["Toy.unused", *unused], ["Toy.one_pos", *one_pos]], "Toy/B": [["Toy.unrelated", *unrelated], ["Toy.uses_one_pos", *uses]]}
        for m, rows in sidecars.items():
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(rows))
        keep = [["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one"]]
        (d / "deps.log").write_text(f"x:1:0: info: BUNDLE_KEEP {json.dumps(keep)} BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps({"Toy.B": ["Toy.uses_one_pos"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
        (d / "build.log").write_text(f"error: Toy/A.lean:{bad}:30: Unknown identifier `foo`\n")
        (d / "gate2.log").write_text("GATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n")
        (d / "tree.txt").write_text("Nat.add_comm\nToy.one_pos\n")
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
                        "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src"), "--tree-names", str(d / "tree.txt")], check=True)
        for out in (d / "bundle", d / "bundle-proposed"):
            rep = json.loads((out / "report.json").read_text())
            self.assertEqual(rep["modules_in_bundle"], 0)  # Toy.A declares Toy.one_pos; Toy.B imports Toy.A
            self.assertEqual(rep["theorems"], 0)
            self.assertIn("declares Toy.one_pos, which the tree already has", rep["dropped"]["Toy.A"])
            self.assertIn("imports a module that cannot go to the tree", rep["dropped"]["Toy.B"])


class Refine(unittest.TestCase):
    """The verification build found modules that do not build: they, and what imports them, are left out of both bundles."""

    def test_modules_that_did_not_build_and_their_importers_go(self):
        d = Path(tempfile.mkdtemp())
        mods = {"X.A": "import Mathlib\ntheorem a : True := trivial\n", "X.B": "import X.A\ntheorem b : True := trivial\n", "X.C": "import Mathlib\ntheorem c : True := trivial\n"}
        for out, src in ((d / "bundle", d / "src"), (d / "bundle-proposed", d / "src-proposed")):
            for m, text in mods.items():
                rel = Path(*m.split(".")).with_suffix(".lean")
                for root in (src, out / "Tengoku" / "ToyLib"):
                    (root / rel).parent.mkdir(parents=True, exist_ok=True)
                    (root / rel).write_text(text)
            (out / "Tengoku" / "ToyLib.lean").write_text("".join(f"import Tengoku.ToyLib.{m}\n" for m in mods))
            rows = [{"name": n, "module": f"Tengoku.ToyLib.{m}"} for n, m in (("a", "X.A"), ("b", "X.B"), ("c", "X.C"))]
            (out / "manifest.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
            (out / "report.json").write_text(json.dumps({"theorems": 3, "modules_in_bundle": 3, "left_out": {}}))
        (d / "verify.json").write_text(json.dumps({"status": {"X.A": {"state": "errors"}, "X.B": {"state": "clean"}, "X.C": {"state": "clean"}}}))
        (d / "verify.log").write_text("error: X/A.lean:2:0: unsolved goals\n")
        r = subprocess.run([sys.executable, str(HERE / "bundle.py"), "refine", "--report", str(d / "verify.json"), "--log", str(d / "verify.log"), "--key", "toy-lib",
                            "--out", str(d / "bundle"), "--src", str(d / "src")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        for out in (d / "bundle", d / "bundle-proposed"):
            self.assertFalse((out / "Tengoku" / "ToyLib" / "X" / "A.lean").exists())
            self.assertFalse((out / "Tengoku" / "ToyLib" / "X" / "B.lean").exists())  # imports A
            self.assertTrue((out / "Tengoku" / "ToyLib" / "X" / "C.lean").exists())
            self.assertEqual((out / "Tengoku" / "ToyLib.lean").read_text(), "import Tengoku.ToyLib.X.C\n")
            self.assertEqual([json.loads(x)["name"] for x in (out / "manifest.jsonl").read_text().splitlines()], ["c"])
            rep = json.loads((out / "report.json").read_text())
            self.assertEqual((rep["theorems"], rep["modules_in_bundle"]), (1, 1))
            self.assertEqual(sorted(rep["verification_dropped"]), ["X.A", "X.B"])
        self.assertFalse((d / "src-proposed" / "X" / "B.lean").exists())

    def test_a_bundle_with_nothing_left_fails(self):
        d = Path(tempfile.mkdtemp())
        for out, src in ((d / "bundle", d / "src"), (d / "bundle-proposed", d / "src-proposed")):
            (src / "X").mkdir(parents=True)
            (src / "X" / "A.lean").write_text("import Mathlib\n")
            (out / "Tengoku" / "ToyLib" / "X").mkdir(parents=True)
            (out / "Tengoku" / "ToyLib" / "X" / "A.lean").write_text("import Mathlib\n")
            (out / "manifest.jsonl").write_text(json.dumps({"name": "a", "module": "Tengoku.ToyLib.X.A"}) + "\n")
            (out / "report.json").write_text("{}")
        (d / "verify.json").write_text(json.dumps({"status": {"X.A": {"state": "errors"}}}))
        (d / "verify.log").write_text("")
        r = subprocess.run([sys.executable, str(HERE / "bundle.py"), "refine", "--report", str(d / "verify.json"), "--log", str(d / "verify.log"), "--key", "toy-lib",
                            "--out", str(d / "bundle"), "--src", str(d / "src")], capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("nothing is left", r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
