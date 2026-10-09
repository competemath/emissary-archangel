import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "tests"))
import test_records as T  # the toy library

sys.path.insert(0, str(HERE))
import bundle  # noqa: E402


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
        self.assertIn("import Tengoku\n", a)  # Mathlib -> the tree's root, whatever the module (the seed sits under Tengoku/Seed/ since tengoku's restructure)
        self.assertNotIn("import Tengoku.Data", a)
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

    def compose_toy(self, drop: str):
        """A two-module toy library, composed with `--drop-modules drop`; returns (work dir, the process)."""
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
        p = subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
                        "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src"), "--drop-modules", drop], capture_output=True, text=True)
        return d, p

    def test_modules_named_as_failed_on_the_tree_are_left_out_with_their_importers(self):
        d, p = self.compose_toy("Toy.A, Toy.NotAModule")
        self.assertEqual(p.returncode, 0, p.stderr)
        for out in (d / "bundle", d / "bundle-proposed"):
            rep = json.loads((out / "report.json").read_text())
            self.assertEqual((rep["modules_in_bundle"], rep["theorems"]), (0, 0))  # Toy.B imports Toy.A
            self.assertEqual(rep["dropped"]["Toy.A"], "did not build on the tree")
            self.assertIn("imports a module that cannot go to the tree", rep["dropped"]["Toy.B"])

    def test_a_drop_list_that_names_no_module_fails_instead_of_cutting_nothing(self):
        """2026-10-08: `Encoding.BitPolynomial.Defs` for the library module `Complexitylib.Encoding.BitPolynomial.Defs` was ignored and the uncut bundle published."""
        d, p = self.compose_toy("Nope.Missing")
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("names no module of the library", p.stderr)
        self.assertFalse((d / "bundle").exists())

    def test_a_module_whose_kept_theorem_uses_a_cut_declaration_is_left_out(self):
        """2026-10-08: a kept theorem called a `private theorem` the closure had not reached; the bundle carried the call without the declaration."""
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        text = "namespace Toy\n\nprivate theorem helper_lemma : 1 = 1 := rfl\n\ntheorem user : 1 = 1 := helper_lemma\n\nend Toy\n"
        (lib / "Toy" / "A.lean").write_text(text)
        lines = text.split("\n")
        ln = lambda needle: next(
            i + 1 for i, x in enumerate(lines) if x.startswith(needle)
        )
        f = lib / ".lake" / "build" / "lib" / "lean" / "Toy" / "A.olean.ranges.json"
        f.parent.mkdir(parents=True)
        f.write_text(
            json.dumps(
                [
                    ["Toy.helper_lemma", ln("private theorem"), ln("private theorem")],
                    ["Toy.user", ln("theorem user"), ln("theorem user")],
                ]
            )
        )
        (d / "deps.log").write_text(
            'x:1:0: info: BUNDLE_KEEP [["Toy.A","Toy.user"]] BUNDLE_END\n'
        )  # the closure missed the helper
        (d / "passed.json").write_text(json.dumps({"Toy.A": ["Toy.user"]}))
        (d / "setup.json").write_text(
            json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"})
        )
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text(
            "GATE2B_PASS old=Toy.user new=Toy.user via=equal\n"
        )
        p = subprocess.run(
            [
                sys.executable,
                str(HERE / "bundle.py"),
                "compose",
                "--lib",
                str(lib),
                "--log",
                str(d / "deps.log"),
                "--passed",
                str(d / "passed.json"),
                "--meta",
                str(d / "setup.json"),
                "--key",
                "toy-lib",
                "--toolchain",
                "tc",
                "--errors",
                str(d / "build.log"),
                "--gate2",
                str(d / "gate2.log"),
                "--out",
                str(d / "bundle"),
                "--src",
                str(d / "src"),
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(p.returncode, 0, p.stderr)
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual((rep["modules_in_bundle"], rep["theorems"]), (0, 0))
        self.assertTrue(
            rep["dropped"]["Toy.A"].startswith(
                "uses a declaration the pruning left out"
            ),
            rep["dropped"],
        )
        self.assertIn("helper_lemma", rep["dropped"]["Toy.A"])

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


class ImportHeader(unittest.TestCase):
    """A bundle's header reaches every seeded package through the root `Tengoku`: the same text is right before and after the seed moved
    into Tengoku/Seed/."""

    def setUp(self):
        sys.path.insert(0, str(HERE))
        import bundle

        self.bundle = bundle

    def test_every_seeded_package_becomes_the_root(self):
        for line in ["public import Mathlib", "public import Batteries.Data.List.Basic", "import Aesop", "public meta import Qq", "import ProofWidgets.Component.Basic"]:
            mapped, kind = self.bundle.map_import_line(line, "toy-lib", set())
            self.assertEqual(kind, "tree", line)
            self.assertEqual(mapped.split()[-1], "Tengoku", mapped)
            self.assertEqual(mapped.split()[:-1], line.split()[:-1], mapped)  # the modifiers stay

    def test_import_all_cannot_name_the_whole_tree(self):
        self.assertEqual(self.bundle.map_import_line("import all Mathlib.Foo", "toy-lib", set())[0], "import Tengoku")

    def test_the_librarys_own_modules_and_core_are_unchanged_in_kind(self):
        self.assertEqual(self.bundle.map_import_line("import Toy.A", "toy-lib", {"Toy.A"}), ("import Tengoku.ToyLib.Toy.A", "own"))
        self.assertEqual(self.bundle.map_import_line("import Lean.Elab", "toy-lib", set()), ("import Lean.Elab", "core"))
        self.assertEqual(self.bundle.map_import_line("import Other.Pkg", "toy-lib", set())[1], "external")

    def test_a_second_copy_of_an_import_line_is_dropped(self):
        lines = ["module", "public import Tengoku", "public import Tengoku", "import Lean", "public import Tengoku", "def x := 1", "def x := 1"]
        self.assertEqual(self.bundle.once(lines), ["module", "public import Tengoku", "import Lean", "def x := 1", "def x := 1"])


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


class ImportLines(unittest.TestCase):
    def test_a_trailing_comment_is_dropped_and_the_module_is_mapped(self):
        sys.path.insert(0, str(HERE))
        import bundle

        own = {"Foo.Bar"}
        self.assertEqual(bundle.map_import_line("public import Foo.Bar -- needed for the notation", "my-lib", own), ("public import Tengoku.MyLib.Foo.Bar", "own"))
        self.assertEqual(bundle.map_import_line("import Mathlib.Data.Nat.Basic  -- x", "my-lib", own), ("import Tengoku", "tree"))  # a module of the seed: the root
        self.assertEqual(bundle.map_import_line("import Lean.Elab -- y", "my-lib", own), ("import Lean.Elab", "core"))
        self.assertEqual(bundle.map_import_line("import Foo.Bar", "my-lib", own), ("import Tengoku.MyLib.Foo.Bar", "own"))
        self.assertEqual(bundle.map_import_line("theorem a : True := trivial -- import Foo", "my-lib", own), ("theorem a : True := trivial -- import Foo", None))


class ExternalImports(unittest.TestCase):
    def test_a_docstring_line_that_starts_with_import_is_not_an_import(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        text = "import Mathlib.Data.Nat.Basic\n\n/-- Module doc.\nimport that into the tree and the rest follows.\n-/\n\ndef one : Nat := 1\n"
        (lib / "Toy" / "A.lean").write_text(text)
        la = text.split("\n")
        n = next(i + 1 for i, x in enumerate(la) if x.startswith("def one"))
        f = lib / ".lake" / "build" / "lib" / "lean" / "Toy/A.olean.ranges.json"
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(json.dumps([["Toy.one", n, n]]))
        (d / "deps.log").write_text('x:1:0: info: BUNDLE_KEEP [["Toy.A", "Toy.one"]] BUNDLE_END\n')
        (d / "passed.json").write_text(json.dumps({"Toy.A": ["Toy.one"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text("GATE2B_PASS old=Toy.one new=Toy.one via=equal\n")
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
                        "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src")], check=True, capture_output=True)
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual((rep["modules_in_bundle"], rep["theorems"]), (1, 1))  # it used to be dropped for "imports that"
        self.assertFalse(rep["dropped_truncated"])


class ToTree(unittest.TestCase):
    """A module as the tree writes it: imports mapped, and the library's auto-generated instance names given the tree's suffix (2026-10-05: flt's
    `attribute [local instance] instAlgebraForall_fLT` was an `Unknown constant` in the tree, where the same instance is `_tengoku`)."""

    def test_imports_and_instance_names_are_both_mapped(self):
        text = "import Mathlib\nimport FLT.Patching.Utils.Lemmas\n\nattribute [local instance] instAlgebraForall_fLT"  # a pruned module has no final newline
        got = bundle.to_tree(text, "flt", {"FLT.Patching.Utils.Lemmas"}, Path("FLT/Patching/Utils/AdicTopology.lean"))
        self.assertEqual(got, "import Tengoku\nimport Tengoku.Flt.FLT.Patching.Utils.Lemmas\n\nattribute [local instance] instAlgebraForall_tengoku\n")

    def test_the_suffix_is_the_files_own_root(self):
        text = "attribute [local instance] instX_fLT instY_pFR"
        self.assertEqual(bundle.to_tree(text, "pfr", set(), Path("PFR/A.lean")), "attribute [local instance] instX_fLT instY_tengoku\n")


class KeepScript(unittest.TestCase):
    """What `#bundle_keep` needs is computed by scripts/bump/BundleKeep.lean, a program that imports only Lean and loads the library at run time. It used to be a script
    compiled in a file that imported the library, so every token the library defines was live while it was parsed: lean-pool defines `]!` (`xs[i]!` stopped parsing)
    and then, in two more shards, the `#bundle_keep` command line itself did not parse; the shard's bundle-deps.log had no BUNDLE_KEEP and 6,943 + 8,639 theorems that had
    passed Gate 2 silently left the bundle (2026-10-05). The Lean function is checked on Leak IV against the old script (the same 98 constants of a seed module)."""

    PROGRAM = (Path(__file__).resolve().parents[1] / "BundleKeep.lean").read_text(encoding="utf-8")

    def test_the_program_imports_only_lean(self):
        imports = re.findall(r"^import\s+(\S+)", self.PROGRAM, re.M)
        self.assertEqual(imports, ["Lean"], "a library's syntax must never be in scope while this file is parsed")

    def test_the_program_prints_the_line_compose_reads(self):
        self.assertIn('IO.println s!"BUNDLE_KEEP {res.compress} BUNDLE_END"', self.PROGRAM)
        self.assertIn("enableInitializersExecution", self.PROGRAM)  # `lean --run` interprets it: the initializers of the loaded library must be allowed to run
        line = 'x:1:0: info: BUNDLE_KEEP [["M", "c"]] BUNDLE_END'
        self.assertTrue(re.search(r"BUNDLE_KEEP (\[.*?\]) BUNDLE_END", line, re.S))  # the pattern compose uses

    def test_keep_input_names_what_the_program_loads(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        base = lib / ".lake" / "build" / "lib" / "lean" / "Toy"
        base.mkdir(parents=True)
        for m in ("A", "B", "Unrelated"):
            (base / f"{m}.olean").write_bytes(b"")
        (lib / "Toy").mkdir()
        (lib / "Toy" / "A.lean").write_text("import Mathlib.Data.Nat.Basic\n")
        (d / "passed.json").write_text(json.dumps({"Toy.B": ["Toy.b2", "Toy.b1"], "Toy.A": ["Toy.a"]}))
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "keep-input", "--lib", str(lib), "--passed", str(d / "passed.json"), "--roots", "Toy", "--out", str(d / "k.json")], check=True, capture_output=True)
        k = json.loads((d / "k.json").read_text())
        self.assertEqual(k["imports"], ["Mathlib", "Toy.A", "Toy.B"])  # the tree's Mathlib when the library uses it, then the modules that have passed theorems
        self.assertEqual(k["names"], ["Toy.a", "Toy.b2", "Toy.b1"])  # in module order, names as Gate 2 printed them
        self.assertEqual(k["libs"], ["Toy.A", "Toy.B", "Toy.Unrelated"])  # every built module of the library, whether or not a theorem of it passed

    def test_a_library_that_does_not_use_mathlib_does_not_import_it(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / ".lake" / "build" / "lib" / "lean" / "Toy").mkdir(parents=True)
        (lib / ".lake" / "build" / "lib" / "lean" / "Toy" / "A.olean").write_bytes(b"")
        (lib / "Toy").mkdir()
        (lib / "Toy" / "A.lean").write_text("theorem a : True := trivial\n")
        (d / "passed.json").write_text(json.dumps({"Toy.A": ["Toy.a"]}))
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "keep-input", "--lib", str(lib), "--passed", str(d / "passed.json"), "--roots", "Toy", "--out", str(d / "k.json")], check=True, capture_output=True)
        self.assertEqual(json.loads((d / "k.json").read_text())["imports"], ["Toy.A"])

    def test_passed_names_the_step_kept_nothing_for_are_found(self):
        passed = {"M.A": ["a", "b"], "M.B": ["c"]}
        self.assertEqual(bundle.keep_gaps(passed, {("M.A", "a"), ("M.A", "b"), ("M.B", "c")}), [])
        self.assertEqual(bundle.keep_gaps(passed, {("M.A", "a"), ("M.B", "c")}), [("M.A", "b")])
        self.assertEqual(sorted(bundle.keep_gaps(passed, set())), [("M.A", "a"), ("M.A", "b"), ("M.B", "c")])

    def test_a_log_that_lost_part_of_the_library_is_refused_with_the_first_errors(self):
        passed = {f"M.{i}": [f"t{i}"] for i in range(100)}
        log = "bundle-deps.lean:485:46: error: unexpected token ']!'; expected ':', ']' or ']''\nbundle-deps.lean:508:0: error: elaboration function has not been implemented\n"
        kept = {(f"M.{i}", f"t{i}") for i in range(100)}
        bundle.check_keep_gaps(passed, kept, log)  # nothing lost
        bundle.check_keep_gaps(passed, kept - {("M.0", "t0")}, log)  # one in a hundred: an alias, tolerated
        with self.assertRaises(SystemExit) as cm:
            bundle.check_keep_gaps(passed, kept - {(f"M.{i}", f"t{i}") for i in range(10)}, log)
        self.assertIn("keeps nothing for 10 of 100 passed theorems", str(cm.exception))
        self.assertIn("unexpected token ']!'", str(cm.exception))

    def test_compose_refuses_a_library_whose_keep_list_lost_the_passed_theorems(self):
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "A.lean").write_text(T.A)
        (lib / "Toy" / "B.lean").write_text(T.B)
        for m in ("Toy/A", "Toy/B"):
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("[]")
        # the keep list names a constant, but not the theorem that passed: the Lean step lost it
        (d / "deps.log").write_text("x:485:46: error: unexpected token ']!'\nx:1:0: info: BUNDLE_KEEP " + json.dumps([["Toy.A", "Toy.one"]]) + " BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps({"Toy.B": ["Toy.uses_one_pos"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text("")
        r = subprocess.run(
            [sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
             "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src")],
            capture_output=True, text=True, check=False,
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("keeps nothing for 1 of 1 passed theorems", r.stderr)
        self.assertIn("unexpected token", r.stderr)
        self.assertFalse((d / "bundle").exists())

    def test_the_threshold_is_two_percent(self):
        passed = {"M": [f"t{i}" for i in range(100)]}
        kept = {("M", f"t{i}") for i in range(100)}
        bundle.check_keep_gaps(passed, kept - {("M", f"t{i}") for i in range(2)}, "")  # 2 %: tolerated
        with self.assertRaises(SystemExit):
            bundle.check_keep_gaps(passed, kept - {("M", f"t{i}") for i in range(3)}, "")  # 3 %: refused


if __name__ == "__main__":
    unittest.main()
