"""vendor_deps.py: the code a library imports from the other Lake packages it requires is copied into it, and nothing else.

Class of bug this guards (2026-10-28, stafford38-formal): the factory downloaded the packages a library requires and built none of them, so every import of one was a "bad import" and 365 of 436
modules were taken out with the 34 that failed of their own accord. The remedy copies code into a library that is then shipped into the tree, so its invariants are about what it will NOT do:

  * closure: exactly the modules reached from the library through imports are copied (checked on random package graphs against an oracle written independently), at the paths a module name
    stands for, byte for byte;
  * the seeded libraries (Mathlib, Batteries, …) and Lean itself are never copied, even if a package has files of those names;
  * the licence is checked before anything is copied: an unlicensed or copyleft package is refused and what imports it stays unresolved;
  * a file the library already has is never overwritten by a different one, and two packages that both claim a module are not chosen between;
  * a second run changes nothing.

The mutants at the end break the code the way the shortcut would; the invariants must notice.
"""

from __future__ import annotations

import json
import random
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import vendor_deps as vd  # noqa: E402

APACHE = "Apache License\nVersion 2.0, January 2004\n"
MIT = "MIT License\n\nPermission is hereby granted, free of charge, to any person obtaining a copy\n"
GPL = "GNU GENERAL PUBLIC LICENSE\nVersion 3\n"


def write(root: Path, rel: str, text: str) -> None:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


def make(tmp: Path, own: dict[str, list[str]], pkgs: dict[str, dict]) -> Path:
    """A library with its own modules (name -> imports) and required packages ({name: {"licence": text|None, "files": {module: imports}, "srcDir": str|None}})."""
    lib = tmp / "lib"
    manifest = {"version": "1.1.0", "packagesDir": ".lake/packages", "packages": []}
    for mod, imps in own.items():
        write(lib, mod.replace(".", "/") + ".lean", "".join(f"public import {i}\n" for i in imps) + f"\ndef own_{mod.replace('.', '_')} := 1\n")
    for name, spec in pkgs.items():
        d = lib / ".lake" / "packages" / name
        src = d / spec["srcDir"] if spec.get("srcDir") else d
        for mod, imps in spec["files"].items():
            write(src, mod.replace(".", "/") + ".lean", "".join(f"import {i}\n" for i in imps) + f"\ndef pkg_{name}_{mod.replace('.', '_')} := 2\n")
        if spec.get("licence") is not None:
            write(d, "LICENSE", spec["licence"])
        if spec.get("srcDir"):
            write(d, "lakefile.toml", f'name = "{name}"\nsrcDir = "{spec["srcDir"]}"\n')
        manifest["packages"].append({"name": name, "url": f"https://example.org/{name}.git", "rev": "abc123", "type": "git"})
    (lib / "lake-manifest.json").write_text(json.dumps(manifest))
    return lib


def module_path(lib: Path, mod: str) -> Path:
    return lib / (mod.replace(".", "/") + ".lean")


class Basics(unittest.TestCase):
    def test_a_reached_module_is_copied_with_what_it_imports_and_nothing_else(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(
                Path(t),
                {"Own.A": ["Mathlib.Tactic", "Dep.X"]},
                {"dep": {"licence": APACHE, "files": {"Dep.X": ["Dep.Y", "Mathlib.Data"], "Dep.Y": [], "Dep.Unused": ["Dep.Y"]}}},
            )
            before = module_path(lib, "Own.A").read_bytes()
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual(sorted(v["module"] for v in rep["vendored"]), ["Dep.X", "Dep.Y"])
            self.assertFalse(module_path(lib, "Dep.Unused").exists())
            self.assertEqual(module_path(lib, "Dep.X").read_bytes(), (lib / ".lake/packages/dep/Dep/X.lean").read_bytes())
            self.assertEqual(rep["roots"], ["Dep"])
            self.assertEqual(rep["packages"]["dep"], {"url": "https://example.org/dep.git", "rev": "abc123", "licence": "Apache-2.0", "modules": 2})
            self.assertEqual(module_path(lib, "Own.A").read_bytes(), before)

    def test_the_seeded_libraries_and_lean_are_never_copied(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(
                Path(t),
                {"Own.A": ["Mathlib.Algebra", "Batteries.Data", "Lean.Elab", "Std.Data", "Init.Core", "Aesop"]},
                {"dep": {"licence": MIT, "files": {"Mathlib.Algebra": [], "Lean.Elab": [], "Aesop": []}}},
            )
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual(rep["vendored"], [])
            self.assertFalse((lib / "Mathlib").exists() or (lib / "Lean").exists())

    def test_the_licence_is_read_before_anything_is_copied(self):
        for licence, ok in ((APACHE, True), (MIT, True), (GPL, False), ("all rights reserved\n", False), (None, False)):
            with tempfile.TemporaryDirectory() as t:
                lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": licence, "files": {"Dep.X": []}}})
                rep = vd.vendor(lib, ["Own"])
                self.assertEqual(bool(rep["vendored"]), ok, licence)
                self.assertEqual(module_path(lib, "Dep.X").exists(), ok, licence)
                if not ok:
                    self.assertEqual([r["package"] for r in rep["refused"]], ["dep"])
                    self.assertEqual(rep["unresolved"], ["Dep.X"])

    def test_a_different_file_is_never_overwritten_and_the_same_one_is_fine(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
            module_path(lib, "Dep.X").parent.mkdir(parents=True, exist_ok=True)
            module_path(lib, "Dep.X").write_text("the library's own Dep.X\n")
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual(module_path(lib, "Dep.X").read_text(), "the library's own Dep.X\n")
            self.assertEqual([c["module"] for c in rep["conflicts"]], ["Dep.X"])
            self.assertEqual(rep["vendored"], [])
            module_path(lib, "Dep.X").write_bytes((lib / ".lake/packages/dep/Dep/X.lean").read_bytes())
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual((len(rep["vendored"]), rep["conflicts"], rep["copied"]), (1, [], 0))

    def test_two_packages_with_the_same_module_are_not_chosen_between(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"one": {"licence": MIT, "files": {"Dep.X": []}}, "two": {"licence": MIT, "files": {"Dep.X": []}}})
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual(rep["vendored"], [])
            self.assertEqual(rep["ambiguous"], [{"module": "Dep.X", "packages": ["one", "two"]}])

    def test_the_package_source_directory_is_respected(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": MIT, "srcDir": "src", "files": {"Dep.X": []}}})
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual([v["module"] for v in rep["vendored"]], ["Dep.X"])

    def test_an_import_nobody_provides_is_reported_not_invented(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Nowhere.Z"]}, {})
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual((rep["vendored"], rep["unresolved"]), ([], ["Nowhere.Z"]))

    def test_a_second_run_changes_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": ["Dep.Y"], "Dep.Y": []}}})
            first = vd.vendor(lib, ["Own"])
            everything = lambda: {p: p.read_bytes() for p in lib.rglob("*") if p.is_file()}  # the marker too, and every other file
            snapshot = everything()
            second = vd.vendor(lib, ["Own", "Dep"])  # the roots now include the copies
            self.assertEqual(second["copied"], 0)
            self.assertEqual(everything(), snapshot)
            self.assertEqual(sorted(v["module"] for v in second["vendored"]), sorted(v["module"] for v in first["vendored"]))

    def test_no_manifest_means_nothing_to_do(self):
        with tempfile.TemporaryDirectory() as t:
            lib = Path(t) / "lib"
            write(lib, "Own/A.lean", "import Foo\n")
            self.assertEqual(vd.vendor(lib, ["Own"])["vendored"], [])


class Closure(unittest.TestCase):
    """Random package graphs against an oracle that follows the imports on its own."""

    def test_exactly_the_reachable_modules_are_copied(self):
        rng = random.Random(5)
        for _ in range(120):
            n_pkgs = rng.randint(1, 3)
            names = [f"P{i}" for i in range(n_pkgs)]
            modules = {f"{rng.choice(names)}Lib.M{i}": None for i in range(rng.randint(2, 12))}
            mods = list(modules)
            owner = {m: m.split(".")[0].removesuffix("Lib") for m in mods}
            graph = {m: rng.sample(mods, rng.randint(0, min(3, len(mods)))) for m in mods}
            graph = {m: [d for d in ds if d != m and mods.index(d) > mods.index(m)] for m, ds in graph.items()}  # acyclic
            own_imports = rng.sample(mods, rng.randint(0, min(3, len(mods)))) + rng.choice([[], ["Mathlib.Algebra"], ["Lean.Elab"]])
            with tempfile.TemporaryDirectory() as t:
                pkgs = {n: {"licence": rng.choice([APACHE, MIT]), "files": {m: graph[m] for m in mods if owner[m] == n}} for n in names}
                lib = make(Path(t), {"Own.Top": own_imports}, pkgs)
                rep = vd.vendor(lib, ["Own"])
                want, stack = set(), [m for m in own_imports if m in graph]
                while stack:
                    m = stack.pop()
                    if m not in want:
                        want.add(m)
                        stack.extend(graph[m])
                self.assertEqual({v["module"] for v in rep["vendored"]}, want, (graph, own_imports))
                for m in mods:
                    self.assertEqual(module_path(lib, m).exists(), m in want, m)
                # every import of a copied module is a copy, the library's, or seeded
                for m in want:
                    for d in graph[m]:
                        self.assertIn(d, want)



class Lifecycle(unittest.TestCase):
    """The copies are the factory's to manage across rounds and steps: edited by repairs, outdated by a new pin, orphaned by a changed import."""

    def test_a_copy_edited_by_a_repair_round_is_kept_and_still_reported(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
            vd.vendor(lib, ["Own"])
            module_path(lib, "Dep.X").write_text("-- edited by a repair round\n")
            rep = vd.vendor(lib, ["Own", "Dep"])
            self.assertEqual(module_path(lib, "Dep.X").read_text(), "-- edited by a repair round\n")
            self.assertEqual(([v["module"] for v in rep["vendored"]], rep["conflicts"]), (["Dep.X"], []))

    def test_a_copy_nothing_reaches_any_more_is_removed(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": ["Dep.Y"], "Dep.Y": []}}})
            vd.vendor(lib, ["Own"])
            self.assertTrue(module_path(lib, "Dep.Y").exists())
            write(lib, "Own/A.lean", "public import Dep.X\n")
            write(lib / ".lake/packages/dep", "Dep/X.lean", "def x := 1\n")  # X no longer imports Y
            rep = vd.vendor(lib, ["Own", "Dep"])
            self.assertFalse(module_path(lib, "Dep.Y").exists())
            self.assertEqual(rep["removed"], ["Dep.Y"])
            self.assertEqual([v["module"] for v in rep["vendored"]], ["Dep.X"])
            write(lib, "Own/A.lean", "def a := 1\n")  # and then nothing
            rep = vd.vendor(lib, ["Own", "Dep"])
            self.assertEqual((rep["vendored"], sorted(rep["removed"])), ([], ["Dep.X"]))
            self.assertFalse(module_path(lib, "Dep.X").exists())

    def test_a_file_the_library_has_of_its_own_is_never_removed_or_taken_for_ours(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
            write(lib, "Dep/Mine.lean", "def mine := 1\n")
            vd.vendor(lib, ["Own"])
            write(lib, "Own/A.lean", "def a := 1\n")
            vd.vendor(lib, ["Own", "Dep"])
            self.assertTrue(module_path(lib, "Dep.Mine").exists())

    def test_a_new_pin_of_the_package_replaces_our_copy(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
            vd.vendor(lib, ["Own"])
            write(lib / ".lake/packages/dep", "Dep/X.lean", "def x := 'new revision'\n")
            m = json.loads((lib / "lake-manifest.json").read_text())
            m["packages"][0]["rev"] = "def456"
            (lib / "lake-manifest.json").write_text(json.dumps(m))
            rep = vd.vendor(lib, ["Own", "Dep"])
            self.assertEqual(module_path(lib, "Dep.X").read_text(), "def x := 'new revision'\n")
            self.assertEqual(rep["packages"]["dep"]["rev"], "def456")

    def test_a_package_with_several_source_directories_is_read_in_all_of_them(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["One.X", "Two.Y"]}, {"dep": {"licence": APACHE, "files": {}}})
            d = lib / ".lake/packages/dep"
            write(d, "lakefile.toml", 'name = "dep"\n[[lean_lib]]\nname = "One"\nsrcDir = "a"\n[[lean_lib]]\nname = "Two"\nsrcDir = "b"\n')
            write(d, "a/One/X.lean", "def x := 1\n")
            write(d, "b/Two/Y.lean", "def y := 1\n")
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual(sorted(v["module"] for v in rep["vendored"]), ["One.X", "Two.Y"])
            self.assertEqual(rep["unresolved"], [])


class Wiring(unittest.TestCase):
    """The step is in the workflow where it has to be: after `lake update` has downloaded the packages, before anything reads the library's imports, and the roots it adds reach the later steps."""

    def setUp(self):
        self.wf = (HERE.parent.parent.parent / ".github" / "workflows" / "bump-library.yml").read_text()

    def test_it_runs_after_lake_update_and_before_the_imports_are_normalised(self):
        i, j, k = self.wf.index("lake update"), self.wf.index("vendor_deps.py"), self.wf.index("normalize-imports")
        self.assertTrue(i < j < k)

    def test_the_roots_it_adds_are_the_roots_of_the_build_and_of_the_later_steps(self):
        line = next(l for l in self.wf.splitlines() if "vendor_deps.py" in l)
        self.assertIn('--print-roots', line)
        self.assertIn('echo "ROOTS=$ROOTS" >> "$GITHUB_ENV"', line)

    def test_its_reports_are_kept(self):
        self.assertIn("emissary/vendored-*.json", self.wf)


class Mutants(unittest.TestCase):
    """Break the code the way the shortcut would; the invariants above must notice. (A surviving mutant means a test is missing.)"""

    def noticed(self, **patches):
        suite = unittest.TestSuite(
            [unittest.defaultTestLoader.loadTestsFromTestCase(Basics), unittest.defaultTestLoader.loadTestsFromTestCase(Closure), unittest.defaultTestLoader.loadTestsFromTestCase(Lifecycle)]
        )
        result = unittest.TestResult()
        saved = {k: getattr(vd, k) for k in patches}
        try:
            for k, v in patches.items():
                setattr(vd, k, v)
            suite.run(result)
        finally:
            for k, v in saved.items():
                setattr(vd, k, v)
        return bool(result.failures or result.errors)

    def test_skipping_the_licence_check_is_noticed(self):
        self.assertTrue(self.noticed(read_licence=lambda d: "MIT"))

    def test_copying_the_seeded_libraries_too_is_noticed(self):
        self.assertTrue(self.noticed(SEEDED=set()))

    def test_an_empty_permissive_list_is_noticed(self):
        original = vd.vendor
        self.assertTrue(self.noticed(vendor=lambda lib, roots, permissive=(): original(lib, roots, permissive=())))

    def test_the_unmutated_code_is_not_noticed(self):
        self.assertFalse(self.noticed())


if __name__ == "__main__":
    unittest.main()
