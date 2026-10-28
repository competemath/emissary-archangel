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


def git(*args, cwd=None):
    import subprocess

    return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()


class Safety(unittest.TestCase):
    """What must not enter the library: code that runs at compile time, a pin that is not what was reviewed, a licence that does not allow it."""

    RISKY = {
        "unsafe def": "unsafe def f : Nat := 1\n",
        "initialize": "initialize myRef : IO.Ref Nat <- IO.mkRef 0\n",
        "elab": 'elab "boom" : term => pure (Lean.mkNatLit 1)\n',
        "run_cmd": "run_cmd Lean.logInfo \"hi\"\n",
        "extern": '@[extern "c_fn"] opaque cFn : Nat -> Nat\n',
        "implemented_by": "@[implemented_by fastImpl] def slow : Nat := 1\n",
        "native_decide": "theorem t : 2 + 2 = 4 := by native_decide\n",
        "#eval": "def x := 1\n#eval x\n",
        "#exec": "#exec foo\n",
        "#eval!": "def x := 1\n#eval! x\n",
        "IO.Process": 'def x : IO Unit := do discard <| IO.Process.output { cmd := "ls" }\n',
    }

    def run_one(self, body: str, licence=APACHE):
        t = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__("shutil").rmtree(t, ignore_errors=True))
        lib = make(Path(t), {"Own.A": ["Dep.X", "Dep.Z"]}, {"dep": {"licence": licence, "files": {"Dep.X": [], "Dep.Z": []}}})
        write(lib / ".lake/packages/dep", "Dep/X.lean", body)
        return lib, vd.vendor(lib, ["Own"])

    def test_every_construct_that_runs_code_keeps_the_module_out(self):
        for name, body in self.RISKY.items():
            lib, rep = self.run_one(body)
            self.assertEqual([u["module"] for u in rep["unsafe"]], ["Dep.X"], name)
            self.assertFalse(module_path(lib, "Dep.X").exists(), name)
            self.assertIn("Dep.X", rep["unresolved"], name)
            self.assertTrue(module_path(lib, "Dep.Z").exists(), "an innocent module of the same package still comes in: " + name)

    def test_notation_and_macros_are_the_trees_policy_for_the_bundle_not_a_reason_to_refuse(self):
        for body in ('notation "⟪" x "⟫" => id x\n', 'macro "mytac" : tactic => `(tactic| rfl)\n', "infixl:65 \" +++ \" => Nat.add\n"):
            lib, rep = self.run_one(body)
            self.assertEqual(rep["unsafe"], [], body)
            self.assertTrue(module_path(lib, "Dep.X").exists(), body)

    def test_a_hash_command_that_only_writes_a_message_is_inert_and_does_not_keep_a_module_out(self):
        lib, rep = self.run_one("def x := 1\n#print axioms x\n#check x\n#reduce x\n#synth Inhabited Nat\n")
        self.assertEqual(rep["unsafe"], [])
        self.assertTrue(module_path(lib, "Dep.X").exists())

    def test_a_module_is_reported_once_however_many_modules_import_it(self):
        t = tempfile.mkdtemp()
        self.addCleanup(lambda: __import__("shutil").rmtree(t, ignore_errors=True))
        lib = make(Path(t), {"Own.A": ["Dep.X"], "Own.B": ["Dep.X"], "Own.C": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
        write(lib / ".lake/packages/dep", "Dep/X.lean", "unsafe def f : Nat := 1\n")
        self.assertEqual([u["module"] for u in vd.vendor(lib, ["Own"])["unsafe"]], ["Dep.X"])

    def test_comments_and_strings_are_not_code(self):
        body = '/- unsafe def x, initialize, native_decide, elab "x" -/\n-- run_cmd foo\ndef s : String := "unsafe def initialize IO.Process"\n'
        lib, rep = self.run_one(body)
        self.assertEqual(rep["unsafe"], [])
        self.assertTrue(module_path(lib, "Dep.X").exists())

    def test_a_module_that_claims_another_licence_is_kept_out(self):
        for header, ok in (("/-\nReleased under Apache 2.0 license as described in the file LICENSE.\n-/\n", True), ("-- SPDX-License-Identifier: MIT\n", True), ("/-\nReleased under GPL-3.0 license\n-/\n", False), ("-- SPDX-License-Identifier: AGPL-3.0\n", False)):
            lib, rep = self.run_one(header + "def x := 1\n")
            self.assertEqual(module_path(lib, "Dep.X").exists(), ok, header)
            self.assertEqual(bool(rep["unsafe"]), not ok, header)

    def test_no_command_that_runs_code_is_called_inert_whatever_it_is_named(self):
        import inspect

        src = inspect.getsource(vd)
        for name in ("eval", "exec", "run_cmd", "run_tac", "run_elab", "run_meta"):
            self.assertNotIn(name, vd.INERT_HASH)
        # an unknown # command is a risk, not assumed harmless
        lib, rep = self.run_one("#mysterious_command foo\n")
        self.assertEqual([u["module"] for u in rep["unsafe"]], ["Dep.X"])

    def test_the_hash_of_every_copy_is_recorded(self):
        import hashlib

        lib, rep = self.run_one("def x := 1\n")
        for v in rep["vendored"]:
            self.assertEqual(v["sha256"], hashlib.sha256(module_path(lib, v["module"]).read_bytes()).hexdigest())

    def test_a_checkout_that_is_not_at_the_pinned_commit_is_not_used(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
            d = lib / ".lake/packages/dep"
            git("init", "-q", cwd=d)
            git("add", ".", cwd=d)
            git("commit", "-qm", "x", cwd=d)
            head = git("rev-parse", "HEAD", cwd=d)
            manifest = json.loads((lib / "lake-manifest.json").read_text())
            manifest["packages"][0]["rev"] = "0" * 40
            (lib / "lake-manifest.json").write_text(json.dumps(manifest))
            rep = vd.vendor(lib, ["Own"])
            self.assertEqual((rep["vendored"], [r["package"] for r in rep["refused"]]), ([], ["dep"]))
            manifest["packages"][0]["rev"] = head
            (lib / "lake-manifest.json").write_text(json.dumps(manifest))
            self.assertEqual([v["module"] for v in vd.vendor(lib, ["Own"])["vendored"]], ["Dep.X"])


class Fetch(unittest.TestCase):
    """A missing package is downloaded at the pinned commit and nothing else: no branch, no tag, no other host, no half-installed checkout."""

    def remote(self, root: Path):
        r = root / "remote"
        r.mkdir()
        git("init", "-q", cwd=r)
        write(r, "Dep/X.lean", "def x := 1\n")
        write(r, "LICENSE", APACHE)
        git("add", ".", cwd=r)
        git("commit", "-qm", "x", cwd=r)
        return r, git("rev-parse", "HEAD", cwd=r)

    def lib_with(self, root: Path, url: str, rev: str):
        lib = root / "lib"
        write(lib, "Own/A.lean", "public import Dep.X\n")
        (lib / "lake-manifest.json").write_text(json.dumps({"packagesDir": ".lake/packages", "packages": [{"name": "dep", "url": url, "rev": rev}]}))
        return lib

    def test_a_missing_package_is_fetched_at_the_pin_and_then_vendored(self):
        with tempfile.TemporaryDirectory() as t:
            remote, head = self.remote(Path(t))
            lib = self.lib_with(Path(t), f"file://{remote}", head)
            rep = vd.vendor(lib, ["Own"], fetch=True, fetch_allow=("file://",))
            self.assertEqual([(f["package"], f["fetched"]) for f in rep["fetched"]], [("dep", True)])
            self.assertEqual([v["module"] for v in rep["vendored"]], ["Dep.X"])

    def test_only_a_full_commit_on_an_allowed_host_is_fetched(self):
        with tempfile.TemporaryDirectory() as t:
            remote, head = self.remote(Path(t))
            for url, rev in ((f"file://{remote}", "main"), (f"file://{remote}", head[:12]), ("https://example.org/x.git", head), (f"file://{remote}", head)):
                lib = self.lib_with(Path(t) / f"l{abs(hash((url, rev)))}", url, rev)
                (lib.parent).mkdir(exist_ok=True)
                rep = vd.vendor(lib, ["Own"], fetch=True)  # the default host list: github.com only
                self.assertEqual([f["fetched"] for f in rep["fetched"]], [False], (url, rev))
                self.assertFalse((lib / ".lake/packages/dep").exists())

    def test_only_the_packages_the_library_imports_from_are_fetched(self):
        with tempfile.TemporaryDirectory() as t:
            remote, head = self.remote(Path(t))
            lib = Path(t) / "lib"
            write(lib, "Own/A.lean", "public import DepThing.X\nimport Mathlib.Algebra\n")
            (lib / "lake-manifest.json").write_text(json.dumps({"packagesDir": ".lake/packages", "packages": [
                {"name": "mathlib", "url": f"file://{remote}", "rev": head},
                {"name": "doc-gen4", "url": f"file://{remote}", "rev": head},
                {"name": "dep_thing", "url": f"file://{remote}", "rev": head}]}))
            rep = vd.vendor(lib, ["Own"], fetch=True, fetch_allow=("file://",))
            self.assertEqual([f["package"] for f in rep["fetched"]], ["dep_thing"])
            self.assertFalse((lib / ".lake/packages/mathlib").exists() or (lib / ".lake/packages/doc-gen4").exists())

    def test_a_failed_fetch_leaves_nothing_behind(self):
        with tempfile.TemporaryDirectory() as t:
            lib = self.lib_with(Path(t), "file:///nonexistent/remote", "a" * 40)
            rep = vd.vendor(lib, ["Own"], fetch=True, fetch_allow=("file://",))
            self.assertEqual([f["fetched"] for f in rep["fetched"]], [False])
            self.assertFalse((lib / ".lake/packages/dep").exists())

    def test_a_package_already_on_disk_is_never_fetched_again(self):
        with tempfile.TemporaryDirectory() as t:
            lib = make(Path(t), {"Own.A": ["Dep.X"]}, {"dep": {"licence": APACHE, "files": {"Dep.X": []}}})
            rep = vd.vendor(lib, ["Own"], fetch=True, fetch_run=lambda *a, **k: self.fail("fetched"))
            self.assertEqual(rep["fetched"], [])


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
        self.assertIn("--fetch", line)
        self.assertIn('echo "ROOTS=$ROOTS" >> "$GITHUB_ENV"', line)

    def test_its_reports_are_kept(self):
        self.assertIn("emissary/vendored-*.json", self.wf)


class Mutants(unittest.TestCase):
    """Break the code the way the shortcut would; the invariants above must notice. (A surviving mutant means a test is missing.)"""

    def noticed(self, **patches):
        suite = unittest.TestSuite(
            [unittest.defaultTestLoader.loadTestsFromTestCase(Basics), unittest.defaultTestLoader.loadTestsFromTestCase(Closure), unittest.defaultTestLoader.loadTestsFromTestCase(Lifecycle), unittest.defaultTestLoader.loadTestsFromTestCase(Safety), unittest.defaultTestLoader.loadTestsFromTestCase(Fetch)]
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

    def test_not_reading_the_code_of_a_module_is_noticed(self):
        self.assertTrue(self.noticed(hard_risks=lambda text: []))

    def test_trusting_any_checkout_is_noticed(self):
        self.assertTrue(self.noticed(pinned_commit=lambda d: None))

    def test_the_unmutated_code_is_not_noticed(self):
        self.assertFalse(self.noticed())


if __name__ == "__main__":
    unittest.main()
