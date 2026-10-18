"""Every bundle is cut with its notation scoped (scripts/bump/scope_bundle.py, called by `bundle.py compose`).

2026-10-17: lean-pool's global `prefix:80 "-" => complement` made `-(3 * x)` on a real number "Ambiguous term" on every Leak service, and the atoms of a global notation/syntax/macro (`v`, `ω`,
`na`) became reserved words of the whole tree. The factory found those AFTER the tree had them (a census, then a scope-fix PR). Tengoku's lint now refuses a global notation-family command in
any mode (scripts/ci/allowlist.py `unscoped_violations`), so compose makes them `scoped`/`local` itself, and leaves out the module whose command cannot be, like one that does not lint."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "tests"))
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "lint"))
import allowlist  # noqa: E402
import notation_census as nc  # noqa: E402
import scope_bundle as sb  # noqa: E402
import test_bundle  # noqa: E402

MODAL = 'namespace Toy\n\nprefix:80 "-" => Nat.succ -- the successor\n\ntheorem modal_one : 1 = 1 := rfl\n\nend Toy\n\ndef modal_tail := -1\n'
ABOVE = "import Toy.Modal\n\nnamespace Toy\n\ntheorem above_one : 1 = 1 := rfl\n\nend Toy\n"
ROOT = 'notation "ℓ" => 1\n\ntheorem root_one : 1 = 1 := rfl\n'
USER = "import Toy.Root\n\ntheorem user_one : 1 = 1 := rfl\n"
# `Real` is a namespace in which Mathlib has scoped entries (`π`, …): `open scoped Real` would switch them on in every importer of the library
REAL = 'namespace Real\n\nnotation "tau" => 6\n\ntheorem real_one : 1 = 1 := rfl\n\nend Real\n'
REAL_USER = "import Toy.RealN\n\ntheorem real_user : 1 = 1 := rfl\n"
# an `elab` and a `macro` in a namespace
MACROS = 'namespace Toy\n\nelab "resolve" : tactic => pure ()\n\nmacro "dub" : term => `(2)\n\ntheorem macros_one : 1 = 1 := rfl\n\nend Toy\n'
# a command written after an `open … in` on its own line is not one this pass reads: it stays global, tengoku's lint would refuse it, so compose leaves the module out
OPEN_IN = 'open Nat in notation "nn" => 1\n\ntheorem open_in_one : 1 = 1 := rfl\n'
# and so is one in the middle of a line (Lean needs no line break between commands): tengoku's check reads every occurrence of the keyword
MID_LINE = 'theorem mid_one : 1 = 1 := rfl prefix:80 "~" => Nat.succ\n'


class Census(unittest.TestCase):
    def test_the_census_without_a_seed_lists_every_global_command_and_no_scoped_one(self):
        text = 'notation "a" => 1\nscoped notation "b" => 2\nlocal infixl:65 " +++ " => Nat.add\n@[inherit_doc] prefix:80 "~" => Nat.succ\nsyntax "z" : term\n'
        got = nc.census(text, None)
        self.assertEqual([(r["line"], r["kw"]) for r in got], [(1, "notation"), (4, "prefix"), (5, "syntax")])

    def test_a_command_it_cannot_read_is_listed_too(self):
        self.assertEqual([r["line"] for r in nc.census("notation => 1\n", None)], [1])


class ScopeDir(unittest.TestCase):
    def bundle(self, files: dict[str, str]) -> Path:
        d = Path(tempfile.mkdtemp())
        for rel, text in files.items():
            f = d / "Tengoku" / "ToyLib" / rel
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(text)
        return d

    def read(self, d: Path, rel: str) -> str:
        return (d / "Tengoku" / "ToyLib" / rel).read_text()

    def test_a_notation_in_a_namespace_is_scoped_and_the_code_after_it_and_the_importers_open_it(self):
        d = self.bundle({"Toy/Modal.lean": MODAL, "Toy/Above.lean": ABOVE.replace("Toy.Modal", "Tengoku.ToyLib.Toy.Modal")})
        r = sb.scope_dir(d, "toy-lib")
        self.assertEqual(r["unscoped"], {})
        modal = self.read(d, "Toy/Modal.lean")
        self.assertIn('scoped prefix:80 "-" => Nat.succ', modal)
        self.assertIn("open scoped Toy", modal)  # `def modal_tail` after `end Toy` may use it
        self.assertIn("open scoped Toy", self.read(d, "Toy/Above.lean"))  # the library's own importer sees it as before
        for rel in ("Toy/Modal.lean", "Toy/Above.lean"):
            self.assertEqual(allowlist.unscoped_violations(self.read(d, rel), macro=True), [], rel)

    def test_a_root_notation_becomes_local_and_the_importer_declares_it_again(self):
        d = self.bundle({"Toy/Root.lean": ROOT, "Toy/User.lean": USER.replace("Toy.Root", "Tengoku.ToyLib.Toy.Root")})
        self.assertEqual(sb.scope_dir(d, "toy-lib")["unscoped"], {})
        self.assertIn('local notation "ℓ" => 1', self.read(d, "Toy/Root.lean"))
        self.assertIn('local notation "ℓ" => 1', self.read(d, "Toy/User.lean"))
        for rel in ("Toy/Root.lean", "Toy/User.lean"):
            self.assertEqual(allowlist.unscoped_violations(self.read(d, rel), macro=True), [], rel)

    def test_elab_and_macro_are_made_scoped(self):
        d = self.bundle({"Toy/Macros.lean": MACROS})
        self.assertEqual(sb.scope_dir(d, "toy-lib")["unscoped"], {})
        text = self.read(d, "Toy/Macros.lean")
        self.assertIn('scoped elab "resolve"', text)
        self.assertIn('scoped macro "dub"', text)
        self.assertEqual(allowlist.unscoped_violations(text, macro=True), [])

    def test_a_namespace_the_seed_has_scoped_entries_in_is_never_opened_for_the_importers(self):
        self.assertIn("Real", sb.seed_scoped())
        d = self.bundle({"Toy/RealN.lean": REAL, "Toy/RealUser.lean": REAL_USER.replace("Toy.RealN", "Tengoku.ToyLib.Toy.RealN")})
        r = sb.scope_dir(d, "toy-lib")
        self.assertEqual(list(r["unscoped"]), ["Tengoku.ToyLib.Toy.RealN"])
        self.assertIn("Real", r["unscoped"]["Tengoku.ToyLib.Toy.RealN"][0])
        self.assertNotIn("open scoped Real", self.read(d, "Toy/RealUser.lean"))

    def test_scoping_twice_changes_nothing(self):
        d = self.bundle({"Toy/Modal.lean": MODAL, "Toy/Root.lean": ROOT, "Toy/Macros.lean": MACROS})
        sb.scope_dir(d, "toy-lib")
        once = {rel: self.read(d, rel) for rel in ("Toy/Modal.lean", "Toy/Root.lean", "Toy/Macros.lean")}
        self.assertEqual(sb.scope_dir(d, "toy-lib")["scoped"], 0)
        self.assertEqual(once, {rel: self.read(d, rel) for rel in once})

    def test_dry_run_scopes_a_copy_and_names_the_modules_that_cannot_be(self):
        scoped, bad = sb.dry_run({"Toy/Modal.lean": MODAL, "Toy/RealN.lean": REAL, "Toy/RealUser.lean": REAL_USER.replace("Toy.RealN", "Tengoku.ToyLib.Toy.RealN")}, "toy-lib")
        self.assertIn('scoped prefix:80 "-"', scoped["Toy/Modal.lean"])
        self.assertEqual(list(bad), ["Toy/RealN.lean"])


class Compose(unittest.TestCase):
    """`bundle.py compose` with the notation modules of a toy library (the harness of test_bundle.AutoDrops)."""

    compose = test_bundle.AutoDrops.compose
    leaks_in_leaky = staticmethod(lambda self, text, keep: [])
    FILES = {"Modal": MODAL, "Above": ABOVE, "Root": ROOT, "User": USER, "RealN": REAL, "RealUser": REAL_USER, "Macros": MACROS, "OpenIn": OPEN_IN, "MidLine": MID_LINE}
    PASSED = {
        "Toy.Modal": ["Toy.modal_one"],
        "Toy.Above": ["Toy.above_one"],
        "Toy.Root": ["Toy.root_one"],
        "Toy.User": ["Toy.user_one"],
        "Toy.RealN": ["Toy.real_one"],
        "Toy.RealUser": ["Toy.real_user"],
        "Toy.Macros": ["Toy.macros_one"],
        "Toy.OpenIn": ["Toy.open_in_one"],
        "Toy.MidLine": ["Toy.mid_one"],
    }

    def modules(self, d: Path, mode: str) -> dict[str, str]:
        base = d / ("bundle" if mode == "strict" else f"bundle-{mode}") / "Tengoku" / "ToyLib" / "Toy"
        return {f.stem: f.read_text() for f in sorted(base.glob("*.lean"))} if base.is_dir() else {}

    def test_every_module_that_ships_in_any_mode_has_no_global_notation(self):
        d, p = self.compose([])
        self.assertEqual(p.returncode, 0, p.stderr)
        for mode in ("strict", "proposed", "wide"):
            for name, text in self.modules(d, mode).items():
                self.assertEqual(allowlist.unscoped_violations(text, macro=True), [], f"{mode}/{name}")

    def test_the_proposed_bundle_keeps_the_notation_modules_scoped(self):
        d, p = self.compose([])
        mods = self.modules(d, "proposed")
        self.assertIn('scoped prefix:80 "-"', mods["Modal"])
        self.assertIn("open scoped Toy", mods["Above"])
        self.assertIn('local notation "ℓ"', mods["Root"])
        self.assertIn('local notation "ℓ"', mods["User"])
        report = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertGreater(report["notation_scoped"], 0)

    def test_a_module_whose_command_cannot_be_scoped_goes_with_its_importers_and_says_why(self):
        d, p = self.compose([])
        for mode in ("proposed", "wide"):
            mods = self.modules(d, mode)
            self.assertNotIn("RealN", mods, mode)
            self.assertNotIn("RealUser", mods, mode)
            report = json.loads((d / ("bundle-" + mode) / "report.json").read_text())
            self.assertIn("cannot be made scoped or local", report["dropped"]["Toy.RealN"])
            self.assertIn("imports a module that cannot go to the tree", report["dropped"]["Toy.RealUser"])

    def test_a_command_the_pass_does_not_read_is_caught_by_the_check_tengoku_makes(self):
        d, p = self.compose([])
        for mode in ("proposed", "wide"):
            report = json.loads((d / ("bundle-" + mode) / "report.json").read_text())
            for name in ("OpenIn", "MidLine"):
                self.assertNotIn(name, self.modules(d, mode), f"{mode}/{name}")
                self.assertIn("without 'scoped' or 'local'", report["dropped"][f"Toy.{name}"], f"{mode}/{name}")

    def test_the_strict_bundle_carries_no_notation_at_all(self):
        d, p = self.compose([])
        mods = self.modules(d, "strict")
        self.assertNotIn("Modal", mods)
        self.assertNotIn("Root", mods)

    def test_composing_again_gives_the_same_bytes(self):
        a, _ = self.compose([])
        b, _ = self.compose([])
        for mode in ("proposed", "wide"):
            self.assertEqual(self.modules(a, mode), self.modules(b, mode), mode)


if __name__ == "__main__":
    unittest.main()
