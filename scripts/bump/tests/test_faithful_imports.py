"""bundle.py --imports faithful: a library module keeps the imports its authors wrote, named as the tree names them (Tengoku/Seed/), and says so in one docstring line.

Why it exists (navier-stokes-euler, 2026-10-16): the default makes every seeded import the umbrella, and with all of Mathlib in scope `open Finset Finset.HasAntidiagonal`
makes `antidiagonal` ambiguous; 330 modules failed on that kind of clash. With the original imports all the way down the chain, the same module compiles in the tree.
No Lean, no network: the mapping, the one-line note, `to_tree`, a whole `compose` on the toy library, and the workflow wiring."""

import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE / "tests"))
import test_records as T  # the toy library

sys.path.insert(0, str(HERE))
import bundle  # noqa: E402

TREE_SEED_TOPS = {  # checked against competemath/tengoku Tengoku/Seed/ on 2026-10-16: each of these files exists there
    "Std": "Tengoku.Seed.Std",
    "Tactic.Aesop": "Tengoku.Seed.Tactic.Aesop",
    "Meta.Qq": "Tengoku.Seed.Meta.Qq",
    "Widgets": "Tengoku.Seed.Widgets",
    "Testing.Random": "Tengoku.Seed.Testing.Random",
    "Search.LeanSearchClient": "Tengoku.Seed.Search.LeanSearchClient",
    "Meta.ImportGraph": "Tengoku.Seed.Meta.ImportGraph",
    "Meta.Cli": "Tengoku.Seed.Meta.Cli",
}


class SeedModule(unittest.TestCase):
    TABLE = [
        ("Mathlib.Algebra.Group.Basic", "Tengoku.Seed.Algebra.Group.Basic"),
        ("Mathlib.Algebra.BigOperators.NatAntidiagonal", "Tengoku.Seed.Algebra.BigOperators.NatAntidiagonal"),
        ("Mathlib.Tactic", "Tengoku.Seed.Tactic"),
        ("Mathlib.Tactic.Ring.Basic", "Tengoku.Seed.Tactic.Ring.Basic"),
        ("Mathlib", "Tengoku"),
        ("Batteries", "Tengoku.Seed.Std"),
        ("Batteries.Data.List.Basic", "Tengoku.Seed.Std.Data.List.Basic"),
        ("Aesop", "Tengoku.Seed.Tactic.Aesop"),
        ("Aesop.Search.Expansion", "Tengoku.Seed.Tactic.Aesop.Search.Expansion"),
        ("Qq", "Tengoku.Seed.Meta.Qq"),
        ("Qq.Macro", "Tengoku.Seed.Meta.Qq.Macro"),
        ("ProofWidgets", "Tengoku.Seed.Widgets"),
        ("ProofWidgets.Component.Basic", "Tengoku.Seed.Widgets.Component.Basic"),
        ("Plausible", "Tengoku.Seed.Testing.Random"),
        ("Plausible.Random", "Tengoku.Seed.Testing.Random.Random"),
        ("LeanSearchClient", "Tengoku.Seed.Search.LeanSearchClient"),
        ("LeanSearchClient.Basic", "Tengoku.Seed.Search.LeanSearchClient.Basic"),
        ("ImportGraph", "Tengoku.Seed.Meta.ImportGraph"),
        ("ImportGraph.Imports", "Tengoku.Seed.Meta.ImportGraph.Imports"),
        ("Cli", "Tengoku.Seed.Meta.Cli"),
        ("Cli.Basic", "Tengoku.Seed.Meta.Cli.Basic"),
    ]

    def test_every_module_maps_to_the_trees_name_for_it(self):
        for old, new in self.TABLE:
            with self.subTest(old):
                self.assertEqual(bundle.seed_module(old), new)

    def test_the_bare_names_are_modules_that_exist_in_the_tree(self):
        for top, want in TREE_SEED_TOPS.items():
            self.assertIn(want, {bundle.seed_module(p) for p in bundle.SEED_PACKAGES if bundle.SEED_TOP[p] == top}, top)

    def test_every_seeded_package_has_a_target_and_nothing_else_does(self):
        self.assertEqual(set(bundle.SEED_TOP), set(bundle.SEED_PACKAGES))

    def test_an_unknown_package_is_refused_not_guessed(self):
        with self.assertRaises(KeyError):
            bundle.seed_module("Foo.Bar")

    def test_no_target_uses_the_old_layout_of_the_seed(self):
        for old, new in self.TABLE:
            self.assertTrue(new == "Tengoku" or new.startswith("Tengoku.Seed."), new)  # `Tengoku.Std`, `Tengoku.Algebra` were the layout before tengoku#278

    def test_a_module_keeps_its_own_path_below_the_package(self):
        self.assertEqual(bundle.seed_module("Mathlib.A.B.C.D"), "Tengoku.Seed.A.B.C.D")
        self.assertEqual(bundle.seed_module("Batteries.A.B"), "Tengoku.Seed.Std.A.B")


class MapImportLine(unittest.TestCase):
    OWN = {"Foo.Bar"}

    def faithful(self, line):
        return bundle.map_import_line(line, "my-lib", self.OWN, True)

    def full(self, line):
        return bundle.map_import_line(line, "my-lib", self.OWN)

    def test_the_default_is_still_the_umbrella(self):
        self.assertEqual(bundle.map_import_line("import Mathlib.Data.Nat.Basic", "my-lib", self.OWN), ("import Tengoku", "tree"))
        self.assertEqual(bundle.map_import_line("import Mathlib.Data.Nat.Basic", "my-lib", self.OWN, False), ("import Tengoku", "tree"))

    def test_faithful_names_the_same_module_in_the_tree(self):
        self.assertEqual(self.faithful("import Mathlib.Data.Nat.Basic"), ("import Tengoku.Seed.Data.Nat.Basic", "tree"))
        self.assertEqual(self.faithful("import Batteries.Data.List.Basic"), ("import Tengoku.Seed.Std.Data.List.Basic", "tree"))

    def test_the_bare_mathlib_is_the_root_in_both_modes(self):
        self.assertEqual(self.faithful("import Mathlib")[0], "import Tengoku")
        self.assertEqual(self.full("import Mathlib")[0], "import Tengoku")

    def test_public_private_and_meta_imports_keep_their_prefix(self):
        for pre in ("public import ", "private import ", "meta import ", "public meta import "):
            with self.subTest(pre):
                self.assertEqual(self.faithful(f"{pre}Mathlib.Order.Basic")[0], f"{pre}Tengoku.Seed.Order.Basic")

    def test_import_all_cannot_name_a_module_of_the_tree_privately(self):
        self.assertEqual(self.faithful("import all Mathlib.Foo")[0], "import Tengoku.Seed.Foo")

    def test_a_trailing_comment_is_dropped_as_in_the_default_mode(self):
        self.assertEqual(self.faithful("import Mathlib.Foo -- needed for the notation")[0], "import Tengoku.Seed.Foo")
        self.assertEqual(self.faithful("import Mathlib.Foo  -- x")[0], "import Tengoku.Seed.Foo")

    def test_the_librarys_own_core_and_other_imports_are_the_same_in_both_modes(self):
        for line in ("import Foo.Bar", "public import Foo.Bar", "import Lean.Elab", "import Std.Data.HashMap", "import Init.Core", "import Other.Pkg"):
            with self.subTest(line):
                self.assertEqual(self.faithful(line), self.full(line))
        self.assertEqual(self.faithful("import Foo.Bar"), ("import Tengoku.MyLib.Foo.Bar", "own"))
        self.assertEqual(self.faithful("import Lean.Elab"), ("import Lean.Elab", "core"))
        self.assertEqual(self.faithful("import Other.Pkg")[1], "external")

    def test_a_line_that_is_not_an_import_is_untouched(self):
        for line in ("theorem a : True := trivial -- import Mathlib.Foo", "  -- import Mathlib.Foo", "open Mathlib", "/-! import Mathlib.Foo -/"):
            with self.subTest(line):
                self.assertEqual(self.faithful(line), (line, None))

    def test_a_package_whose_name_only_starts_like_a_seeded_one_is_not_seeded(self):
        self.assertEqual(self.faithful("import MathlibExtras.Foo")[1], "external")
        self.assertEqual(self.faithful("import QqFoo")[1], "external")


class FaithfulNote(unittest.TestCase):
    NOTE = bundle.FAITHFUL_NOTE

    def add(self, text):
        return "\n".join(bundle.add_faithful_note(text.split("\n")))

    def test_the_note_follows_the_last_import_of_the_header(self):
        out = self.add("import A\nimport B\n\nnamespace X\nend X\n").split("\n")
        self.assertEqual(out[:5], ["import A", "import B", "", self.NOTE, ""])
        self.assertEqual(out.count(self.NOTE), 1)

    def test_everything_after_the_header_is_byte_for_byte_the_same(self):
        body = "\n/-! the library's own doc -/\n\nnoncomputable section\n\ntheorem t : True := trivial\n"
        out = self.add("import A\n" + body)
        self.assertTrue(out.endswith(body), out)

    def test_adding_it_twice_changes_nothing(self):
        once = self.add("import A\n\ntheorem t : True := trivial\n")
        self.assertEqual(self.add(once), once)

    def test_a_module_with_no_import_gets_none(self):
        text = "namespace X\ntheorem t : True := trivial\nend X\n"
        self.assertEqual(self.add(text), text)

    def test_comments_before_and_between_the_imports_do_not_confuse_it(self):
        text = "/-\nCopyright (c) test\nimport Fake.Not.An.Import\n-/\nimport A\n-- a comment\nimport B\n\ntheorem t : True := trivial\n"
        out = self.add(text).split("\n")
        i = out.index("import B")
        self.assertEqual(out[i + 2], self.NOTE)  # after the LAST real import, not after the one named in the copyright block
        self.assertEqual(out.index("import A"), 4)

    def test_the_module_keyword_stays_first(self):
        out = self.add("module\n\nimport A\npublic import B\n\ntheorem t : True := trivial\n").split("\n")
        self.assertEqual(out[0], "module")
        self.assertEqual(out[out.index("public import B") + 2], self.NOTE)

    def test_the_note_is_a_docstring_and_never_an_import_line(self):
        self.assertTrue(self.NOTE.startswith("/-!") and self.NOTE.endswith("-/"))
        self.assertIsNone(bundle.IMPORT_RE.match(self.NOTE))
        self.assertNotIn("\n", self.NOTE)  # one line

    def test_the_note_says_what_was_done_in_few_words(self):
        self.assertLess(len(self.NOTE), 160)
        self.assertIn("imports", self.NOTE)


class ToTree(unittest.TestCase):
    TEXT = (
        "import Euler.FiniteGradeAlgebra\nimport Mathlib.Algebra.BigOperators.NatAntidiagonal\nimport Mathlib.Tactic\n\n"
        "/-! The finite residual convolution. -/\n\nnoncomputable section\n\nnamespace EulerFiniteGrades\n\nopen Finset Finset.HasAntidiagonal\n\n"
        "theorem t : True := trivial\n\nend EulerFiniteGrades\n"
    )
    OWN = {"Euler.FiniteGradeAlgebra"}
    REL = Path("Tengoku/NavierStokesEuler/Euler/FiniteGradeDiagonal.lean")

    def both(self):
        full = bundle.to_tree(self.TEXT, "navier-stokes-euler", self.OWN, self.REL)
        faithful = bundle.to_tree(self.TEXT, "navier-stokes-euler", self.OWN, self.REL, faithful=True)
        return full, faithful

    def test_the_default_is_unchanged(self):
        full, _ = self.both()
        self.assertEqual(full.split("\n")[:2], ["import Tengoku.NavierStokesEuler.Euler.FiniteGradeAlgebra", "import Tengoku"])
        self.assertNotIn(bundle.FAITHFUL_NOTE, full)

    def test_faithful_keeps_each_seeded_import_as_its_own_module(self):
        _, faithful = self.both()
        head = faithful.split("\n")[:4]
        self.assertEqual(head[:3], ["import Tengoku.NavierStokesEuler.Euler.FiniteGradeAlgebra", "import Tengoku.Seed.Algebra.BigOperators.NatAntidiagonal", "import Tengoku.Seed.Tactic"])
        self.assertNotIn("import Tengoku\n", faithful)

    def test_faithful_differs_from_the_default_only_in_the_header_and_the_note(self):
        full, faithful = self.both()
        body = lambda t: t.split("/-! The finite residual convolution. -/", 1)[1]  # noqa: E731
        self.assertEqual(body(full), body(faithful))
        self.assertEqual(faithful.count(bundle.FAITHFUL_NOTE), 1)

    def test_the_default_merges_two_seeded_imports_into_one_and_faithful_keeps_both(self):
        full, faithful = self.both()
        self.assertEqual(full.count("import Tengoku\n"), 1)
        self.assertEqual(sum(1 for ln in faithful.split("\n") if ln.startswith("import ")), 3)

    def test_the_same_text_composed_twice_is_the_same_bytes(self):
        a = bundle.to_tree(self.TEXT, "navier-stokes-euler", self.OWN, self.REL, faithful=True)
        b = bundle.to_tree(self.TEXT, "navier-stokes-euler", self.OWN, self.REL, faithful=True)
        self.assertEqual(a, b)

    def test_text_that_is_already_faithful_is_not_changed_by_a_second_pass_of_the_note(self):
        _, faithful = self.both()
        again = bundle.to_tree(faithful, "navier-stokes-euler", self.OWN | {"Tengoku.NavierStokesEuler.Euler.FiniteGradeAlgebra"}, self.REL, faithful=True)
        self.assertEqual(again.count(bundle.FAITHFUL_NOTE), 1)


class Compose(unittest.TestCase):
    """The whole bundle of the toy library (the setup of test_bundle's first test), composed in both modes."""

    GATE2 = "GATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n"

    def compose(self, *extra, gate2=GATE2, extra_modules=None, passed=None, keep=None):
        """`extra_modules`: {"Toy/C": (text, [[name, first line, last line], ...])}, library modules next to A and B whose declarations have ranges too."""
        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "A.lean").write_text(T.A)
        (lib / "Toy" / "B.lean").write_text(T.B)
        la, lb = T.A.split("\n"), T.B.split("\n")
        ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)  # noqa: E731
        one = (ln(la, "/-- the number one"), ln(la, "def one"))
        one_pos = (ln(la, "theorem one_pos"),) * 2
        uses = (ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos"))
        sidecars = {"Toy/A": [["Toy.one", *one], ["Toy.one_pos", *one_pos]], "Toy/B": [["Toy.uses_one_pos", *uses]]}
        for m, (text, rows) in (extra_modules or {}).items():
            (lib / (m + ".lean")).write_text(text)
            sidecars[m] = rows
        for m, rows in sidecars.items():
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(rows))
        keep = keep or [["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one"]]
        (d / "deps.log").write_text(f"x:1:0: info: BUNDLE_KEEP {json.dumps(keep)} BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps(passed or {"Toy.B": ["Toy.uses_one_pos"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text(gate2)
        (d / "killed.json").write_text("[]")
        r = subprocess.run(
            [sys.executable, str(HERE / "bundle.py"), "compose", "--gate2-killed", str(d / "killed.json"), "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"),
             "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src"), *extra],
            capture_output=True, text=True, check=False,
        )
        return d, r

    def read(self, d, mode, rel):
        return (d / f"bundle-{mode}" / "Tengoku" / "ToyLib" / rel).read_text()

    def test_the_default_mode_is_unchanged(self):
        d, r = self.compose()
        self.assertEqual(r.returncode, 0, r.stderr)
        a = self.read(d, "proposed", "Toy/A.lean")
        self.assertIn("import Tengoku\n", a)
        self.assertNotIn("Tengoku.Seed", a)
        self.assertNotIn(bundle.FAITHFUL_NOTE, a)

    def test_the_explicit_full_mode_is_the_default(self):
        d1, r1 = self.compose()
        d2, r2 = self.compose("--imports", "full")
        self.assertEqual((r1.returncode, r2.returncode), (0, 0))
        for rel in ("Toy/A.lean", "Toy/B.lean"):
            self.assertEqual(self.read(d1, "proposed", rel), self.read(d2, "proposed", rel))

    def test_faithful_mode_names_the_same_modules_in_the_tree_and_says_so(self):
        d, r = self.compose("--imports", "faithful")
        self.assertEqual(r.returncode, 0, r.stderr)
        a = self.read(d, "proposed", "Toy/A.lean")
        self.assertIn("import Tengoku.Seed.Data.Nat.Basic\n", a)
        self.assertNotIn("import Tengoku\n", a)
        self.assertEqual(a.count(bundle.FAITHFUL_NOTE), 1)
        self.assertIn("def one : Nat := 1", a)  # the library's own text is as before
        b = self.read(d, "proposed", "Toy/B.lean")
        self.assertIn("import Tengoku.ToyLib.Toy.A", b)  # the library's own module -> its place in the tree, as before
        self.assertEqual(b.count(bundle.FAITHFUL_NOTE), 1)

    def test_every_mode_of_the_bundle_gets_the_same_headers(self):
        d, r = self.compose("--imports", "faithful")
        self.assertEqual(r.returncode, 0, r.stderr)
        seen = []
        for mode in ("strict", "proposed", "wide"):
            f = d / f"bundle-{mode}" / "Tengoku" / "ToyLib" / "Toy" / "A.lean"
            if not f.exists():  # the strict allow-list refuses the toy's `notation`: that mode has no module A
                continue
            seen.append(mode)
            with self.subTest(mode):
                self.assertIn("import Tengoku.Seed.Data.Nat.Basic\n", f.read_text())
                self.assertEqual(f.read_text().count(bundle.FAITHFUL_NOTE), 1)
        self.assertEqual(seen, ["proposed", "wide"])

    def test_faithful_changes_headers_only_not_the_manifest_or_the_root_file_or_the_report_counts(self):
        d1, _ = self.compose()
        d2, _ = self.compose("--imports", "faithful")
        self.assertEqual((d1 / "bundle-proposed" / "manifest.jsonl").read_text(), (d2 / "bundle-proposed" / "manifest.jsonl").read_text())
        self.assertEqual((d1 / "bundle-proposed" / "Tengoku" / "ToyLib.lean").read_text(), (d2 / "bundle-proposed" / "Tengoku" / "ToyLib.lean").read_text())
        r1, r2 = (json.loads((d / "bundle-proposed" / "report.json").read_text()) for d in (d1, d2))
        for k in ("theorems", "modules_in_bundle", "passed_total"):
            self.assertEqual(r1[k], r2[k], k)

    def test_the_two_modes_differ_in_a_module_only_by_its_header_lines(self):
        d1, _ = self.compose()
        d2, _ = self.compose("--imports", "faithful")
        for rel in ("Toy/A.lean", "Toy/B.lean"):
            keep = lambda t: [ln for ln in t.split("\n") if ln and not ln.startswith("import ") and ln != bundle.FAITHFUL_NOTE]  # noqa: E731  (blank lines too: the note brings one)
            self.assertEqual(keep(self.read(d1, "proposed", rel)), keep(self.read(d2, "proposed", rel)), rel)

    def test_a_mode_that_is_neither_is_refused(self):
        _, r = self.compose("--imports", "bogus")
        self.assertEqual(r.returncode, 2)
        self.assertIn("invalid choice", r.stderr)


class Wiring(unittest.TestCase):
    """The workflows pass the mode on, and only `full` normalises the library's imports (a faithful library must keep the ones its authors wrote)."""

    SHARDED = (ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text()
    SHARD = (ROOT / ".github" / "workflows" / "bump-shard.yml").read_text()

    def test_bump_sharded_has_the_input_and_it_defaults_to_full(self):
        m = re.search(r"^      imports: \{ description: \"(.*?)\", type: choice, options: \[(.*?)\], default: \"(\w+)\" \}", self.SHARDED, re.M)
        self.assertIsNotNone(m, "no `imports` choice input in bump-sharded.yml")
        self.assertEqual(m.group(3), "full")
        self.assertIn("faithful", m.group(1))

    def test_bump_sharded_input_rejects_a_typo_before_any_shard_starts(self):
        # a free-text value such as `faithfull` would skip normalize-imports, build for hours and only then fail in compose (argparse): the dispatch form must refuse it
        m = re.search(r"^      imports: \{ .*?options: \[(.*?)\]", self.SHARDED, re.M)
        self.assertIsNotNone(m)
        self.assertEqual([o.strip() for o in m.group(1).split(",")], ["full", "faithful"])

    def test_bump_sharded_hands_it_to_the_shards(self):
        call = self.SHARDED.split("uses: ./.github/workflows/bump-shard.yml", 1)[1].split("permissions:", 1)[0]
        self.assertIn("imports: ${{ inputs.imports }}", call)

    def test_both_compose_calls_carry_it(self):
        calls = re.findall(r"bundle\.py compose .*?(?=\n      - |\n  \w)", self.SHARDED, re.S)
        self.assertEqual(len(calls), 2)
        for c in calls:
            self.assertIn('--imports "$IMPORTS"', c)

    def test_the_jobs_that_compose_have_IMPORTS_in_their_environment(self):
        envs = re.findall(r'^    env: \{ KEY: "\$\{\{ inputs.key \}\}", TOOLCHAIN:.*IMPORTS: "\$\{\{ inputs.imports \}\}" \}', self.SHARDED, re.M)
        self.assertEqual(len(envs), 2)  # compose and finish

    def test_bump_shard_takes_the_input_with_the_same_default(self):
        self.assertRegex(self.SHARD, r"imports: \{ type: string, default: \"full\" \}")
        self.assertIn("IMPORTS: ${{ inputs.imports }}", self.SHARD)

    def test_normalize_imports_runs_only_in_full_mode(self):
        lines = [ln for ln in self.SHARD.split("\n") if "normalize-imports" in ln and not ln.lstrip().startswith("#")]
        self.assertEqual(len(lines), 1)
        self.assertRegex(lines[0], r'^\s*if \[ "\$IMPORTS" = full \]; then python3 scripts/bump/engine\.py normalize-imports .*; fi\s*$')

    def test_a_single_job_bump_is_untouched(self):
        lib = (ROOT / ".github" / "workflows" / "bump-library.yml").read_text()
        self.assertIn('if [ "$IMPORTS" = full ]; then python3 scripts/bump/engine.py normalize-imports', lib)


if __name__ == "__main__":
    unittest.main()
