"""tree_dups.py: a library's copy of a module the tree already has is not shipped, and what imports it imports the tree's module, when the two are provably the same.

Every test names what the step guarantees in that case, and the tests marked (without the step) fail on the code before it: a copy and everything built on it was dropped.
"""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import tree_dups as td  # noqa: E402
import tree_verify as tv  # noqa: E402
import test_bundle  # noqa: E402  (the module, not its test classes: they would run again here)


def h(n: int) -> str:
    """a 32-digit fingerprint"""
    return f"{n:032x}"


def fp(rows: dict[str, dict[str, tuple[str, int]]]) -> str:
    """what ModuleFingerprint.lean prints: a module's `FP` lines, then its `FPEND`; the total last"""
    lines = []
    for m, decls in rows.items():
        lines += [f"FP\t{m}\t{n}\t{kind}\t{h(v)}" for n, (kind, v) in decls.items()]
        lines.append(f"FPEND\t{m}\t{len(decls)}")
    return "\n".join(lines) + f"\nfingerprints: {sum(len(d) for d in rows.values())} declarations\n"


def write(root: Path, files: dict[str, str]) -> Path:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return root


class AliasText(unittest.TestCase):
    ALIAS = {"Tengoku.Lib.Copy": ["Tengoku.Other.Real"]}

    def test_a_header_import_of_the_copy_becomes_an_import_of_the_tree_module(self):
        text = "import Tengoku\nimport Tengoku.Lib.Copy\n\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_alias_text(text, self.ALIAS), "import Tengoku\nimport Tengoku.Other.Real\n\ntheorem t : 1 = 1 := rfl\n")

    def test_the_other_lines_and_the_other_imports_are_not_touched(self):
        text = "import Tengoku\nimport Tengoku.Lib.Other\n\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_alias_text(text, self.ALIAS), text)

    def test_a_second_copy_of_an_import_line_is_dropped(self):
        text = "import Tengoku.Other.Real\nimport Tengoku.Lib.Copy\n\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_alias_text(text, self.ALIAS), "import Tengoku.Other.Real\n\ntheorem t : 1 = 1 := rfl\n")

    def test_several_tree_modules_replace_one_import_in_order(self):
        text = "import Tengoku.Lib.Copy\n\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_alias_text(text, {"Tengoku.Lib.Copy": ["Tengoku.A.X", "Tengoku.B.Y"]}), "import Tengoku.A.X\nimport Tengoku.B.Y\n\ntheorem t : 1 = 1 := rfl\n")

    def test_only_the_header_is_read(self):
        text = "import Tengoku\n\n/-- the word import starts this line:\nimport Tengoku.Lib.Copy\n-/\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_alias_text(text, self.ALIAS), text)

    def test_the_prefix_of_an_import_and_a_name_with_a_dash_are_kept(self):
        text = "public import Tengoku.Lib.Copy\n"
        self.assertEqual(td.apply_alias_text(text, {"Tengoku.Lib.Copy": ["Tengoku.Other.A-B"]}), "public import Tengoku.Other.«A-B»\n")
        self.assertEqual(td.apply_alias_text("import Tengoku.Lib.«A-B»\n", {"Tengoku.Lib.A-B": ["Tengoku.Other.Real"]}), "import Tengoku.Other.Real\n")

    def test_it_is_idempotent(self):
        text = "import Tengoku.Lib.Copy\nimport Tengoku.Z\n"
        once = td.apply_alias_text(text, self.ALIAS)
        self.assertEqual(td.apply_alias_text(once, self.ALIAS), once)


class AliasKeep(unittest.TestCase):
    """An importer that stops importing the copy would lose what the copy imported (Navier 2026-10-20: `unknown namespace EulerCylinderSobolevSpace`, 72 importers refused)."""

    def test_the_importers_import_what_the_copy_imported_after_the_trees_modules(self):
        aliases = {"Tengoku.Lib.Copy": ["Tengoku.Other.Real"]}
        keep = td.alias_keep(aliases, {"Tengoku.Lib.Copy": "import Tengoku\nimport Tengoku.Lib.D1\nimport Tengoku.Lib.D2\n\ndef c := 1\n"})
        self.assertEqual(keep, {"Tengoku.Lib.Copy": ["Tengoku", "Tengoku.Lib.D1", "Tengoku.Lib.D2"]})
        text = "import Tengoku\nimport Tengoku.Lib.Copy\n\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_alias_text(text, td.with_kept(aliases, keep)), "import Tengoku\nimport Tengoku.Other.Real\nimport Tengoku.Lib.D1\nimport Tengoku.Lib.D2\n\ntheorem t : 1 = 1 := rfl\n")

    def test_the_tree_s_own_module_is_not_repeated_and_the_prefix_of_the_import_is_kept(self):
        aliases = {"Tengoku.Lib.Copy": ["Tengoku.Other.Real"]}
        keep = td.alias_keep(aliases, {"Tengoku.Lib.Copy": "import Tengoku.Other.Real\nimport Tengoku.Lib.D1\n"})
        self.assertEqual(keep, {"Tengoku.Lib.Copy": ["Tengoku.Lib.D1"]})
        self.assertEqual(td.apply_alias_text("public import Tengoku.Lib.Copy\n", td.with_kept(aliases, keep)), "public import Tengoku.Other.Real\npublic import Tengoku.Lib.D1\n")

    def test_a_copy_that_imported_another_aliased_copy_keeps_that_one_s_tree_modules_and_imports(self):
        aliases = {"Tengoku.Lib.A": ["Tengoku.Other.A"], "Tengoku.Lib.B": ["Tengoku.Other.B"]}
        texts = {"Tengoku.Lib.A": "import Tengoku.Lib.B\nimport Tengoku.Lib.X\n", "Tengoku.Lib.B": "import Tengoku.Lib.Y\n"}
        keep = td.alias_keep(aliases, texts)
        self.assertEqual(keep["Tengoku.Lib.A"], ["Tengoku.Other.B", "Tengoku.Lib.Y", "Tengoku.Lib.X"])  # B is replaced by its tree module and by what B kept
        self.assertEqual(keep["Tengoku.Lib.B"], ["Tengoku.Lib.Y"])

    def test_two_copies_that_import_each_other_do_not_loop(self):
        aliases = {"Tengoku.Lib.A": ["Tengoku.Other.A"], "Tengoku.Lib.B": ["Tengoku.Other.B"]}
        texts = {"Tengoku.Lib.A": "import Tengoku.Lib.B\n", "Tengoku.Lib.B": "import Tengoku.Lib.A\n"}
        self.assertEqual(sorted(td.alias_keep(aliases, texts)), ["Tengoku.Lib.A", "Tengoku.Lib.B"])

    def test_nothing_is_kept_for_a_copy_without_a_text(self):
        self.assertEqual(td.alias_keep({"Tengoku.Lib.Copy": ["Tengoku.Other.Real"]}, {}), {})


class Parsing(unittest.TestCase):
    def test_a_module_cut_short_is_absent_not_an_error_and_not_a_clean_empty_module(self):
        """A run that was killed in the middle of a module: that module is not fingerprinted (it must not pass as the same), and the modules it finished are."""
        got = td.parse_fp(f"FP\tA\tf\tdef\t{h(1)}\nFPEND\tA\t1\nFP\tB\tg\tdef\t{h(2)}\n")
        self.assertEqual(list(got), ["A"])
        self.assertNotIn("B", got)

    def test_a_module_whose_count_does_not_match_is_not_fingerprinted_and_says_why(self):
        got = td.parse_fp(f"FP\tA\tf\tdef\t{h(1)}\nFPEND\tA\t2\nfingerprints: 2 declarations\n")
        self.assertEqual(dict(got), {})
        self.assertIn("incomplete", got.errors["A"])

    def test_a_module_the_program_could_not_load_carries_the_programs_message(self):
        """Lean-pool 2026-10-19: one import clash lost a whole batch. Now it loses the module it happened in."""
        got = td.parse_fp(f"FPERR\tTengoku.L.M\timport failed, environment already contains 'Foo.bar'\nFP\tN\tf\tdef\t{h(1)}\nFPEND\tN\t1\n")
        self.assertEqual(list(got), ["N"])
        self.assertIn("already contains", got.errors["Tengoku.L.M"])

    def test_a_module_with_no_declaration_is_there_and_empty(self):
        self.assertEqual(dict(td.parse_fp("FPEND\tA\t0\n")), {"A": {}})

    def test_the_outputs_of_several_processes_are_read_as_one(self):
        got = td.parse_fp(fp({"A": {"f": ("def", 1)}}) + fp({"B": {"g": ("def", 2)}}))
        self.assertEqual(sorted(got), ["A", "B"])

    def test_modules_are_read_without_guillemets(self):
        got = td.parse_fp(f"FP\tTengoku.L.«A-B»\tf\tdef\t{h(1)}\nFPEND\tTengoku.L.«A-B»\t1\nfingerprints: 1 declarations\n")
        self.assertEqual(list(got), ["Tengoku.L.A-B"])

    def test_a_file_that_is_not_there_is_none(self):
        self.assertIsNone(td.parse_fp_file("/nonexistent/fp.txt"))

    def test_clashes_name_the_tree_module_a_new_module_shares_a_name_with_on_either_side(self):
        text = "CLASH\tTengoku.L.M\tTengoku.O.X\t2\tf\nCLASH\tTengoku.O.Y\tTengoku.L.N\t1\tg\nclashes: 2 module pair(s), 3 name(s)\n"
        partners, both = td.clash_pairs(text, {"Tengoku.L.M", "Tengoku.L.N"})
        self.assertEqual({k: sorted(v) for k, v in partners.items()}, {"Tengoku.L.M": ["Tengoku.O.X"], "Tengoku.L.N": ["Tengoku.O.Y"]})
        self.assertEqual(both, set())

    def test_two_new_modules_that_clash_are_not_a_copy_of_a_tree_module(self):
        text = "CLASH\tTengoku.L.N\tTengoku.L.M\t1\tf\nclashes: 1 module pair(s), 1 name(s)\n"
        partners, both = td.clash_pairs(text, {"Tengoku.L.M", "Tengoku.L.N"})
        self.assertEqual(partners, {})
        self.assertEqual(both, {"Tengoku.L.M", "Tengoku.L.N"})

    def test_a_clash_check_without_its_ending_is_refused(self):
        with self.assertRaises(SystemExit):
            td.clash_pairs("CLASH\tA\tB\t1\tf\n", {"A"})


class Decide(unittest.TestCase):
    """What `same` lets you say: every declaration of the copy is a declaration of the tree's module(s), with the fingerprint (type, value, and everything below them) the tree's has."""

    PARTNER = td.parse_fp(fp({"Tengoku.O.X": {"f": ("def", 1), "g": ("theorem", 2), "extra": ("def", 3)}}))

    def test_same_when_every_declaration_has_the_same_fingerprint(self):
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1), "g": ("theorem", 2)}}))
        self.assertEqual(td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER), (["Tengoku.O.X"], ""))

    def test_the_tree_may_have_more_than_the_copy(self):
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1)}}))
        self.assertEqual(td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)[0], ["Tengoku.O.X"])

    def test_not_the_same_when_one_fingerprint_differs_and_it_says_which(self):
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1), "g": ("theorem", 99)}}))
        got, why = td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)
        self.assertIsNone(got)
        self.assertIn("`g`", why)

    def test_not_the_same_when_a_declaration_is_not_in_the_tree(self):
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1), "mine": ("def", 5)}}))
        got, why = td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)
        self.assertIsNone(got)
        self.assertIn("`mine`", why)

    def test_a_kind_that_differs_is_a_difference(self):
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("theorem", 1)}}))
        self.assertIsNone(td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)[0])

    def test_lean_s_numbered_helpers_are_not_compared_one_by_one(self):
        """Schoenflies rehearsal: 10 of 45 copies that were 'not the same' differed only in `match_1_5`-style names, which Lean numbers by the order it elaborates in."""
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1), "f.match_1_5": ("def", 50), "g.proof_3": ("theorem", 51), "g.eq_1": ("theorem", 52)}}))
        self.assertEqual(td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)[0], ["Tengoku.O.X"])

    def test_but_a_helper_a_definition_stands_on_is_in_that_definitions_fingerprint(self):
        """The fingerprint program takes a referenced constant's NAME into the referencing term, so a definition that matches on a different matcher differs: here as the fingerprint of `f` itself."""
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 999), "f.match_1_5": ("def", 50)}}))
        self.assertIsNone(td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)[0])

    def test_a_module_of_nothing_but_helpers_is_no_verdict(self):
        before = td.parse_fp(fp({"Tengoku.L.M": {"f.match_1_5": ("def", 50)}}))
        self.assertIsNone(td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)[0])

    def test_no_declaration_is_no_verdict_not_a_vacuous_yes(self):
        self.assertIsNone(td.decide("Tengoku.L.M", ["Tengoku.O.X"], td.parse_fp("FPEND\tTengoku.L.M\t0\n"), self.PARTNER)[0])

    def test_a_copy_that_was_not_fingerprinted_is_no_verdict_and_the_reason_is_the_programs(self):
        before = td.parse_fp("FPERR\tTengoku.L.M\timport failed, environment already contains 'Foo.bar'\n")
        got, why = td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, self.PARTNER)
        self.assertIsNone(got)
        self.assertIn("already contains", why)

    def test_a_copy_the_run_never_reached_is_no_verdict(self):
        got, why = td.decide("Tengoku.L.M", ["Tengoku.O.X"], td.parse_fp(""), self.PARTNER)
        self.assertIsNone(got)
        self.assertIn("did not reach", why)

    def test_a_tree_module_that_was_not_fingerprinted_is_no_verdict_and_is_named(self):
        """Never 'same' on the strength of nothing: the declaration may be in the module that could not be read."""
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1)}}))
        partner = td.parse_fp("FPERR\tTengoku.O.X\tcould not load\n")
        got, why = td.decide("Tengoku.L.M", ["Tengoku.O.X"], before, partner)
        self.assertIsNone(got)
        self.assertIn("Tengoku.O.X: could not load", why)

    def test_one_tree_module_that_was_not_fingerprinted_does_not_hide_a_match_in_another(self):
        partner = td.parse_fp(fp({"Tengoku.O.Y": {"f": ("def", 1)}}) + "FPERR\tTengoku.O.X\tcould not load\n")
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1)}}))
        self.assertEqual(td.decide("Tengoku.L.M", ["Tengoku.O.X", "Tengoku.O.Y"], before, partner)[0], ["Tengoku.O.Y"])

    def test_the_declarations_may_come_from_several_tree_modules(self):
        partner = td.parse_fp(fp({"Tengoku.O.X": {"f": ("def", 1)}, "Tengoku.O.Y": {"g": ("theorem", 2)}}))
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1), "g": ("theorem", 2)}}))
        self.assertEqual(td.decide("Tengoku.L.M", ["Tengoku.O.X", "Tengoku.O.Y"], before, partner)[0], ["Tengoku.O.X", "Tengoku.O.Y"])


class FlowBase(unittest.TestCase):
    """The whole step on a checkout: M is the library's copy of Tengoku.Other.Lib.X; B imports M, C imports B (an importer that is not a direct one), U is unrelated."""

    FILES = {
        "Tengoku/ToyLib/Toy/M.lean": "import Tengoku\n\ndef Toy.f := 1\n",
        "Tengoku/ToyLib/Toy/B.lean": "import Tengoku\nimport Tengoku.ToyLib.Toy.M\n\ntheorem Toy.t : Toy.f = 1 := rfl\n",
        "Tengoku/ToyLib/Toy/C.lean": "import Tengoku.ToyLib.Toy.B\n\ntheorem Toy.u : 1 = 1 := rfl\n",
        "Tengoku/ToyLib/Toy/U.lean": "import Tengoku\n\ntheorem Toy.v : 2 = 2 := rfl\n",
        "Tengoku/ToyLib.lean": "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in "MBCU"),
        "Tengoku/ToyLib/Deps.lean": "-- ToyLib\n",
    }
    BUILT = "".join(f"✔ [{i}/4] Built Tengoku.ToyLib.Toy.{m} (1s)\n" for i, m in enumerate("MBCU", 1)) + "Build completed successfully.\n"
    CLASH = "CLASH\tTengoku.ToyLib.Toy.M\tTengoku.Other.Lib.X\t1\tToy.f\nclashes: 1 module pair(s), 1 name(s)\n"

    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        self.bundle = write(self.d / "bundle", self.FILES)
        self.tree = write(self.d / "tree", {"Tengoku/Other/Lib/X.lean": "def Toy.f := 1\n"})
        self.out = self.d / "out"
        tv.main(["apply", "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out)])
        (self.d / "build.log").write_text(self.BUILT)
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle)])
        (self.d / "clashes.txt").write_text(self.CLASH)
        # the stale compiled files of the copy
        write(self.tree, {".lake/build/lib/lean/Tengoku/ToyLib/Toy/M.olean": "x", ".lake/build/lib/lean/Tengoku/ToyLib/Toy/M.ilean": "x", ".lake/build/lib/lean/Tengoku/ToyLib/Toy/B.olean": "x"})
        td.main(["candidates", "--clashes", str(self.d / "clashes.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])

    def plan(self, before_hash: int = 1, fork: bool = False, before: str | None = None, fork_identical: bool = False):
        before = before if before is not None else fp({"Tengoku.ToyLib.Toy.M": {"Toy.f": ("def", before_hash)}, "Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}, "Tengoku.ToyLib.Toy.C": {"Toy.u": ("theorem", 11)}})
        (self.d / "fp-before.txt").write_text(before)
        (self.d / "fp-partners.txt").write_text(fp({"Tengoku.Other.Lib.X": {"Toy.f": ("def", 1)}}))
        td.main(["plan", "--candidates", str(self.out / "dups-candidates.json"), "--fp-before", str(self.d / "fp-before.txt"), "--fp-partners", str(self.d / "fp-partners.txt"),
                 "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed", *(["--fork"] if fork else []), *(["--fork-identical"] if fork_identical else [])])

    def after(self, log2: str, after_rows: dict):
        (self.d / "log2.txt").write_text(log2)
        (self.d / "fp-after.txt").write_text(fp(after_rows))
        common = ["--candidates", str(self.out / "dups-candidates.json"), "--dups", str(self.out / "dups.json"), "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--log2", str(self.d / "log2.txt"), "--out", str(self.out)]
        td.main(["after-list", *common])
        td.main(["after-verdict", *common, "--fp-before", str(self.d / "fp-before.txt"), "--fp-after", str(self.d / "fp-after.txt")])

    SAME_AFTER = {"Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}, "Tengoku.ToyLib.Toy.C": {"Toy.u": ("theorem", 11)}}
    BUILT2 = "✔ [1/2] Built Tengoku.ToyLib.Toy.B (1s)\n✔ [2/2] Built Tengoku.ToyLib.Toy.C (1s)\nBuild completed successfully.\n"



class Flow(FlowBase):
    """The whole step on a checkout, copies that are aliased or stay clashes."""

    def test_the_copy_and_the_modules_that_import_it_are_found(self):
        cand = json.loads((self.out / "dups-candidates.json").read_text())["candidates"]
        self.assertEqual(list(cand), ["Tengoku.ToyLib.Toy.M"])
        self.assertEqual(cand["Tengoku.ToyLib.Toy.M"]["partners"], ["Tengoku.Other.Lib.X"])
        self.assertEqual(cand["Tengoku.ToyLib.Toy.M"]["importers"], ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])  # C imports B, which imports M
        self.assertEqual((self.out / "dups-before.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.M"])
        self.assertEqual((self.out / "dups-partners.txt").read_text().split(), ["Tengoku.Other.Lib.X"])

    def test_a_copy_that_did_not_build_is_no_candidate(self):
        (self.out / "built.txt").write_text("Tengoku.ToyLib.Toy.B\n")
        td.main(["candidates", "--clashes", str(self.d / "clashes.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        got = json.loads((self.out / "dups-candidates.json").read_text())
        self.assertEqual(json.loads((self.out / "dups.json").read_text())["aliases"], {})  # the default verdict is always there
        self.assertEqual(got["candidates"], {})
        self.assertIn("did not build", got["skipped"]["Tengoku.ToyLib.Toy.M"])

    def test_same_the_copy_leaves_the_checkout_and_its_importer_imports_the_tree_module(self):
        before_sha = json.loads((self.out / "new.json").read_text())["modules"]["Tengoku.ToyLib.Toy.B"]["sha256"]
        self.plan()
        self.assertFalse((self.tree / "Tengoku/ToyLib/Toy/M.lean").exists())
        self.assertFalse(list((self.tree / ".lake/build/lib/lean/Tengoku/ToyLib/Toy").glob("M.*")), "a stale olean of the copy is still there")
        self.assertTrue((self.tree / ".lake/build/lib/lean/Tengoku/ToyLib/Toy/B.olean").exists())  # the importers are rebuilt by lake, not deleted here
        self.assertEqual((self.tree / "Tengoku/ToyLib/Toy/B.lean").read_text(), "import Tengoku\nimport Tengoku.Other.Lib.X\n\ntheorem Toy.t : Toy.f = 1 := rfl\n")
        self.assertEqual((self.tree / "Tengoku/ToyLib/Toy/C.lean").read_text(), self.FILES["Tengoku/ToyLib/Toy/C.lean"])  # an indirect importer is not edited
        new = json.loads((self.out / "new.json").read_text())["modules"]
        self.assertNotIn("Tengoku.ToyLib.Toy.M", new)
        self.assertNotEqual(new["Tengoku.ToyLib.Toy.B"]["sha256"], before_sha)  # `check` holds the shipped bytes to THESE bytes
        self.assertEqual(new["Tengoku.ToyLib.Toy.B"]["sha256"], td.sha256((self.tree / "Tengoku/ToyLib/Toy/B.lean").read_bytes()))
        self.assertEqual((self.out / "targets.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.U"])
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual(dups["aliases"], {"Toy.M": ["Tengoku.Other.Lib.X"]})
        self.assertEqual((self.out / "dups-importers.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])

    def test_not_the_same_nothing_changes_and_the_copy_stays_a_clash(self):
        """The copy is refused by the clash check with what imports it, as it was before this step existed."""
        before = {p: (self.tree / p).read_text() for p in self.FILES if (self.tree / p).exists()}
        self.plan(before_hash=999)
        self.assertTrue((self.tree / "Tengoku/ToyLib/Toy/M.lean").exists())
        self.assertEqual({p: (self.tree / p).read_text() for p in before}, before)
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual(dups["aliases"], {})
        self.assertIn("`Toy.f`", dups["not_same"]["Toy.M"])
        self.assertIn("Tengoku.ToyLib.Toy.M", json.loads((self.out / "new.json").read_text())["modules"])

    def test_after_the_swap_importers_that_are_exactly_what_they_were_are_kept(self):
        self.plan()
        self.after(self.BUILT2, self.SAME_AFTER)
        self.assertEqual((self.out / "dups-after.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])
        self.assertEqual((self.out / "dups-failures.txt").read_text(), "")
        self.assertEqual(json.loads((self.out / "dups.json").read_text())["refused"], {})

    def test_an_importer_whose_declaration_changed_is_refused_and_the_reason_names_it(self):
        self.plan()
        rows = {"Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 77)}, "Tengoku.ToyLib.Toy.C": self.SAME_AFTER["Tengoku.ToyLib.Toy.C"]}
        self.after(self.BUILT2, rows)
        refused = (self.out / "dups-failures.txt").read_text()
        self.assertIn("Tengoku.ToyLib.Toy.B\t`Toy.t` is not the same", refused)
        self.assertNotIn("Toy.C", refused)  # C's own declarations are what they were; it goes with B because it imports it (tree_verify.collect)
        self.assertEqual(list(json.loads((self.out / "dups.json").read_text())["refused"]), ["Toy.B"])

    def test_a_declaration_that_appears_or_disappears_is_a_change(self):
        self.plan()
        rows = {"Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10), "Toy.extra": ("def", 1)}, "Tengoku.ToyLib.Toy.C": {}}
        self.after(self.BUILT2, rows)
        refused = (self.out / "dups-failures.txt").read_text()
        self.assertIn("`Toy.extra` is new", refused)
        self.assertIn("`Toy.u` is missing", refused)

    def test_an_importer_that_no_longer_builds_is_refused_with_what_imports_it(self):
        self.plan()
        log2 = "error: Tengoku/ToyLib/Toy/B.lean:3:0: unknown identifier\nerror: Lean exited with code 1\nSome required targets logged failures:\n- Tengoku.ToyLib.Toy.B\nerror: build failed\n"
        self.after(log2, {})
        refused = dict(ln.split("\t") for ln in (self.out / "dups-failures.txt").read_text().splitlines())
        self.assertEqual(sorted(refused), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])
        self.assertEqual((self.out / "dups-after.txt").read_text(), "")  # nothing is left to fingerprint

    def test_a_second_build_with_no_ending_keeps_only_what_it_built(self):
        """A build that was killed or ran out of time: a module with no `Built` line was not reached, and nothing is claimed about it."""
        self.plan()
        self.after("✔ [1/2] Built Tengoku.ToyLib.Toy.B (1s)\n", self.SAME_AFTER)
        refused = dict(ln.split("\t") for ln in (self.out / "dups-failures.txt").read_text().splitlines())
        self.assertEqual(list(refused), ["Tengoku.ToyLib.Toy.C"])
        self.assertIn("not reached", refused["Tengoku.ToyLib.Toy.C"])
        self.assertEqual((self.out / "dups-after.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B"])

    def test_a_fingerprint_run_that_did_not_finish_aliases_nothing_and_changes_nothing(self):
        """No verdict is never a yes: the copy stays where it was and goes the way it went before this step."""
        (self.d / "fp-before.txt").write_text("FP\tTengoku.ToyLib.Toy.M\tToy.f\tdef\t" + h(1) + "\n")  # cut short: no FPEND for the module
        (self.d / "fp-partners.txt").write_text(fp({"Tengoku.Other.Lib.X": {"Toy.f": ("def", 1)}}))
        before = {p: (self.tree / p).read_text() for p in self.FILES if (self.tree / p).exists()}
        td.main(["plan", "--candidates", str(self.out / "dups-candidates.json"), "--fp-before", str(self.d / "fp-before.txt"), "--fp-partners", str(self.d / "fp-partners.txt"),
                 "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        self.assertEqual({p: (self.tree / p).read_text() for p in before}, before)
        self.assertEqual(json.loads((self.out / "dups.json").read_text())["aliases"], {})

    def test_a_copy_the_program_could_not_load_is_not_aliased_and_the_reason_is_recorded(self):
        (self.d / "fp-before.txt").write_text("FPERR\tTengoku.ToyLib.Toy.M\timport failed, environment already contains 'Toy.f'\n")
        (self.d / "fp-partners.txt").write_text(fp({"Tengoku.Other.Lib.X": {"Toy.f": ("def", 1)}}))
        td.main(["plan", "--candidates", str(self.out / "dups-candidates.json"), "--fp-before", str(self.d / "fp-before.txt"), "--fp-partners", str(self.d / "fp-partners.txt"),
                 "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual(dups["aliases"], {})
        self.assertIn("already contains", dups["not_same"]["Toy.M"])
        self.assertTrue((self.tree / "Tengoku/ToyLib/Toy/M.lean").exists())

    def test_a_tree_module_that_is_only_a_stale_compiled_file_is_no_partner(self):
        """2026-10-19: the cache keeps the compiled file of a module that moved; the clash scan reads it, and an import of it is an import of a file the tree does not have."""
        (self.d / "stale.txt").write_text("CLASH\tTengoku.ToyLib.Toy.M\tTengoku.Gone.Lib.X\t1\tToy.f\nclashes: 1 module pair(s), 1 name(s)\n")
        td.main(["candidates", "--clashes", str(self.d / "stale.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        got = json.loads((self.out / "dups-candidates.json").read_text())
        self.assertEqual(got["candidates"], {})
        self.assertIn("no source in the tree", got["skipped"]["Tengoku.ToyLib.Toy.M"])
        self.assertEqual((self.out / "dups-partners.txt").read_text(), "")

    def test_a_stale_partner_does_not_hide_a_real_one(self):
        (self.d / "both.txt").write_text("CLASH\tTengoku.ToyLib.Toy.M\tTengoku.Gone.Lib.X\t1\tToy.f\nCLASH\tTengoku.ToyLib.Toy.M\tTengoku.Other.Lib.X\t1\tToy.f\nclashes: 2 module pair(s), 2 name(s)\n")
        td.main(["candidates", "--clashes", str(self.d / "both.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        self.assertEqual(json.loads((self.out / "dups-candidates.json").read_text())["candidates"]["Tengoku.ToyLib.Toy.M"]["partners"], ["Tengoku.Other.Lib.X"])

    def test_after_the_swap_importers_that_cannot_be_compared_are_refused(self):
        self.plan()
        (self.d / "log2.txt").write_text(self.BUILT2)
        (self.d / "fp-after.txt").write_text("FP\tTengoku.ToyLib.Toy.B\tToy.t\ttheorem\t" + h(10) + "\n")  # cut short: no FPEND
        common = ["--candidates", str(self.out / "dups-candidates.json"), "--dups", str(self.out / "dups.json"), "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--log2", str(self.d / "log2.txt"), "--out", str(self.out)]
        td.main(["after-verdict", *common, "--fp-before", str(self.d / "fp-before.txt"), "--fp-after", str(self.d / "fp-after.txt")])
        refused = dict(ln.split("\t") for ln in (self.out / "dups-failures.txt").read_text().splitlines())
        self.assertEqual(sorted(refused), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])
        self.assertIn("could not be compared", refused["Tengoku.ToyLib.Toy.B"])

    def test_nothing_to_decide_when_there_is_no_copy(self):
        (self.d / "none.txt").write_text("clashes: 0 module pair(s), 0 name(s)\n")
        td.main(["candidates", "--clashes", str(self.d / "none.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        self.assertEqual((self.out / "dups-before.txt").read_text(), "")
        td.main(["plan", "--candidates", str(self.out / "dups-candidates.json"), "--fp-before", "/nonexistent", "--fp-partners", "/nonexistent", "--new", str(self.out / "new.json"), "--tree", str(self.tree),
                 "--out", str(self.out), "--mode", "proposed"])
        self.assertEqual(json.loads((self.out / "dups.json").read_text())["aliases"], {})

    def test_collect_refuses_the_importers_the_swap_refused_and_what_imports_them(self):
        self.plan()
        (self.d / "swap.txt").write_text("Tengoku.ToyLib.Toy.B\t`Toy.t` is not the same on the tree's module\n")
        (self.d / "build.log").write_text(self.BUILT2.replace("Build completed", "✔ [3/3] Built Tengoku.ToyLib.Toy.U (1s)\nBuild completed"))
        tv.main(["collect", "--new", str(self.out / "new.json"), "--log", str(self.d / "build.log"), "--out", str(self.out), "--bundle", str(self.bundle), "--extra-failing", str(self.d / "swap.txt")])
        self.assertEqual(sorted(json.loads((self.out / "ok.json").read_text())), ["Tengoku.ToyLib.Toy.U"])  # B is refused and C imports B
        self.assertEqual((self.out / "failing.txt").read_text().split(), ["Toy.B"])
        self.assertIn("1 more import a refused one", (self.out / "summary.txt").read_text())
        self.assertIn("swap: Toy.B: `Toy.t` is not the same", (self.out / "summary.txt").read_text())

    def test_merge_keeps_the_verdict_of_each_mode(self):
        self.plan()
        (self.out / "dups.json").write_text(json.dumps({**json.loads((self.out / "dups.json").read_text()), "mode": "proposed"}))
        td.main(["merge", "--out", str(self.d / "merged.json"), str(self.out / "dups.json")])
        self.assertEqual(td.load_for_compose(str(self.d / "merged.json")), {"proposed": {"Toy.M": ["Tengoku.Other.Lib.X"]}})

    def test_a_malformed_merged_file_is_an_error_not_an_empty_answer(self):
        (self.d / "bad.json").write_text(json.dumps({"modes": {"proposed": {"aliases": ["Toy.M"]}}}))
        with self.assertRaises(SystemExit):
            td.load_for_compose(str(self.d / "bad.json"))


class KeepFlow(FlowBase):
    """The copy M imports a module Q of the library; what imports M must import Q too once it imports the tree's module in M's place."""

    FILES = {**FlowBase.FILES, "Tengoku/ToyLib/Toy/Q.lean": "import Tengoku\n\ndef Toy.q := 3\n", "Tengoku/ToyLib/Toy/M.lean": "import Tengoku.ToyLib.Toy.Q\n\ndef Toy.f := 1\n",
             "Tengoku/ToyLib.lean": "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in "MBCUQ")}
    BUILT = "".join(f"✔ [{i}/5] Built Tengoku.ToyLib.Toy.{m} (1s)\n" for i, m in enumerate("MBCUQ", 1)) + "Build completed successfully.\n"

    def test_the_importer_imports_the_tree_s_module_and_what_the_copy_imported(self):
        self.plan()
        b = (self.tree / "Tengoku/ToyLib/Toy/B.lean").read_text()
        self.assertIn("import Tengoku.Other.Lib.X\nimport Tengoku.ToyLib.Toy.Q\n", b)
        self.assertNotIn("Toy.M", b)
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual(dups["aliases"], {"Toy.M": ["Tengoku.Other.Lib.X"]})
        self.assertIn("Tengoku.ToyLib.Toy.Q", dups["alias_keep"]["Toy.M"])  # what compose needs to ship the same bytes

    def test_the_merged_file_carries_it_to_compose(self):
        self.plan()
        merged = self.d / "merged.json"
        td.main(["merge", str(self.out / "dups.json"), "--out", str(merged)])
        self.assertIn("Tengoku.ToyLib.Toy.Q", td.load_alias_keep_for_compose(str(merged))["proposed"]["Toy.M"])


class ForkFlow(FlowBase):
    """A copy that differs from the tree's module: it is wrapped, with what imports it, in `ToyLibFork`; the tree builds it so; it ships only if every declaration is what the library has."""

    ROWS_BEFORE = {"Tengoku.ToyLib.Toy.M": {"Toy.f": ("def", 999)}, "Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}, "Tengoku.ToyLib.Toy.C": {"Toy.u": ("theorem", 11)}}
    BUILT_WRAPPED = "".join(f"✔ [{i}/3] Built Tengoku.ToyLib.Toy.{m} (1s)\n" for i, m in enumerate("MBC", 1)) + "Build completed successfully.\n"

    def wrapped(self, name: str) -> bool:
        text = (self.tree / f"Tengoku/ToyLib/Toy/{name}.lean").read_text()
        return "\nnamespace ToyLibFork\n" in text and "end ToyLibFork" not in text

    def test_a_copy_that_differs_is_wrapped_with_what_imports_it_and_stays(self):
        self.plan(before_hash=999, fork=True)
        self.assertTrue(all(self.wrapped(m) for m in "MBC"))
        self.assertEqual((self.tree / "Tengoku/ToyLib/Toy/U.lean").read_text(), self.FILES["Tengoku/ToyLib/Toy/U.lean"])  # unrelated: not touched
        new = json.loads((self.out / "new.json").read_text())["modules"]
        for m in "MBC":
            self.assertEqual(new[f"Tengoku.ToyLib.Toy.{m}"]["sha256"], td.sha256((self.tree / f"Tengoku/ToyLib/Toy/{m}.lean").read_bytes()))  # `check` holds the shipped bytes to THESE bytes
        self.assertIn("Tengoku.ToyLib.Toy.M", new)  # the copy is not removed: it is built, wrapped
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual((dups["aliases"], dups["not_same"]), ({}, {}))
        self.assertEqual(list(dups["forks"]), ["Toy.M"])
        self.assertEqual(dups["forked"], ["Toy.B", "Toy.C", "Toy.M"])
        self.assertEqual(dups["fork_namespace"], "ToyLibFork")

    MODULE_B = "module\n\npublic import Tengoku.ToyLib.Toy.M\n\ntheorem Toy.t : Toy.f = 1 := rfl\n"

    def test_with_the_switch_an_identical_copy_that_a_module_system_file_would_import_is_forked(self):
        """lean-pool 2026-10-20: 'cannot import non-`module` Tengoku.NavierStokesEuler… from `module`': the tree's module is a plain file, the library's importers are files of the module system"""
        write(self.tree, {"Tengoku/ToyLib/Toy/B.lean": self.MODULE_B})
        self.plan(before_hash=1, fork=True, fork_identical=True)
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual(dups["aliases"], {})
        self.assertEqual(dups["forks_identical"], ["Toy.M"])
        self.assertEqual(dups["forked"], ["Toy.B", "Toy.C", "Toy.M"])
        self.assertIn("which a file of the module system cannot import", dups["forks"]["Toy.M"])
        self.assertTrue(all(self.wrapped(m) for m in "MBC"))
        self.assertTrue((self.tree / "Tengoku/ToyLib/Toy/M.lean").exists())  # shipped again, wrapped: it is not removed
        self.assertIn("import Tengoku.ToyLib.Toy.M\n", (self.tree / "Tengoku/ToyLib/Toy/B.lean").read_text())  # still imports the copy: no alias edit

    def test_without_the_switch_the_same_copy_is_aliased_whatever_the_importers_are(self):
        write(self.tree, {"Tengoku/ToyLib/Toy/B.lean": self.MODULE_B})
        self.plan(before_hash=1, fork=True)
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual((dups["aliases"], dups["forks_identical"], dups["forked"]), ({"Toy.M": ["Tengoku.Other.Lib.X"]}, [], []))

    def test_with_the_switch_an_importer_that_is_not_of_the_module_system_keeps_the_alias(self):
        self.plan(before_hash=1, fork=True, fork_identical=True)
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual((list(dups["aliases"]), dups["forks_identical"]), (["Toy.M"], []))

    def test_with_the_switch_a_tree_module_of_the_module_system_keeps_the_alias(self):
        write(self.tree, {"Tengoku/ToyLib/Toy/B.lean": self.MODULE_B, "Tengoku/Other/Lib/X.lean": "module\n\n@[expose] public section\ndef Toy.f := 1\n"})
        self.plan(before_hash=1, fork=True, fork_identical=True)
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual((list(dups["aliases"]), dups["forks_identical"]), (["Toy.M"], []))

    def test_the_identical_forks_are_merged_for_compose(self):
        write(self.tree, {"Tengoku/ToyLib/Toy/B.lean": self.MODULE_B})
        self.plan(before_hash=1, fork=True, fork_identical=True)
        td.main(["merge", "--out", str(self.d / "merged.json"), str(self.out / "dups.json")])
        self.assertEqual(td.load_identical_forks_for_compose(str(self.d / "merged.json")), {"proposed": {"Toy.M"}})
        (self.d / "old.json").write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": {"aliases": {}, "not_same": {}, "refused": {}}}}))
        self.assertEqual(td.load_identical_forks_for_compose(str(self.d / "old.json")), {"proposed": set()})

    def test_a_file_of_the_module_system_is_told_from_a_plain_one_by_its_header(self):
        self.assertTrue(td.is_module_system("/- c -/\nmodule\n\npublic import A\n"))
        self.assertFalse(td.is_module_system("import A\n\n/-- module -/\ndef a := 1\n"))
        self.assertFalse(td.is_module_system("import A\n\ndef module_name := 1\n"))

    def test_the_importer_of_an_identical_copy_is_edited_and_the_wrap_goes_on_after_it(self):
        """one text can need both edits: its import of an identical copy is pointed at the tree's module, and it is wrapped because it imports a copy that differs"""
        write(self.tree, {"Tengoku/ToyLib/Toy/B.lean": "import Tengoku\nimport Tengoku.ToyLib.Toy.M\nimport Tengoku.ToyLib.Toy.A\n\ntheorem Toy.t : Toy.f = 1 := rfl\n", "Tengoku/ToyLib/Toy/A.lean": "def Toy.a := 1\n"})
        self.assertEqual(td.apply_fork_text(td.apply_alias_text((self.tree / "Tengoku/ToyLib/Toy/B.lean").read_text(), {"Tengoku.ToyLib.Toy.A": ["Tengoku.Other.Lib.X"]}), "ToyLibFork").count("import "), 3)

    def test_without_the_switch_a_copy_that_differs_stays_a_clash_as_before(self):
        self.plan(before_hash=999)
        self.assertFalse(any(self.wrapped(m) for m in "MBC"))
        self.assertEqual(json.loads((self.out / "dups.json").read_text())["forked"], [])

    def test_a_copy_that_was_not_fingerprinted_is_not_forked(self):
        self.plan(before=fp({"Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}}) + "FPERR\tTengoku.ToyLib.Toy.M\tcould not load\n", fork=True)
        self.assertFalse(any(self.wrapped(m) for m in "MBC"))
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual((dups["forks"], dups["forked"]), ({}, []))
        self.assertIn("could not load", dups["not_same"]["Toy.M"])

    def test_a_prelude_file_stops_the_fork(self):
        write(self.tree, {"Tengoku/ToyLib/Toy/B.lean": "prelude\nimport Tengoku.ToyLib.Toy.M\n\ntheorem Toy.t : Toy.f = 1 := rfl\n"})
        self.plan(before_hash=999, fork=True)
        self.assertFalse(any(self.wrapped(m) for m in "MC"))
        self.assertIn("cannot be wrapped", json.loads((self.out / "dups.json").read_text())["not_same"]["Toy.M"])

    def test_after_the_build_every_wrapped_module_that_is_what_it_was_is_kept(self):
        self.plan(before=fp(self.ROWS_BEFORE), fork=True)
        self.after(self.BUILT_WRAPPED, self.ROWS_BEFORE)  # the program leaves the namespace off: the rows are the same
        self.assertEqual((self.out / "dups-after.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.M"])
        self.assertEqual((self.out / "dups-failures.txt").read_text(), "")

    def test_a_wrapped_module_whose_declaration_is_not_what_it_was_is_refused_and_names_it(self):
        """A name that resolves to another declaration once the module is wrapped (dot notation, an `open`) changes the fingerprint of what stands on it."""
        self.plan(before=fp(self.ROWS_BEFORE), fork=True)
        rows = {**self.ROWS_BEFORE, "Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 77)}}
        self.after(self.BUILT_WRAPPED, rows)
        self.assertIn("Tengoku.ToyLib.Toy.B\t`Toy.t` is not the same", (self.out / "dups-failures.txt").read_text())

    def test_a_wrapped_copy_that_does_not_build_is_refused_and_so_is_what_imports_it(self):
        self.plan(before=fp(self.ROWS_BEFORE), fork=True)
        log2 = "error: Tengoku/ToyLib/Toy/M.lean:5:0: unknown identifier\nerror: Lean exited with code 1\nSome required targets logged failures:\n- Tengoku.ToyLib.Toy.M\nerror: build failed\n"
        self.after(log2, {})
        refused = dict(ln.split("\t") for ln in (self.out / "dups-failures.txt").read_text().splitlines())
        self.assertEqual(sorted(refused), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.M"])

    def test_the_forks_of_each_mode_are_merged_for_compose(self):
        self.plan(before=fp(self.ROWS_BEFORE), fork=True)
        td.main(["merge", "--out", str(self.d / "merged.json"), str(self.out / "dups.json")])
        self.assertEqual(td.load_forks_for_compose(str(self.d / "merged.json")), {"proposed": ("ToyLibFork", {"Toy.B", "Toy.C", "Toy.M"})})
        self.assertEqual(td.load_for_compose(str(self.d / "merged.json")), {"proposed": {}})

    def test_a_merged_file_from_before_forks_existed_wraps_nothing(self):
        (self.d / "old.json").write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": {"aliases": {}, "not_same": {}, "refused": {}}}}))
        self.assertEqual(td.load_forks_for_compose(str(self.d / "old.json")), {"proposed": ("", set())})

    def test_a_malformed_fork_list_is_an_error_not_an_empty_answer(self):
        (self.d / "bad.json").write_text(json.dumps({"modes": {"proposed": {"aliases": {}, "forked": ["Toy.M"], "fork_namespace": ""}}}))
        with self.assertRaises(SystemExit):
            td.load_forks_for_compose(str(self.d / "bad.json"))


class ForkText(unittest.TestCase):
    """`apply_fork_text`: the one edit that makes a forked copy, made on the checkout and on the bundle that ships."""

    NS = "ToyLibFork"

    def test_the_namespace_opens_after_the_last_import_and_is_left_open(self):
        """Lean closes the scopes a file leaves open at its end; 4,049 of lean-pool's 4,131 files leave a `public section` open, where an `end X` at the end would be an error."""
        text = "import Tengoku\nimport Tengoku.A\n\n/-- doc -/\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(td.apply_fork_text(text, self.NS), "import Tengoku\nimport Tengoku.A\n\nnamespace ToyLibFork\n\n/-- doc -/\ntheorem t : 1 = 1 := rfl\n")

    def test_nothing_closes_the_namespace_so_a_file_that_leaves_a_section_open_still_builds(self):
        out = td.apply_fork_text("import Tengoku\n\n@[expose] public section\ndef a := 1\n", self.NS)
        self.assertNotIn("end ToyLibFork", out)
        self.assertEqual(out.count("namespace ToyLibFork"), 1)

    def test_a_docstring_of_the_first_declaration_is_not_separated_from_it(self):
        out = td.apply_fork_text("import Tengoku\n/-- the first -/\ndef a := 1\n", self.NS)
        self.assertLess(out.index("namespace ToyLibFork"), out.index("/-- the first -/"))

    def test_an_import_in_a_comment_below_the_header_is_prose(self):
        text = "import Tengoku\n\n/-- about\nimport Tengoku.B\n-/\ndef a := 1\n"
        self.assertTrue(td.apply_fork_text(text, self.NS).startswith("import Tengoku\n\nnamespace ToyLibFork\n"))

    def test_the_prefix_of_an_import_is_still_an_import(self):
        self.assertIn("namespace ToyLibFork", td.apply_fork_text("public import Tengoku.A\n\ndef a := 1\n", self.NS))

    def test_a_file_of_lean_s_module_system_is_wrapped_below_its_module_line_and_imports(self):
        """every file of lean-pool but one is one: `module`, the imports, then `@[expose] public section`"""
        text = "/- c -/\nmodule\n\npublic import Tengoku.A\nimport Tengoku.B\n\n@[expose] public section\ndef a := 1\n"
        self.assertEqual(td.apply_fork_text(text, self.NS), "/- c -/\nmodule\n\npublic import Tengoku.A\nimport Tengoku.B\n\nnamespace ToyLibFork\n\n@[expose] public section\ndef a := 1\n")

    def test_a_module_system_file_with_no_import_is_wrapped_after_its_module_line(self):
        self.assertEqual(td.apply_fork_text("module\n\n@[expose] public section\ndef a := 1\n", self.NS), "module\n\nnamespace ToyLibFork\n\n@[expose] public section\ndef a := 1\n")

    def test_a_file_that_imports_nothing_is_wrapped_from_its_top(self):
        self.assertEqual(td.apply_fork_text("/-- a -/\ndef a := 1\n", self.NS), "namespace ToyLibFork\n/-- a -/\ndef a := 1\n")

    def test_a_namespace_the_file_re_opens_keeps_the_names_of_the_modules_it_imports_in_reach(self):
        """Navier 2026-10-20: `namespace EulerQuadraticSource` + a bare `source` that the imported module declares: wrapped, the namespace is `ToyLibFork.EulerQuadraticSource` and `source` is lost."""
        out = td.apply_fork_text("import Tengoku.A\n\nnamespace EulerQuadraticSource\ndef c := source\nend EulerQuadraticSource\n", self.NS)
        self.assertEqual(out, "import Tengoku.A\n\nnamespace ToyLibFork\n\nnamespace EulerQuadraticSource\nopen _root_.EulerQuadraticSource\ndef c := source\nend EulerQuadraticSource\n")

    def test_a_dotted_namespace_opens_every_prefix_of_it_innermost_first_and_keeps_the_indentation(self):
        out = td.apply_fork_text("import Tengoku.A\nsection S\n  namespace A.B.C -- about it\n  def c := 1\n  end A.B.C\nend S\n", self.NS)
        self.assertIn("  namespace A.B.C -- about it\n  open _root_.A.B.C _root_.A.B _root_.A\n  def c := 1\n", out)

    def test_a_guillemet_name_is_one_component(self):
        out = td.apply_fork_text("import Tengoku.A\nnamespace «A-B».C\nend «A-B».C\n", self.NS)
        self.assertIn("namespace «A-B».C\nopen _root_.«A-B».C _root_.«A-B»\n", out)

    def test_namespace_in_is_not_a_namespace_that_stays_open(self):
        text = "import Tengoku.A\nnamespace X in\ndef c := 1\n"
        self.assertNotIn("open _root_", td.apply_fork_text(text, self.NS))

    def test_a_file_without_a_namespace_gets_only_the_fork_s(self):
        self.assertNotIn("open _root_", td.apply_fork_text("import Tengoku.A\ndef c := 1\n", self.NS))

    def test_a_prelude_file_cannot_be_wrapped(self):
        self.assertIsNone(td.apply_fork_text("prelude\nimport Init.Core\n\ndef a := 1\n", self.NS))

    def test_a_file_without_a_final_line_break_ends_with_one(self):
        self.assertTrue(td.apply_fork_text("import Tengoku\ndef a := 1", self.NS).endswith("def a := 1\n"))

    def test_the_namespace_of_a_library(self):
        self.assertEqual(td.fork_namespace("LeanPool"), "LeanPoolFork")


class ChooseForks(unittest.TestCase):
    NOT_SAME = {"Tengoku.L.M": "`f` is not the same"}
    CAND = {"Tengoku.L.M": {"partners": ["Tengoku.O.X"], "importers": ["Tengoku.L.B"]}}
    TEXTS = {"Tengoku.L.M": "import Tengoku\n\ndef f := 1\n", "Tengoku.L.B": "import Tengoku.L.M\n\ndef g := f\n"}

    def choose(self, not_same=None, before=None, aliased=frozenset(), texts=None):
        before = before if before is not None else td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1)}}))
        return td.choose_forks(dict(not_same or self.NOT_SAME), self.CAND, before, set(aliased), dict(texts or self.TEXTS), "L")

    def test_a_copy_with_a_complete_fingerprint_is_forked_with_what_imports_it(self):
        forks, wrap, kept = self.choose()
        self.assertEqual(list(forks), ["Tengoku.L.M"])
        self.assertEqual(wrap, {"Tengoku.L.M", "Tengoku.L.B"})
        self.assertEqual(kept, {})

    def test_a_copy_that_was_not_fingerprinted_is_not_forked(self):
        forks, wrap, kept = self.choose(before=td.parse_fp("FPERR\tTengoku.L.M\tcould not load\n"))
        self.assertEqual((forks, wrap), ({}, set()))
        self.assertIn("Tengoku.L.M", kept)

    def test_a_module_that_cannot_be_wrapped_stops_the_fork_and_says_so(self):
        forks, wrap, kept = self.choose(texts={**self.TEXTS, "Tengoku.L.B": "prelude\nimport Tengoku.L.M\n\ndef g := f\n"})
        self.assertEqual((forks, wrap), ({}, set()))
        self.assertIn("cannot be wrapped", kept["Tengoku.L.M"])

    def test_a_file_of_the_module_system_is_forked_like_any_other(self):
        text = "module\n\npublic import Tengoku.L.M\n\n@[expose] public section\ntheorem g : True := trivial\nend\n"
        forks, wrap, _ = self.choose(texts={**self.TEXTS, "Tengoku.L.B": text})
        self.assertEqual(list(forks), ["Tengoku.L.M"])

    def test_the_end_of_a_public_section_does_not_make_the_module_look_like_it_left_the_namespace(self):
        """lean_names.names pops its scope stack at every `end`: a `public section` it does not know would pop the namespace, and every declaration after it would look like an escape"""
        text = "import Tengoku.L.M\n\n@[expose] public section\nsection Inner\ntheorem a : True := trivial\nend Inner\nend\ntheorem b : True := trivial\n"
        self.assertEqual(td.wrap_escapes(text, "LFork"), [])

    def test_a_declaration_that_escapes_the_namespace_stops_the_fork_and_says_so(self):
        """CodeRabbit on emissary#73: `theorem _root_.foo` stays `foo` inside the namespace, so the wrapped module would still declare the clashing name."""
        forks, wrap, kept = self.choose(texts={**self.TEXTS, "Tengoku.L.B": "import Tengoku.L.M\n\ntheorem _root_.escapes : True := trivial\n"})
        self.assertEqual((forks, wrap), ({}, set()))
        self.assertIn("`escapes`", kept["Tengoku.L.M"])

    def test_a_root_reference_in_a_type_a_comment_or_a_string_is_not_an_escape(self):
        text = "import Tengoku.L.M\n\n/-- _root_.no -/\ntheorem g : _root_.Nat.zero = 0 := rfl\ndef s := \"theorem _root_.not_a_decl\"\n"
        forks, wrap, _ = self.choose(texts={**self.TEXTS, "Tengoku.L.B": text})
        self.assertEqual(list(forks), ["Tengoku.L.M"])

    def test_a_private_declaration_is_not_an_escape(self):
        forks, _, _ = self.choose(texts={**self.TEXTS, "Tengoku.L.B": "import Tengoku.L.M\n\nprivate theorem hidden : True := trivial\n"})
        self.assertEqual(list(forks), ["Tengoku.L.M"])

    def test_an_identical_copy_that_imports_a_forked_one_is_not_wrapped(self):
        forks, wrap, _ = self.choose(aliased={"Tengoku.L.B"})
        self.assertEqual(wrap, {"Tengoku.L.M"})


class Compose(unittest.TestCase):
    """`bundle.py compose --keep-dups`: the copy is kept for the tree's build to decide (the draft), and in the final cut the ones it showed to be the same are not shipped while what imports
    them is; every other copy is dropped with its importers, exactly as without the flag."""

    FILES = ["Owned", "AboveOwned", "Clean"]

    @staticmethod
    def harness():
        """the toy library and the compose runner of test_bundle.AutoDrops, without running its tests again"""
        return type("Harness", (), {"FILES": test_bundle.AutoDrops.FILES, "PASSED": test_bundle.AutoDrops.PASSED, "leaks_in_leaky": staticmethod(test_bundle.AutoDrops.leaks_in_leaky)})()

    def run_compose(self, *extra: str):
        return test_bundle.AutoDrops.compose(self.harness(), ["Toy.owned"], "--tree-names", "@names", *extra, files=self.FILES)

    def shipped(self, d: Path, mode: str = "proposed") -> list[str]:
        return [json.loads(x)["name"] for x in (d / ("bundle" if mode == "strict" else f"bundle-{mode}") / "manifest.jsonl").read_text().splitlines()]

    def dups_file(self, aliases: dict[str, list[str]], mode: str = "proposed", forked: list[str] | None = None, identical: list[str] | None = None) -> str:
        p = Path(tempfile.mkdtemp()) / "dups.json"
        spec = {"aliases": aliases, "not_same": {}, "refused": {}, "forks": {}, "forked": forked or [], "fork_namespace": "ToyLibFork" if forked else "", "forks_identical": identical or []}
        p.write_text(json.dumps({"ns": "ToyLib", "modes": {mode: spec}}))
        return str(p)

    def text(self, d: Path, mod: str, mode: str = "proposed") -> str:
        return (d / f"bundle-{mode}" / "Tengoku" / "ToyLib" / "Toy" / f"{mod}.lean").read_text()

    def test_without_the_flag_the_copy_and_its_importers_are_dropped(self):
        """(without the step) the situation this step exists for."""
        d, p = self.run_compose()
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(self.shipped(d), ["Toy.clean_one"])

    def test_the_draft_keeps_the_copy_and_its_importers_for_the_tree_to_build(self):
        d, p = self.run_compose("--keep-dups")
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(self.shipped(d)), ["Toy.above_owned", "Toy.clean_one", "Toy.owned"])
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(rep["dups"]["kept_for_the_tree_build"], 1)
        self.assertEqual(rep["dups"]["aliased"], 0)
        self.assertIn("import Tengoku.ToyLib.Toy.Owned", self.text(d, "AboveOwned"))

    def test_the_final_cut_does_not_ship_the_aliased_copy_and_ships_what_imports_it_on_the_tree_module(self):
        draft, _ = self.run_compose("--keep-dups")
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({"Toy.Owned": ["Tengoku.Other.Lib.Owned"]}))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(self.shipped(d)), ["Toy.above_owned", "Toy.clean_one"])  # not Toy.owned: the tree has it
        self.assertFalse((d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "Owned.lean").exists())
        self.assertEqual((d / "bundle-proposed" / "Tengoku" / "ToyLib.lean").read_text(), "import Tengoku.ToyLib.Toy.AboveOwned\nimport Tengoku.ToyLib.Toy.Clean\n")
        # the bytes the tree built, with the one edit tree_dups.py made on the checkout: nothing else about the importer changed
        self.assertEqual(self.text(d, "AboveOwned"), td.apply_alias_text(self.text(draft, "AboveOwned"), {"Tengoku.ToyLib.Toy.Owned": ["Tengoku.Other.Lib.Owned"]}))
        self.assertIn("import Tengoku.Other.Lib.Owned", self.text(d, "AboveOwned"))
        self.assertNotIn("Tengoku.ToyLib.Toy.Owned", self.text(d, "AboveOwned"))
        self.assertEqual(self.text(d, "Clean"), self.text(draft, "Clean"))
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(rep["dups"]["aliased"], 1)
        ledger = json.loads((d / "bundle-proposed.ledger.json").read_text())
        self.assertIn("identical to Tengoku.Other.Lib.Owned", ledger["modules"]["Toy.Owned"]["reason"])  # nothing is missing without a reason
        self.assertEqual(rep["theorems"] + sum(rep["left_out"].values()), rep["passed_total"])  # the accounting identity still holds

    def test_a_copy_the_tree_did_not_show_to_be_the_same_is_dropped_with_its_importers_as_before(self):
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({}))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(self.shipped(d), ["Toy.clean_one"])
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(rep["dropped"]["Toy.Owned"], "declares a record the tree already has: Toy.owned")
        self.assertEqual(rep["dropped"]["Toy.AboveOwned"], "imports a module that cannot go to the tree")

    def test_a_copy_that_differs_ships_wrapped_with_what_imports_it_and_its_theorems_carry_the_namespace(self):
        draft, _ = self.run_compose("--keep-dups")
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({}, forked=["Toy.Owned", "Toy.AboveOwned"]))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(self.shipped(d)), ["Toy.clean_one", "ToyLibFork.Toy.above_owned", "ToyLibFork.Toy.owned"])
        for mod in ("Owned", "AboveOwned"):
            self.assertEqual(self.text(d, mod), td.apply_fork_text(self.text(draft, mod), "ToyLibFork"))  # the bytes the tree built: the draft's text with the one edit
            self.assertIn("namespace ToyLibFork\n", self.text(d, mod))
        self.assertEqual(self.text(d, "Clean"), self.text(draft, "Clean"))  # not wrapped
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual((rep["dups"]["forked_modules"], rep["dups"]["fork_namespace"]), (2, "ToyLibFork"))
        self.assertEqual(rep["theorems"] + sum(rep["left_out"].values()), rep["passed_total"])  # the accounting identity still holds

    def test_the_theorems_of_a_copy_that_is_the_trees_own_are_counted_as_duplicates(self):
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({}, forked=["Toy.Owned", "Toy.AboveOwned"], identical=["Toy.Owned"]))
        self.assertEqual(p.returncode, 0, p.stderr)
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual((rep["dups"]["forked_modules"], rep["dups"]["duplicate_theorems"]), (2, 1))  # Toy.owned is the duplicate; Toy.above_owned is new

    def test_with_no_identical_fork_there_are_no_duplicates(self):
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({}, forked=["Toy.Owned", "Toy.AboveOwned"]))
        self.assertEqual(json.loads((d / "bundle-proposed" / "report.json").read_text())["dups"]["duplicate_theorems"], 0)

    def test_a_wrapped_copy_the_tree_refused_is_dropped_with_what_imports_it(self):
        failures = Path(tempfile.mkdtemp()) / "failures.txt"
        failures.write_text("Toy.Owned\n")
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({}, forked=["Toy.Owned", "Toy.AboveOwned"]), "--tree-failures", str(failures))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(self.shipped(d), ["Toy.clean_one"])

    def test_a_mode_the_tree_did_not_build_never_wraps(self):
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({}, forked=["Toy.Owned", "Toy.AboveOwned"]))
        self.assertEqual(self.shipped(d, "strict"), ["Toy.clean_one"])  # the strict bundle has no verdict: dropped like before

    def test_a_module_only_the_aliased_copy_imported_ships_and_the_importer_imports_it(self):
        """Copy imports Base (a definition-only module nobody else needs); Imp imports Copy. The tree has Copy; Imp must import the tree's module AND Base, and Base must ship."""
        ad = test_bundle.AutoDrops
        files = {**ad.FILES, "Base": "namespace Toy\n\ndef base_d : Nat := 1\n\nend Toy\n", "Copy": "import Toy.Base\n\nnamespace Toy\n\ntheorem copy_t : 1 = 1 := rfl\n\nend Toy\n",
                 "Imp": "import Toy.Copy\n\nnamespace Toy\n\ntheorem imp_t : 1 = 1 := rfl\n\nend Toy\n"}
        harness = type("Harness", (), {"FILES": files, "PASSED": {**ad.PASSED, "Toy.Copy": ["Toy.copy_t"], "Toy.Imp": ["Toy.imp_t"]}, "leaks_in_leaky": staticmethod(ad.leaks_in_leaky)})()
        p = Path(tempfile.mkdtemp()) / "dups.json"
        p.write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": {"aliases": {"Toy.Copy": ["Tengoku.Other.Lib.Copy"]}, "alias_keep": {"Toy.Copy": ["Tengoku.ToyLib.Toy.Base"]},
                                                                      "not_same": {}, "refused": {}, "forks": {}, "forked": [], "fork_namespace": "", "forks_identical": []}}}))
        d, r = ad.compose(harness, [], "--keep-dups", "--tree-dups", str(p), files=["Base", "Copy", "Imp"])
        self.assertEqual(r.returncode, 0, r.stderr)
        root = d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy"
        self.assertTrue((root / "Base.lean").is_file(), "the module only the copy imported is shipped")
        self.assertFalse((root / "Copy.lean").exists())
        imp = (root / "Imp.lean").read_text()
        self.assertIn("import Tengoku.Other.Lib.Copy", imp)
        self.assertIn("import Tengoku.ToyLib.Toy.Base", imp)
        self.assertNotIn("Toy.Copy", imp)

    def test_without_what_the_copy_imported_the_module_only_it_imported_does_not_ship(self):
        """(the old behaviour, the case that lost 72 modules)"""
        ad = test_bundle.AutoDrops
        files = {**ad.FILES, "Base": "namespace Toy\n\ndef base_d : Nat := 1\n\nend Toy\n", "Copy": "import Toy.Base\n\nnamespace Toy\n\ntheorem copy_t : 1 = 1 := rfl\n\nend Toy\n",
                 "Imp": "import Toy.Copy\n\nnamespace Toy\n\ntheorem imp_t : 1 = 1 := rfl\n\nend Toy\n"}
        harness = type("Harness", (), {"FILES": files, "PASSED": {**ad.PASSED, "Toy.Copy": ["Toy.copy_t"], "Toy.Imp": ["Toy.imp_t"]}, "leaks_in_leaky": staticmethod(ad.leaks_in_leaky)})()
        p = Path(tempfile.mkdtemp()) / "dups.json"
        p.write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": {"aliases": {"Toy.Copy": ["Tengoku.Other.Lib.Copy"]}, "not_same": {}, "refused": {}, "forks": {}, "forked": [],
                                                                      "fork_namespace": "", "forks_identical": []}}}))
        d, r = ad.compose(harness, [], "--keep-dups", "--tree-dups", str(p), files=["Base", "Copy", "Imp"])
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertFalse((d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "Base.lean").exists())

    def test_a_mode_the_tree_did_not_build_never_ships_an_alias(self):
        """Only the verified modes carry a verdict; the strict bundle (not built in the tree) drops the copy like before."""
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({"Toy.Owned": ["Tengoku.Other.Lib.Owned"]}))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(self.shipped(d, "strict"), ["Toy.clean_one"])  # the copy is dropped with its importer, not aliased
        rep = json.loads((d / "bundle" / "report.json").read_text())
        self.assertEqual(rep["dups"]["aliased"], 0)

    def test_a_copy_that_only_the_trees_clash_scan_found_is_aliased_too(self):
        """CodeRabbit on emissary#69: the verify job finds copies from the compiled modules, compose from text rules. A copy of the first kind leaves `new.json` when it is aliased; compose, not
        flagging it, would ship it (a module that clashes, unchecked: `check` only reads `new.json`)."""
        owner = self.harness()
        d, p = test_bundle.AutoDrops.compose(owner, [], "--keep-dups", "--tree-dups", self.dups_file({"Toy.Owned": ["Tengoku.Other.Lib.Owned"]}), files=self.FILES)  # no --tree-names: the text rules flag nothing
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(self.shipped(d)), ["Toy.above_owned", "Toy.clean_one"])
        self.assertFalse((d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "Owned.lean").exists())
        self.assertIn("import Tengoku.Other.Lib.Owned", self.text(d, "AboveOwned"))

    def test_a_module_the_verdict_does_not_name_and_the_text_rules_do_not_flag_is_shipped_as_before(self):
        owner = self.harness()
        d, p = test_bundle.AutoDrops.compose(owner, [], "--keep-dups", "--tree-dups", self.dups_file({}), files=self.FILES)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(self.shipped(d)), ["Toy.above_owned", "Toy.clean_one", "Toy.owned"])

    def test_the_lean_name_rule_keeps_the_copy_too(self):
        (decls := Path(tempfile.mkdtemp()) / "decls.txt").write_text("Toy.owned\n")
        owner = self.harness()
        d, p = test_bundle.AutoDrops.compose(owner, [], "--tree-decls", str(decls), "--keep-dups", files=self.FILES)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(self.shipped(d)), ["Toy.above_owned", "Toy.clean_one", "Toy.owned"])
        d2, p2 = test_bundle.AutoDrops.compose(owner, [], "--tree-decls", str(decls), "--keep-dups", "--tree-dups", self.dups_file({"Toy.Owned": ["Tengoku.Other.Lib.Owned"]}), files=self.FILES)
        self.assertEqual(p2.returncode, 0, p2.stderr)
        self.assertEqual(sorted(self.shipped(d2)), ["Toy.above_owned", "Toy.clean_one"])


if __name__ == "__main__":
    unittest.main()
