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
    lines = [f"FP\t{m}\t{n}\t{kind}\t{h(v)}" for m, decls in rows.items() for n, (kind, v) in decls.items()]
    return "\n".join(lines) + f"\nfingerprints: {len(lines)} declarations\n"


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


class Parsing(unittest.TestCase):
    def test_a_fingerprint_run_without_its_ending_is_refused(self):
        with self.assertRaises(SystemExit) as e:
            td.parse_fp(f"FP\tA\tf\tdef\t{h(1)}\n")
        self.assertIn("no ending", str(e.exception))

    def test_a_fingerprint_run_whose_count_does_not_match_is_refused(self):
        with self.assertRaises(SystemExit) as e:
            td.parse_fp(f"FP\tA\tf\tdef\t{h(1)}\nfingerprints: 2 declarations\n")
        self.assertIn("incomplete", str(e.exception))

    def test_modules_are_read_without_guillemets(self):
        got = td.parse_fp(f"FP\tTengoku.L.«A-B»\tf\tdef\t{h(1)}\nfingerprints: 1 declarations\n")
        self.assertEqual(list(got), ["Tengoku.L.A-B"])

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

    def test_no_declaration_is_no_verdict_not_a_vacuous_yes(self):
        self.assertIsNone(td.decide("Tengoku.L.M", ["Tengoku.O.X"], {}, self.PARTNER)[0])

    def test_the_declarations_may_come_from_several_tree_modules(self):
        partner = td.parse_fp(fp({"Tengoku.O.X": {"f": ("def", 1)}, "Tengoku.O.Y": {"g": ("theorem", 2)}}))
        before = td.parse_fp(fp({"Tengoku.L.M": {"f": ("def", 1), "g": ("theorem", 2)}}))
        self.assertEqual(td.decide("Tengoku.L.M", ["Tengoku.O.X", "Tengoku.O.Y"], before, partner)[0], ["Tengoku.O.X", "Tengoku.O.Y"])


class Flow(unittest.TestCase):
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
        td.main(["candidates", "--clashes", str(self.d / "clashes.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--out", str(self.out), "--mode", "proposed"])

    def plan(self, before_hash: int = 1):
        before = fp({"Tengoku.ToyLib.Toy.M": {"Toy.f": ("def", before_hash)}, "Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}, "Tengoku.ToyLib.Toy.C": {"Toy.u": ("theorem", 11)}})
        (self.d / "fp-before.txt").write_text(before)
        (self.d / "fp-partners.txt").write_text(fp({"Tengoku.Other.Lib.X": {"Toy.f": ("def", 1)}}))
        td.main(["plan", "--candidates", str(self.out / "dups-candidates.json"), "--fp-before", str(self.d / "fp-before.txt"), "--fp-partners", str(self.d / "fp-partners.txt"),
                 "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])

    def after(self, log2: str, after_rows: dict):
        (self.d / "log2.txt").write_text(log2)
        (self.d / "fp-after.txt").write_text(fp(after_rows))
        common = ["--candidates", str(self.out / "dups-candidates.json"), "--dups", str(self.out / "dups.json"), "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--log2", str(self.d / "log2.txt"), "--out", str(self.out)]
        td.main(["after-list", *common])
        td.main(["after-verdict", *common, "--fp-before", str(self.d / "fp-before.txt"), "--fp-after", str(self.d / "fp-after.txt")])

    SAME_AFTER = {"Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}, "Tengoku.ToyLib.Toy.C": {"Toy.u": ("theorem", 11)}}
    BUILT2 = "✔ [1/2] Built Tengoku.ToyLib.Toy.B (1s)\n✔ [2/2] Built Tengoku.ToyLib.Toy.C (1s)\nBuild completed successfully.\n"

    def test_the_copy_and_the_modules_that_import_it_are_found(self):
        cand = json.loads((self.out / "dups-candidates.json").read_text())["candidates"]
        self.assertEqual(list(cand), ["Tengoku.ToyLib.Toy.M"])
        self.assertEqual(cand["Tengoku.ToyLib.Toy.M"]["partners"], ["Tengoku.Other.Lib.X"])
        self.assertEqual(cand["Tengoku.ToyLib.Toy.M"]["importers"], ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])  # C imports B, which imports M
        self.assertEqual((self.out / "dups-before.txt").read_text().split(), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C", "Tengoku.ToyLib.Toy.M"])
        self.assertEqual((self.out / "dups-partners.txt").read_text().split(), ["Tengoku.Other.Lib.X"])

    def test_a_copy_that_did_not_build_is_no_candidate(self):
        (self.out / "built.txt").write_text("Tengoku.ToyLib.Toy.B\n")
        td.main(["candidates", "--clashes", str(self.d / "clashes.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--out", str(self.out), "--mode", "proposed"])
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
        (self.d / "fp-before.txt").write_text("FP\tTengoku.ToyLib.Toy.M\tToy.f\tdef\t" + h(1) + "\n")  # cut short: no ending
        (self.d / "fp-partners.txt").write_text(fp({"Tengoku.Other.Lib.X": {"Toy.f": ("def", 1)}}))
        before = {p: (self.tree / p).read_text() for p in self.FILES if (self.tree / p).exists()}
        td.main(["plan", "--candidates", str(self.out / "dups-candidates.json"), "--fp-before", str(self.d / "fp-before.txt"), "--fp-partners", str(self.d / "fp-partners.txt"),
                 "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--out", str(self.out), "--mode", "proposed"])
        self.assertEqual({p: (self.tree / p).read_text() for p in before}, before)
        self.assertEqual(json.loads((self.out / "dups.json").read_text())["aliases"], {})

    def test_after_the_swap_importers_that_cannot_be_compared_are_refused(self):
        self.plan()
        (self.d / "log2.txt").write_text(self.BUILT2)
        (self.d / "fp-after.txt").write_text("FP\tTengoku.ToyLib.Toy.B\tToy.t\ttheorem\t" + h(10) + "\n")  # cut short
        common = ["--candidates", str(self.out / "dups-candidates.json"), "--dups", str(self.out / "dups.json"), "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--log2", str(self.d / "log2.txt"), "--out", str(self.out)]
        td.main(["after-verdict", *common, "--fp-before", str(self.d / "fp-before.txt"), "--fp-after", str(self.d / "fp-after.txt")])
        refused = dict(ln.split("\t") for ln in (self.out / "dups-failures.txt").read_text().splitlines())
        self.assertEqual(sorted(refused), ["Tengoku.ToyLib.Toy.B", "Tengoku.ToyLib.Toy.C"])
        self.assertIn("could not be compared", refused["Tengoku.ToyLib.Toy.B"])

    def test_nothing_to_decide_when_there_is_no_copy(self):
        (self.d / "none.txt").write_text("clashes: 0 module pair(s), 0 name(s)\n")
        td.main(["candidates", "--clashes", str(self.d / "none.txt"), "--new", str(self.out / "new.json"), "--built", str(self.out / "built.txt"), "--bundle", str(self.bundle), "--out", str(self.out), "--mode", "proposed"])
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

    def dups_file(self, aliases: dict[str, list[str]], mode: str = "proposed") -> str:
        p = Path(tempfile.mkdtemp()) / "dups.json"
        p.write_text(json.dumps({"ns": "ToyLib", "modes": {mode: {"aliases": aliases, "not_same": {}, "refused": {}}}}))
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

    def test_a_mode_the_tree_did_not_build_never_ships_an_alias(self):
        """Only the verified modes carry a verdict; the strict bundle (not built in the tree) drops the copy like before."""
        d, p = self.run_compose("--keep-dups", "--tree-dups", self.dups_file({"Toy.Owned": ["Tengoku.Other.Lib.Owned"]}))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(self.shipped(d, "strict"), ["Toy.clean_one"])  # the copy is dropped with its importer, not aliased
        rep = json.loads((d / "bundle" / "report.json").read_text())
        self.assertEqual(rep["dups"]["aliased"], 0)

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
