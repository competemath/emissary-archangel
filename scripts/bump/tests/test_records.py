"""records.py compose on a two-module toy library (no Lean): the log lines Lean would print are written by hand."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]

A = """/-
Copyright (c) test
-/
import Mathlib.Data.Nat.Basic

namespace Toy

/-- the number one -/
def one : Nat := 1

/-- never used -/
theorem unused : one = 1 := rfl

notation "ℓ" => one

theorem one_pos : 0 < one := by decide

end Toy
"""
B = """import Toy.A

namespace Toy

variable (n : Nat)

theorem unrelated : n = n := rfl

open Nat in
theorem uses_one_pos : 0 < one := one_pos

end Toy
"""


class Compose(unittest.TestCase):
    def test_compose_and_stage(self):
        with tempfile.TemporaryDirectory() as d:
            lib = Path(d) / "lib"
            (lib / "Toy").mkdir(parents=True)
            (lib / "Toy" / "A.lean").write_text(A)
            (lib / "Toy" / "B.lean").write_text(B)
            # lines (1-based) of the blocks: A: one 8-9? compute from the text
            la, lb = A.split("\n"), B.split("\n")
            ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
            one = (ln(la, "/-- the number one"), ln(la, "def one"))
            unused = (ln(la, "/-- never used"), ln(la, "theorem unused"))
            one_pos = (ln(la, "theorem one_pos"),) * 2
            unrelated = (ln(lb, "theorem unrelated"),) * 2
            uses = (ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos"))
            sidecars = {
                "Toy/A": [["Toy.one", *one], ["Toy.unused", *unused], ["Toy.one_pos", *one_pos], ["Toy.one.match_1", *one]],
                "Toy/B": [["Toy.unrelated", *unrelated], ["Toy.uses_one_pos", *uses]],
            }
            for m, rows in sidecars.items():
                f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(json.dumps(rows))
            deps = {
                "name": "Toy.uses_one_pos",
                "module": "Toy.B",
                "consts": [["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one.match_1"], ["Toy.A", "Toy.one"]],
            }
            log = f"x.lean:1:0: info: REC_DEPS {json.dumps(deps)} REC_END\n"
            (Path(d) / "deps.log").write_text(log)
            (Path(d) / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy.git", "commit": "abc123"}))
            subprocess.run([sys.executable, str(HERE / "records.py"), "compose", "--lib", str(lib), "--log", str(Path(d) / "deps.log"), "--meta", str(Path(d) / "setup.json"), "--out", str(Path(d) / "composed.jsonl")], check=True)
            rec = json.loads((Path(d) / "composed.jsonl").read_text().splitlines()[0])
            text = rec["proof"]
            self.assertIn("-- [Emissary prelude] Toy.A — verbatim (imports stripped)", text)
            self.assertIn("def one : Nat := 1", text)
            self.assertIn("theorem one_pos", text)
            self.assertNotIn("theorem unused", text)  # pruned: nothing uses it
            self.assertIn('notation "ℓ" => one', text)  # glue stays
            self.assertNotIn("theorem unrelated", text)  # pruned from the own file
            self.assertIn("variable (n : Nat)", text)  # glue of the own file stays
            self.assertNotIn("import Mathlib", text)
            self.assertIn("-- [Emissary] Toy/B.lean, everything before line", text)
            self.assertTrue(text.rstrip().endswith("theorem uses_one_pos : 0 < one := one_pos"))
            self.assertEqual(rec["sourceUrl"], "https://github.com/o/toy/blob/abc123/Toy/B.lean")
            # and the staging record the pipeline's own splitter makes of it
            r = subprocess.run(["node", str(HERE / "stage-records.mjs"), str(Path(d) / "composed.jsonl"), "--source", "toy", "--toolchain", "tc", "--out", str(Path(d) / "bank.jsonl")], capture_output=True, text=True)
            if r.returncode == 0:
                staged = json.loads((Path(d) / "bank.jsonl").read_text().splitlines()[0])
                self.assertEqual(staged["statement"].split(":")[0].split()[-1], "uses_one_pos")
                self.assertTrue(staged["proof"].startswith(":="))
                self.assertIn("-- [Emissary prelude] Toy.A", staged["context"])


PREFIXED = """import Toy.A

namespace Toy

open Nat in
/-- a theorem under an `open … in` prefix -/
theorem prefixed : 1 = 1 := rfl

set_option maxHeartbeats 400000 in
open Nat in
theorem two_prefixes : 2 = 2 := rfl

theorem plain : 3 = 3 := rfl

end Toy
"""


class PrefixedDeclarations(unittest.TestCase):
    """A declaration under `open Foo in` is a block like any other, and its prefix lines go with it. Regression (complexitylib part 1, 2026-10-07): such a
    theorem was never a block, so it stayed in the module after the theorem it calls was cut, and the module no longer built; and when an errored
    declaration was cut, its `open scoped Classical in` was left dangling."""

    def module(self):
        sys.path.insert(0, str(HERE))
        import records

        d = tempfile.mkdtemp()
        lib = Path(d) / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "B.lean").write_text(PREFIXED)
        lines = PREFIXED.split("\n")
        ln = lambda needle: next(i + 1 for i, x in enumerate(lines) if x.startswith(needle))
        # the ranges Lean reports: from the docstring (or the keyword) to the end of the declaration; never the `open … in` above
        ranges = [(ln("/-- a theorem"), ln("theorem prefixed")), (ln("theorem two_prefixes"),) * 2, (ln("theorem plain"),) * 2]
        return records.Module(lib, "Toy.B", ranges), ln

    def test_the_prefix_lines_belong_to_the_block(self):
        m, ln = self.module()
        self.assertEqual(m.blocks, [(ln("open Nat in"), ln("theorem prefixed")), (ln("set_option"), ln("theorem two_prefixes")), (ln("theorem plain"),) * 2])

    def test_an_unkept_prefixed_declaration_goes_with_its_prefix(self):
        m, _ = self.module()
        plain = m.blocks[2]
        text = m.text({plain})
        for gone in ("open Nat in", "prefixed", "set_option", "two_prefixes"):
            self.assertNotIn(gone, text)
        self.assertIn("theorem plain", text)
        self.assertIn("namespace Toy", text)

    def test_a_kept_prefixed_declaration_keeps_its_prefix(self):
        m, _ = self.module()
        text = m.text(set(m.blocks))
        self.assertIn("open Nat in\n/-- a theorem", text)
        self.assertIn("set_option maxHeartbeats 400000 in\nopen Nat in\ntheorem two_prefixes", text)

    def test_a_kept_range_names_the_block_whatever_line_it_starts_at(self):
        """compose keeps by the range Lean reported (docstring or keyword line); the block starts at the prefix line. They must meet."""
        m, ln = self.module()
        by_range = m.text({(ln("/-- a theorem"), ln("theorem prefixed")), (ln("theorem two_prefixes"),) * 2})
        self.assertIn("open Nat in\n/-- a theorem", by_range)
        self.assertIn("theorem two_prefixes", by_range)
        self.assertNotIn("theorem plain", by_range)
        self.assertEqual(m.kept_blocks({(ln("theorem prefixed"),) * 2}), {m.blocks[0]})

    def test_with_prefix_from_a_bare_declaration_line(self):
        """compose adds the blocks of errored declarations from portfolio.blocks, which start at the keyword: the prefix must be reattached there too."""
        m, ln = self.module()
        self.assertEqual(m.with_prefix(ln("theorem two_prefixes")), ln("set_option"))
        self.assertEqual(m.with_prefix(ln("theorem plain")), ln("theorem plain"))

    def test_a_range_that_includes_the_prefix_is_the_same_block(self):
        """Lean's range starts at the docstring or keyword; a range written by hand may start at the `open … in` line. Both name one block."""
        sys.path.insert(0, str(HERE))
        import records

        lines = PREFIXED.split("\n")
        ln = lambda needle: next(i + 1 for i, x in enumerate(lines) if x.startswith(needle))
        d = tempfile.mkdtemp()
        lib = Path(d) / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "B.lean").write_text(PREFIXED)
        m = records.Module(lib, "Toy.B", [(ln("open Nat in"), ln("theorem prefixed")), (ln("set_option"), ln("theorem two_prefixes"))])
        self.assertEqual(m.blocks[:2], [(ln("open Nat in"), ln("theorem prefixed")), (ln("set_option"), ln("theorem two_prefixes"))])
        self.assertEqual(set(m.blocks[:2]), m.ranged)
        self.assertNotIn(m.blocks[2], m.ranged)  # `plain` has no range here: a declaration Lean never elaborated, cut whatever `keep` says
        self.assertNotIn("theorem plain", m.text(set(m.blocks)))

    def test_an_attribute_on_a_command_that_is_no_declaration_is_glue(self):
        """`@[expose] public section` (complexitylib's NatBits) is not a lead-in of the declaration below it, and `@[simp] theorem` on one line is a declaration."""
        sys.path.insert(0, str(HERE))
        import records

        src = "@[expose] public section\n\n/-- doc -/\ndef toBits : Nat → Nat\n| 0 => 0\n| n + 1 => n\n\n@[simp] theorem a : 1 = 1 := rfl\n@[simp] theorem b : 2 = 2 := rfl\n\n@[ext] theorem e : 3 = 3 := rfl\n\nend\n"
        lines = src.split("\n")
        ln = lambda needle: next(i + 1 for i, x in enumerate(lines) if x.startswith(needle))
        d = tempfile.mkdtemp()
        lib = Path(d) / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "E.lean").write_text(src)
        ranges = [(ln("/-- doc"), ln("| n + 1")), (ln("@[simp] theorem a"),) * 2, (ln("@[simp] theorem b"),) * 2, (ln("@[ext] theorem e"),) * 2]
        m = records.Module(lib, "Toy.E", ranges)
        self.assertEqual(m.blocks, [(ln("/-- doc"), ln("| n + 1")), (ln("@[simp] theorem a"),) * 2, (ln("@[simp] theorem b"),) * 2, (ln("@[ext] theorem e"),) * 2])
        pruned = m.text({m.blocks[1]})
        self.assertIn("@[expose] public section", pruned)
        self.assertIn("@[simp] theorem a", pruned)
        self.assertIn("@[ext] theorem e", pruned)  # built, and `ext` registers it for the proofs that stay: glue
        for gone in ("toBits", "| 0 => 0", "/-- doc", "theorem b"):
            self.assertNotIn(gone, pruned)
        self.assertEqual(m.leaks(pruned, {m.blocks[1]}), [])
        self.assertTrue(m.leaks(pruned.replace("theorem a", "theorem a_leaked"), {m.blocks[1]}))


class NothingEscapesPruning(unittest.TestCase):
    """`Module.leaks` is the guard compose runs on every pruned module: the text must be glue plus whole kept blocks, and no `… in` may dangle.
    It would have refused the complexitylib bundle whatever the cause, and refuses any future way for an unverified declaration to stay."""

    def module(self):
        sys.path.insert(0, str(HERE))
        import records

        lines = PREFIXED.split("\n")
        ln = lambda needle: next(i + 1 for i, x in enumerate(lines) if x.startswith(needle))
        d = tempfile.mkdtemp()
        lib = Path(d) / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "B.lean").write_text(PREFIXED)
        return records.Module(lib, "Toy.B", [(ln("/-- a theorem"), ln("theorem prefixed")), (ln("theorem two_prefixes"),) * 2, (ln("theorem plain"),) * 2])

    def test_a_correct_pruning_leaks_nothing(self):
        m = self.module()
        for keep in (set(), {m.blocks[2]}, set(m.blocks)):
            self.assertEqual(m.leaks(m.text(keep), keep), [], keep)

    def test_the_complexitylib_shapes_are_caught(self):
        m = self.module()
        # 1. the declaration stayed although it was not kept (the old bug: `open … in` + docstring + theorem treated as glue)
        kept_only_plain = m.text({m.blocks[2]})
        keep = {m.blocks[2]}
        leaked = kept_only_plain.replace("theorem plain", "open Nat in\n/-- doc -/\ntheorem prefixed : 1 = 1 := rfl\n\ntheorem plain", 1)
        self.assertTrue(any("not a kept block" in x for x in m.leaks(leaked, keep)), m.leaks(leaked, keep))
        # 2. the declaration went but its prefix stayed: `open scoped Classical in` with only `end …` after it (the shape in the bundle), or at the end of the file
        dangling = kept_only_plain.replace("end Toy", "open scoped Classical in\n\nend Toy", 1)
        self.assertTrue(any("dangling prefix" in x for x in m.leaks(dangling, keep)), m.leaks(dangling, keep))
        dangling_at_end = kept_only_plain + "\nopen Nat in\n"
        self.assertTrue(any("dangling prefix" in x for x in m.leaks(dangling_at_end, keep)))
        # a prefix that a declaration follows, even after a blank line, is not dangling
        fine = kept_only_plain.replace("theorem plain", "open scoped Classical in\n\ntheorem plain", 1)
        self.assertEqual([x for x in m.leaks(fine, keep) if "dangling" in x], [])

    def test_prose_and_comments_are_not_declarations(self):
        """A module docstring line that starts with "lemma." or "theorem;" (complexitylib has fifty), a `--` line at column 0 inside a proof, and a
        docstring are not commands: the guard reads only column-0 lines outside comments."""
        sys.path.insert(0, str(HERE))
        import records

        src = "namespace Toy\n\ntheorem long : 3 = 3 :=\n  -- indented\n  rfl\n\nend Toy\n"
        d = tempfile.mkdtemp()
        lib = Path(d) / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "D.lean").write_text(src)
        m = records.Module(lib, "Toy.D", [(3, 5)])
        text = (
            "/-! # Notes\n\nlemma. If every wire has depth at most one,\ntheorem; no alternative is introduced.\nclass, not for full cover complexity.\n-/\n\n"
            + m.text(set(m.blocks)).replace("  -- indented", "-- a comment at column 0 inside the proof")
            + "\n/- a block comment\ntheorem inside_comment : False := sorry\n-/\n"
        )
        self.assertEqual(m.leaks(text, set(m.blocks)), [])
        self.assertTrue(m.leaks(text.replace("theorem long", "theorem other"), set(m.blocks)))  # the same scan does see a real declaration

    def test_a_prefix_binds_across_blank_and_comment_lines(self):
        """`set_option maxHeartbeats 800000 in` with a blank line, then the docstring and the theorem (causalean): one block, cut together."""
        sys.path.insert(0, str(HERE))
        import records

        src = "namespace Toy\n\nset_option maxHeartbeats 800000 in\n\n-- why the budget\ninclude h in\n/-- doc -/\ntheorem heavy : 1 = 1 := rfl\n\ntheorem light : 2 = 2 := rfl\n\nend Toy\n"
        lines = src.split("\n")
        ln = lambda needle: next(i + 1 for i, x in enumerate(lines) if x.startswith(needle))
        d = tempfile.mkdtemp()
        lib = Path(d) / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "C.lean").write_text(src)
        m = records.Module(lib, "Toy.C", [(ln("/-- doc"), ln("theorem heavy")), (ln("theorem light"),) * 2])
        self.assertEqual(m.blocks[0], (ln("set_option"), ln("theorem heavy")))
        pruned = m.text({m.blocks[1]})
        for gone in ("set_option", "include h in", "heavy", "why the budget"):
            self.assertNotIn(gone, pruned)
        self.assertEqual(m.leaks(pruned, {m.blocks[1]}), [])
        dangling = pruned.replace("theorem light", "set_option maxHeartbeats 800000 in\n\nend Toy\n\ntheorem light", 1)
        self.assertTrue(any("dangling" in x for x in m.leaks(dangling, {m.blocks[1]})))

    def test_glue_commands_are_not_leaks(self):
        m = self.module()
        text = m.text(set(m.blocks)) + "\n\nopen Nat\n\nvariable (k : Nat)\n\nnotation \"one\" => 1\n"
        self.assertEqual(m.leaks(text, set(m.blocks)), [])


if __name__ == "__main__":
    unittest.main()
