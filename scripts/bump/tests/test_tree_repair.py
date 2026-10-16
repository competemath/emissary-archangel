"""tree_repair.py, rule R2: a declaration that ran out of heartbeats in the tree is given room, and the module says so in one docstring line per repair.

Why it exists (navier-stokes-euler, 2026-10-16): `NavierStokes.PositiveAxisSystem` failed the tree's build on two `whnf` timeouts at 200000 heartbeats and an "unknown constant" that followed from
them; on Leak IV the same module compiles with `set_option maxHeartbeats 1600000 in` above the two declarations. No Lean, no network here: reading the log, finding the declaration, the edit,
the plan on a checkout, `collect` reading a two-part log, `compose --tree-repairs` on the toy library giving the bytes the tree accepted, and the workflow wiring."""

import contextlib
import io
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
import tree_repair as tr  # noqa: E402
import tree_verify as tv  # noqa: E402

# the real log of the tree's build of NavierStokes.PositiveAxisSystem (run 38867234062, 2026-10-16), cut to its four messages
REAL_LOG = """✔ [9632/9642] Built Tengoku.NavierStokesEuler.NavierStokes.ParticularWaveBounds (57s)
✖ [9633/9642] Building Tengoku.NavierStokesEuler.NavierStokes.PositiveAxisSystem (86s)
trace: .> LEAN_PATH=/home/runner/work/tree/.lake/build/lib/lean /home/runner/.elan/bin/lean /home/runner/work/tree/Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean -o x
error: Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean:675:1: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
error: Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean:746:1: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
error: Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean:811:8: (kernel) unknown constant 'NavierStokes.PositiveAxisSystem.coefficient0_contDiffAt_of_pullback'
error: Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean:829:8: (kernel) unknown constant 'NavierStokes.PositiveAxisSystem.coefficient0_contDiffAt_of_pullback'
✔ [9637/9642] Built Tengoku.NavierStokesEuler.NavierStokes.SubcoverPeriodicity (8.2s)
Some required targets logged failures:
- Tengoku.NavierStokesEuler.NavierStokes.PositiveAxisSystem
error: build failed
"""

TYPECLASS_LOG = """✖ [5/9] Building Tengoku.ToyLib.Toy.B (12s)
error: Tengoku/ToyLib/Toy/B.lean:12:2: failed to synthesize
  ZeroHomClass F A B
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Some required targets logged failures:
- Tengoku.ToyLib.Toy.B
error: build failed
"""

MODULE = """import Tengoku

/-!
# A module
-/

namespace Toy

theorem first : 1 = 1 := by
  simp

/-- the second one -/
@[simp]
theorem second : 2 = 2 := by
  simp
  simp

 theorem third : 3 = 3 := by
  simp

end Toy
"""


def line_of(text: str, needle: str) -> int:
    return next(i + 1 for i, ln in enumerate(text.split("\n")) if needle in ln)


def err(line: int, option: str = "maxHeartbeats", limit: int = 200000) -> dict:
    return {"path": "Tengoku/ToyLib/Toy/B.lean", "line": line, "option": option, "limit": limit}


class Parse(unittest.TestCase):
    def test_the_real_log_has_two_timeouts_and_the_unknown_constants_are_not_timeouts(self):
        ts = tr.timeouts(REAL_LOG)
        self.assertEqual([(t["line"], t["option"], t["limit"]) for t in ts], [(675, "maxHeartbeats", 200000), (746, "maxHeartbeats", 200000)])
        self.assertEqual({t["path"] for t in ts}, {"Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean"})

    def test_a_typeclass_timeout_is_on_a_continuation_line_and_names_the_search_option(self):
        ts = tr.timeouts(TYPECLASS_LOG)
        self.assertEqual([(t["line"], t["option"], t["limit"]) for t in ts], [(12, "synthInstance.maxHeartbeats", 20000)])

    def test_the_option_comes_from_leans_own_note_before_the_kind_of_search(self):
        log = "error: Tengoku/L/A.lean:3:0: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached\nNote: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.\n"
        self.assertEqual(tr.timeouts(log)[0]["option"], "synthInstance.maxHeartbeats")

    def test_without_a_note_the_kind_of_search_decides(self):
        base = "error: Tengoku/L/A.lean:3:0: (deterministic) timeout at `{}`, maximum number of heartbeats ({}) has been reached\n"
        self.assertEqual(tr.timeouts(base.format("typeclass", 20000))[0]["option"], "synthInstance.maxHeartbeats")
        self.assertEqual(tr.timeouts(base.format("whnf", 200000))[0]["option"], "maxHeartbeats")

    def test_an_option_that_is_not_on_the_list_is_not_repaired(self):
        log = "error: Tengoku/L/A.lean:3:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\nNote: Use `set_option maxRecDepth <num>` to set the limit.\n"
        self.assertEqual(tr.timeouts(log), [])

    def test_a_warning_with_the_same_words_is_not_an_error(self):
        log = "warning: Tengoku/L/A.lean:3:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n"
        self.assertEqual(tr.timeouts(log), [])

    def test_other_errors_and_other_messages_are_ignored(self):
        log = "error: Tengoku/L/A.lean:3:0: type mismatch\nerror: Tengoku/L/A.lean:9:0: unknown constant 'x'\n✔ [1/2] Built Tengoku.L.A (1s)\n"
        self.assertEqual(tr.timeouts(log), [])

    def test_a_message_ends_at_the_next_line_that_is_not_part_of_it(self):
        # the timeout words belong to the message that precedes the Lake line, not to a later one
        log = "error: Tengoku/L/A.lean:3:0: type mismatch\n✖ [2/3] Building Tengoku.L.B (1s)\n(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n"
        self.assertEqual(tr.timeouts(log), [])

    def test_a_lake_prefix_before_error_is_read(self):
        log = "✖ error: Tengoku/L/A.lean:3:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached\n"
        self.assertEqual(tr.timeouts(log)[0]["limit"], 400000)

    def test_a_file_outside_the_tengoku_tree_is_not_read(self):
        log = "error: Mathlib/X.lean:3:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n"
        self.assertEqual(tr.timeouts(log), [])


class NewLimit(unittest.TestCase):
    def test_eight_times_the_limit_that_was_reached(self):
        self.assertEqual(tr.new_limit("maxHeartbeats", 200000), 1_600_000)
        self.assertEqual(tr.new_limit("synthInstance.maxHeartbeats", 20000), 160_000)

    def test_never_more_than_the_cap(self):
        self.assertEqual(tr.new_limit("maxHeartbeats", 400000), 1_600_000)
        self.assertEqual(tr.new_limit("synthInstance.maxHeartbeats", 100000), 400_000)

    def test_a_declaration_that_has_all_the_room_a_repair_gives_gets_none(self):
        self.assertIsNone(tr.new_limit("maxHeartbeats", 1_600_000))
        self.assertIsNone(tr.new_limit("maxHeartbeats", 2_000_000))
        self.assertIsNone(tr.new_limit("synthInstance.maxHeartbeats", 400_000))

    def test_the_caps_are_eight_times_leans_defaults(self):
        self.assertEqual(tr.CAPS, {"maxHeartbeats": 8 * 200000, "synthInstance.maxHeartbeats": 8 * 50000})

    def test_both_options_are_on_the_gates_allowlist(self):
        allowed = {"maxHeartbeats", "synthInstance.maxHeartbeats"}
        self.assertTrue(set(tr.CAPS) <= allowed)


class Anchor(unittest.TestCase):
    def a(self, text: str, needle: str):
        return tr.anchor(text.split("\n"), line_of(text, needle))

    def test_an_error_inside_the_proof_finds_its_declaration(self):
        ln = line_of(MODULE, "theorem first")
        self.assertEqual(tr.anchor(MODULE.split("\n"), ln + 1), (ln, "first"))

    def test_an_error_on_the_declaration_line_itself(self):
        self.assertEqual(self.a(MODULE, "theorem first"), (line_of(MODULE, "theorem first"), "first"))

    def test_the_docstring_and_the_attribute_stay_under_the_set_option(self):
        text = MODULE
        lines = text.split("\n")
        err_line = line_of(text, "theorem second") + 1  # the first `simp` of the proof
        at, name = tr.anchor(lines, err_line)
        self.assertEqual(name, "second")
        self.assertEqual(lines[at - 1], "/-- the second one -/")

    def test_a_declaration_with_one_leading_space_where_private_was_cut(self):
        self.assertEqual(self.a(MODULE, " theorem third"), (line_of(MODULE, " theorem third"), "third"))

    def test_a_set_option_that_is_already_there_stays_above_the_new_one(self):
        text = "import Tengoku\n\nset_option maxHeartbeats 400000 in\ntheorem t : 1 = 1 := by\n  simp\n"
        lines = text.split("\n")
        self.assertEqual(tr.anchor(lines, 5)[0], 4)  # below the existing line: the new one is the inner one and wins

    def test_a_docstring_with_several_lines(self):
        text = "import Tengoku\n\n/-- one\ntwo\nthree -/\ntheorem t : 1 = 1 := by\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 7), (3, "t"))

    def test_a_plain_block_comment_above_the_declaration_is_not_a_docstring(self):
        text = "import Tengoku\n\n/-- doc -/\ndef x : Nat := 1\n\n/- a note -/\ntheorem t : 1 = 1 := by\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 8), (7, "t"))

    def test_a_plain_comment_below_a_docstring_does_not_pull_the_docstring_in(self):
        text = "import Tengoku\n\n/-- doc -/\n/- note -/\ntheorem t : 1 = 1 := by\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 6)[0], 5)

    def test_attributes_on_their_own_line_and_two_of_them(self):
        text = "import Tengoku\n\n@[simp]\n@[norm_cast]\ntheorem t : 1 = 1 := by\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 6)[0], 3)

    def test_an_attribute_on_the_declaration_line(self):
        text = "import Tengoku\n\n@[simp] theorem t : 1 = 1 := by\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 4), (3, "t"))

    def test_an_open_in_above_stays_above_the_set_option(self):
        text = "import Tengoku\n\nopen Nat in\ntheorem t : 1 = 1 := by\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 5)[0], 4)

    def test_modifiers_before_the_keyword(self):
        for kw in ("private theorem", "protected def", "noncomputable def", "private noncomputable def", "instance", "lemma", "abbrev", "structure", "class", "inductive"):
            text = f"import Tengoku\n\n{kw} T where\n  x : Nat\n"
            self.assertIsNotNone(tr.anchor(text.split("\n"), 4), kw)

    def test_an_unnamed_instance_is_named_by_its_line(self):
        text = "import Tengoku\n\ninstance : Inhabited Nat := ⟨0⟩\n"
        self.assertEqual(tr.anchor(text.split("\n"), 3), (3, "instance at line 3"))

    def test_a_command_between_the_error_and_the_declaration_means_no_declaration(self):
        for cmd in ("end Toy", "namespace X", "variable (n : Nat)", "open Nat", "section", "universe u", "attribute [simp] foo", "#check 1", "mutual", "noncomputable section"):
            text = f"import Tengoku\n\ntheorem t : 1 = 1 := rfl\n\n{cmd}\n\nexample : 1 = 1 := by\n  simp\n"
            # the error is on the line after the command, above any later declaration
            self.assertIsNone(tr.anchor(text.split("\n"), 6), cmd)

    def test_nothing_above_the_error_is_a_declaration(self):
        self.assertIsNone(tr.anchor("import Tengoku\n\n/-! doc -/\n".split("\n"), 3))

    def test_an_indented_theorem_is_not_a_declaration_start(self):
        text = "import Tengoku\n\ntheorem t : 1 = 1 := by\n  have h : 2 = 2 := by\n    simp\n  theorem inner : 3 = 3 := rfl\n  simp\n"
        self.assertEqual(tr.anchor(text.split("\n"), 7), (3, "t"))

    def test_a_line_past_the_end_is_the_last_line(self):
        text = "import Tengoku\n\ntheorem t : 1 = 1 := rfl\n"
        self.assertEqual(tr.anchor(text.split("\n"), 99), (3, "t"))

    def test_line_zero_is_nothing(self):
        self.assertIsNone(tr.anchor(["theorem t : 1 = 1 := rfl"], 0))


class PlanText(unittest.TestCase):
    def test_two_timeouts_in_one_declaration_ask_for_the_larger_limit_once(self):
        ln = line_of(MODULE, "theorem first")
        syn = "synthInstance.maxHeartbeats"
        for limits in ((20000, 50000), (50000, 20000)):  # 160000 and 400000, in either order
            reps, skipped = tr.plan_text(MODULE, [err(ln + 1, syn, limits[0]), err(ln + 1, syn, limits[1])])
            self.assertEqual([(r["from"], r["to"]) for r in reps], [(50000, 400_000)], limits)
            self.assertEqual(skipped, [])

    def test_both_options_in_one_declaration_make_two_repairs(self):
        ln = line_of(MODULE, "theorem first")
        reps, _ = tr.plan_text(MODULE, [err(ln + 1), err(ln + 1, "synthInstance.maxHeartbeats", 20000)])
        self.assertEqual([r["option"] for r in reps], ["maxHeartbeats", "synthInstance.maxHeartbeats"])

    def test_a_limit_that_cannot_grow_is_skipped_with_its_reason(self):
        reps, skipped = tr.plan_text(MODULE, [err(line_of(MODULE, "theorem first"), limit=1_600_000)])
        self.assertEqual(reps, [])
        self.assertIn("already 1600000", skipped[0])

    def test_an_error_outside_a_declaration_is_skipped_with_its_reason(self):
        text = "import Tengoku\n\ntheorem t : 1 = 1 := rfl\n\nend Toy\n"
        reps, skipped = tr.plan_text(text, [err(5)])
        self.assertEqual(reps, [])
        self.assertIn("not inside a declaration", skipped[0])

    def test_a_module_without_an_import_line_is_not_repaired(self):
        reps, skipped = tr.plan_text("theorem t : 1 = 1 := rfl\n", [err(1)])
        self.assertEqual(reps, [])
        self.assertIn("no import line", skipped[0])

    def test_the_repairs_are_in_file_order(self):
        reps, _ = tr.plan_text(MODULE, [err(line_of(MODULE, " theorem third")), err(line_of(MODULE, "theorem first"))])
        self.assertEqual([r["name"] for r in reps], ["first", "third"])

    def test_the_repair_says_where_what_and_how_much(self):
        ln = line_of(MODULE, "theorem first")
        (r,), _ = tr.plan_text(MODULE, [err(ln + 1)])
        self.assertEqual(r, {"line": ln + 1, "at": ln, "name": "first", "option": "maxHeartbeats", "from": 200000, "to": 1_600_000})


class RepairText(unittest.TestCase):
    def repair(self, text=MODULE, needles=("theorem first",)):
        errs = [err(line_of(text, n) + 1) for n in needles]
        reps, _ = tr.plan_text(text, errs)
        return tr.repair_text(text, reps), reps

    def test_the_set_option_is_above_the_declaration_and_the_note_after_the_imports(self):
        out, _ = self.repair()
        self.assertEqual(
            out.split("\n")[:12],
            ["import Tengoku", "",
             "/-! Tengoku repair: `first` ran out of heartbeats in the tree; `maxHeartbeats` is 1600000 for it (was 200000). -/",
             "", "/-!", "# A module", "-/", "", "namespace Toy", "", "set_option maxHeartbeats 1600000 in", "theorem first : 1 = 1 := by"],
        )

    def test_the_declaration_text_is_untouched(self):
        out, _ = self.repair()
        removed = [ln for ln in out.split("\n") if ln.startswith("set_option") or ln.startswith("/-! Tengoku repair")]
        kept = out.split("\n")
        for ln in removed:
            kept.remove(ln)
        # the one blank line the note brought is the only other difference
        self.assertEqual("\n".join(kept).replace("import Tengoku\n\n\n", "import Tengoku\n\n"), MODULE)

    def test_a_docstring_and_attribute_stay_attached_to_their_declaration(self):
        out, _ = self.repair(needles=("theorem second",))
        lines = out.split("\n")
        i = lines.index("set_option maxHeartbeats 1600000 in")
        self.assertEqual(lines[i + 1 : i + 4], ["/-- the second one -/", "@[simp]", "theorem second : 2 = 2 := by"])

    def test_two_repairs_two_notes_and_two_set_options_in_file_order(self):
        out, _ = self.repair(needles=("theorem first", " theorem third"))
        self.assertEqual(out.count("/-! Tengoku repair:"), 2)
        self.assertEqual(out.count("set_option maxHeartbeats 1600000 in"), 2)
        self.assertLess(out.index("`first` ran out"), out.index("`third` ran out"))
        self.assertLess(out.index("set_option maxHeartbeats 1600000 in\ntheorem first"), out.index("set_option maxHeartbeats 1600000 in\n theorem third"))

    def test_both_options_of_one_declaration_are_stacked_in_name_order(self):
        ln = line_of(MODULE, "theorem first")
        reps, _ = tr.plan_text(MODULE, [err(ln + 1), err(ln + 1, "synthInstance.maxHeartbeats", 20000)])
        out = tr.repair_text(MODULE, reps)
        self.assertIn("set_option maxHeartbeats 1600000 in\nset_option synthInstance.maxHeartbeats 160000 in\ntheorem first", out)

    def test_the_note_follows_the_faithful_imports_note_when_there_is_one(self):
        note = "/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/"
        text = f"import Tengoku.Seed.Data.Nat.Basic\n\n{note}\n\ntheorem t : 1 = 1 := by\n  simp\n"
        reps, _ = tr.plan_text(text, [err(6)])
        out = tr.repair_text(text, reps).split("\n")
        self.assertEqual(out[:5], ["import Tengoku.Seed.Data.Nat.Basic", "", note, out[3], ""])
        self.assertTrue(out[3].startswith("/-! Tengoku repair:"))
        self.assertIn("set_option maxHeartbeats 1600000 in", out)

    def test_a_declaration_right_under_the_imports_gets_both_in_order(self):
        text = "import Tengoku\ntheorem t : 1 = 1 := by\n  simp\n"
        reps, _ = tr.plan_text(text, [err(3)])
        self.assertEqual(
            tr.repair_text(text, reps).split("\n")[:5],
            ["import Tengoku", "", "/-! Tengoku repair: `t` ran out of heartbeats in the tree; `maxHeartbeats` is 1600000 for it (was 200000). -/", "set_option maxHeartbeats 1600000 in", "theorem t : 1 = 1 := by"],
        )

    def test_a_note_is_one_short_line(self):
        out, reps = self.repair()
        for r in reps:
            self.assertNotIn("\n", tr.note(r))
            self.assertLess(len(tr.note(r)), 160)
            self.assertTrue(tr.note(r).startswith("/-! ") and tr.note(r).endswith(" -/"))

    def test_the_result_is_deterministic(self):
        a, _ = self.repair()
        b, _ = self.repair()
        self.assertEqual(a, b)

    def test_a_module_that_is_a_module_system_file_keeps_its_header(self):
        text = "module\n\npublic import Tengoku\n\npublic theorem t : 1 = 1 := by\n  simp\n"
        reps, _ = tr.plan_text(text, [err(6)])
        out = tr.repair_text(text, reps).split("\n")
        self.assertEqual(out[:3], ["module", "", "public import Tengoku"])
        self.assertIn("set_option maxHeartbeats 1600000 in\npublic theorem t : 1 = 1 := by", "\n".join(out))


class ApplyToText(unittest.TestCase):
    def entry(self, text=MODULE):
        (r,), _ = tr.plan_text(text, [err(line_of(text, "theorem first") + 1)])
        after = tr.repair_text(text, [r])
        return {"before": tr.sha256(text), "after": tr.sha256(after), "repairs": [r]}, after

    def test_the_planned_text_gives_the_planned_bytes(self):
        e, after = self.entry()
        self.assertEqual(tr.apply_to_text(MODULE, e), after)

    def test_other_bytes_are_not_repaired(self):
        e, _ = self.entry()
        self.assertIsNone(tr.apply_to_text(MODULE + "\n-- changed\n", e))

    def test_a_result_that_is_not_the_planned_one_is_a_bug_and_says_so(self):
        e, _ = self.entry()
        e["after"] = "0" * 64
        with self.assertRaises(ValueError):
            tr.apply_to_text(MODULE, e)


class PlanCommand(unittest.TestCase):
    """`plan` on a checkout: the real module and the real log of PositiveAxisSystem, and small ones for the refusals."""

    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        self.tree = self.d / "tree"
        self.out = self.d / "out"

    def put_module(self, text, rel="Tengoku/ToyLib/Toy/B.lean", ns="ToyLib", mod="Tengoku.ToyLib.Toy.B"):
        p = self.tree / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        self.out.mkdir(exist_ok=True)
        (self.out / "new.json").write_text(json.dumps({"ns": ns, "modules": {mod: {"path": rel, "sha256": tr.sha256(text)}}}))
        return p

    def plan(self, log: str):
        (self.d / "build.log").write_text(log)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            tr.main(["plan", "--log", str(self.d / "build.log"), "--new", str(self.out / "new.json"), "--tree", str(self.tree), "--out", str(self.out)])
        return buf.getvalue(), json.loads((self.out / "repairs.json").read_text()), json.loads((self.out / "new.json").read_text())

    LOG_B = """✖ [2/3] Building Tengoku.ToyLib.Toy.B (3s)
error: Tengoku/ToyLib/Toy/B.lean:{line}:2: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.
Some required targets logged failures:
- Tengoku.ToyLib.Toy.B
error: build failed
"""

    def test_a_timeout_repairs_the_file_in_the_checkout_and_the_new_bytes_are_recorded(self):
        p = self.put_module(MODULE)
        said, rep, new = self.plan(self.LOG_B.format(line=line_of(MODULE, "theorem first") + 1))
        self.assertIn("1 repair(s) in 1 module(s)", said)
        self.assertIn("first (line", said)
        entry = rep["modules"]["Toy.B"]
        self.assertEqual(entry["before"], tr.sha256(MODULE))
        self.assertEqual(entry["after"], tr.sha256(p.read_text()))
        self.assertIn("set_option maxHeartbeats 1600000 in", p.read_text())
        spec = new["modules"]["Tengoku.ToyLib.Toy.B"]
        self.assertEqual((spec["sha256"], spec["original_sha256"], spec["repaired"]), (tr.sha256(p.read_text()), tr.sha256(MODULE), True))

    def test_the_file_the_plan_writes_is_what_apply_to_text_makes_from_the_original(self):
        p = self.put_module(MODULE)
        _, rep, _ = self.plan(self.LOG_B.format(line=line_of(MODULE, "theorem first") + 1))
        self.assertEqual(tr.apply_to_text(MODULE, rep["modules"]["Toy.B"]), p.read_text())

    def test_the_real_module_and_the_real_log(self):
        rel = "Tengoku/NavierStokesEuler/NavierStokes/PositiveAxisSystem.lean"
        # a module of the real shape: the two declarations the real errors name sit where the log says (lines 675 and 746), the second with a leading space
        lines = ["import Tengoku", "", "/-! # Explicit positive-order axis matrices -/", ""] + ["-- filler"] * 670
        lines += [" theorem coefficient0_contDiffAt_of_pullback {n : WithTop ℕ∞} : True := by", "  trivial"]  # line 675
        lines += ["-- filler"] * 69
        lines += [" theorem coefficient0_analyticAt {h : ℂ} : True := by", "  trivial"]  # line 746
        text = "\n".join(lines) + "\n"
        self.assertEqual(text.split("\n")[674][:9], " theorem ")
        self.assertEqual(text.split("\n")[745][:9], " theorem ")
        self.put_module(text, rel=rel, ns="NavierStokesEuler", mod="Tengoku.NavierStokesEuler.NavierStokes.PositiveAxisSystem")
        said, rep, _ = self.plan(REAL_LOG)
        self.assertIn("2 repair(s) in 1 module(s)", said)
        reps = rep["modules"]["NavierStokes.PositiveAxisSystem"]["repairs"]
        self.assertEqual([(r["name"], r["option"], r["from"], r["to"]) for r in reps], [("coefficient0_contDiffAt_of_pullback", "maxHeartbeats", 200000, 1600000), ("coefficient0_analyticAt", "maxHeartbeats", 200000, 1600000)])
        new_text = (self.tree / rel).read_text()
        self.assertEqual(new_text.count("set_option maxHeartbeats 1600000 in\n theorem coefficient0_"), 2)

    def test_a_module_without_a_timeout_is_left_alone(self):
        p = self.put_module(MODULE)
        said, rep, new = self.plan("error: Tengoku/ToyLib/Toy/B.lean:3:0: type mismatch\nSome required targets logged failures:\n- Tengoku.ToyLib.Toy.B\nerror: build failed\n")
        self.assertEqual(rep["modules"], {})
        self.assertEqual(p.read_text(), MODULE)
        self.assertNotIn("repaired", new["modules"]["Tengoku.ToyLib.Toy.B"])
        self.assertIn("0 repair(s) in 0 module(s)", said)

    def test_a_timeout_in_a_module_that_is_not_new_is_left_alone(self):
        self.put_module(MODULE, rel="Tengoku/ToyLib/Toy/Other.lean", mod="Tengoku.ToyLib.Toy.Other")
        _, rep, _ = self.plan(self.LOG_B.format(line=3))
        self.assertEqual(rep["modules"], {})

    def test_a_checkout_file_that_is_not_the_bundles_is_not_repaired(self):
        p = self.put_module(MODULE)
        p.write_text(MODULE + "-- someone else's edit\n")
        said, rep, _ = self.plan(self.LOG_B.format(line=line_of(MODULE, "theorem first") + 1))
        self.assertEqual(rep["modules"], {})
        self.assertIn("not the bundle's", said)
        self.assertNotIn("set_option", p.read_text())

    def test_a_log_without_an_ending_repairs_nothing(self):
        p = self.put_module(MODULE)
        log = f"error: Tengoku/ToyLib/Toy/B.lean:{line_of(MODULE, 'theorem first') + 1}:2: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n"
        said, rep, _ = self.plan(log)
        self.assertEqual(rep["modules"], {})
        self.assertIn("no ending", said)
        self.assertEqual(p.read_text(), MODULE)

    def test_a_log_that_already_has_a_repair_round_gets_no_second_one(self):
        p = self.put_module(MODULE)
        log = self.LOG_B.format(line=line_of(MODULE, "theorem first") + 1) + tr.MARKER + "\n" + self.LOG_B.format(line=line_of(MODULE, "theorem first") + 1)
        said, rep, _ = self.plan(log)
        self.assertEqual(rep["modules"], {})
        self.assertIn("no second round", said)
        self.assertEqual(p.read_text(), MODULE)

    def test_a_declaration_with_all_the_room_it_can_get_is_left_to_the_old_path(self):
        p = self.put_module(MODULE)
        log = self.LOG_B.format(line=line_of(MODULE, "theorem first") + 1).replace("(200000)", "(1600000)")
        said, rep, _ = self.plan(log)
        self.assertEqual(rep["modules"], {})
        self.assertIn("already 1600000", said)
        self.assertEqual(p.read_text(), MODULE)

    def test_the_repairs_file_is_written_even_when_there_is_nothing_to_repair(self):
        self.put_module(MODULE)
        _, rep, _ = self.plan("Build completed successfully\n")
        self.assertEqual(rep, {"rule": "R2", "modules": {}})

    def test_the_typeclass_search_gets_its_own_option(self):
        text = "import Tengoku\n\nnamespace Toy\n\n" + "-- filler\n" * 7 + "theorem t : 1 = 1 := by\n  simp\n  simp\n  simp\n"
        self.put_module(text)
        _, rep, _ = self.plan(TYPECLASS_LOG)
        (r,) = rep["modules"]["Toy.B"]["repairs"]
        self.assertEqual((r["option"], r["from"], r["to"]), ("synthInstance.maxHeartbeats", 20000, 160000))


class MergeCommand(unittest.TestCase):
    def write(self, d, name, mods):
        p = Path(d) / name
        p.write_text(json.dumps({"rule": "R2", "modules": mods}))
        return str(p)

    def test_the_repairs_of_two_modes_are_one_file(self):
        d = tempfile.mkdtemp()
        a = self.write(d, "a.json", {"X": {"before": "1", "after": "2", "repairs": []}})
        b = self.write(d, "b.json", {"X": {"before": "1", "after": "2", "repairs": []}, "Y": {"before": "3", "after": "4", "repairs": []}})
        out = str(Path(d) / "m.json")
        with contextlib.redirect_stdout(io.StringIO()):
            tr.main(["merge", "--out", out, a, b])
        self.assertEqual(sorted(json.loads(Path(out).read_text())["modules"]), ["X", "Y"])

    def test_the_same_module_from_other_bytes_is_an_error(self):
        d = tempfile.mkdtemp()
        a = self.write(d, "a.json", {"X": {"before": "1", "after": "2", "repairs": []}})
        b = self.write(d, "b.json", {"X": {"before": "9", "after": "2", "repairs": []}})
        with self.assertRaises(SystemExit) as cm:
            tr.main(["merge", "--out", str(Path(d) / "m.json"), a, b])
        self.assertIn("different bytes", str(cm.exception))

    def test_empty_inputs_give_an_empty_file(self):
        d = tempfile.mkdtemp()
        a = self.write(d, "a.json", {})
        out = str(Path(d) / "m.json")
        with contextlib.redirect_stdout(io.StringIO()):
            tr.main(["merge", "--out", out, a])
        self.assertEqual(json.loads(Path(out).read_text()), {"rule": "R2", "modules": {}})


MODS = {
    f"Tengoku.ToyLib.Toy.{m}": {"path": f"Tengoku/ToyLib/Toy/{m}.lean", "sha256": m.lower() * 8} for m in "ABCDE"
}


def mk_new(repaired: str = "") -> dict:
    mods = {k: dict(v) for k, v in MODS.items()}
    for m in repaired:
        mods[f"Tengoku.ToyLib.Toy.{m}"]["repaired"] = True
    return {"ns": "ToyLib", "modules": mods}


def built(m: str) -> str:
    return f"✔ [1/9] Built Tengoku.ToyLib.Toy.{m} (1s)\n"


def timeout(m: str, line: int = 5) -> str:
    return f"error: Tengoku/ToyLib/Toy/{m}.lean:{line}:2: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\n"


def tail(*failed: str) -> str:
    return "Some required targets logged failures:\n" + "".join(f"- Tengoku.ToyLib.Toy.{m}\n" for m in failed) + "error: build failed\n"


class Collect(unittest.TestCase):
    """`collect` reads a log with a repair round: a repaired module is judged on the second part, every other module as before."""

    def run_collect(self, log: str, repaired: str = "", *flags):
        d = Path(tempfile.mkdtemp())
        (d / "new.json").write_text(json.dumps(mk_new(repaired)))
        (d / "build.log").write_text(log)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            tv.main(["collect", "--new", str(d / "new.json"), "--log", str(d / "build.log"), "--out", str(d), *flags])
        return d, buf.getvalue()

    def failing(self, d):
        return set((d / "failing.txt").read_text().split())

    def ok(self, d):
        return set(json.loads((d / "ok.json").read_text()))

    def log(self):
        return (
            built("E") + timeout("A") + timeout("B") + "error: Tengoku/ToyLib/Toy/C.lean:3:0: type mismatch\n" + tail("A", "B", "C")
            + tr.MARKER + "\n" + built("A") + built("D") + timeout("B") + "error: Tengoku/ToyLib/Toy/C.lean:3:0: type mismatch\n" + tail("B", "C")
        )

    def test_a_repaired_module_that_builds_the_second_time_is_accepted(self):
        d, said = self.run_collect(self.log(), "AB")
        self.assertNotIn("Toy.A", self.failing(d))
        self.assertIn("Tengoku.ToyLib.Toy.A", self.ok(d))

    def test_a_repaired_module_that_still_times_out_is_refused(self):
        d, _ = self.run_collect(self.log(), "AB")
        self.assertIn("Toy.B", self.failing(d))
        self.assertNotIn("Tengoku.ToyLib.Toy.B", self.ok(d))

    def test_a_module_that_failed_for_another_reason_stays_refused_even_if_the_second_round_did_not_say_so(self):
        log = built("E") + "error: Tengoku/ToyLib/Toy/C.lean:3:0: type mismatch\n" + timeout("A") + tail("A", "C") + tr.MARKER + "\n" + built("A") + built("B") + built("D") + "Build completed successfully\n"
        d, _ = self.run_collect(log, "A")
        self.assertEqual(self.failing(d), {"Toy.C"})
        self.assertEqual(self.ok(d), {f"Tengoku.ToyLib.Toy.{m}" for m in "ABDE"})

    def test_a_module_that_was_never_reached_is_still_not_verified(self):
        log = built("A") + built("E") + tail()
        d, _ = self.run_collect(log, "")
        self.assertEqual(self.failing(d), {"Toy.B", "Toy.C", "Toy.D"})

    def test_a_module_built_in_the_second_round_only_counts_as_built(self):
        d, _ = self.run_collect(self.log(), "AB")
        self.assertIn("Tengoku.ToyLib.Toy.D", self.ok(d))

    def test_the_summary_says_how_many_were_mended(self):
        _, said = self.run_collect(self.log(), "AB")
        self.assertIn("1 of 2 module(s) the tree timed out on were mended", said)
        self.assertIn("repaired: Toy.A", said)
        self.assertNotIn("repaired: Toy.B", said)

    def test_the_repaired_bytes_are_what_is_accepted(self):
        d = Path(tempfile.mkdtemp())
        new = mk_new("A")
        new["modules"]["Tengoku.ToyLib.Toy.A"]["sha256"] = "f" * 64
        (d / "new.json").write_text(json.dumps(new))
        (d / "build.log").write_text(built("A") + "Build completed successfully\n")
        with contextlib.redirect_stdout(io.StringIO()):
            tv.main(["collect", "--new", str(d / "new.json"), "--log", str(d / "build.log"), "--out", str(d)])
        self.assertEqual(json.loads((d / "ok.json").read_text())["Tengoku.ToyLib.Toy.A"], "f" * 64)

    def test_a_log_without_a_marker_is_read_exactly_as_before(self):
        log = built("A") + built("B") + built("D") + built("E") + "error: Tengoku/ToyLib/Toy/C.lean:3:0: type mismatch\n" + tail("C")
        d, said = self.run_collect(log, "")
        self.assertEqual(self.failing(d), {"Toy.C"})
        self.assertNotIn("mended", said)

    def test_a_second_part_that_was_killed_is_unfinished(self):
        log = built("E") + timeout("A") + tail("A") + tr.MARKER + "\n" + built("D")
        with self.assertRaises(SystemExit) as cm:
            self.run_collect(log, "A")
        self.assertIn("no ending", str(cm.exception))

    def test_an_unfinished_second_part_can_be_accepted_for_what_it_built(self):
        log = built("E") + timeout("A") + tail("A") + tr.MARKER + "\n" + built("A")
        d, _ = self.run_collect(log, "A", "--allow-unfinished")
        self.assertIn("Tengoku.ToyLib.Toy.A", self.ok(d))

    def test_the_first_part_ending_does_not_count_for_a_second_part_that_has_none(self):
        # the first part ends with "build failed"; the second was cut short: the whole log must not look finished
        log = built("E") + timeout("A") + tail("A") + tr.MARKER + "\n"
        with self.assertRaises(SystemExit):
            self.run_collect(log, "A")

    def test_a_repaired_module_with_a_sorry_in_the_first_part_only_is_not_refused_for_it(self):
        log = built("E") + "warning: Tengoku/ToyLib/Toy/A.lean:4:0: declaration uses `sorry`\n" + timeout("A") + tail("A") + tr.MARKER + "\n" + built("A") + "Build completed successfully\n"
        d, _ = self.run_collect(log, "A")
        self.assertIn("Tengoku.ToyLib.Toy.A", self.ok(d))

    def test_a_dependent_of_a_still_failing_repaired_module_goes_with_it(self):
        d = Path(tempfile.mkdtemp())
        files = {
            "Tengoku/ToyLib.lean": "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in "ABCDE"),
            "Tengoku/ToyLib/Toy/A.lean": "theorem a : 1 = 1 := rfl\n",
            "Tengoku/ToyLib/Toy/B.lean": "theorem b : 2 = 2 := rfl\n",
            "Tengoku/ToyLib/Toy/C.lean": "theorem c : 3 = 3 := rfl\n",
            "Tengoku/ToyLib/Toy/D.lean": "import Tengoku.ToyLib.Toy.B\n\ntheorem d : 4 = 4 := rfl\n",
            "Tengoku/ToyLib/Toy/E.lean": "theorem e : 5 = 5 := rfl\n",
            "Tengoku/ToyLib/Deps.lean": "-- marker\n",
        }
        for rel, t in files.items():
            (d / "b" / rel).parent.mkdir(parents=True, exist_ok=True)
            (d / "b" / rel).write_text(t)
        (d / "new.json").write_text(json.dumps(mk_new("B")))
        (d / "build.log").write_text(built("A") + built("C") + built("E") + timeout("B") + tail("B") + tr.MARKER + "\n" + timeout("B") + tail("B"))
        with contextlib.redirect_stdout(io.StringIO()):
            tv.main(["collect", "--new", str(d / "new.json"), "--log", str(d / "build.log"), "--out", str(d), "--bundle", str(d / "b")])
        self.assertEqual(self.failing(d), {"Toy.B"})
        self.assertNotIn("Tengoku.ToyLib.Toy.D", self.ok(d))


class ComposeAndCheck(unittest.TestCase):
    """The loop on the toy library: compose, plan on the module the tree timed out on, compose again with the repairs, and `check` accepts exactly those bytes."""

    def compose(self, *extra):
        from test_faithful_imports import Compose

        return Compose("compose").compose(*extra)

    def read(self, d, rel):
        return (d / "bundle-proposed" / "Tengoku" / "ToyLib" / rel).read_text()

    def planned(self, d):
        text = self.read(d, "Toy/B.lean")
        tree = d / "tree"
        out = d / "out"
        (tree / "Tengoku/ToyLib/Toy").mkdir(parents=True)
        out.mkdir()
        (tree / "Tengoku/ToyLib/Toy/B.lean").write_text(text)
        shaA = tr.sha256(self.read(d, "Toy/A.lean"))
        new = {"ns": "ToyLib", "modules": {
            "Tengoku.ToyLib.Toy.A": {"path": "Tengoku/ToyLib/Toy/A.lean", "sha256": shaA},
            "Tengoku.ToyLib.Toy.B": {"path": "Tengoku/ToyLib/Toy/B.lean", "sha256": tr.sha256(text)},
        }}
        (out / "new.json").write_text(json.dumps(new))
        line = line_of(text, "theorem uses_one_pos")
        (d / "build.log").write_text(
            f"error: Tengoku/ToyLib/Toy/B.lean:{line}:2: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\nSome required targets logged failures:\n- Tengoku.ToyLib.Toy.B\nerror: build failed\n"
        )
        with contextlib.redirect_stdout(io.StringIO()):
            tr.main(["plan", "--log", str(d / "build.log"), "--new", str(out / "new.json"), "--tree", str(tree), "--out", str(out)])
        return text, out

    def test_compose_with_the_repairs_ships_the_bytes_the_plan_wrote_and_check_accepts_them(self):
        d, r = self.compose()
        self.assertEqual(r.returncode, 0, r.stderr)
        before, out = self.planned(d)
        repaired_in_tree = (d / "tree/Tengoku/ToyLib/Toy/B.lean").read_text()
        self.assertNotEqual(before, repaired_in_tree)
        d2, r2 = self.compose("--tree-repairs", str(out / "repairs.json"))
        self.assertEqual(r2.returncode, 0, r2.stderr)
        self.assertEqual(self.read(d2, "Toy/B.lean"), repaired_in_tree)
        self.assertEqual(self.read(d2, "Toy/A.lean"), self.read(d, "Toy/A.lean"))
        new = json.loads((out / "new.json").read_text())
        ok = {m: s["sha256"] for m, s in new["modules"].items()}
        (out / "ok.json").write_text(json.dumps(ok))
        res = subprocess.run([sys.executable, str(HERE / "tree_verify.py"), "check", "--bundle", str(d2 / "bundle-proposed"), "--new", str(out / "new.json"), "--ok", str(out / "ok.json")], capture_output=True, text=True, check=False)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_without_the_repairs_check_refuses_the_unrepaired_bytes(self):
        d, _ = self.compose()
        _, out = self.planned(d)
        new = json.loads((out / "new.json").read_text())
        (out / "ok.json").write_text(json.dumps({m: s["sha256"] for m, s in new["modules"].items()}))
        res = subprocess.run([sys.executable, str(HERE / "tree_verify.py"), "check", "--bundle", str(d / "bundle-proposed"), "--new", str(out / "new.json"), "--ok", str(out / "ok.json")], capture_output=True, text=True, check=False)
        self.assertNotEqual(res.returncode, 0)
        self.assertIn("other bytes", res.stderr)

    def test_repairs_for_a_module_whose_bytes_changed_are_not_applied(self):
        d, _ = self.compose()
        _, out = self.planned(d)
        rep = json.loads((out / "repairs.json").read_text())
        rep["modules"]["Toy.B"]["before"] = "0" * 64
        (out / "repairs.json").write_text(json.dumps(rep))
        d2, r2 = self.compose("--tree-repairs", str(out / "repairs.json"))
        self.assertEqual(r2.returncode, 0, r2.stderr)
        self.assertNotIn("Tengoku repair", self.read(d2, "Toy/B.lean"))

    def test_an_empty_repairs_file_changes_nothing(self):
        d, _ = self.compose()
        e = d / "none.json"
        e.write_text(json.dumps({"rule": "R2", "modules": {}}))
        d2, r2 = self.compose("--tree-repairs", str(e))
        self.assertEqual(r2.returncode, 0, r2.stderr)
        for rel in ("Toy/A.lean", "Toy/B.lean"):
            self.assertEqual(self.read(d, rel), self.read(d2, rel))

    def test_the_repair_works_with_the_faithful_imports_note(self):
        d, _ = self.compose("--imports", "faithful")
        text, out = self.planned(d)
        self.assertIn("/-! Tengoku: the imports are the original's", text)
        repaired = (d / "tree/Tengoku/ToyLib/Toy/B.lean").read_text().split("\n")
        i = next(k for k, ln in enumerate(repaired) if ln.startswith("/-! Tengoku: the imports"))
        self.assertTrue(repaired[i + 1].startswith("/-! Tengoku repair:"))
        d2, r2 = self.compose("--imports", "faithful", "--tree-repairs", str(out / "repairs.json"))
        self.assertEqual(self.read(d2, "Toy/B.lean"), "\n".join(repaired))


class Wiring(unittest.TestCase):
    SHARDED = (ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text()

    def verify_job(self):
        return self.SHARDED.split("\n  verify:\n", 1)[1].split("\n  finish:\n", 1)[0]

    def test_the_repair_step_sits_between_the_build_and_the_verdict(self):
        v = self.verify_job()
        i_build = v.index("- name: Build them (the queue's own command)")
        i_repair = v.index("- name: Give the declarations that ran out of heartbeats room, and build again (tree_repair.py)")
        i_accept = v.index("- name: What the build accepted")
        self.assertLess(i_build, i_repair)
        self.assertLess(i_repair, i_accept)

    def test_the_repair_step_plans_then_builds_the_same_targets_after_the_marker(self):
        v = self.verify_job()
        step = v[v.index("- name: Give the declarations"):v.index("- name: What the build accepted")]
        self.assertIn("tree_repair.py plan --log out/build.log --new out/new.json --tree tree --out out", step)
        self.assertIn("tree_repair.MARKER", step)
        self.assertLess(step.index("MARKER"), step.index("lake build"))
        self.assertIn("lake build $targets", step)
        self.assertIn("tee -a ../out/build.log", step)  # appended: collect reads the two parts
        self.assertIn('json.load(open("out/repairs.json"))["modules"]', step)  # no repairs, no second build

    def test_the_second_build_has_its_own_time_limit_below_the_first(self):
        v = self.verify_job()
        first = int(re.search(r"timeout -k 60 (\d+)m lake build \$targets 2>&1 \| tee \.\./out/build\.log", v)[1])
        second = int(re.search(r"timeout -k 60 (\d+)m lake build \$targets 2>&1 \| tee -a \.\./out/build\.log", v)[1])
        self.assertLess(second, first)

    def test_the_verdict_artifact_carries_the_repairs(self):
        v = self.verify_job()
        up = v[v.index("upload-artifact"):]
        self.assertIn("out/repairs.json", up)
        self.assertIn("out/repairs.txt", up)

    def test_finish_needs_the_repairs_of_every_verified_mode_and_merges_them(self):
        f = self.SHARDED.split("\n  finish:\n", 1)[1]
        self.assertIn("for f in failing.txt ok.json new.json summary.txt repairs.json; do", f)
        self.assertIn("repair_files+=(", f)
        self.assertIn("tree_repair.py merge --out tree-repairs.json", f)
        self.assertIn("""echo '{"rule": "R2", "modules": {}}' > tree-repairs.json""", f)  # no verified mode: an empty file, not a missing one

    def test_compose_in_finish_gets_the_repairs(self):
        f = self.SHARDED.split("\n  finish:\n", 1)[1]
        compose = f[f.index("bundle.py compose"):f.index("- name: Make the registrations")]
        self.assertIn("--tree-repairs ../tree-repairs.json", compose)
        self.assertIn("--tree-failures ../tree-failures.txt", compose)

    def test_the_draft_compose_has_no_repairs(self):
        # the draft is what the tree builds first: the repairs come out of that build
        head = self.SHARDED.split("\n  verify:\n", 1)[0]
        self.assertNotIn("--tree-repairs", head)

    def test_the_marker_is_one_line_and_cannot_be_a_lake_message(self):
        self.assertNotIn("\n", tr.MARKER)
        self.assertFalse(tv.FAILED_TARGET.search(tr.MARKER) or tv.ERROR.search(tr.MARKER) or tv.BUILT.search(tr.MARKER))

    def test_tree_verify_and_tree_repair_agree_on_when_a_build_has_ended(self):
        self.assertIs(tv.FINISHED, tr.FINISHED)


if __name__ == "__main__":
    unittest.main()
