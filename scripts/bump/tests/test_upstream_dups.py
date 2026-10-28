"""upstream_dups.py: a compatibility shim that Mathlib now declares too is blanked, and nothing else changes.

Class of bug this guards (2026-10-28, stafford38-formal): `abbrev MvPolynomial.coeff`, a shim for a name Mathlib added later, failed with "has already been declared"; the module was dropped and 372
of 436 modules with it. The remedy deletes a declaration of the library's own, so the invariants are about what it must NOT touch:

  * line numbers: the output has the same number of lines, and every line outside the removed blocks is byte for byte what it was (positions of the rest of the log stay valid);
  * only a block the log names, whose first line is an abbrev/def/theorem/lemma of that name, is blanked; its docstring and attributes go with it, the next block does not;
  * a name the library declares anywhere else (this file or any other module) is the library's own duplicate and stays;
  * instance, structure, inductive, class and opaque are never removed;
  * a second run on the output (with the same log) changes nothing.

The mutants at the end break the code the way the shortcut would; the invariants must notice.
"""

from __future__ import annotations

import random
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import upstream_dups as ud  # noqa: E402

SHIM = """module
public import Mathlib.Algebra.MvPolynomial.Basic

namespace MvPolynomial

/-- Compatibility spelling.
Second line of the docstring. -/
@[simp]
abbrev coeff {σ : Type*} {R : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R := AddMonoidAlgebra.coeff p m

theorem coeff_zero_compat : True := trivial

end MvPolynomial
"""


def lib_with(tmp: Path, files: dict[str, str]) -> Path:
    for rel, text in files.items():
        p = tmp / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return tmp


def log_for(rel: str, text: str, name: str, needle: str) -> str:
    line = next(i + 1 for i, l in enumerate(text.split("\n")) if needle in l)
    return f"error: {rel}:{line}:7: `{name}` has already been declared\n"


class Basics(unittest.TestCase):
    def test_the_shim_goes_with_its_docstring_and_attribute_and_the_rest_stays_in_place(self):
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": SHIM})
            done = ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff"))
            self.assertEqual([(d["name"], d["kind"]) for d in done], [("MvPolynomial.coeff", "abbrev")])
            out = (lib / "Own/Shim.lean").read_text()
            a, b = SHIM.split("\n"), out.split("\n")
            self.assertEqual(len(a), len(b))
            self.assertIn("removed `MvPolynomial.coeff`", b[5])
            self.assertTrue(all(x == "" for x in b[6:10]))
            self.assertEqual(a[:5] + a[10:], b[:5] + b[10:])
            self.assertIn("theorem coeff_zero_compat", out)
            self.assertNotIn("abbrev coeff", out)
            self.assertNotIn("Compatibility spelling", out)

    def test_a_second_run_changes_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": SHIM})
            log = log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff")
            ud.remove(lib, ["Own"], log)
            once = (lib / "Own/Shim.lean").read_text()
            self.assertEqual(ud.remove(lib, ["Own"], log), [])
            self.assertEqual((lib / "Own/Shim.lean").read_text(), once)

    def test_a_name_the_library_declares_elsewhere_is_its_own_duplicate_and_stays(self):
        other = "namespace MvPolynomial\ndef coeff := 1\nend MvPolynomial\n"
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": SHIM, "Own/Other.lean": other})
            self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff")), [])
            self.assertEqual((lib / "Own/Shim.lean").read_text(), SHIM)
        twice = SHIM.replace("theorem coeff_zero_compat", "def coeff := 2\n\ntheorem coeff_zero_compat")
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": twice})
            self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/Shim.lean", twice, "MvPolynomial.coeff", "abbrev coeff")), [])

    def test_instances_structures_and_classes_are_never_removed(self):
        for kw in ("instance coeffInst : Inhabited Nat := ⟨0⟩", "structure Coeff where\n  x : Nat", "inductive Coeff | a", "class Coeff (α : Type) where\n  x : α", "opaque coeff : Nat"):
            text = f"namespace N\n\n{kw}\n\nend N\n"
            with tempfile.TemporaryDirectory() as t:
                lib = lib_with(Path(t), {"Own/A.lean": text})
                last = "coeffInst" if kw.startswith("instance") else "coeff" if kw.startswith("opaque") else "Coeff"
                self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "N." + last, kw.split("\n")[0])), [], kw)
                self.assertEqual((lib / "Own/A.lean").read_text(), text)

    def test_an_error_on_a_line_that_is_not_the_declaration_changes_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": SHIM})
            for needle in ("namespace MvPolynomial", "AddMonoidAlgebra", "theorem coeff_zero_compat"):
                self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", needle)), [], needle)
            self.assertEqual((lib / "Own/Shim.lean").read_text(), SHIM)

    def test_a_name_that_does_not_match_the_declaration_is_not_removed(self):
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": SHIM})
            self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.other", "abbrev coeff")), [])

    def test_text_in_comments_and_strings_is_not_a_declaration(self):
        text = '/- def coeff := 1 -/\nnamespace N\n-- theorem coeff : True\nabbrev coeff : Nat := 0\nend N\ndef s := "def coeff"\n'
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/A.lean": text})
            done = ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "N.coeff", "abbrev coeff"))
            self.assertEqual(len(done), 1)

    def test_attributes_on_the_same_line_as_the_keyword_go_with_the_declaration(self):
        for head in ("@[simp] abbrev coeff", "@[simp, reducible]   abbrev coeff", "@[simp] @[reducible] protected abbrev coeff"):
            text = f"namespace N\n\n{head} : Nat := 0\n\ntheorem keep : True := trivial\nend N\n"
            with tempfile.TemporaryDirectory() as t:
                lib = lib_with(Path(t), {"Own/A.lean": text})
                done = ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "N.coeff", "coeff"))
                self.assertEqual(len(done), 1, head)
                out = (lib / "Own/A.lean").read_text()
                self.assertIn("theorem keep", out)
                self.assertNotIn("abbrev coeff", out, head)

    def test_an_attribute_over_several_lines_is_removed_whole(self):
        text = "namespace N\n\n@[simp,\n  reducible]\nabbrev coeff : Nat := 0\n\n@[ext]\ntheorem keep : True := trivial\nend N\n"
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/A.lean": text})
            done = ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "N.coeff", "abbrev coeff"))
            self.assertEqual(len(done), 1)
            out = (lib / "Own/A.lean").read_text()
            self.assertNotIn("reducible", out)  # not left attached to the next declaration
            self.assertIn("@[ext]\ntheorem keep", out)
            self.assertEqual(len(out.split("\n")), len(text.split("\n")))

    def test_an_earlier_complete_attribute_or_list_is_not_mistaken_for_the_shims_attribute(self):
        # the line above the shim ends with `]`, and an `@[` is a few lines up: it must be the attribute OF the shim to go with it
        for earlier in ("@[simp] theorem early : [1, 2] = [1, 2] := by\n  rfl\n  -- done ]", "@[simp]\ndef early : List Nat :=\n  [1, 2,\n   3]"):
            text = f"namespace N\n\n{earlier}\nabbrev coeff : Nat := 0\n\nend N\n"
            with tempfile.TemporaryDirectory() as t:
                lib = lib_with(Path(t), {"Own/A.lean": text})
                done = ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "N.coeff", "abbrev coeff"))
                out = (lib / "Own/A.lean").read_text()
                self.assertEqual(len(done), 1, earlier)
                self.assertNotIn("abbrev coeff", out)
                self.assertIn(earlier.split("\n")[0], out, earlier)  # the earlier declaration is still there
                self.assertEqual(len(out.split("\n")), len(text.split("\n")))

    def test_the_command_after_a_shim_is_never_swallowed(self):
        for nxt in ("macro_rules | `(tactic| foo) => `(tactic| rfl)", "elab_rules : term | `(foo) => pure ()", "declare_syntax_cat mycat", "initialize myRef : IO.Ref Nat <- IO.mkRef 0", "register_simp_attr my_simp", "notation3 \"foo\" => 1", "#print axioms x"):
            text = f"namespace N\n\nabbrev coeff : Nat := 0\n\n{nxt}\n\nend N\n"
            with tempfile.TemporaryDirectory() as t:
                lib = lib_with(Path(t), {"Own/A.lean": text})
                done = ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "N.coeff", "abbrev coeff"))
                out = (lib / "Own/A.lean").read_text()
                self.assertEqual(len(done), 1, nxt)  # the shim really went ...
                self.assertNotIn("abbrev coeff", out, nxt)
                self.assertIn(nxt, out, nxt)  # ... and the command after it stayed

    def test_a_declaration_of_the_same_last_name_in_another_namespace_keeps_the_shim_a_conservative_choice(self):
        # the check is by last component, not namespace aware: it errs towards keeping a declaration, never towards deleting one (see CLASSES.md)
        text = "namespace A\n\nabbrev coeff : Nat := 0\n\nend A\n\nnamespace B\n\ndef coeff : Nat := 1\n\nend B\n"
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/A.lean": text})
            self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/A.lean", text, "A.coeff", "abbrev coeff")), [])
            self.assertEqual((lib / "Own/A.lean").read_text(), text)

    def test_a_log_with_no_such_error_changes_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t), {"Own/Shim.lean": SHIM})
            self.assertEqual(ud.remove(lib, ["Own"], "error: Own/Shim.lean:3:1: unknown namespace `X`\n"), [])
            self.assertEqual((lib / "Own/Shim.lean").read_text(), SHIM)


class Hostile(unittest.TestCase):
    """The library is third-party and the log names the file to edit: nothing outside the library may be written, whatever path or link the library or the log offers."""

    def test_a_symlinked_file_is_never_written_through(self):
        with tempfile.TemporaryDirectory() as t:
            outside = Path(t) / "outside.lean"
            outside.write_text(SHIM)
            lib = lib_with(Path(t) / "lib", {"Own/Other.lean": "def other := 1\n"})
            (lib / "Own/Shim.lean").symlink_to(outside)
            done = ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff"))
            self.assertEqual(done, [])
            self.assertEqual(outside.read_text(), SHIM)

    def test_a_directory_symlink_and_dotdot_and_absolute_paths_in_the_log_write_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            outside = Path(t) / "outside"
            outside.mkdir()
            (outside / "Shim.lean").write_text(SHIM)
            victim = Path(t) / "victim.lean"
            victim.write_text(SHIM)
            lib = lib_with(Path(t) / "lib", {"Own/Other.lean": "def other := 1\n"})
            (lib / "Linked").symlink_to(outside)
            logs = [log_for("Linked/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff"), log_for("../victim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff"), log_for(str(victim), SHIM, "MvPolynomial.coeff", "abbrev coeff")]
            for log in logs:
                self.assertEqual(ud.remove(lib, ["Own"], log), [], log)
            self.assertEqual(((outside / "Shim.lean").read_text(), victim.read_text()), (SHIM, SHIM))

    def test_a_module_that_cannot_be_scanned_keeps_the_shim(self):
        other = "namespace MvPolynomial\ndef coeff := 1\nend MvPolynomial\n"
        with tempfile.TemporaryDirectory() as t:
            elsewhere = Path(t) / "elsewhere.lean"
            elsewhere.write_text(other)
            lib = lib_with(Path(t) / "lib", {"Own/Shim.lean": SHIM})
            (lib / "Own/Other.lean").symlink_to(elsewhere)  # declares the name, but is a link: it cannot be read safely
            self.assertEqual(ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff")), [])
            self.assertEqual((lib / "Own/Shim.lean").read_text(), SHIM)

    def test_an_ordinary_file_inside_the_library_is_still_edited(self):
        with tempfile.TemporaryDirectory() as t:
            lib = lib_with(Path(t) / "lib", {"Own/Shim.lean": SHIM})
            self.assertEqual(len(ud.remove(lib, ["Own"], log_for("Own/Shim.lean", SHIM, "MvPolynomial.coeff", "abbrev coeff"))), 1)


class Structure(unittest.TestCase):
    """Random files of blocks, some of them named in the log: the output is the input with exactly those blocks blanked."""

    def test_exactly_the_named_blocks_are_blanked_and_no_line_moves(self):
        rng = random.Random(9)
        for _ in range(150):
            blocks, names, spans = [], [], []
            for i in range(rng.randint(2, 9)):
                kind = rng.choice(["abbrev", "def", "theorem", "instance", "structure"])
                doc = rng.choice(["", "/-- doc " + str(i) + " -/\n", "/-- two\nlines -/\n"])
                attr = rng.choice(["", "@[simp]\n"])
                body = f"{kind} n{i} : Nat := {i}\n" if kind in ("abbrev", "def") else f"{kind} n{i} : True := trivial\n" if kind == "theorem" else f"{kind} N{i} where\n  x : Nat\n" if kind == "structure" else f"{kind} inst{i} : Inhabited Nat := ⟨{i}⟩\n"
                blocks.append(doc + attr + body + rng.choice(["", "  more\n"]))
                names.append(f"n{i}" if kind in ("abbrev", "def", "theorem") else None)
            text = "namespace X\n\n" + "\n".join(blocks) + "\nend X\n"
            named = [i for i in range(len(blocks)) if names[i] and rng.random() < 0.5]
            log = "".join(log_for("Own/A.lean", text, "X." + names[i], f" {names[i]} :") for i in named)
            with tempfile.TemporaryDirectory() as t:
                lib = lib_with(Path(t), {"Own/A.lean": text})
                ud.remove(lib, ["Own"], log)
                out = (lib / "Own/A.lean").read_text()
            a, b = text.split("\n"), out.split("\n")
            self.assertEqual(len(a), len(b), text)
            changed = [i for i in range(len(a)) if a[i] != b[i]]
            for i in range(len(blocks)):
                if i in named:
                    self.assertNotIn(f" {names[i]} :", out, text)
                else:
                    keep = [l for l in blocks[i].split("\n") if l.strip()]
                    self.assertTrue(all(l in out for l in keep), (blocks[i], out))
            # nothing outside the named blocks moved or changed
            kept_lines = {l for i, blk in enumerate(blocks) if i not in named for l in blk.split("\n") if l.strip()}
            self.assertTrue(all(l in kept_lines or l.startswith("-- [Emissary] removed") or l in ("namespace X", "end X") or not l.strip() for l in b), (text, out))
            # nothing that is kept is lost or repeated: the sorted non-blank lines of the kept blocks are exactly the output's, notes and the file's own frame aside (a set would pass a repair that
            # deleted one of two identical lines of a retained block)
            kept_sorted = sorted(l for i, blk in enumerate(blocks) if i not in named for l in blk.split("\n") if l.strip())
            out_sorted = sorted(l for l in b if l.strip() and not l.startswith("-- [Emissary] removed") and l not in ("namespace X", "end X"))
            self.assertEqual(kept_sorted, out_sorted, (text, out))
            self.assertEqual(sum(1 for l in b if l.startswith("-- [Emissary] removed")), len(named))


class Mutants(unittest.TestCase):
    """Break the code the way the shortcut would; the invariants above must notice. (A surviving mutant means a test is missing.)"""

    def noticed(self, **patches):
        suite = unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromTestCase(Basics), unittest.defaultTestLoader.loadTestsFromTestCase(Structure), unittest.defaultTestLoader.loadTestsFromTestCase(Hostile)])
        result = unittest.TestResult()
        saved = {k: getattr(ud, k) for k in patches}
        try:
            for k, v in patches.items():
                setattr(ud, k, v)
            suite.run(result)
        finally:
            for k, v in saved.items():
                setattr(ud, k, v)
        return bool(result.failures or result.errors)

    def test_removing_instances_too_is_noticed(self):
        self.assertTrue(self.noticed(REMOVABLE={"abbrev", "def", "theorem", "lemma", "instance", "structure", "inductive", "class", "opaque"}))

    def test_ignoring_the_librarys_own_duplicates_is_noticed(self):
        self.assertTrue(self.noticed(declares=lambda code, last, skip=None: False))

    def test_a_block_that_ends_too_late_is_noticed(self):
        original = ud.block_bounds
        self.assertTrue(self.noticed(block_bounds=lambda lines, code, decl: (original(lines, code, decl)[0], len(lines))))

    def test_the_unmutated_code_is_not_noticed(self):
        self.assertFalse(self.noticed())


class Wiring(unittest.TestCase):
    def test_the_repair_rounds_of_both_workflows_use_it(self):
        for wf in ("bump-library.yml", "bump-shard.yml"):
            text = (HERE.parent.parent.parent / ".github" / "workflows" / wf).read_text()
            line = next(l for l in text.splitlines() if "engine.py repair" in l)
            self.assertIn("--upstream-duplicates", line, wf)

    def test_engine_runs_it_before_it_edits_imports_and_counts_it_as_a_change(self):
        src = (HERE.parent / "engine.py").read_text()
        self.assertLess(src.index("upstream_dups.remove"), src.index("# 2. imports of modules that no longer exist"))
        self.assertIn('summary["upstream_duplicates_removed"]', src.split('summary["changed"]')[1].split("\n")[0])


if __name__ == "__main__":
    unittest.main()
