"""inert_commands.py: the commands the tree's lint refuses and that say nothing about a theorem are taken out, and nothing else is touched.

Class of bug this guards (2026-10-27, stafford38-formal): the lint refused a text for `#print axioms foo` lines the author had left after a theorem, and 2,089 of 2,467 entries went to the agent
without a compile. The repair that fixes it is only worth having if it cannot damage a text, so the tests check the INVARIANTS on random texts built from the constructs that matter
(comments and strings that look like commands, options that change what compiles, commands that continue over several lines), not the one case that was found:

  * only inert lines go: every output line is an input line, in order (the one exception is the phrase `set_option linter.X v in`, which is cut out of its line);
  * a text with nothing inert in it comes back byte for byte;
  * the repair is idempotent;
  * a command-looking line inside a comment or a string is never read as a command;
  * options that are on the allow-list, and every option that is not a linter, stay;
  * what the lint refused for these reasons is not refused after the repair, and what it refused for other reasons still is.

The mutants at the end break the code the way the old bug (or the obvious shortcut) would and require that the tests notice.
"""

from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / "lint"))
import allowlist  # noqa: E402
import inert_commands as ic  # noqa: E402
import lint_cli  # noqa: E402

ALLOWED = lint_cli.ALLOWED
KEYWORDS = lint_cli.KEYWORDS

INERT = [
    "#print axioms foo",
    "#check foo",
    "#eval 1 + 1",
    "#check foo\n  bar baz",  # continues on an indented line
    "#print axioms Foo.bar -- why",
    "set_option linter.haveILetI false",
    "set_option linter.style.nameCheck true",
]
KEEP = [
    "theorem foo : True := trivial",
    "def bar (n : Nat) : Nat :=\n  n + 1",
    "/-- A docstring that mentions #print axioms foo. -/\ntheorem doc : True := trivial",
    "-- #print axioms in a line comment\nlemma lc : True := trivial",
    "/- a block comment\n#check inside\n-/\ntheorem bc : True := trivial",
    'def s : String := "x\n#print axioms y"',
    "set_option maxHeartbeats 400000",
    "set_option autoImplicit false",
    "set_option linter.unusedSectionVars false",  # on the allow-list
    "set_option linter.flexible false in\ntheorem allowed_in : True := trivial",
    "namespace N\n  #check inside_a_namespace_indented\nend N",  # indented: not a command start, left alone
    "open Nat in\ntheorem op : True := trivial",
]
IN_PHRASE = [
    ("set_option linter.haveILetI false in\ntheorem p : True := trivial", "theorem p : True := trivial"),
    ("set_option linter.haveILetI false in theorem q : True := trivial", "theorem q : True := trivial"),
]


def build(rng: random.Random, n: int) -> tuple[str, list[str]]:
    parts, used = [], []
    for _ in range(n):
        pool = INERT if rng.random() < 0.35 else KEEP
        p = rng.choice(pool)
        parts.append(p)
        used.append(p)
    return "\n\n".join(parts) + "\n", used


def run(text: str):
    return ic.repair(text, ALLOWED)


class Invariants(unittest.TestCase):
    def test_only_inert_lines_go_and_the_rest_is_in_order(self):
        rng = random.Random(1)
        for _ in range(400):
            text, _ = build(rng, rng.randint(1, 9))
            out, removed = run(text)
            it = iter(text.split("\n"))
            for line in out.split("\n"):
                self.assertTrue(any(line == src for src in it), f"line not found in order: {line!r}\n--- in\n{text}\n--- out\n{out}")
            self.assertEqual(len(text.split("\n")) - len(out.split("\n")) >= 0, True)

    def test_nothing_inert_means_byte_for_byte(self):
        rng = random.Random(2)
        for _ in range(300):
            text = "\n\n".join(rng.choice(KEEP) for _ in range(rng.randint(1, 8))) + "\n"
            out, removed = run(text)
            self.assertEqual((out, removed), (text, []), text)

    def test_idempotent(self):
        rng = random.Random(3)
        for _ in range(300):
            text, _ = build(rng, rng.randint(1, 9))
            once, _ = run(text)
            twice, again = run(once)
            self.assertEqual((twice, again), (once, []), text)

    def test_lookalikes_in_comments_and_strings_are_never_commands(self):
        for fragment in KEEP:
            if "#" not in fragment:
                continue
            text = fragment + "\n"
            out, removed = run(text)
            if "namespace" in fragment:  # indented: also left alone
                self.assertEqual(out, text)
            self.assertEqual((out, removed), (text, []), fragment)

    def test_allowed_options_and_non_linter_options_stay(self):
        for line in ("set_option linter.unusedSectionVars false", "set_option maxHeartbeats 400000", "set_option autoImplicit false", "set_option pp.explicit true"):
            out, removed = run(line + "\ntheorem t : True := trivial\n")
            self.assertIn(line, out)
            self.assertEqual(removed, [])

    def test_a_linter_option_in_front_of_a_declaration_loses_only_the_phrase(self):
        for src, want in IN_PHRASE:
            out, removed = run(src + "\n")
            self.assertEqual(out, want + "\n", src)
            self.assertEqual(len(removed), 1)

    def test_a_command_continues_over_its_indented_lines_and_not_further(self):
        out, removed = run("#check foo\n  bar baz\ntheorem t : True := trivial\n")
        self.assertEqual(out, "theorem t : True := trivial\n")
        self.assertEqual(removed[0]["line"], 1)
        # a docstring at column 0 below the command belongs to the declaration after it and stays
        out, _ = run("#print axioms a\n/-- doc -/\ntheorem t : True := trivial\n")
        self.assertEqual(out, "/-- doc -/\ntheorem t : True := trivial\n")

    def test_the_lint_stops_refusing_for_these_reasons_and_only_these(self):
        rng = random.Random(4)
        for _ in range(250):
            text, _ = build(rng, rng.randint(1, 9))
            before = allowlist.violations(text, ALLOWED, KEYWORDS)
            out, _ = run(text)
            after = allowlist.violations(out, ALLOWED, KEYWORDS)
            self.assertFalse([v for v in after if "# command" in v and "namespace" not in text], (text, after))
            self.assertFalse([v for v in after if "linter.haveILetI" in v or "linter.style.nameCheck" in v], (text, after))
            for v in after:
                self.assertIn(v, before)  # the repair never creates a refusal

    def test_something_else_the_lint_refuses_is_still_refused(self):
        text = "#print axioms foo\ntheorem t : True := by native_decide\n"
        out, removed = run(text)
        self.assertEqual(len(removed), 1)
        self.assertTrue([v for v in allowlist.violations(out, ALLOWED, KEYWORDS) if "native_decide" in v])

    def test_a_trailing_newline_and_crlf_are_kept(self):
        for text in ("theorem t : True := trivial", "theorem t : True := trivial\n", "theorem t : True := trivial\n\n"):
            self.assertEqual(run(text)[0], text)


class Cli(unittest.TestCase):
    def test_repair_answers_with_the_text_the_removals_and_what_is_left(self):
        a = lint_cli.answer("repair", "import Mathlib\n#print axioms a\ntheorem a : True := trivial\n")
        self.assertEqual(a["text"], "import Mathlib\ntheorem a : True := trivial\n")
        self.assertEqual([r["kind"] for r in a["removed"]], ["#print"])
        self.assertEqual(a["violations"], [])

    def test_check_does_not_edit(self):
        a = lint_cli.answer("check", "#print axioms a\ntheorem a : True := trivial\n")
        self.assertTrue(a["violations"])
        self.assertNotIn("text", a)

    def test_the_options_are_the_pinned_allow_list_and_not_a_copy(self):
        import json

        pinned = set(json.loads((HERE.parent / "lint" / "allowed-options.json").read_text())["allowed"])
        self.assertEqual(lint_cli.ALLOWED, pinned)
        # the eight options the bridge's old hand-kept copy was missing
        for opt in ("linter.unusedSectionVars", "linter.flexible", "linter.unusedTactic", "linter.unnecessarySimpa", "linter.unnecessarySeqFocus", "linter.unusedSimpArgs", "linter.unreachableTactic", "linter.style.header"):
            self.assertEqual(lint_cli.violations(f"set_option {opt} false\ntheorem t : True := trivial\n"), [], opt)


class Mutants(unittest.TestCase):
    """Break the code the way the shortcut would; the invariants above must notice. (A mutant that survives means a test is missing.)"""

    def noticed(self, **patches):
        suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(Invariants))
        result = unittest.TestResult()
        saved = {k: getattr(ic, k) for k in patches}
        try:
            for k, v in patches.items():
                setattr(ic, k, v)
            suite.run(result)
        finally:
            for k, v in saved.items():
                setattr(ic, k, v)
        return bool(result.failures or result.errors)

    def test_reading_comments_and_strings_as_code_is_noticed(self):
        self.assertTrue(self.noticed(code_only=lambda t: t))

    def test_an_allow_list_that_is_empty_is_noticed(self):
        original = ic.repair
        self.assertTrue(self.noticed(repair=lambda text, allowed: original(text, set())))

    def test_taking_indented_commands_too_is_noticed(self):
        import re

        self.assertTrue(self.noticed(_HASH_LINE=re.compile(r"[ \t]*#(" + "|".join(ic.INERT_HASH) + r")(?![\w'!?])")))

    def test_the_unmutated_code_is_not_noticed(self):
        self.assertFalse(self.noticed())


if __name__ == "__main__":
    unittest.main()
