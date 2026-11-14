"""The factory's count of what it changed includes the removed printing commands (grind_sets.shipped_changes, open_intake_pr.changes_line).

The real case: tda-lib part 1 (competemath/tengoku#826, 14 Nov 2026). Gitar read the part's files and found 4 changed modules and 13 removed lines where the PR said 2 modules and 3 lines: the 11
`/-! Tengoku repair: removed `#print axioms ...` -/` notes of two modules (bundle.py print_note) were never counted, and the description said every changed file carries a notice naming the upstream
commit, which a repair note does not. fixtures/tda-lib-826/ holds three of that part's real files: AlgebraicFamily.lean (one change notice, 2 inert lines), CompatibleOrder.lean (1 repair note),
CompatibleOrderExistence.lean (10 repair notes).
Invariants: every repair note of the shipped files is counted (exactly the lines of the files), a module with only repair notes counts as changed, a module with both counts once, the notes bundle.py
writes are the notes grind_sets reads, files without notes count nothing, the description says what the notes are. Mutants (each must fail a check): the repair notes not counted; a repair-only
module not counted as changed; a module with both counted twice.
"""

import inspect
import random
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import bundle  # noqa: E402
import grind_sets as gs  # noqa: E402
import open_intake_pr as oip  # noqa: E402

FX = HERE / "fixtures" / "tda-lib-826"
TEXT = {p.stem: p.read_text(encoding="utf-8") for p in sorted(FX.glob("*.lean"))}
REAL = ["AlgebraicFamily", "CompatibleOrder", "CompatibleOrderExistence"]
NOTES = re.compile(r"Tengoku repair: removed `#print axioms ")


def expected(texts):
    """what the files hold, counted apart from the code under test: lines with a repair note, files with any note or notice"""
    printed = sum(len(NOTES.findall(t)) for t in texts)
    changed = sum(1 for t in texts if NOTES.search(t) or "Tengoku change notice" in t)
    return printed, changed


class RealPart(unittest.TestCase):
    def test_the_real_files(self):
        self.assertEqual(sorted(TEXT), REAL)
        self.assertEqual({k: len(NOTES.findall(v)) for k, v in TEXT.items()}, {"AlgebraicFamily": 0, "CompatibleOrder": 1, "CompatibleOrderExistence": 10})

    def test_the_part_counts_what_gitar_counted(self):
        got = gs.shipped_changes(TEXT[k] for k in REAL)
        self.assertEqual(got, {"modules changed": 3, "inert lines removed": 2, "print lines removed": 11})  # the PR said 2 modules and 3 lines for 4 modules and 13 lines in all

    def test_each_file_alone(self):
        self.assertEqual(gs.shipped_changes([TEXT["CompatibleOrder"]]), {"modules changed": 1, "print lines removed": 1})
        self.assertEqual(gs.shipped_changes([TEXT["CompatibleOrderExistence"]]), {"modules changed": 1, "print lines removed": 10})
        self.assertEqual(gs.shipped_changes([TEXT["AlgebraicFamily"]]), {"modules changed": 1, "inert lines removed": 2})

    def test_5000_random_parts_against_a_count_made_apart(self):
        rng = random.Random(14)
        pool = list(TEXT.values()) + ["theorem t : True := trivial\n", ""]
        for _ in range(5000):
            texts = [rng.choice(pool) for _ in range(rng.randrange(0, 9))]
            printed, changed = expected(texts)
            got = gs.shipped_changes(texts)
            self.assertEqual(got.get("print lines removed", 0), printed)
            self.assertEqual(got.get("modules changed", 0), changed)

    def test_a_module_with_a_notice_and_a_repair_note_counts_once(self):
        both = TEXT["AlgebraicFamily"] + "\n" + TEXT["CompatibleOrder"].split("\n")[8] + "\n"
        self.assertIn("Tengoku change notice", both)
        self.assertIn("Tengoku repair: removed", both)
        self.assertEqual(gs.shipped_changes([both]), {"modules changed": 1, "inert lines removed": 2, "print lines removed": 1})

    def test_what_bundle_writes_is_what_grind_sets_reads(self):
        rng = random.Random(3)
        for _ in range(2000):
            cmd = "#print axioms " + ".".join(rng.choice(["Foo", "bar", "baz_1", "A'", "x"]) for _ in range(rng.randrange(1, 5)))
            self.assertEqual(gs.shipped_changes(["import A\n\n" + bundle.print_note(cmd) + "\ntheorem t : True := trivial\n"]), {"modules changed": 1, "print lines removed": 1}, cmd)

    def test_other_text_is_not_a_repair_note(self):
        for t in ("-- Tengoku repair: removed `#print axioms X`", "/-! Tengoku repair: removed `#eval 1` (it only prints; x). -/", "/-! removed `#print axioms X` (it only prints;"):
            self.assertEqual(gs.shipped_changes([t]), {}, t)


class Description(unittest.TestCase):
    def test_the_sentence_says_what_the_notes_are(self):
        line = oip.changes_line({"factory_changes": {"modules changed": 3, "inert lines removed": 2, "print lines removed": 11}})
        self.assertIn("print lines removed: 11", line)
        self.assertIn("a repair note for a removed `#print` command", line)
        self.assertNotIn("each changed file carries a change notice naming the upstream commit and the change", line)  # a repair note names no commit
        self.assertEqual(oip.changes_line({"factory_changes": {}}), "")


class Mutants(unittest.TestCase):
    def broken(self, old, new):
        src = inspect.getsource(gs.shipped_changes)
        self.assertEqual(src.count(old), 1, old)
        ns = dict(vars(gs))
        exec(src.replace(old, new), ns)
        return ns["shipped_changes"]

    def test_mutant_the_repair_notes_not_counted(self):
        f = self.broken("printed = len(PRINT_REPAIR.findall(text))", "printed = 0")
        self.assertNotEqual(f(TEXT[k] for k in REAL), {"modules changed": 3, "inert lines removed": 2, "print lines removed": 11})

    def test_mutant_a_repair_only_module_not_counted_as_changed(self):
        f = self.broken("if not m and not printed:", "if not m:")
        self.assertNotEqual(f(TEXT[k] for k in REAL)["modules changed"], 3)

    def test_mutant_a_module_with_both_counted_twice(self):
        f = self.broken("        stats[\"modules changed\"] += 1\n        stats[\"print lines removed\"] += printed\n", "        stats[\"modules changed\"] += 1 + (1 if (m and printed) else 0)\n        stats[\"print lines removed\"] += printed\n")
        both = TEXT["AlgebraicFamily"] + "\n" + TEXT["CompatibleOrder"].split("\n")[8] + "\n"
        self.assertNotEqual(f([both])["modules changed"], 1)


if __name__ == "__main__":
    unittest.main()
