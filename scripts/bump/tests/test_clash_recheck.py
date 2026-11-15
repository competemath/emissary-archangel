"""clash_recheck.py: the tree modules to build again before a name clash is believed, and the verify step that builds them.

The real case (15 Nov 2026, flt-anthropic, bump run 43686274801): the verify job seeded its tree from `cache-20261114T1152Z`, built only the new modules, and ModuleClashes.lean read every olean in
`.lake/build`. `fixtures/real-clashes-flt-stale-cache-2026-11-15.txt` is its output: five pairs, the library's Frey package and three Mathlib copies against `Tengoku.Flt.*` modules. The tree's own source
(`fixtures/real-tree-flt-freycurve-basic-excerpt-2026-11-14.lean`, main at ec6d359d, qualified by tengoku #799 on 14 Nov 15:09, four hours after that cache) declares `Tengoku.Flt.FreyPackage.freyCurveInt`,
not `FreyPackage.freyCurveInt`: the clash was read from the old olean. Four modules were refused for it, and with their importers 15,006 names.

Invariants: the modules built again are exactly the tree side of the pairs, each once; a line that is not a CLASH line says nothing; a name with a shell character or no `Tengoku.` prefix is refused; at most LIMIT.
The step: it comes after the build is read and before every scan that decides (the dups scan, the final clash scan); the modules are passed as separate arguments; its time is what the job has left; a helper that fails
builds nothing and refuses nothing; its files reach the artifact; no token. Mutants (each must fail a check): the new side built instead of the old one, the duplicates kept, the name check dropped, the step after the
dups scan, the step removed, the modules passed as one shell word list, the time cap dropped.
"""

from __future__ import annotations

import contextlib
import inspect
import io
import re
import sys
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import clash_recheck as cr  # noqa: E402

FX = HERE / "fixtures"
REAL = (FX / "real-clashes-flt-stale-cache-2026-11-15.txt").read_text()
TREE_SOURCE = (FX / "real-tree-flt-freycurve-basic-excerpt-2026-11-14.lean").read_text()
WORKFLOW = HERE.parents[2] / ".github" / "workflows" / "bump-sharded.yml"
STEP = "Build again the tree modules that a name clash names"
FIVE = [
    "Tengoku.Flt.FLT.FreyCurve.Basic",
    "Tengoku.Flt.FLT.FreyCurve.FreyPackage",
    "Tengoku.Flt.FLT.Mathlib.Algebra.IsDirectLimit",
    "Tengoku.Flt.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.RestrictedProduct",
    "Tengoku.Flt.FLT.Mathlib.Topology.Algebra.ContinuousSMulDiscrete",
]


def mutated(old: str, new: str):
    src = inspect.getsource(cr.others)
    assert src.count(old) == 1, old
    ns = dict(vars(cr))
    exec(src.replace(old, new), ns)
    return ns["others"]


class TheModules(unittest.TestCase):
    def test_the_real_log_names_five_tree_modules(self):
        self.assertEqual(cr.others(REAL), FIVE)
        self.assertEqual(len([ln for ln in REAL.splitlines() if ln.startswith("CLASH\t")]), 5)

    def test_it_is_the_tree_side_not_the_new_side(self):
        self.assertTrue(all(m.startswith("Tengoku.Flt.") for m in cr.others(REAL)))
        self.assertFalse(any("FltAnthropic" in m for m in cr.others(REAL)))

    def test_the_real_clash_was_read_from_an_old_olean(self):
        """The evidence, from the two real files: the log's first name is the unqualified one, and the tree's source has only the qualified one."""
        first = next(ln.split("\t")[4] for ln in REAL.splitlines() if ln.startswith("CLASH\t") and ln.split("\t")[2].endswith("FreyCurve.Basic"))
        self.assertEqual(first, "FreyPackage.freyCurveInt")
        self.assertIn("namespace Tengoku.Flt.FreyPackage", TREE_SOURCE)
        self.assertIn("def freyCurveInt", TREE_SOURCE)
        self.assertNotRegex(TREE_SOURCE, r"(?m)^namespace FreyPackage")  # no root namespace: the name in the log is not one the source can make

    def test_every_module_once_and_sorted(self):
        text = "CLASH\tTengoku.A.X\tTengoku.T.Z\t2\tf\nCLASH\tTengoku.B.Y\tTengoku.T.Z\t1\tg\nCLASH\tTengoku.A.W\tTengoku.T.A\t1\th\nclashes: 3 module pair(s), 4 name(s)\n"
        self.assertEqual(cr.others(text), ["Tengoku.T.A", "Tengoku.T.Z"])

    def test_lines_that_are_not_clashes_say_nothing(self):
        self.assertEqual(cr.others("clashes: 0 module pair(s), 0 name(s)\nwarning: x\n\nCLASH only\n"), [])
        self.assertEqual(cr.others(""), [])

    def test_a_name_that_is_not_a_plain_module_is_refused(self):
        for bad in ("Other.Mod", "Tengoku.A;rm -rf x", "Tengoku.A B", "Tengoku.A$(x)", "Tengoku.A`x`", "Tengoku.A|B", "Tengoku.A\"B", "Tengoku."):
            with self.assertRaises(SystemExit, msg=bad):
                cr.others(f"CLASH\tTengoku.N.X\t{bad}\t1\tf\n")

    def test_guillemets_survive(self):
        self.assertEqual(cr.others("CLASH\tTengoku.N.X\tTengoku.L.«1102.4662».A\t1\tf\n"), ["Tengoku.L.«1102.4662».A"])

    def test_at_most_the_limit(self):
        text = "".join(f"CLASH\tTengoku.N.X{i}\tTengoku.T.M{i:04d}\t1\tf\n" for i in range(cr.LIMIT + 20))
        got = cr.others(text)
        self.assertEqual(len(got), cr.LIMIT)
        self.assertEqual(got, sorted(got))

    def test_the_command_prints_one_module_per_line(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(cr.main(["others", str(FX / "real-clashes-flt-stale-cache-2026-11-15.txt")]), 0)
        self.assertEqual(out.getvalue().splitlines(), FIVE)
        err = io.StringIO()
        with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as stop:
            cr.main(["nonsense"])
        self.assertEqual(stop.exception.code, 2)

    def test_mutant_the_new_side_is_built(self):
        self.assertNotEqual(mutated('other = m.group("other")', 'other = m.group("new")')(REAL), FIVE)

    def test_mutant_duplicates_are_kept(self):
        text = "CLASH\tTengoku.A.X\tTengoku.T.Z\t2\tf\nCLASH\tTengoku.B.Y\tTengoku.T.Z\t1\tg\n"
        src = inspect.getsource(cr.others).replace("found: set[str] = set()", "found = []").replace("found.add(other)", "found.append(other)")
        ns = dict(vars(cr))
        exec(src, ns)
        self.assertNotEqual(ns["others"](text), ["Tengoku.T.Z"])

    def test_mutant_the_name_check_dropped(self):
        f = mutated("if not MODULE.fullmatch(other):", "if False:")
        self.assertEqual(f("CLASH\tTengoku.N.X\tTengoku.A;rm\t1\tf\n"), ["Tengoku.A;rm"])  # what the check refuses


def load(text: str) -> dict:
    return yaml.safe_load(text)


def names(doc: dict) -> list[str]:
    return [s.get("name", "") for s in doc["jobs"]["verify"]["steps"]]


def order_ok(doc: dict) -> bool:
    n = names(doc)
    try:
        accepted = next(i for i, x in enumerate(n) if x.startswith("What the build accepted"))
        refresh = next(i for i, x in enumerate(n) if x.startswith(STEP))
        dups = next(i for i, x in enumerate(n) if x.startswith("Copies of tree modules in the draft"))
        final = next(i for i, x in enumerate(n) if x.startswith("The names that two modules"))
    except StopIteration:
        return False
    return accepted < refresh < dups < final


class TheStep(unittest.TestCase):
    text = WORKFLOW.read_text(encoding="utf-8")
    doc = load(text)

    def step(self) -> dict:
        found = [s for s in self.doc["jobs"]["verify"]["steps"] if s.get("name", "").startswith(STEP)]
        self.assertEqual(len(found), 1)
        return found[0]

    def test_it_comes_after_the_build_is_read_and_before_every_scan_that_decides(self):
        self.assertTrue(order_ok(self.doc))

    def test_it_builds_the_modules_as_separate_arguments(self):
        run = self.step()["run"]
        self.assertIn("python3 emissary/scripts/bump/clash_recheck.py others out/clashes-first.txt > out/clash-others.txt", run)
        self.assertIn('mapfile -t og < out/clash-others.txt', run)
        self.assertIn('lake build "${og[@]}"', run)

    def test_its_time_is_what_the_job_has_left(self):
        run = self.step()["run"]
        self.assertIn("cap=$(( (JOB_START + 355 * 60 - $(date +%s)) / 60 - 110 )); [ \"$cap\" -gt 45 ] && cap=45", run)
        self.assertIn('timeout -k 60 "$(( cap - 10 ))m" lake build', run)
        self.assertEqual(self.doc["jobs"]["verify"]["timeout-minutes"], 355)  # the 355 in the formula is the job's own limit
        self.assertIn('if [ "$cap" -ge 15 ]; then', run)  # the scan takes up to 10 minutes: less than 15 left builds nothing

    def test_a_helper_that_fails_builds_nothing_and_refuses_nothing(self):
        run = self.step()["run"]
        self.assertIn('|| { echo "::warning::the modules of the clashes could not be read: nothing is built again"; : > out/clash-others.txt; }', run)
        self.assertIn("set +e", run)  # a lake build that fails leaves the oleans as they were; the scans below decide

    def test_it_refuses_no_module_itself(self):
        run = self.step()["run"]
        self.assertNotIn("tree_verify.py", run)
        self.assertNotIn("failing", run)

    def test_its_files_reach_the_artifact(self):
        up = next(s for s in self.doc["jobs"]["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        for f in ("out/clashes-first.txt", "out/clash-others.txt", "out/clash-refresh.log"):
            self.assertIn(f, up)

    def test_it_holds_no_token(self):
        self.assertNotIn("env", self.step())
        self.assertNotIn("secrets.", self.step()["run"])

    def test_the_scan_it_runs_is_the_one_the_verdict_runs(self):
        run = self.step()["run"]
        self.assertIn("lake env lean --run ../emissary/scripts/bump/ModuleClashes.lean .lake/build/lib/lean ../out/built.txt Tengoku", run)

    def test_mutant_the_step_after_the_dups_scan(self):
        i = self.text.index("      # The tree's cache may be older than the tree.")
        j = self.text.index("      # COPIES OF TREE MODULES")
        block = self.text[i:j]
        moved = self.text[:i] + self.text[j:]
        k = moved.index("      - name: The names that two modules of the tree both declare")
        self.assertFalse(order_ok(load(moved[:k] + block + moved[k:])))

    def test_mutant_the_step_removed(self):
        i = self.text.index("      # The tree's cache may be older than the tree.")
        j = self.text.index("      # COPIES OF TREE MODULES")
        self.assertFalse(order_ok(load(self.text[:i] + self.text[j:])))

    def test_mutant_one_word_list_instead_of_an_array(self):
        run = self.step()["run"]
        self.assertNotIn("lake build $(", run)  # a list the shell splits again
        self.assertNotIn("lake build $og", run)
        mutant = run.replace('lake build "${og[@]}"', "lake build $(cat out/clash-others.txt)")
        self.assertIn("lake build $(", mutant)  # the check above sees the mutant

    def test_mutant_the_time_cap_dropped(self):
        run = self.step()["run"]
        mutant = run.replace('timeout -k 60 "$(( cap - 10 ))m" ', "")
        self.assertNotEqual(mutant, run)
        self.assertNotIn("timeout -k 60", mutant.split("lake build")[0].splitlines()[-1])  # the line that builds has no timeout: the budget test below reads `timeout` and fails on it
        self.assertIsNone(re.search(r'timeout -k 60 "\$\(\( cap - 10 \)\)m" lake build', mutant))


class TheBudgets(unittest.TestCase):
    def test_the_other_budgets_still_fit_the_job(self):
        """the refresh takes what is left over 110 minutes and at most 45 + 10 of its own scan; the static budgets of the build and the scans are tested in test_bump_sharded_verify.py"""
        doc = load(WORKFLOW.read_text(encoding="utf-8"))
        run = next(s for s in doc["jobs"]["verify"]["steps"] if s.get("name", "").startswith(STEP))["run"]
        scan = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", run).group(1))
        cap = int(re.search(r'\[ "\$cap" -gt (\d+) \] && cap=\d+', run).group(1))
        self.assertLessEqual(scan + cap, 55)
        self.assertLessEqual(scan + cap + 110, doc["jobs"]["verify"]["timeout-minutes"])


if __name__ == "__main__":
    unittest.main()
