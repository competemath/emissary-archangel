"""Class-level tests of `bundle.py compose` with the tree's verdicts: what ships, on random libraries, random refusals, random aliased copies and random repairs.

The invariants hold for every library, so a new way of editing or dropping modules cannot break them without a test failing, whatever the example:

  * CLOSED: every library module a shipped file imports is shipped (the umbrella lists exactly the shipped files). Navier 2026-10-21: an aliased copy's own imports were not shipped and not imported by
    its importers (`unknown namespace`), 72 modules refused and 971 with their importers.
  * EXACT CONE: with tree failures F, what is dropped is exactly F and everything that imports F (the verdict's notion of 'importer' and the cut's must be one notion; Navier: the verdict said 0 more
    modules go with the refused ones, the cut dropped 971).
  * NO PHANTOM: a theorem of a module that does not ship is not in the manifest, and every shipped module's theorems are there.
  * ACCOUNTING: shipped + left out == passed, for every mode (nothing is missing without a reason).
  * ALIAS: an aliased copy is not shipped, nothing imports it, and what imported it imports the tree's module AND what the copy imported.
  * REPAIR LAST: a repair planned on the bytes of the importers' build is made after the alias and fork edits, byte for byte.
  * THE TREE DECIDES: a module a text rule flags (it declares a record the tree already has) is dropped with its importers when no tree check ran; when the tree built it and refused it by none of its
    checks it ships, with the records the tree already has left out of the manifest and counted; when a tree check refused it, it goes with its importers as any refused module does (Navier recut 10:
    16 such modules, 5,875 theorems with their importers).
"""

from __future__ import annotations

import contextlib
import io
import json
import random
import re
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import tree_dups as td  # noqa: E402
import tree_repair as tr  # noqa: E402
import test_bundle  # noqa: E402  (the module, not its test classes)

SEEDS = range(60)
ROOT = ("bundle-proposed", "Tengoku", "ToyLib", "Toy")


class Case:
    def __init__(self, seed: int):
        self.seed = seed
        self.rnd = random.Random(seed)
        n = self.rnd.randint(3, 11)
        self.mods = [f"M{i}" for i in range(n)]
        self.imports = {m: sorted(self.rnd.sample(self.mods[:i], self.rnd.randint(0, min(i, 3)))) for i, m in enumerate(self.mods)}
        # a module with no theorem is no root of the cut: it ships only when something that ships imports it (through an aliased copy too), which is what keeps the 'closed' invariant honest
        self.has_theorem = {m: self.rnd.random() > 0.35 for m in self.mods}
        self.files = {m: "".join(f"import Toy.{j}\n" for j in self.imports[m]) + "\nnamespace Toy\n\n" + (f"theorem t_{m} : 1 = 1 := rfl\n\ntheorem u_{m} : 1 = 1 := rfl" if self.has_theorem[m] else f"def d_{m} : Nat := 1") + "\n\nend Toy\n" for m in self.mods}
        self.passed = {f"Toy.{m}": [f"Toy.t_{m}", f"Toy.u_{m}"] for m in self.mods if self.has_theorem[m]}  # two theorems: the flagged one (a record of the tree) and one that is not
        self.harness = type("Harness", (), {"FILES": self.files, "PASSED": self.passed, "leaks_in_leaky": staticmethod(test_bundle.AutoDrops.leaks_in_leaky)})()

    def importers(self, roots: set[str]) -> set[str]:
        out, todo = set(), list(roots)
        while todo:
            x = todo.pop()
            for m in self.mods:
                if x in self.imports[m] and m not in out:
                    out.add(m)
                    todo.append(m)
        return out

    def expected_shipped(self, gone: set[str], aliased: set[str]) -> set[str]:
        """the oracle: the modules that ship are the imports (an aliased copy is transparent: what it imported counts) of the modules that have a theorem, are not aliased and are not gone"""
        need: set[str] = set()
        todo = [m for m in self.mods if self.has_theorem[m] and m not in gone and m not in aliased]
        while todo:
            m = todo.pop()
            if m in need or m in gone:
                continue
            if m in aliased:
                todo.extend(self.imports[m])
                continue
            need.add(m)
            todo.extend(self.imports[m])
        return need

    def compose(self, *, failures: set[str] = frozenset(), aliases: set[str] = frozenset(), repairs: dict | None = None, records: set[str] = frozenset(), verified: bool = False, keep_dups: bool = False,
                verdict_only: bool = False):
        """`records`: modules whose theorem is a record the tree already has (`--tree-names`); `verified`: the tree's checks ran (a failures file, even an empty one, and a verdict); `keep_dups`: the flag"""
        extra: list[str] = []
        tmp = Path(tempfile.mkdtemp())
        if (failures or verified) and not verdict_only:
            (tmp / "failures.txt").write_text("".join(f"Toy.{m}\n" for m in sorted(failures)))
            extra += ["--tree-failures", str(tmp / "failures.txt")]
        if records:
            extra += ["--tree-names", "@names"]
        if keep_dups and not (aliases or repairs):
            extra += ["--keep-dups"]
        if (verified or verdict_only) and not (aliases or repairs):
            (tmp / "dups.json").write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": {"aliases": {}, "alias_keep": {}, "not_same": {}, "refused": {}, "forks": {}, "forked": [], "fork_namespace": "", "forks_identical": [], "repairs": {}}}}))
            extra += ["--keep-dups", "--tree-dups", str(tmp / "dups.json")]
        if aliases or repairs:
            texts = {f"Tengoku.ToyLib.Toy.{m}": self.files[m].replace("import Toy.", "import Tengoku.ToyLib.Toy.") for m in self.mods}
            al = {f"Tengoku.ToyLib.Toy.{m}": [f"Tengoku.Other.Lib.{m}"] for m in aliases}
            keep = td.alias_keep(al, texts)
            spec = {"aliases": {f"Toy.{m}": [f"Tengoku.Other.Lib.{m}"] for m in aliases}, "alias_keep": {k.replace("Tengoku.ToyLib.", ""): v for k, v in keep.items()},
                    "not_same": {}, "refused": {}, "forks": {}, "forked": [], "fork_namespace": "", "forks_identical": [], "repairs": repairs or {}}
            (tmp / "dups.json").write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": spec}}))
            extra += ["--keep-dups", "--tree-dups", str(tmp / "dups.json")]
        with contextlib.redirect_stdout(io.StringIO()):  # compose prints its summaries
            return test_bundle.AutoDrops.compose(self.harness, [f"Toy.t_{m}" for m in sorted(records)], *extra, files=list(self.mods))

    def shipped_files(self, d: Path) -> dict[str, str]:
        root = d.joinpath(*ROOT)
        return {f.stem: f.read_text() for f in root.glob("*.lean")} if root.is_dir() else {}


def library_imports(text: str) -> list[str]:
    return re.findall(r"^(?:public )?import Tengoku\.ToyLib\.Toy\.(\w+)", text, re.M)


class Closed(unittest.TestCase):
    def check_invariants(self, case: Case, d: Path, p, *, gone: set[str], aliased: set[str]):
        self.assertEqual(p.returncode, 0, f"seed {case.seed}: {p.stderr}")
        shipped = case.shipped_files(d)
        want = case.expected_shipped(gone, aliased)
        self.assertEqual(set(shipped), want, f"seed {case.seed}: EXACT CONE / ALIAS / TRANSPARENT: what ships is not the imports of the modules with a theorems, minus failures, importers of failures and aliased copies")
        umbrella = (d / "bundle-proposed" / "Tengoku" / "ToyLib.lean").read_text()
        self.assertEqual(set(re.findall(r"import Tengoku\.ToyLib\.Toy\.(\w+)", umbrella)), set(shipped), f"seed {case.seed}: CLOSED: the umbrella lists exactly what ships")
        for m, text in shipped.items():
            for dep in library_imports(text):
                self.assertIn(dep, shipped, f"seed {case.seed}: CLOSED: {m} ships and imports {dep}, which does not")
            self.assertNotIn("import Toy.", text, f"seed {case.seed}: an import was left in the library's spelling")
        manifest = [json.loads(x)["module"] for x in (d / "bundle-proposed" / "manifest.jsonl").read_text().splitlines()]
        self.assertEqual({m.rsplit(".", 1)[1] for m in manifest}, {m for m in shipped if case.has_theorem[m]}, f"seed {case.seed}: NO PHANTOM: the manifest names the theorems of the modules that ship, and only those")
        rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(rep["theorems"] + sum(rep["left_out"].values()), rep["passed_total"], f"seed {case.seed}: ACCOUNTING")

    def test_tree_failures_drop_exactly_their_cone(self):
        for seed in SEEDS:
            case = Case(seed)
            failures = {m for m in case.mods if case.rnd.random() < 0.2}
            d, p = case.compose(failures=failures)
            self.check_invariants(case, d, p, gone=failures | case.importers(failures), aliased=set())

    def test_an_aliased_copy_leaves_and_its_importers_stay_with_everything_the_copy_imported(self):
        for seed in SEEDS:
            case = Case(seed)
            aliased = {m for m in case.mods if case.rnd.random() < 0.25}
            d, p = case.compose(aliases=aliased)
            self.check_invariants(case, d, p, gone=set(), aliased=aliased)
            for m, text in case.shipped_files(d).items():
                deps = library_imports(text)
                for a in aliased:
                    if a in case.imports[m]:
                        self.assertIn(f"import Tengoku.Other.Lib.{a}", text, f"seed {seed}: ALIAS: {m} imported {a}, it imports the tree's module now")
                        for k in case.imports[a]:
                            self.assertTrue(k in deps or k in aliased, f"seed {seed}: ALIAS: {m} lost {k}, which the aliased {a} imported")

    def test_failures_and_aliases_together(self):
        for seed in SEEDS:
            case = Case(seed)
            failures = {m for m in case.mods if case.rnd.random() < 0.15}
            gone = failures | case.importers(failures)
            aliased = {m for m in case.mods if m not in gone and case.rnd.random() < 0.25}
            d, p = case.compose(failures=failures, aliases=aliased)
            self.check_invariants(case, d, p, gone=gone, aliased=aliased)


class TheTreeDecides(unittest.TestCase):
    """A module flagged by a text rule (`--tree-names`: it proves a record the tree already has) and what happens to it."""

    def flagged(self, case: Case) -> set[str]:
        return {m for m in case.mods if case.has_theorem[m] and case.rnd.random() < 0.3}

    def manifest(self, d: Path) -> set[str]:
        return {json.loads(x)["name"] for x in (d / "bundle-proposed" / "manifest.jsonl").read_text().splitlines()}

    def test_with_no_tree_check_a_flagged_module_goes_with_its_importers(self):
        for seed in SEEDS:
            case = Case(seed)
            flagged = self.flagged(case)
            d, p = case.compose(records=flagged)  # no --keep-dups: the cut as it was
            Closed().check_invariants(case, d, p, gone=flagged | case.importers(flagged), aliased=set())

    def test_with_a_verdict_but_no_record_of_the_tree_building_it_is_dropped_as_well(self):
        """the final cut with the dups verdict but without the tree's failures file: nothing says the tree built the module, so the text rule stands"""
        for seed in SEEDS[:60]:
            case = Case(seed)
            flagged = self.flagged(case)
            d, p = case.compose(records=flagged, verdict_only=True)
            Closed().check_invariants(case, d, p, gone=flagged | case.importers(flagged), aliased=set())

    def test_when_the_tree_built_it_and_refused_nothing_it_ships_and_its_records_are_not_made_again(self):
        done = 0
        for seed in SEEDS:
            case = Case(seed)
            flagged = self.flagged(case)
            failures = {m for m in case.mods if case.rnd.random() < 0.1}
            gone = failures | case.importers(failures)
            d, p = case.compose(records=flagged, verified=True, failures=failures)
            self.assertEqual(p.returncode, 0, p.stderr)
            shipped = case.shipped_files(d)
            # the flag drops nothing the tree did not refuse: what ships is what ships without the flag
            self.assertEqual(set(shipped), case.expected_shipped(gone, set()), f"seed {seed}: THE TREE DECIDES: the flag changed what ships")
            names = self.manifest(d)
            for m in shipped:
                if case.has_theorem[m]:
                    self.assertEqual(f"Toy.t_{m}" in names, m not in flagged, f"seed {seed}: {m}: a record the tree has is not made again, any other is")
                    self.assertIn(f"Toy.u_{m}", names, f"seed {seed}: {m}: only the record the tree has is left out, not the module's other theorems")
            for m in flagged:
                self.assertNotIn(f"Toy.t_{m}", names)
            rep = json.loads((d / "bundle-proposed" / "report.json").read_text())
            self.assertEqual(rep["theorems"] + sum(rep["left_out"].values()), rep["passed_total"], f"seed {seed}: ACCOUNTING")
            omitted = {m for m in flagged if m in shipped}
            self.assertEqual(set(rep["dups"]["tolerated_records_not_made_again"]), {f"Toy.{m}" for m in omitted}, f"seed {seed}")
            self.assertEqual(sum(len(v) for v in rep["dups"]["tolerated_records_not_made_again"].values()), len(omitted), f"seed {seed}")
            done += len(omitted)
        self.assertGreater(done, 20, "the generator found too few shipped flagged modules")

    def test_a_flagged_module_the_tree_refused_goes_with_its_importers(self):
        for seed in SEEDS:
            case = Case(seed)
            flagged = self.flagged(case)
            failures = flagged & {m for m in flagged if case.rnd.random() < 0.5}
            gone = failures | case.importers(failures)
            d, p = case.compose(records=flagged, verified=True, failures=failures)
            self.assertEqual(p.returncode, 0, p.stderr)
            self.assertEqual(set(case.shipped_files(d)), case.expected_shipped(gone, set()), f"seed {seed}: a module a tree check refused must go, flagged or not")


class RepairLast(unittest.TestCase):
    def test_a_repair_of_the_importers_build_is_made_last_whatever_the_alias_edit_did(self):
        """REPAIR LAST. For a random aliased copy and a random importer, the repair planned on the bytes the importers' build had is what ships."""
        done = 0
        for seed in SEEDS:
            case = Case(seed)
            aliased = {m for m in case.mods if case.rnd.random() < 0.3}
            importers = [m for m in case.mods if m not in aliased and case.has_theorem[m] and any(a in case.imports[m] for a in aliased)]
            if not importers:
                continue
            m = case.rnd.choice(importers)
            d0, p0 = case.compose(aliases=aliased)
            self.assertEqual(p0.returncode, 0, p0.stderr)
            built = case.shipped_files(d0)[m]  # the bytes of the importers' build: the alias edit made
            line = built.split("\n").index(f"theorem t_{m} : 1 = 1 := rfl") + 1
            repairs, _ = tr.plan_text(built, [{"line": line, "option": "synthInstance.maxHeartbeats", "limit": 20000}])
            fixed = tr.repair_text(built, repairs)
            entry = {"module": f"Tengoku.ToyLib.Toy.{m}", "path": f"Tengoku/ToyLib/Toy/{m}.lean", "before": tr.sha256(built), "after": tr.sha256(fixed), "repairs": repairs}
            d1, p1 = case.compose(aliases=aliased, repairs={f"Toy.{m}": entry})
            self.assertEqual(p1.returncode, 0, p1.stderr)
            self.assertEqual(case.shipped_files(d1)[m], fixed, f"seed {seed}")
            for other, text in case.shipped_files(d0).items():
                if other != m:
                    self.assertEqual(case.shipped_files(d1)[other], text, f"seed {seed}: a repair of {m} changed {other}")
            done += 1
        self.assertGreater(done, 10, "the generator found too few cases")


if __name__ == "__main__":
    unittest.main()
