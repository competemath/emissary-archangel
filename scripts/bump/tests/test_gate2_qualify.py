"""Records name a declaration as its source writes it, inside its namespace; the exports name it in full. foundation (2026-11-06): 5,565 records, 193 of 196 modules
compiled clean, and Gate 2 judged 21 declarations: the other records (`mem_set_iff` for `AdjunctiveSet.mem_set_iff`) were 'not in the export' and never judged.
gate2_batch.qualify resolves such a name to the ONE name the module declares itself (its export minus the exports of the library modules it imports: an export holds
the library constants the module uses too) that ends in `.<name>`.

The real case is scripts/bump/tests/fixtures/real-foundation-names.json.gz: every record of foundation at 81810b9f (name, source path), the export names of its 183
modules as emissary main has them, and the header imports of its 196 modules. Invariants checked on all of it:
  1. a name the export has is never changed;
  2. a changed name is declared by its own module (in its export, in no export of a module it imports), ends in `.<old name>`, and is the only such name;
  3. a name with no match, or with several, is left as it was;
  4. nothing is lost: every record is in the result, or another record resolved to the same declaration of the same module;
  5. qualify is idempotent;
  6. the count of resolved names equals an independent brute-force count.
"""

from __future__ import annotations

import gzip
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import gate2_batch as g  # noqa: E402
import tolerant_build as tb  # noqa: E402

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "real-foundation-names.json.gz"
ROOT = Path(__file__).resolve().parents[3]


def real():
    return json.load(gzip.open(FIXTURE, "rt"))


def write_exports(d: Path, names: dict[str, list[str]]) -> Path:
    exp = d / "exports"
    exp.mkdir(parents=True, exist_ok=True)
    for mod, ns in names.items():
        (exp / f"{mod}.names.json").write_text(json.dumps({"names": ns}))
    return exp


def write_lib(d: Path, imports: dict[str, list[str]]) -> Path:
    lib = d / "lib"
    for m, imps in imports.items():
        parts = tb.split_mod(m)
        f = lib.joinpath(*parts[:-1], parts[-1] + ".lean")
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text("".join(f"import {i}\n" for i in imps) + "\ntheorem x : True := trivial\n")
    return lib


def closure(imports: dict[str, list[str]], m: str) -> set[str]:
    seen, todo = set(), list(imports.get(m, []))
    while todo:
        x = todo.pop()
        if x not in seen:
            seen.add(x)
            todo += imports.get(x, [])
    return seen


def write_records(d: Path, rows: list[dict], lib: str = "foundation") -> str:
    f = d / "tent.jsonl"
    f.write_text("".join(json.dumps({"name": r["name"], "library": lib, "source_url": f"https://github.com/o/r/blob/{'a' * 40}/{r['sourcePath']}#L1"}) + "\n" for r in rows))
    return str(f)


class RealFoundation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        d = real()
        cls.names = d["names"]
        cls.imports = d["imports"]
        cls.exports = write_exports(cls.tmp, cls.names)
        cls.lib = write_lib(cls.tmp, cls.imports)
        cls.entries = g.tentative_entries([write_records(cls.tmp, d["records"])])
        cls.out = g.qualify(cls.entries, cls.exports, cls.lib)
        cls.own = {m: set(ns) - set().union(*[set(cls.names.get(x, [])) for x in closure(cls.imports, m)]) for m, ns in cls.names.items()}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_the_premise_most_records_are_short_names(self):
        have = {n for ns in self.names.values() for n in ns}
        self.assertGreater(len(self.entries), 5000)
        self.assertLess(sum(r["name"] in have for r in self.entries.values()), 100)

    def test_invariants_on_every_record(self):
        changed = 0
        for key, r in self.entries.items():
            mod = g.module_of(r["sourcePath"])
            have = set(self.names.get(mod, []))
            got = [x for x in self.out.values() if x.get("short") == r["name"] and g.module_of(x["sourcePath"]) == mod]
            if r["name"] in have or mod not in self.names:
                self.assertIn(key, self.out, r)  # 1: a name the export has (or a module without an export) is never changed
                self.assertEqual(self.out[key]["name"], r["name"])
                continue
            if not got:  # 3: unresolved, under its own key, unchanged
                self.assertEqual(self.out[key]["name"], r["name"])
                continue
            full = got[0]["name"]
            changed += 1
            self.assertIn(full, have)  # 2: in its own module's export, ending in .<name>
            self.assertTrue(full.endswith("." + r["name"]), full)
            for d in closure(self.imports, mod):  # and in no export of a module it imports
                self.assertNotIn(full, self.names.get(d, []), (full, mod, d))
            # the only candidate: no other name of the module's export that no import exports ends in .<name>
            others = [h for h in self.own[mod] if h.endswith("." + r["name"]) and h != full]
            self.assertEqual(others, [], (full, others))
        self.assertGreater(changed, 4000)

    def test_counts_equal_an_independent_count(self):
        """The rule, written again from its definition (recursive, not the implementation's loop): modules in import order (the record modules sorted, each after what it imports, imports
        in file order); a name's module is the first in that order whose export has it; a record resolves exactly when its module's export lacks the name, ONE name of the module's own ends
        in .<name>, and every other name of the export ending in .<name> belongs to a module it imports."""
        sys.setrecursionlimit(100000)
        order, seen = [], set()

        def visit(m):
            if m in seen:
                return
            seen.add(m)
            for d in self.imports.get(m, []):
                visit(d)
            order.append(m)

        for m in sorted({g.module_of(r["sourcePath"]) for r in self.entries.values()}):
            visit(m)
        owner = {}
        for m in order:
            for n in self.names.get(m, []):
                owner.setdefault(n, m)
        expected = set()
        for r in self.entries.values():
            mod, n = g.module_of(r["sourcePath"]), r["name"]
            have = self.names.get(mod)
            if have is None or n in have:
                continue
            ends = [h for h in have if h.endswith("." + n)]
            own = [h for h in ends if owner.get(h) == mod]
            below = closure(self.imports, mod)
            if len(own) == 1 and all(owner.get(h) in below for h in ends if h != own[0]):
                expected.add((own[0], mod))
        got = {(r["name"], g.module_of(r["sourcePath"])) for r in self.out.values() if "short" in r}
        self.assertEqual(got, expected)
        self.assertGreaterEqual(len(got), 4600)  # foundation: 21 judged before (4,680 at 81810b9f)
        self.assertEqual(len({n for n, _ in got}), len(got))  # one record per declaration

    def test_each_resolution_stays_with_its_module(self):
        for full, r in self.out.items():
            if "short" in r:
                self.assertIn(full, self.names[g.module_of(r["sourcePath"])])

    def test_idempotent(self):
        self.assertEqual(g.qualify(self.out, self.exports, self.lib), self.out)

    def test_no_resolution_without_the_sources(self):
        self.assertEqual(g.qualify(self.entries, self.exports, None), self.entries)

    def test_a_name_of_an_imported_module_is_never_chosen(self):
        for full, r in self.out.items():
            if "short" in r:
                mod = g.module_of(r["sourcePath"])
                for d in closure(self.imports, mod):
                    self.assertNotIn(full, self.names.get(d, []), (full, mod, d))


class Synthetic(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def test_one_short_name_in_two_modules_both_survive(self):
        rows = [{"name": "foo", "sourcePath": "L/A.lean"}, {"name": "foo", "sourcePath": "L/B.lean"}]
        ents = g.tentative_entries([write_records(self.tmp, rows, "x")])
        self.assertEqual(len(ents), 2)  # the old dict kept only the last one
        exp = write_exports(self.tmp, {"L.A": ["A.foo"], "L.B": ["B.foo"]})
        out = g.qualify(ents, exp, write_lib(self.tmp, {"L.A": [], "L.B": []}))
        self.assertEqual(sorted((r["name"], r["sourcePath"]) for r in out.values()), [("A.foo", "L/A.lean"), ("B.foo", "L/B.lean")])

    def test_a_name_two_modules_resolve_to_stays_with_the_first(self):
        rows = [{"name": "foo", "sourcePath": "L/A.lean"}, {"name": "foo", "sourcePath": "L/B.lean"}]
        ents = g.tentative_entries([write_records(self.tmp, rows, "x")])
        exp = write_exports(self.tmp, {"L.A": ["N.foo"], "L.B": ["N.foo"]})  # two unrelated modules whose exports both have N.foo
        out = g.qualify(ents, exp, write_lib(self.tmp, {"L.A": [], "L.B": []}))
        self.assertEqual(sorted((r["name"], r["sourcePath"]) for r in out.values()), [("N.foo", "L/A.lean"), ("foo", "L/B.lean")])

    def test_ambiguous_none_missing_export_and_exact(self):
        rows = [{"name": "amb", "sourcePath": "L/A.lean"}, {"name": "none", "sourcePath": "L/A.lean"}, {"name": "x", "sourcePath": "L/Gone.lean"},
                {"name": "N.exact", "sourcePath": "L/A.lean"}, {"name": "deep", "sourcePath": "L/A.lean"}]
        ents = g.tentative_entries([write_records(self.tmp, rows, "x")])
        exp = write_exports(self.tmp, {"L.A": ["N.amb", "M.amb", "N.exact", "N.exact.deep2", "P.Q.deep", "deep.aux"]})
        out = g.qualify(ents, exp, write_lib(self.tmp, {"L.A": []}))
        self.assertEqual(sorted(r["name"] for r in out.values()), ["N.exact", "P.Q.deep", "amb", "none", "x"])

    def test_the_ledger_row_wins_over_a_record_that_resolves_to_it(self):
        exp = write_exports(self.tmp, {"L.A": ["N.foo"]})
        ents = {"N.foo": {"name": "N.foo", "sourcePath": "L/A.lean", "outcome": "verified"}, "foo": {"name": "foo", "sourcePath": "L/A.lean", "outcome": "untriaged"}}
        out = g.qualify(ents, exp, write_lib(self.tmp, {"L.A": []}))
        self.assertEqual(list(out), ["N.foo"])
        self.assertEqual(out["N.foo"]["outcome"], "verified")

    def test_an_inherited_name_is_not_chosen_but_an_own_one_is(self):
        rows = [{"name": "foo", "sourcePath": "L/B.lean"}, {"name": "bar", "sourcePath": "L/B.lean"}]
        ents = g.tentative_entries([write_records(self.tmp, rows, "x")])
        exp = write_exports(self.tmp, {"L.A": ["A.foo"], "L.B": ["A.foo", "B.bar"]})  # B's export holds A.foo because B uses it
        out = g.qualify(ents, exp, write_lib(self.tmp, {"L.A": [], "L.B": ["L.A"]}))
        self.assertEqual(sorted(r["name"] for r in out.values()), ["B.bar", "foo"])

    def test_generate_asks_gate2_for_the_qualified_names(self):
        rows = [{"name": "foo", "sourcePath": "L/A.lean"}, {"name": "B.bar", "sourcePath": "L/A.lean"}]
        recs = write_records(self.tmp, rows, "x")
        exp = write_exports(self.tmp, {"L.A": ["N.foo", "B.bar"]})
        (exp / "L.A.ndjson").write_text("{}\n")
        lib = write_lib(self.tmp, {"L.A": []})
        olean = lib / ".lake" / "build" / "lib" / "lean" / "L" / "A.olean"
        olean.parent.mkdir(parents=True)
        olean.write_bytes(b"")
        out = self.tmp / "check.lean"
        ns = type("A", (), {"key": "x", "lib": str(lib), "exports": str(exp), "ledger": str(self.tmp / "none.jsonl"), "roots": "L", "out": str(out), "controls": 0,
                            "tentative": recs, "exclude": "", "only": ""})()
        g.generate(ns)
        asked = {n for line in out.read_text().splitlines() if line.startswith("#gate2_batch") for n in line.split('"')[1].split(",")}
        self.assertEqual(asked, {"N.foo", "B.bar"})

    def run_parse(self, exports: str) -> dict:
        rows = [{"name": "foo", "sourcePath": "L/A.lean"}, {"name": "bar", "sourcePath": "L/B.lean"}]
        recs = write_records(self.tmp, rows, "x")
        write_exports(self.tmp, {"L.A": ["N.foo"], "L.B": ["M.bar"]})
        lib = write_lib(self.tmp, {"L.A": [], "L.B": []})
        log = self.tmp / "gate2.log"
        log.write_text("GATE2B_PASS old=N.foo new=N.foo via=equal\nGATE2B_FAIL old=M.bar new=M.bar reason=uses_sorry\n")
        ns = type("A", (), {"log": str(log), "ledger": str(self.tmp / "none.jsonl"), "out": str(self.tmp / "res.json"), "tentative": recs, "exports": exports, "lib": str(lib)})()
        g.parse(ns)
        return json.loads((self.tmp / "passed.json").read_text())

    def test_parse_files_a_qualified_pass_under_its_module(self):
        self.assertEqual(self.run_parse(str(self.tmp / "exports")), {"L.A": ["N.foo"]})

    def test_parse_without_exports_cannot_place_it(self):
        self.assertEqual(self.run_parse(""), {})  # the behaviour the workflows had: the pass is lost


class Workflows(unittest.TestCase):
    def test_both_bump_workflows_hand_the_exports_to_parse(self):
        for wf in ("bump-shard.yml", "bump-library.yml"):
            text = (ROOT / ".github" / "workflows" / wf).read_text()
            self.assertIn('gate2_batch.py parse --log gate2.log --ledger "data/translate/$KEY.jsonl" --out gate2-results.json --exports "data/exports/$KEY" --lib lib', text, wf)


if __name__ == "__main__":
    unittest.main()
