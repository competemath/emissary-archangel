"""The library's modules are the roots' modules AND what they import from the rest of the library (tolerant_build.module_files), and the planner can plan a library of 60,000 modules.

Why: flt-anthropic (6 Nov 2026). Roots `Theorems` and `Definitions`; each of its 29,511 Theorems modules imports its proof `P2M.Sol.S_...` and a tactic from `P2M.Util`. Those 29,513 modules
were not library modules: every shard called them bad imports (424 of 584 modules), the repair dropped them, the proofs became sorry, and Gate 2 passed 320 names of 23,500. The planner then
needed hours for 60,474 modules (a bit-by-bit sum of lines, quadratic in the size) and put the whole library into one shard.

The real case is scripts/bump/tests/fixtures/real-flt-imports.json.gz: the header imports and the line count of every module of anthropics/fermats-last-theorem at aa2d8b34 (60,474 modules).
"""

import gzip
import json
import math
import random
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import plan_shards as ps  # noqa: E402
import tolerant_build as tb  # noqa: E402

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "real-flt-imports.json.gz"
_REAL = None


def real():
    global _REAL
    if _REAL is None:
        d = json.load(gzip.open(FIXTURE, "rt"))
        own = set(d["imports"])
        _REAL = (d["imports"], {m: [x for x in v if x in own] for m, v in d["imports"].items()}, d["lines"])
    return _REAL


_TREE = None


def real_tree() -> Path:
    """The real flt library as a tree of files that hold only their header imports (written once for the module, removed when the tests are done)."""
    global _TREE
    if _TREE is None:
        _TREE = tempfile.TemporaryDirectory()
        write_tree(Path(_TREE.name), real()[0])
    return Path(_TREE.name)


def tearDownModule():
    if _TREE is not None:
        _TREE.cleanup()


def write_tree(root: Path, imports: dict[str, list[str]]) -> None:
    for m, imps in imports.items():
        parts = tb.split_mod(m)
        p = root.joinpath(*parts[:-1], parts[-1] + ".lean")
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("".join(f"import {i}\n" for i in imps) + "\ntheorem x : True := trivial\n")


class FollowImports(unittest.TestCase):
    def lib(self, files: dict[str, str]) -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for rel, text in files.items():
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return root

    def test_a_package_the_roots_import_is_part_of_the_library(self):
        lib = self.lib(
            {
                "Theorems/A.lean": "import Mathlib\nimport P2M.Sol.S_A\nimport P2M.Util\n",
                "Definitions/D.lean": "import Mathlib\n",
                "P2M/Util.lean": "import Lean\n",
                "P2M/Sol/S_A.lean": "import Mathlib\nimport Helpers.H\n",
                "Helpers/H.lean": "import Mathlib\n",
                "Unused/U.lean": "import Mathlib\n",
            }
        )
        got = set(tb.module_files(lib, ["Theorems", "Definitions"], follow_imports=True))
        self.assertEqual(got, {"Theorems.A", "Definitions.D", "P2M.Util", "P2M.Sol.S_A", "Helpers.H"}, "P2M through the imports of Theorems, Helpers through P2M; Unused imported by nobody")
        self.assertEqual(set(tb.module_files(lib, ["Theorems", "Definitions"])), {"Theorems.A", "Definitions.D"})

    def test_a_root_file_next_to_its_directory_and_public_and_all_imports(self):
        lib = self.lib(
            {
                "Theorems.lean": "import Pkg\n",
                "Pkg.lean": "public import Pkg.Sub\n",
                "Pkg/Sub.lean": "import all Other\n",
                "Other.lean": "import Mathlib\n",
            }
        )
        self.assertEqual(set(tb.module_files(lib, ["Theorems"], follow_imports=True)), {"Theorems", "Pkg", "Pkg.Sub", "Other"})

    def test_only_the_imported_files_are_followed_not_the_package_around_them(self):
        lib = self.lib({"Theorems/A.lean": "import Pkg.Used\n", "Pkg/Used.lean": "import Pkg.Deeper\n", "Pkg/Deeper.lean": "", "Pkg/Unused.lean": "import Mathlib\n", "Pkg/Sub/Also.lean": ""})
        got = set(tb.module_files(lib, ["Theorems"], follow_imports=True))
        self.assertEqual(got, {"Theorems.A", "Pkg.Used", "Pkg.Deeper"})
        self.assertEqual(tb.library_roots(lib, ["Theorems"]), ["Theorems", "Pkg"], "the names to filter built modules and prefixes by: the package of every followed module")

    def test_toolchain_and_dependency_names_are_never_followed(self):
        # a directory of the library that is called like Mathlib or Lean is not the library's own module set
        lib = self.lib({"Theorems/A.lean": "import Mathlib.Tactic\nimport Lean.Elab\nimport Batteries.Data\n", "Mathlib/Tactic.lean": "", "Lean/Elab.lean": "", "Batteries/Data.lean": ""})
        self.assertEqual(set(tb.module_files(lib, ["Theorems"], follow_imports=True)), {"Theorems.A"})

    def test_imports_that_are_not_in_the_header_are_not_followed(self):
        lib = self.lib({"Theorems/A.lean": "import Mathlib\n/- import Hidden.X -/\n-- import Hidden.Y\ntheorem t : True := trivial\n-- import Late\n", "Hidden/X.lean": "", "Hidden/Y.lean": "", "Late.lean": ""})
        self.assertEqual(set(tb.module_files(lib, ["Theorems"], follow_imports=True)), {"Theorems.A"})

    def test_guillemet_names_and_cycles_terminate(self):
        lib = self.lib({"Theorems/A.lean": "import «Odd.Pkg».Sub\nimport B\n", "Odd.Pkg/Sub.lean": "import B\n", "B.lean": "import B2\n", "B2.lean": "import B\n"})
        got = set(tb.module_files(lib, ["Theorems"], follow_imports=True))
        self.assertIn("Theorems.A", got)
        self.assertIn("B", got)
        self.assertIn("B2", got)
        self.assertIn("«Odd.Pkg».Sub", got)

    def test_nothing_changes_for_a_library_whose_roots_import_only_themselves(self):
        lib = self.lib({"Lib/A.lean": "import Mathlib\nimport Lib.B\n", "Lib/B.lean": "import Mathlib\n", "Tests/T.lean": "import Lib.A\n"})
        self.assertEqual(tb.module_files(lib, ["Lib"], follow_imports=True), tb.module_files(lib, ["Lib"]))

    def test_the_real_flt_library(self):
        imports, _, _ = real()
        root = real_tree()
        old = tb.module_files(root, ["Theorems", "Definitions"])
        new = tb.module_files(root, ["Theorems", "Definitions"], follow_imports=True)
        self.assertEqual((len(old), len(new)), (30961, 60474), "Theorems + Definitions, then P2M (29,513 modules) through the imports")
        self.assertEqual(sum(1 for m in new if m.startswith("P2M")), 29513)
        self.assertEqual(tb.library_roots(root, ["Theorems", "Definitions"]), ["Theorems", "Definitions", "P2M"])
        # every import of a Theorems module that is a file of the library is a library module now
        missing = [(m, d) for m, ds in imports.items() if m.startswith("Theorems.") for d in ds if d in imports and d not in new]
        self.assertEqual(missing, [])
        # and the old view lost exactly those: 424 of 584 modules of shard 22 had a bad import because of it
        bad_old = [m for m in old if any(d in imports and d not in old for d in imports[m])]
        self.assertGreaterEqual(len(bad_old), 29000)


class InternalMissingImports(unittest.TestCase):
    """A module of the library that the roots import but that is not in the module set is a pipeline error, not a `bad_import` of the library (which the repair would silently drop)."""

    def lib(self, files):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for rel, text in files.items():
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return root

    def imports_of(self, mods):
        return {m: tb.header_imports(p.read_text()) for m, p in mods.items()}

    def test_a_library_file_outside_the_module_set_is_found(self):
        lib = self.lib({"Theorems/A.lean": "import Mathlib\nimport P2M.S\nimport Gone.X\n", "P2M/S.lean": "import Mathlib\n", "Mathlib/Fake.lean": ""})
        old = tb.module_files(lib, ["Theorems"])
        self.assertEqual(tb.internal_missing_imports(lib, old, self.imports_of(old)), [("Theorems.A", "P2M.S")], "P2M.S is a file of the library; Gone.X does not exist anywhere: that one stays an ordinary bad import")
        new = tb.module_files(lib, ["Theorems"], follow_imports=True)
        self.assertEqual(tb.internal_missing_imports(lib, new, self.imports_of(new)), [])

    def test_the_real_flt_library_with_and_without_the_closure(self):
        root = real_tree()
        old = tb.module_files(root, ["Theorems", "Definitions"])
        found = tb.internal_missing_imports(root, old, self.imports_of(old))
        self.assertGreaterEqual(len(found), 29511, "every Theorems module names its P2M proof")
        self.assertTrue(all(d.startswith("P2M.") for _, d in found))
        new = tb.module_files(root, ["Theorems", "Definitions"], follow_imports=True)
        self.assertEqual(tb.internal_missing_imports(root, new, self.imports_of(new)), [])

    def test_a_shard_module_list_that_is_not_closed_is_found(self):
        lib = self.lib({"Lib/A.lean": "import Lib.B\n", "Lib/B.lean": "import Lib.C\n", "Lib/C.lean": ""})
        mods = tb.module_files(lib, ["Lib"])
        shard = {m: p for m, p in mods.items() if m != "Lib.C"}
        self.assertEqual(tb.internal_missing_imports(lib, shard, self.imports_of(shard)), [("Lib.B", "Lib.C")])


class ThePackageTheRootsImportReachesEveryStep(unittest.TestCase):
    """cubic, #144: the shard pack, the bundle's keep step and the leak scan each had their own idea of the library's modules. A module the roots import from outside them (flt-anthropic: P2M) is copied
    into the shard's sources, kept by the keep step and scanned for leaks; reverting any of the three leaves the plan and the build intact, so each has its own test."""

    def lib(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for rel, text in {"Theorems/A.lean": "import Mathlib\nimport P2M.S\n", "P2M/S.lean": "import Mathlib\n", "Other/U.lean": "import Mathlib\n"}.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_text(text)
        return root

    def test_the_shard_pack_copies_the_modules_outside_the_roots_that_the_build_has(self):
        lib = self.lib()
        out = lib.parent / (lib.name + "-out")
        self.addCleanup(lambda: __import__("shutil").rmtree(out, ignore_errors=True))
        mods = lib.parent / (lib.name + "-build.txt")
        mods.write_text("Theorems.A\nP2M.S\n")
        self.addCleanup(lambda: mods.unlink(missing_ok=True))
        empty = lib.parent / (lib.name + "-empty")
        empty.write_text("")
        self.addCleanup(lambda: empty.unlink(missing_ok=True))
        (lib / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
        p = subprocess.run(
            [sys.executable, str(HERE / "shard_pack.py"), "pack", "--lib", str(lib), "--roots", "Theorems", "--modules", str(mods), "--out", str(out), "--gate2", str(empty), "--errors", str(empty), "--passed", str(empty), "--keep", str(empty)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertTrue((out / "src" / "Theorems" / "A.lean").is_file())
        self.assertTrue((out / "src" / "P2M" / "S.lean").is_file(), "the proof module the root imports is in the shard pack")
        self.assertFalse((out / "src" / "Other" / "U.lean").exists(), "a module nobody imports is not")

    def test_the_keep_step_lists_the_built_modules_of_the_packages_the_roots_import(self):
        lib = self.lib()
        base = lib / ".lake" / "build" / "lib" / "lean"
        for rel in ("Theorems/A.olean", "P2M/S.olean", "Other/U.olean"):
            (base / rel).parent.mkdir(parents=True, exist_ok=True)
            (base / rel).write_text("")
        passed = lib / "passed.json"
        passed.write_text("{}")
        out = lib / "keep.json"
        p = subprocess.run([sys.executable, str(HERE / "bundle.py"), "keep-input", "--lib", str(lib), "--passed", str(passed), "--roots", "Theorems", "--out", str(out)], capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(sorted(json.loads(out.read_text())["libs"]), ["P2M.S", "Theorems.A"], "the library's own modules for BundleKeep: the roots' and the imported package's, not the unrelated one")

    def test_the_leak_scan_gets_the_modules_and_the_prefix_of_the_imported_package(self):
        import leakscan_args

        lib = self.lib()
        args = leakscan_args.args_for("some-lib", lib, ["Theorems"])
        pairs = list(zip(args[::2], args[1::2]))
        self.assertIn(("--module", "P2M.S"), pairs)
        self.assertIn(("--prefix", "P2M"), pairs)
        self.assertNotIn(("--prefix", "Other"), pairs)


class Planner(unittest.TestCase):
    @staticmethod
    def old_lines_of(bits, w_of):
        s = 0
        while bits:
            low = bits & -bits
            s += w_of[low.bit_length() - 1]
            bits ^= low
        return s

    def random_dag(self, rnd, n):
        names = [f"M{i}" for i in range(n)]
        imp = {names[i]: sorted({names[j] for j in rnd.sample(range(i), min(i, rnd.randint(0, 4)))}) for i in range(n)}
        return imp, {m: rnd.randint(1, 500) for m in names}

    def test_small_libraries_get_the_plan_they_always_got(self):
        """The bit-by-bit sum of lines and the table of bytes give the same number, and below FAST_ABOVE every shard is priced: the plan of every library set up so far is unchanged."""
        rnd = random.Random(7)
        cases = 0
        for n in (1, 2, 5, 30, 120, 400):
            for _ in range(8):
                imp, w = self.random_dag(rnd, n)
                wanted = {m for m in imp if rnd.random() < 0.7} or None
                for k in (1, 2, 5, 17):
                    p = ps.plan(imp, w, k, wanted=wanted)
                    cases += 1
                    # the reference: the old algorithm, written out
                    order = ps.topo(imp)
                    idx = {m: i for i, m in enumerate(order)}
                    clos = {}
                    for m in order:
                        b = 1 << idx[m]
                        for d in imp[m]:
                            b |= clos[d]
                        clos[m] = b
                    w_of = [w[m] for m in order]
                    limit = 1.05 * sum(w.values()) / k
                    built, load, tg = [0] * k, [0] * k, [[] for _ in range(k)]
                    for m in order:
                        if wanted is not None and m not in wanted:
                            continue
                        cands = []
                        for s in range(k):
                            eb = clos[m] & ~built[s]
                            extra = self.old_lines_of(eb, w_of) if eb else 0
                            cands.append((load[s] + extra > limit, extra, load[s], s))
                        _, extra, _, s = min(cands)
                        tg[s].append(m)
                        built[s] |= clos[m]
                        load[s] += extra
                    self.assertEqual([x["targets"] for x in p["shards"]], tg)
                    self.assertEqual([x["lines"] for x in p["shards"]], load)
        self.assertGreaterEqual(cases, 190)

    def test_the_big_library_plan_covers_every_target_and_every_closure(self):
        _, imp, w = real()
        wanted = {m for m in imp if m.startswith("Theorems.")}
        t = time.time()
        k, p = ps.choose_k(imp, w, wanted, max(1, math.ceil(sum(w.values()) / 200_000)))
        p = ps.plan(imp, w, k, wanted=wanted, max_targets=400)
        took = time.time() - t
        self.assertLess(took, 600, "the plan of 60,474 modules took hours before the table of bytes")
        got = [m for s in p["shards"] for m in s["targets"]]
        deferred = set(p.get("deferred", []))
        self.assertEqual(len(got) + len(deferred), len(wanted))
        self.assertEqual(set(got) | deferred, wanted, "every Theorems module is judged by exactly one shard, or deferred (listed in the plan)")
        self.assertEqual(len(set(got)), len(got))
        self.assertEqual(set(got) & deferred, set())
        self.assertLessEqual(max(len(s["targets"]) for s in p["shards"]), 400)
        # each shard builds the closure of its targets (a sample of 3,000 targets, all shards)
        rnd = random.Random(1)
        in_shard = {m: s for s in p["shards"] for m in s["targets"]}
        build_sets = {}
        for m in rnd.sample(sorted(set(got)), 3000):
            s = in_shard[m]
            if s["shard"] not in build_sets:
                build_sets[s["shard"]] = set(s["build"])
            bs = build_sets[s["shard"]]
            stack, seen = [m], set()
            while stack:
                x = stack.pop()
                if x in seen:
                    continue
                seen.add(x)
                self.assertIn(x, bs, f"{x} (closure of {m}) is not built by its shard")
                stack.extend(imp[x])
        # P2M is built by the shards: the plan has them in `build` (the old plan had no P2M module at all)
        self.assertTrue(any(x.startswith("P2M.Sol.") for s in p["shards"] for x in s["build"]))

    def test_the_final_theorem_is_deferred_and_no_shard_holds_the_library(self):
        """The final theorem of flt-anthropic imports the whole library (13.5M lines): no shard job can build it before what it imports is in the tree. The plan defers such targets and lists them; every
        other shard stays within a few times the share of one shard (before this a single shard took 13.5M lines)."""
        _, imp, w = real()
        wanted = {m for m in imp if m.startswith("Theorems.")}
        k, p = ps.choose_k(imp, w, wanted, max(1, math.ceil(sum(w.values()) / 200_000)))
        p = ps.plan(imp, w, k, wanted=wanted, max_targets=400)
        deferred = p["deferred"]
        self.assertGreaterEqual(len(deferred), 18, "at least the 18 theorems whose closure is over 6M lines")
        self.assertIn("Theorems.Thm_FLT_fermatLastTheorem", deferred)
        planned = {m for s in p["shards"] for m in s["targets"]}
        self.assertEqual(planned | set(deferred), wanted)
        self.assertEqual(planned & set(deferred), set())
        self.assertLess(max(s["lines"] for s in p["shards"]), 4_000_000, "no shard holds the library any more")
        self.assertGreater(len(planned), 28000)
        # a plan without a deferred target has no `deferred` key: the plan of every other library is the same bytes
        small = ps.plan({"A": [], "B": ["A"]}, {"A": 1, "B": 1}, 1, wanted={"B"})
        self.assertNotIn("deferred", small)

    def test_no_targets_is_a_plan_with_nothing_to_do(self):
        imp = {f"M{i}": ([f"M{i - 1}"] if i else []) for i in range(30)}
        w = {m: 3 for m in imp}
        for fast in (0, 10**9):
            old = ps.FAST_ABOVE
            ps.FAST_ABOVE = fast
            try:
                p = ps.plan(imp, w, 3, wanted=set())
            finally:
                ps.FAST_ABOVE = old
            self.assertEqual([s["targets"] for s in p["shards"]], [[], [], []])

    def test_the_fast_path_prices_few_shards_but_loses_no_target(self):
        rnd = random.Random(3)
        old = ps.FAST_ABOVE
        try:
            ps.FAST_ABOVE = 0
            for n in (50, 300, 800):
                imp, w = self.random_dag(rnd, n)
                for k in (2, 7):
                    p = ps.plan(imp, w, k, wanted=set(imp))
                    got = [m for s in p["shards"] for m in s["targets"]]
                    self.assertEqual(sorted(got), sorted(imp))
                    for s in p["shards"]:
                        bs = set(s["build"])
                        for m in s["targets"]:
                            self.assertTrue(set(imp[m]) <= bs)
        finally:
            ps.FAST_ABOVE = old


if __name__ == "__main__":
    unittest.main()
