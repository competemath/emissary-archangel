"""The plan of a build-once (build_waves.py) on flt-anthropic's real import graph (fixtures/real-flt-imports.json.gz: 60,474 modules, 13,499,321 lines, depth 236) and on 3,000 random graphs.

Invariants: every module is in exactly one job; what a job imports inside the library is in the job or in an earlier wave, never in another job of its wave or a later wave; a job stays within the
budget unless it is one piece that cannot be cut; a wave never has more jobs than the depth bands allow; the same input gives the same plan; a cycle is an error."""

import gzip
import json
import random
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import build_waves as bw  # noqa: E402

G = json.loads(gzip.open(HERE / "fixtures" / "real-flt-imports.json.gz").read())


def violations(imports, lines, waves, budget):
    where = {}
    out = []
    for w, wave in enumerate(waves):
        for j, job in enumerate(wave["jobs"]):
            for m in job["modules"]:
                if m in where:
                    out.append(f"{m} is in two jobs")
                where[m] = (w, j)
    if set(where) != set(imports):
        out.append(f"{len(set(imports) ^ set(where))} modules are missing or unknown")
    for m, ds in imports.items():
        for d in ds:
            if d in imports and m in where and d in where:
                (w, j), (dw, dj) = where[m], where[d]
                if dw > w or (dw == w and dj != j):
                    out.append(f"{m} (wave {w} job {j}) imports {d} (wave {dw} job {dj})")
    for wave in waves:
        for job in wave["jobs"]:
            if job["lines"] != sum(lines.get(m, 1) for m in job["modules"]):
                out.append("a job's lines are wrong")
    return out


class RealGraph(unittest.TestCase):
    def test_the_case_is_the_real_one(self):
        self.assertEqual((len(G["imports"]), sum(G["lines"].values())), (60474, 13499321))
        self.assertEqual(max(bw.depths(G["imports"]).values()), 236)

    def test_plans(self):
        for minutes, runners in ((60, 10), (120, 10), (120, 17), (200, 17), (270, 10)):
            budget = 1100 * minutes
            w = bw.plan(G["imports"], G["lines"], budget, runners)
            self.assertEqual(violations(G["imports"], G["lines"], w, budget)[:5], [], (minutes, runners))
            over = [j for x in w for j in x["jobs"] if j["lines"] > budget]
            self.assertLessEqual(len(over), 1, (minutes, runners, [o["lines"] for o in over][:3]))

    def test_the_same_input_gives_the_same_plan(self):
        a = bw.plan(G["imports"], G["lines"], 132000, 17)
        keys = list(G["imports"])
        random.Random(1).shuffle(keys)
        b = bw.plan({k: G["imports"][k] for k in keys}, G["lines"], 132000, 17)
        self.assertEqual(json.dumps(a), json.dumps(b))


class WhatAJobRestores(unittest.TestCase):
    def test_real_graph(self):
        w = bw.plan(G["imports"], G["lines"], 132000, 17)
        where = {m: (i, j) for i, x in enumerate(w) for j, y in enumerate(x["jobs"]) for m in y["modules"]}
        checked = 0
        for wi in (0, 1, 5, 10, len(w) - 1):
            for ji in range(min(3, len(w[wi]["jobs"]))):
                mods, jobs = bw.job_inputs(w, G["imports"], wi, ji)
                own = set(w[wi]["jobs"][ji]["modules"])
                self.assertFalse(set(mods) & own)
                self.assertTrue(all(where[m][0] < wi for m in mods), (wi, ji))
                self.assertEqual({tuple(t) for t in jobs}, {where[m] for m in mods})
                # closed: with what it restores, everything the job's modules import is present
                have = own | set(mods)
                self.assertEqual([d for m in have for d in G["imports"][m] if d in G["imports"] and d not in have][:3], [])
                checked += 1
        self.assertGreaterEqual(checked, 10)

    def test_the_first_wave_restores_nothing(self):
        w = bw.plan({"A": [], "B": ["A"]}, {"A": 1, "B": 1}, 1, 1)
        self.assertEqual(bw.job_inputs(w, {"A": [], "B": ["A"]}, 0, 0), ([], []))
        self.assertEqual(bw.job_inputs(w, {"A": [], "B": ["A"]}, 1, 0), (["A"], [[0, 0]]))


class RandomGraphs(unittest.TestCase):
    def test_property(self):
        rnd = random.Random(20261108)
        for case in range(3000):
            n = rnd.randint(1, 40)
            names = [f"M{i}" for i in range(n)]
            imports = {m: sorted({names[rnd.randrange(i)] for _ in range(rnd.randint(0, 3))}) if i else [] for i, m in enumerate(names)}
            lines = {m: rnd.randint(1, 50) for m in names}
            budget = rnd.randint(1, 200)
            w = bw.plan(imports, lines, budget, rnd.randint(1, 6))
            self.assertEqual(violations(imports, lines, w, budget), [], case)
            deps = [x["depths"] for x in w]
            self.assertEqual(deps[0][0], 0)
            for p, q in zip(deps, deps[1:]):
                self.assertEqual(p[1] + 1, q[0])


class Determinism(unittest.TestCase):
    def test_equal_sizes_in_any_input_order_give_the_same_plan(self):
        """a plan is built once and re-read wave after wave: the jobs must not depend on the order of the input (many pieces of one size is where the order would show)"""
        rnd = random.Random(7)
        for case in range(500):
            n = rnd.randint(2, 30)
            names = [f"M{i}" for i in range(n)]
            imports = {m: sorted({names[rnd.randrange(i)] for _ in range(rnd.randint(0, 3))}) if i else [] for i, m in enumerate(names)}
            lines = {m: 5 for m in names}
            a = bw.plan(imports, lines, 15, 3)
            keys = list(imports)
            rnd.shuffle(keys)
            b = bw.plan({k: rnd.sample(imports[k], len(imports[k])) for k in keys}, lines, 15, 3)
            self.assertEqual(json.dumps(a), json.dumps(b), case)


class Shards(unittest.TestCase):
    """the plan handed to the shard workflow, on the real graph"""

    @classmethod
    def setUpClass(cls):
        cls.waves = bw.plan(G["imports"], G["lines"], 132000, 17)
        cls.wanted = {m for i, m in enumerate(sorted(G["imports"])) if i % 2 == 0}
        cls.plan = bw.to_shards(cls.waves, G["imports"], cls.wanted)

    def test_every_module_is_owned_once_and_judged_once(self):
        own = [m for s in self.plan["shards"] for m in s["own"]]
        self.assertEqual(len(own), len(set(own)))
        self.assertEqual(set(own), set(G["imports"]))
        targets = [m for s in self.plan["shards"] for m in s["targets"]]
        self.assertEqual(len(targets), len(set(targets)))
        self.assertEqual(set(targets), self.wanted)

    def test_a_shard_is_numbered_after_what_it_restores_and_restores_only_earlier_waves(self):
        wave = {s["shard"]: s["wave"] for s in self.plan["shards"]}
        self.assertEqual([s["shard"] for s in self.plan["shards"]], list(range(len(wave))))
        for s in self.plan["shards"]:
            for r in s["restore"]:
                self.assertLess(r, s["shard"])
                self.assertLess(wave[r], s["wave"])

    def test_what_a_shard_builds_is_closed_under_imports(self):
        for s in self.plan["shards"]:
            build = set(s["build"])
            for m in build:
                self.assertTrue(set(d for d in G["imports"][m] if d in G["imports"]) <= build, m)

    def test_the_restored_shards_hold_everything_that_is_not_its_own(self):
        owner = {m: s["shard"] for s in self.plan["shards"] for m in s["own"]}
        for s in self.plan["shards"]:
            self.assertEqual({owner[m] for m in set(s["build"]) - set(s["own"])}, set(s["restore"]))

    def test_a_shard_with_nothing_to_judge_is_still_in_the_plan(self):
        p = bw.to_shards(bw.plan({"A": [], "B": ["A"]}, {"A": 5, "B": 5}, 5, 1), {"A": [], "B": ["A"]}, {"B"})
        self.assertEqual([(s["own"], s["targets"]) for s in p["shards"]], [(["A"], []), (["B"], ["B"])])


class Edges(unittest.TestCase):
    def test_a_chain_of_one_piece_is_cut_at_the_budget(self):
        names = [f"M{i}" for i in range(10)]
        imports = {m: ([names[i - 1]] if i else []) for i, m in enumerate(names)}
        w = bw.plan(imports, {m: 10 for m in names}, 30, 4)
        self.assertEqual(violations(imports, {m: 10 for m in names}, w, 30), [])
        self.assertTrue(all(j["lines"] <= 30 for x in w for j in x["jobs"]))

    def test_one_module_over_the_budget_gets_a_job(self):
        w = bw.plan({"A": []}, {"A": 500}, 10, 2)
        self.assertEqual([j["modules"] for x in w for j in x["jobs"]], [["A"]])

    def test_a_cycle_is_an_error(self):
        with self.assertRaises(ValueError):
            bw.plan({"A": ["B"], "B": ["A"]}, {}, 10, 2)

    def test_an_import_outside_the_library_is_ignored(self):
        w = bw.plan({"A": ["Mathlib.X"]}, {"A": 1}, 10, 1)
        self.assertEqual(len(w), 1)

    def test_nothing_to_plan(self):
        self.assertEqual(bw.plan({}, {}, 10, 1), [])

    def test_a_silly_budget_is_an_error(self):
        with self.assertRaises(ValueError):
            bw.plan({"A": []}, {}, 0, 1)


if __name__ == "__main__":
    unittest.main()
