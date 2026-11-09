#!/usr/bin/env python3
"""build_waves.py — the plan of a build-once: a library too big for shards that each rebuild their own closure is compiled once, in waves of jobs.

flt-anthropic (8 Nov 2026): 60,474 modules, 13.5M lines, import depth 236. Shards that rebuild their closure duplicate the work 4.7 times and a shard's closure did not fit a job. Here every module
is built by exactly one job. A wave is a band of consecutive import depths; a job is a set of connected pieces of its band (modules joined by an import inside the band stay together), so what a
job imports is either in the job or was built by an earlier wave. The jobs of a wave run side by side; each restores what the earlier waves built.

  build_waves.py IMPORTS.json OUT.json --budget-lines N --runners R     IMPORTS.json: {"imports": {module: [modules]}, "lines": {module: n}}

Imports of modules outside the library are ignored. A piece bigger than the budget is cut only by making the band thinner: a single depth has no import inside it, so it can always be packed.
"""

import argparse
import gzip
import json
from collections import defaultdict


def depths(imports: dict[str, list[str]]) -> dict[str, int]:
    """module -> the length of its longest import chain inside the library. A cycle is an error (Lean has none, a wrong graph might)."""
    missing = {m: 0 for m in imports}
    importers = defaultdict(list)
    for m, ds in imports.items():
        for d in set(ds):
            if d in imports:
                missing[m] += 1
                importers[d].append(m)
    level = {m: 0 for m, n in missing.items() if n == 0}
    ready = list(level)
    done = 0
    while ready:
        m = ready.pop()
        done += 1
        for n in importers[m]:
            level[n] = max(level.get(n, 0), level[m] + 1)
            missing[n] -= 1
            if missing[n] == 0:
                ready.append(n)
    if done != len(imports):
        raise ValueError(f"the import graph has a cycle: {len(imports) - done} modules are in it or behind it")
    return level


class Pieces:
    """The connected pieces of a growing band of modules, with their sizes."""

    def __init__(self):
        self.parent: dict[str, str] = {}
        self.size: dict[str, int] = {}
        self.largest = 0
        self.total = 0

    def find(self, m: str) -> str:
        while self.parent[m] != m:
            self.parent[m] = self.parent[self.parent[m]]
            m = self.parent[m]
        return m

    def add(self, m: str, lines: int, band_imports: list[str]) -> None:
        self.parent[m] = m
        self.size[m] = lines
        self.total += lines
        self.largest = max(self.largest, lines)
        for d in band_imports:
            a, b = self.find(m), self.find(d)
            if a != b:  # the smaller name names the piece, so that the order of the input cannot change the plan
                a, b = max(a, b), min(a, b)
                self.parent[a] = b
                self.size[b] += self.size[a]
                self.largest = max(self.largest, self.size[b])


def band(modules: list[str], imports: dict[str, list[str]], lines: dict[str, int]) -> Pieces:
    p = Pieces()
    inside: set[str] = set()
    for m in modules:  # lowest depth first: what a module imports inside the band has been added
        p.add(m, lines.get(m, 1), [d for d in imports[m] if d in inside])
        inside.add(m)
    return p


def pack(pieces: dict[str, int], budget: int) -> list[list[str]]:
    """First fit by decreasing size, the same input giving the same jobs. A piece over the budget gets a job of its own."""
    bins: list[tuple[int, list[str]]] = []
    for root, size in sorted(pieces.items(), key=lambda kv: (-kv[1], kv[0])):
        for i, (used, roots) in enumerate(bins):
            if used + size <= budget:
                bins[i] = (used + size, roots + [root])
                break
        else:
            bins.append((size, [root]))
    return [roots for _, roots in bins]


def plan(imports: dict[str, list[str]], lines: dict[str, int], budget: int, runners: int) -> list[dict]:
    if budget < 1 or runners < 1:
        raise ValueError("budget and runners are positive")
    level = depths(imports)
    by_depth: dict[int, list[str]] = defaultdict(list)
    for m, k in level.items():
        by_depth[k].append(m)
    deepest = max(level.values(), default=-1)
    waves, a = [], 0
    while a <= deepest:
        b, p, inside = a, Pieces(), set()
        last = a
        while b <= deepest:
            for m in by_depth[b]:
                p.add(m, lines.get(m, 1), [d for d in imports[m] if d in inside])
            inside.update(by_depth[b])
            # this depth joined pieces beyond a job, or the band no longer fits the runners: the band ends before it. One depth alone may need more jobs than there are runners: they queue
            if b > a and (p.largest > budget or len(pack({r: p.size[r] for r in p.parent if p.find(r) == r}, budget)) > runners):
                break
            last = b
            b += 1
        modules = [m for k in range(a, last + 1) for m in by_depth[k]]
        q = band(modules, imports, lines)
        members: dict[str, list[str]] = defaultdict(list)
        for m in modules:
            members[q.find(m)].append(m)
        jobs = []
        for roots in pack({r: q.size[r] for r in members}, budget):
            ms = sorted(m for r in roots for m in members[r])
            jobs.append({"modules": ms, "lines": sum(lines.get(m, 1) for m in ms)})
        waves.append({"depths": [a, last], "jobs": jobs})
        a = last + 1
    return waves


def job_inputs(waves: list[dict], imports: dict[str, list[str]], wave: int, job: int) -> tuple[list[str], list[list[int]]]:
    """What one job must restore before it builds: the modules of earlier waves that its modules reach through imports, and which jobs built them ([wave, job], sorted)."""
    where = {m: (w, j) for w, x in enumerate(waves) for j, y in enumerate(x["jobs"]) for m in y["modules"]}
    own = set(waves[wave]["jobs"][job]["modules"])
    seen: set[str] = set()
    stack = [d for m in own for d in imports[m] if d in imports and d not in own]
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack.extend(d for d in imports[m] if d in imports)
    return sorted(seen), [list(t) for t in sorted({where[m] for m in seen})]


def to_shards(waves: list[dict], imports: dict[str, list[str]], wanted: set[str]) -> dict:
    """The plan a build-once runs, in the format of plan_shards.plan: one shard per job, numbered wave after wave. `own` is what it builds, `build` that and everything it imports, `targets` the modules of
    `own` Gate 2 judges, `restore` the shards whose packs hold the rest. A shard with no targets still runs: later waves need what it builds."""
    number: dict[tuple[int, int], int] = {}
    for w, wave in enumerate(waves):
        for j in range(len(wave["jobs"])):
            number[(w, j)] = len(number)
    shards = []
    for w, wave in enumerate(waves):
        for j, job in enumerate(wave["jobs"]):
            closure, sources = job_inputs(waves, imports, w, j)
            shards.append(
                {
                    "shard": number[(w, j)],
                    "wave": w,
                    "targets": sorted(set(job["modules"]) & wanted),
                    "own": sorted(job["modules"]),
                    "build": sorted({*job["modules"], *closure}),
                    "restore": sorted(number[(a, b)] for a, b in sources),
                }
            )
    return {"shards": shards, "waves": len(waves)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("graph")
    ap.add_argument("out")
    ap.add_argument("--budget-lines", type=int, required=True)
    ap.add_argument("--runners", type=int, required=True)
    a = ap.parse_args()
    opener = gzip.open if a.graph.endswith(".gz") else open
    with opener(a.graph, "rt", encoding="utf-8") as f:
        g = json.load(f)
    w = plan(g["imports"], g["lines"], a.budget_lines, a.runners)
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump({"waves": w}, f)
    print(f"{len(w)} waves, {sum(len(x['jobs']) for x in w)} jobs, at most {max((len(x['jobs']) for x in w), default=0)} jobs in a wave")


if __name__ == "__main__":
    main()
