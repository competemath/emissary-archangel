#!/usr/bin/env python3
"""plan_shards.py — split a big library into shards, each a dependency-closed set of modules one runner can build.

A shard has TARGETS (the modules it is responsible for: Gate 2 and the intake bundle are computed for their declarations) and
BUILD = the targets plus everything they import, directly or not (all of it has to be compiled to check them). The cost of
sharding is the closure that several shards each rebuild. Modules are assigned in import order (dependencies first) to the shard
that already holds most of their closure, so a module follows what it imports; a shard stops attracting modules past a size cap,
which keeps the loads even. The modules every shard needs (the library's core) are duplicated, nothing else is.

  plan_shards.py DIR ROOTS K [--ledger FILE] [--out plan.json]    prints the plan's statistics, writes the plan
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tolerant_build as tb  # noqa: E402


def graph(lib: Path, roots: list[str]):
    mods = tb.module_files(lib, roots)
    own = set(mods)
    imp = {m: [d for d in tb.header_imports(p.read_text(errors="replace")) if d in own] for m, p in mods.items()}
    weight = {m: max(1, len(p.read_text(errors="replace").splitlines())) for m, p in mods.items()}
    return imp, weight


def topo(imp: dict[str, list[str]]) -> list[str]:
    order, seen = [], set()
    sys.setrecursionlimit(1_000_000)

    def visit(m: str) -> None:
        if m in seen:
            return
        seen.add(m)
        for d in imp[m]:
            visit(d)
        order.append(m)

    for m in sorted(imp):
        visit(m)
    return order


def plan(imp: dict[str, list[str]], weight: dict[str, int], k: int, cap: float = 1.05, wanted: set[str] | None = None) -> dict:
    """`wanted`: the modules that need checking (those with ledger entries); the rest is only built where something imports it."""
    order = topo(imp)
    idx = {m: i for i, m in enumerate(order)}
    clos: dict[str, int] = {}  # closure of m as a bitset over `idx`
    for m in order:
        b = 1 << idx[m]
        for d in imp[m]:
            b |= clos[d]
        clos[m] = b
    total = sum(weight.values())
    limit = cap * total / k
    built = [0] * k
    load = [0] * k  # lines of the built set
    targets: list[list[str]] = [[] for _ in range(k)]
    w_of = [weight[m] for m in order]

    def lines_of(bits: int) -> int:
        s, i = 0, 0
        while bits:
            low = bits & -bits
            s += w_of[low.bit_length() - 1]
            bits ^= low
        return s

    for m in order:
        if wanted is not None and m not in wanted:
            continue
        cands = []
        for s in range(k):
            extra_bits = clos[m] & ~built[s]
            extra = lines_of(extra_bits) if extra_bits else 0
            cands.append((load[s] + extra > limit, extra, load[s], s))
        _, extra, _, s = min(cands)
        targets[s].append(m)
        built[s] |= clos[m]
        load[s] += extra
    shards = []
    for s in range(k):
        b = [order[i] for i in range(len(order)) if built[s] >> i & 1]
        shards.append({"shard": s, "targets": targets[s], "build": b, "lines": load[s]})
    dup = sum(len(x["build"]) for x in shards) / max(1, len(order))
    return {"modules": len(order), "lines": total, "k": k, "duplication": round(dup, 2),
            "max_shard_lines": max(x["lines"] for x in shards), "mean_shard_lines": round(total * dup / k), "shards": shards}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("lib")
    ap.add_argument("roots")
    ap.add_argument("k", type=int)
    ap.add_argument("--out", default="")
    ap.add_argument("--ledger", default="", help="only the modules with entries in this ledger are targets")
    a = ap.parse_args()
    imp, weight = graph(Path(a.lib), [r for r in a.roots.split(",") if r])
    wanted = None
    if a.ledger:
        wanted = set()
        for ln in Path(a.ledger).read_text().splitlines():
            try:
                sp = json.loads(ln).get("sourcePath", "")
            except ValueError:
                continue
            if sp.endswith(".lean"):
                wanted.add(".".join(tb.esc(x) for x in sp[:-5].split("/")))
        wanted &= set(imp)
    p = plan(imp, weight, a.k, wanted=wanted)
    p["targets_total"] = sum(len(s["targets"]) for s in p["shards"])
    if a.out:
        Path(a.out).write_text(json.dumps(p))
    print(json.dumps({k: v for k, v in p.items() if k != "shards"}))
