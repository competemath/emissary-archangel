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
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tolerant_build as tb  # noqa: E402


def graph(lib: Path, roots: list[str]):
    mods = tb.module_files(lib, roots, follow_imports=True)
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


FAST_ABOVE = 20_000  # modules: above it a target is priced against a few shards, not all (below it every plan is the one the exhaustive search always made)


def plan(imp: dict[str, list[str]], weight: dict[str, int], k: int, cap: float = 1.05, wanted: set[str] | None = None, max_targets: int = 0, max_closure_lines: int | None = None) -> dict:
    """`wanted`: the modules that need checking (those with ledger entries); the rest is only built where something imports it.
    `max_targets`: a shard with more targets than this is cut into shards of at most that many, in import order (0: never). Gate 2 judges a shard's targets one after the other inside the
    shard job's time (navier-stokes-euler, 2026-10-20: shard 1 had 1,758 targets, one flat chain of 1,838 modules that cannot be spread by closure; its Gate 2 got through 535 of them in
    185 minutes and the other 1,223 modules, 12.7k theorems, have no verdict and do not ship). Each part builds only the closure of its own targets, so the early parts are cheap."""
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
    nbytes = (len(order) + 7) // 8
    # lines of a set of modules (a bitset over `idx`): one table lookup per byte of the bitset instead of one step per module (the old loop was quadratic in the library's size: 60,474 modules
    # of flt-anthropic took hours). The sum is the same number.
    table = [[sum(w_of[8 * c + j] for j in range(8) if b >> j & 1 and 8 * c + j < len(order)) for b in range(256)] for c in range(nbytes)]

    def lines_of(bits: int) -> int:
        return sum(table[c][b] for c, b in enumerate(bits.to_bytes(nbytes, "little")) if b)

    fast = len(order) > FAST_ABOVE
    deferred: list[str] = []
    if fast:
        # every target of a big library shares a large base (flt-anthropic: its Definitions, up to 279k lines, are imported by almost every theorem): a shard is full when it holds a typical closure
        # (the 90th percentile of the targets') plus its share of the rest. Without it every shard is over the limit from the first target on and one shard ends up with the whole library.
        # A target whose closure is far bigger than a shard (the final theorem of flt-anthropic imports the whole library: 13.5M lines) cannot be judged in one shard job: it is DEFERRED to a later
        # wave, when what it imports is in the tree, and listed in the plan (`deferred`). `max_closure_lines` sets the bound (0: none; default 8 x the share of one shard).
        sized = {m: lines_of(clos[m]) for m in order if wanted is None or m in wanted}
        if max_closure_lines is None:
            max_closure_lines = int(8 * limit)
        if max_closure_lines > 0:
            deferred = [m for m in order if m in sized and sized[m] > max_closure_lines]
            wanted = {m for m in sized if m not in set(deferred)}
        kept = sorted(v for m, v in sized.items() if m not in set(deferred))
        limit += kept[int(0.9 * (len(kept) - 1))] if kept else 0

    for m in order:
        if wanted is not None and m not in wanted:
            continue
        cands = []
        pool = range(k)
        if fast:  # a library this big (flt-anthropic: 60,474 modules): only the shards that already hold most of the closure, and the least loaded one, are priced exactly
            ranked = sorted(range(k), key=lambda s: (-(clos[m] & built[s]).bit_count(), load[s], s))[:3]
            pool = list(dict.fromkeys(ranked + [min(range(k), key=lambda s: (load[s], s))]))
        for s in pool:
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
    if max_targets > 0:
        cut: list[dict] = []
        for sh in shards:
            t = sh["targets"]
            parts = math.ceil(len(t) / max_targets) if t else 1
            if parts <= 1:
                cut.append(sh)
                continue
            size = math.ceil(len(t) / parts)
            for i in range(0, len(t), size):
                chunk = t[i : i + size]
                bits = 0
                for m in chunk:
                    bits |= clos[m]
                cut.append({"shard": 0, "targets": chunk, "build": [order[j] for j in range(len(order)) if bits >> j & 1], "lines": lines_of(bits)})
        shards = cut
        for n, sh in enumerate(shards):
            sh["shard"] = n
        k = len(shards)
    dup = sum(len(x["build"]) for x in shards) / max(1, len(order))
    out = {"modules": len(order), "lines": total, "k": k, "duplication": round(dup, 2),
           "max_shard_lines": max(x["lines"] for x in shards), "mean_shard_lines": round(total * dup / k), "shards": shards}
    if deferred:  # only when there are some: the plan of every other library stays the same bytes
        out["deferred"] = deferred
    return out


def parse_only(raw: str) -> set[str]:
    """The comma list of `only_modules` as a set. Empty (nothing asked for) is the empty set, which restricts nothing; a non-empty list that holds no name at all (",", ",,", " ") is an error:
    it must not silently turn into 'judge every module'."""
    names = {m.strip() for m in raw.split(",") if m.strip()}
    if raw.strip() and not names:
        raise ValueError(f"only_modules holds no module name: {raw[:40]!r}")
    return names


def restrict_wanted(wanted: set[str], only: set[str], modules: set[str]) -> set[str]:
    """ONLY THESE (bump-sharded `only_modules`): of the modules that need checking, only the named ones. A name the library does not have is an error, and so is a result with nothing
    to judge: a typo must not turn into a bump that judges nothing and looks like success."""
    if not only:
        return set(wanted)
    unknown = sorted(only - modules)
    if unknown:
        raise ValueError(f"only_modules names modules the library does not have: {unknown[:5]}")
    kept = wanted & only
    if not kept:
        raise ValueError("only_modules: none of the named modules has entries to judge")
    return kept


MAX_SHARD_LINES = 250_000  # what one 7 GB runner's Gate 2 (one lean process loading the whole shard) survives; navier-stokes-euler's 601k-line shard was OOM-killed twice
MAX_SHARDS = 32


def choose_k(imp: dict[str, list[str]], weight: dict[str, int], wanted: set[str] | None, k0: int, cap_lines: int = MAX_SHARD_LINES, kmax: int = MAX_SHARDS) -> tuple[int, dict]:
    """The number of shards and its plan, for `k0` or more shards: the dependency closures several shards each rebuild make the biggest shard much larger than total/k (2.87 times
    the library on navier-stokes-euler with 4 shards), so `k0` (one per ~200k lines of the library) is only a start. Raise k until no shard builds more than `cap_lines`, or `kmax`."""
    k = max(1, k0)
    p = plan(imp, weight, k, wanted=wanted)
    for _ in range(4):
        if p["max_shard_lines"] <= cap_lines or k >= kmax:
            break
        k = min(kmax, max(k + 1, math.ceil(k * p["max_shard_lines"] / cap_lines)))
        p = plan(imp, weight, k, wanted=wanted)
    return k, p


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("lib")
    ap.add_argument("roots")
    ap.add_argument("k", type=int)
    ap.add_argument("--out", default="")
    ap.add_argument("--ledger", default="", help="only the modules with entries in this ledger are targets")
    ap.add_argument("--max-targets", type=int, default=0, help="cut a shard with more targets than this into shards of at most that many")
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
    p = plan(imp, weight, a.k, wanted=wanted, max_targets=a.max_targets)
    p["targets_total"] = sum(len(s["targets"]) for s in p["shards"])
    if a.out:
        Path(a.out).write_text(json.dumps(p))
    print(json.dumps({k: v for k, v in p.items() if k != "shards"}))
