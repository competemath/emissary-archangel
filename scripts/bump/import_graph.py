#!/usr/bin/env python3
"""import_graph.py DIR ROOTS — the import graph of a library's own modules: size, depth, independent files, closure sizes.
It decides how a big library can be sharded: a module whose imports are all external (Mathlib) can be built by any shard on its own;
a deep graph needs each shard to rebuild the closure of its modules."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tolerant_build as tb  # noqa: E402

lib = Path(sys.argv[1])
roots = [r for r in sys.argv[2].split(",") if r]
mods = tb.module_files(lib, roots)
own = set(mods)
imp = {m: [d for d in tb.header_imports(p.read_text(errors="replace")) if d in own] for m, p in mods.items()}
depth, closure = {}, {}


def d(m: str) -> int:
    if m not in depth:
        depth[m] = 0
        depth[m] = 1 + max((d(x) for x in imp[m]), default=0)
    return depth[m]


def c(m: str) -> set:
    if m not in closure:
        closure[m] = set()
        s = {m}
        for x in imp[m]:
            s |= c(x)
        closure[m] = s
    return closure[m]


sys.setrecursionlimit(100000)
for m in mods:
    d(m), c(m)
sizes = sorted(len(closure[m]) for m in mods)
# weakly connected components
parent = {m: m for m in mods}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


for m, ds in imp.items():
    for x in ds:
        parent[find(m)] = find(x)
comps = {}
for m in mods:
    comps.setdefault(find(m), []).append(m)
loc = sum(len(p.read_text(errors="replace").splitlines()) for p in mods.values())
out = {
    "modules": len(mods),
    "lines": loc,
    "edges": sum(len(v) for v in imp.values()),
    "no_own_imports": sum(1 for v in imp.values() if not v),
    "max_depth": max(depth.values(), default=0),
    "components": len(comps),
    "largest_component": max((len(v) for v in comps.values()), default=0),
    "closure_median": sizes[len(sizes) // 2] if sizes else 0,
    "closure_p90": sizes[int(len(sizes) * 0.9)] if sizes else 0,
    "closure_max": sizes[-1] if sizes else 0,
}
# what sharding would cost, for a few K: modules with ledger entries are the targets (an aggregator that imports everything is not)
if len(sys.argv) > 3 and sys.argv[3]:
    import plan_shards as ps

    wanted = set()
    for ln in Path(sys.argv[3]).read_text().splitlines():
        try:
            sp = json.loads(ln).get("sourcePath", "")
        except ValueError:
            continue
        if sp.endswith(".lean"):
            wanted.add(".".join(tb.esc(x) for x in sp[:-5].split("/")))
    wanted &= own
    out["modules_with_entries"] = len(wanted)
    w_ = {m: max(1, len(p.read_text(errors="replace").splitlines())) for m, p in mods.items()}
    out["sharding"] = {}
    for k in (4, 8, 16, 24):
        pl = ps.plan(imp, w_, k, wanted=wanted)
        out["sharding"][k] = {"duplication": pl["duplication"], "max_shard_share": round(pl["max_shard_lines"] / max(1, pl["lines"]), 3)}
print(json.dumps(out))
