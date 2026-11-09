#!/usr/bin/env python3
"""plan_waves.py KEY LIB --tengoku DIR --budget-lines N --runners N --out DIR: the plan of a build-once of a library (bump-waves.yml): plan.json in the format the shard workflow reads, and which shards
each wave runs, for $GITHUB_OUTPUT. bump-waves.yml has a fixed chain of MAX_WAVES jobs; a plan that needs more stops here and not at the wave that falls off the end."""

import argparse
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import build_waves as bw  # noqa: E402

MAX_WAVES = 32


def outputs(plan: dict, max_waves: int = MAX_WAVES) -> dict[str, str]:
    """w0 ... w31 -> the JSON list of shards of that wave ('[]' for a wave the plan does not have)"""
    if plan["waves"] > max_waves:
        raise ValueError(f"the plan has {plan['waves']} waves and the workflow runs {max_waves}: a larger --budget-lines makes fewer")
    by_wave: dict[int, list[int]] = {}
    for s in plan["shards"]:
        by_wave.setdefault(s["wave"], []).append(s["shard"])
    return {f"w{w}": json.dumps(by_wave.get(w, [])) for w in range(max_waves)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("key")
    ap.add_argument("lib")
    ap.add_argument("--tengoku", required=True)
    ap.add_argument("--budget-lines", type=int, required=True)
    ap.add_argument("--runners", type=int, required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    import gate2_batch as g
    import plan_shards as ps
    import tentative_files as tf
    import tolerant_build as tb

    roots = json.load(open(f"data/exports/{a.key}/setup.ci.json"))["roots"]
    ents = g.tentative_entries(tf.files(json.load(open("sources.json")), a.key, a.tengoku))
    imp, weight = ps.graph(Path(a.lib), roots)
    wanted = {".".join(tb.esc(x) for x in r["sourcePath"][:-5].split("/")) for r in ents.values()} & set(imp)
    plan = bw.to_shards(bw.plan(imp, weight, a.budget_lines, a.runners), imp, wanted)
    out = outputs(plan)
    Path(a.out).mkdir(parents=True, exist_ok=True)
    json.dump(plan, open(Path(a.out) / "plan.json", "w"))
    print(f"{plan['waves']} waves, {len(plan['shards'])} shards, {len(wanted)} modules to judge of {len(imp)}")
    with open(os.environ["GITHUB_OUTPUT"], "a") as f:
        for k, v in out.items():
            f.write(f"{k}={v}\n")


if __name__ == "__main__":
    main()
