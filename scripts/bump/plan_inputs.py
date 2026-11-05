#!/usr/bin/env python3
"""plan_inputs.py — what a bump's shards are built with, as the plan records it (plan/inputs.json). A resume (fill_from) may only fill in shards built under the same settings.

  plan_inputs.py OUT.json        reads MATHLIB, TOOLCHAIN, IMPORTS, TENGOKU_REF (and SWAP_GB, BUILD_TIMEOUT_MIN) from the environment

swap_gb and build_timeout_min change what a shard can build and judge (a module too big for RAM builds on swap, or is killed after its timeout), so a resume must not mix shards built with
different values. They are recorded only when they are not the defaults (0 and 90): the record of a run that used the defaults is byte for byte what it was before they existed, so that such a
run can still be resumed from (`cmp` in bump-sharded.yml).
"""

from __future__ import annotations

import json
import os
import sys

BASE = ("MATHLIB", "TOOLCHAIN", "IMPORTS", "TENGOKU_REF")
DEFAULTS = {"SWAP_GB": "0", "BUILD_TIMEOUT_MIN": "90"}


def record(env) -> dict:
    out = {k.lower(): env[k] for k in BASE}
    for k, default in DEFAULTS.items():
        v = env.get(k, default)
        if v != default:
            out[k.lower()] = v
    return out


def dump(rec: dict) -> str:
    return json.dumps(rec, indent=1, sort_keys=True)


if __name__ == "__main__":
    with open(sys.argv[1], "w") as f:
        f.write(dump(record(os.environ)))
