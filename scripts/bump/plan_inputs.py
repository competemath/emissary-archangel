#!/usr/bin/env python3
"""plan_inputs.py — what a bump's shards are built with, as the plan records it (plan/inputs.json). A resume (fill_from) may only fill in shards built under the same settings.

  plan_inputs.py OUT.json        reads MATHLIB, TOOLCHAIN, IMPORTS, TENGOKU_REF (and SWAP_GB, BUILD_TIMEOUT_MIN) from the environment
  plan_inputs.py swap IN.json    prints swap_gb=N: the swap the shards of that plan were built with (bump-sharded.yml compose -> verify)

verify builds the shards' new modules again, in the tree; a module that needed swap in its shard needs it there too. prime-gaps-186 (run 42549840777, 9 and 12 Nov 2026): its
shard built PrimeGaps186's one new module on 48 GB of swap in 64 minutes; verify, which had no swap, lost its runner 16 minutes into the same build, twice, with no log.

swap_gb and build_timeout_min change what a shard can build and judge (a module too big for RAM builds on swap, or is killed after its timeout), so a resume must not mix shards built with
different values. They are recorded only when they are not the defaults (0 and 90): the record of a run that used the defaults is byte for byte what it was before they existed, so that such a
run can still be resumed from (`cmp` in bump-sharded.yml).
"""

from __future__ import annotations

import json
import os
import re
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


# a Lean module name as setup-source.mjs accepts it: components separated by dots, each a letter or underscore followed by letters, digits, _ ' ! ?, or anything between « and »
_COMPONENT = r"(?:[^\W\d][\w'!?]*|«[^»]+»)"
MODULE_NAME = re.compile(rf"{_COMPONENT}(?:\.{_COMPONENT})*")
HEAVY_KEYS = ("swap_gb", "build_timeout_min", "only_modules")
HEAVY_DEFAULTS = {"swap_gb": "0", "build_timeout_min": "90", "only_modules": ""}
MAX_BUILD_TIMEOUT_MIN = 170  # the shard job has 345 minutes; its setup and Gate 2 come out of them


def parse_heavy(raw: str) -> dict:
    """The `heavy` input of bump-sharded: settings for modules too big for a runner, as `key=value` pairs separated by `;`
    (swap_gb=48;build_timeout_min=150;only_modules=A.B,C.D). GitHub allows 25 inputs for a dispatch and the workflow had 24, so three settings share one. Anything malformed is an error:
    an unknown key, a repeated key, a value outside its range, a character that does not belong in a module list."""
    out = dict(HEAVY_DEFAULTS)
    if raw.strip() == "":
        return out
    seen = set()
    for item in raw.split(";"):
        if item.strip() == "":
            raise ValueError("heavy: an empty item (a stray ';')")
        if "=" not in item:
            raise ValueError(f"heavy: {item[:40]!r} is not key=value")
        k, v = item.split("=", 1)
        k = k.strip()
        if k not in HEAVY_KEYS:
            raise ValueError(f"heavy: unknown key {k[:40]!r} (swap_gb, build_timeout_min, only_modules)")
        if k in seen:
            raise ValueError(f"heavy: {k} given twice")
        seen.add(k)
        if k == "swap_gb":
            if not re.fullmatch(r"0|[1-9][0-9]{0,2}", v):
                raise ValueError(f"heavy: swap_gb is a number of GB, not {v[:20]!r}")
        elif k == "build_timeout_min":
            if not re.fullmatch(r"[1-9][0-9]{0,2}", v) or int(v) > MAX_BUILD_TIMEOUT_MIN:
                raise ValueError(f"heavy: build_timeout_min is 1-{MAX_BUILD_TIMEOUT_MIN} minutes, not {v[:20]!r}")
        else:
            if len(v) > 60000 or re.search(r"[\s;&|<>()`$\"\\*]", v):
                raise ValueError("heavy: only_modules is a comma list of module names, without spaces or shell characters")
            names = [m for m in v.split(",") if m != ""]
            if v != "" and not names:
                raise ValueError("heavy: only_modules holds no module name")
            for m in names:
                if len(m) > 300 or not MODULE_NAME.fullmatch(m):
                    raise ValueError(f"heavy: only_modules has {m[:40]!r}, which is not a module name")
        out[k] = v.strip() if k == "only_modules" else v
    return out


SWAP_GB = re.compile(r"0|[1-9][0-9]{0,2}")


def swap_of(rec: dict) -> str:
    """the swap (GB) a plan's shards were built with: what the record says, or the default when it says nothing (a record leaves out the defaults)"""
    if not isinstance(rec, dict):
        raise ValueError(f"inputs.json: a record is a JSON object, not {type(rec).__name__}")  # cubic, #182
    v = rec.get("swap_gb", DEFAULTS["SWAP_GB"])
    if not isinstance(v, str) or not SWAP_GB.fullmatch(v):
        raise ValueError(f"inputs.json: swap_gb is a number of GB, not {str(v)[:20]!r}")
    return v


if __name__ == "__main__":
    if sys.argv[1] == "swap":
        # no record (a recut of a run older than the plan's 14 days of retention): said plainly, and the build goes on as it did before there was a record
        if not os.path.isfile(sys.argv[2]):
            print(f"::warning::{sys.argv[2]}: no record of what the shards were built with; verify adds no swap", file=sys.stderr)
            print("swap_gb=0")
            sys.exit(0)
        try:
            print(f"swap_gb={swap_of(json.load(open(sys.argv[2])))}")
        except (ValueError, json.JSONDecodeError) as e:
            print(f"::error::{e}", file=sys.stderr)  # stdout is $GITHUB_OUTPUT
            sys.exit(1)
    elif sys.argv[1] == "heavy":
        try:
            for k, v in parse_heavy(sys.argv[2] if len(sys.argv) > 2 else "").items():
                print(f"{k}={v}")
        except ValueError as e:
            print(f"::error::{e}")
            sys.exit(1)
    else:
        with open(sys.argv[1], "w") as f:
            f.write(dump(record(os.environ)))
