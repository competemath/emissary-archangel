#!/usr/bin/env python3
"""gate2_driver.py — Gate 2 over a library or a shard, in chunks, each in a Lean process that is killed cleanly if it outgrows the machine.

It replaces the shell loops of bump-library.yml and bump-shard.yml, which ran ONE `lean gate2-check.lean` over every declaration: that process grew until the
kernel killed it or the runner went down with it (navier-stokes-euler, 2026-10-10: four shards lost, three of them with only 38 to 249 modules). Here:

  1. the plan (gate2_batch.py generate) says which modules have declarations to check; they are cut into chunks of at most --max-decls declarations;
  2. each chunk is a Lean process under gate2_guard.run_guarded (memory and time limits);
  3. a chunk that is killed is split in two and both halves are tried again, until one module is left: a module that kills Lean alone is recorded in
     gate2-killed.json and gets no verdict (so nothing of it is verified, and nothing of it reaches a bundle); the other modules of the chunk are checked;
  4. a module whose import fails (two copies of one file, a notation Mathlib also has) is left out of the chunk, as before, and checked in a chunk of its own
     (at most six rounds), and the verdicts of every finished chunk go into one log for `gate2_batch.py parse`.
The controls (--controls) run once, in the first chunk. A budget (--budget-min) bounds the whole thing: the chunks it has no time for are recorded as killed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

IMPORT_FAILED = re.compile(r"import (\S+) failed")
MAX_ROUNDS = 6  # a module left out by an import clash is checked in a later round; the same limit the shell loops had
MAX_ATTEMPTS = 15  # import clashes found one after the other inside a chunk


@dataclass
class Chunk:
    modules: list[str]
    controls: int
    round: int


def cut(plan_modules: list[list], max_decls: int) -> list[list[str]]:
    """Consecutive modules of the plan, at most `max_decls` declarations together (a module over the limit is a chunk of its own)."""
    out: list[list[str]] = []
    cur: list[str] = []
    n = 0
    for mod, count in plan_modules:
        if cur and n + count > max_decls:
            out.append(cur)
            cur, n = [], 0
        cur.append(mod)
        n += count
    if cur:
        out.append(cur)
    return out


def drive(
    first_only: list[str],
    gen: Callable[[list[str], list[str], int], dict],
    run: Callable[[dict], tuple[str, str]],
    controls: int,
    max_decls: int,
    now: Callable[[], float] = time.monotonic,
    budget_s: float = float("inf"),
    say: Callable[[str], None] = print,
) -> tuple[list[str], list[str], dict]:
    """(logs of the finished chunks, modules that killed Lean alone or never got their turn, the last plan). `gen(only, exclude, controls)` writes the check file for
    those modules and returns its plan (`plan_modules`: [module, declarations], `excluded_modules`); `run(plan)` runs it and returns (kind, log text): kind `ok`
    for a process that ended by itself."""
    start = now()
    first = gen(first_only, [], 0)
    queue: deque[Chunk] = deque(Chunk(c, controls if i == 0 else 0, 1) for i, c in enumerate(cut(first["plan_modules"], max_decls)))
    logs: list[str] = []
    killed: list[str] = []
    last = first
    runs = 0
    while queue:
        ch = queue.popleft()
        if now() - start > budget_s:
            killed += ch.modules
            say(f"gate2: out of time, {len(ch.modules)} modules not checked")
            continue
        exclude: list[str] = []
        left_out: list[str] = []
        for _ in range(MAX_ATTEMPTS):
            meta = gen(ch.modules, exclude, ch.controls)
            last = meta
            left_out = meta.get("excluded_modules", [])  # kept out of this chunk by an import clash; the last attempt's list is the one that counts
            mods = [m for m, _ in meta["plan_modules"]]
            if not mods:
                break
            kind, text = run(meta)
            runs += 1
            if kind != "ok":
                if len(mods) > 1:
                    half = len(mods) // 2
                    queue.appendleft(Chunk(mods[half:], 0, ch.round))
                    queue.appendleft(Chunk(mods[:half], ch.controls, ch.round))
                    say(f"gate2: a chunk of {len(mods)} modules ended with '{kind}': split in two")
                else:
                    killed.append(mods[0])
                    say(f"gate2: {mods[0]} alone ended with '{kind}': no verdict for it")
                break
            bad = IMPORT_FAILED.search(text)
            if bad:
                exclude.append(bad.group(1))
                continue
            logs.append(text)
            break
        if left_out and ch.round < MAX_ROUNDS:
            queue.append(Chunk(left_out, 0, ch.round + 1))  # what an import clash kept out: a chunk of its own, in a later round
    say(f"gate2: {runs} Lean processes, {len(killed)} modules without a verdict")
    return logs, killed, last


def main(argv: list[str]) -> int:
    import gate2_batch as g
    from gate2_guard import mem_limit_kb, run_guarded

    ap = argparse.ArgumentParser()
    for f in ("key", "lib", "exports", "ledger", "roots", "lean-path"):
        ap.add_argument(f"--{f}", required=True)
    ap.add_argument("--controls", type=int, default=0)
    ap.add_argument("--tentative", default="")
    ap.add_argument("--only", default="", help="check only these modules (comma list); default all")
    ap.add_argument("--max-decls", type=int, default=250)
    ap.add_argument("--chunk-timeout-min", type=float, default=60)
    ap.add_argument("--budget-min", type=float, default=270)
    ap.add_argument("--rss-share", type=float, default=0.80)
    ap.add_argument("--rss-limit-mb", type=int, default=0, help="a fixed limit per Lean process instead of the share of the machine (tests)")
    ap.add_argument("--log", default="gate2.log")
    ap.add_argument("--killed", default="gate2-killed.json")
    ap.add_argument("--plan", default="plan.json")
    a = ap.parse_args(argv)
    lib = Path(a.lib)
    check = lib / "gate2-check.lean"
    pass_log = Path(a.log).resolve().with_name("gate2-pass.log")

    def gen(only: list[str], exclude: list[str], controls: int) -> dict:
        ns = argparse.Namespace(key=a.key, lib=str(lib), exports=a.exports, ledger=a.ledger, roots=a.roots, out=str(check), controls=controls,
                                tentative=a.tentative, exclude=",".join(exclude), only=",".join(only))
        import contextlib
        import io

        with contextlib.redirect_stdout(io.StringIO()):
            g.generate(ns)
        return json.loads(check.with_suffix(".plan.json").read_text())

    limit = a.rss_limit_mb * 1024 if a.rss_limit_mb else mem_limit_kb(a.rss_share)
    print(f"gate2: memory limit {limit // 1024} MB per Lean process, chunks of at most {a.max_decls} declarations")

    def run(meta: dict) -> tuple[str, str]:
        res = run_guarded(["lean", "gate2-check.lean"], lib, {**os.environ, "LEAN_PATH": a.lean_path}, pass_log, a.chunk_timeout_min * 60, limit)
        text = pass_log.read_text(errors="replace")
        print(f"gate2: {meta['modules_checked']} modules, {meta['declarations']} declarations: {res.kind}, {res.seconds}s, peak {res.peak_kb // 1024} MB, "
              f"{text.count('GATE2B_')} verdict lines")
        return res.kind, text

    first_only = [m for m in a.only.split(",") if m]
    logs, killed, last = drive(first_only, gen, run, a.controls, a.max_decls, budget_s=a.budget_min * 60)
    Path(a.log).write_text("".join(logs))
    Path(a.killed).write_text(json.dumps(sorted(set(killed))))
    Path(a.plan).write_text(json.dumps(last))
    print(f"gate2: {sum(t.count('GATE2B_') for t in logs)} verdict lines from {len(logs)} chunks; killed: {sorted(set(killed))[:8]}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
