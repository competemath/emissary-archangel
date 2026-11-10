"""The build and its repair rounds inside the job's time (scripts/bump/build_rounds.py, tolerant_build.py --deadline, bump-shard.yml).

flt-anthropic's build-once job 28 (run 42678283150, 10 Nov 2026) built for 172 minutes, ran rounds for 163 more and ended 2 minutes inside its 345-minute
limit. The real timelines of the 35 jobs that had finished (fixtures/flt_round_times.json) are replayed here, as measured and scaled up to 3 times slower.

Invariants:
  I1  the build step never runs past its deadline (a build is stopped at it);
  I2  after a round that ran out of time the files are exactly those of the last finished build, and the shard goes on with that build's log;
  I3  a job whose real timeline fits keeps every round it really ran (the limit costs nothing when there is time);
  I4  a stopped module is not built: no olean, no other output, no cache key; the run exits 3; modules started after the deadline are not built;
  I5  tolerant_build removes every output of a module before Lean writes a new one, so a hard-linked copy keeps the old content;
  I6  the workflow's clock is the job's: JOB_MIN equals timeout-minutes, the reserve covers the measured steps after the build, Gate 2's budget and
      the keep step's deadline stop before the job's end.
Mutants (each must make a test fail): no put-back after a round that ran out of time; a deadline that does not stop a running build; an olean left by a
stopped module; outputs not removed before a rebuild.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
BUMP = HERE.parent
ROOT = BUMP.parents[1]
sys.path.insert(0, str(BUMP))


def load(name):
    spec = importlib.util.spec_from_file_location(name, BUMP / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


tb = load("tolerant_build")
br = load("build_rounds")

JOBS = json.loads((HERE / "fixtures" / "flt_round_times.json").read_text())["jobs"]
JOB_MIN = 345


class Replay:
    """One job's real timeline against run_rounds: a fake clock, builds that take their measured minutes (stopped at the deadline, as tolerant_build is),
    and sources that each round really changes, saved and put back by the functions under test's contract."""

    def __init__(self, job, scale=1.0, reserve=30, put_back=True):
        self.job, self.scale = job, scale
        self.now = job["before_min"] * scale
        self.deadline = JOB_MIN - reserve
        self.sources = {"version": "s0"}  # what the edits change; the finished build of each name records the sources it built
        self.built_from: dict[str, dict] = {}
        self.saved = None
        self.put_back_enabled = put_back
        self.times = {"s0": job["first_build_min"] * scale}
        self.changes = {}
        for r in job["rounds"]:
            self.times[r["round"]] = r["rebuild_min"] * scale
            self.changes[r["round"]] = r["changed"]
        self.undone = 0

    def clock(self):
        return self.now

    def build(self, name):
        end = self.now + self.times[name]
        if end > self.deadline:
            self.now = self.deadline
            if name == "s0":  # a first build keeps what it finished
                self.built_from[name] = dict(self.sources)
            return br.OUT_OF_TIME
        self.now = end
        self.built_from[name] = dict(self.sources)
        return 0

    def edit(self, kind, n, last):
        name = ("r" if kind == "repair" else "p") + str(n)
        if not self.changes.get(name, False):
            return False
        self.sources = {"version": name}
        return True

    def snapshot(self):
        self.saved = dict(self.sources)

    def restore(self):
        self.undone += 1
        if self.put_back_enabled:
            self.sources = dict(self.saved)

    def run(self):
        return br.run_rounds(self.build, self.edit, self.snapshot, self.restore, 4, 3, clock=self.clock, deadline=self.deadline)


class RealTimelines(unittest.TestCase):
    SCALES = [round(1 + i * 0.05, 2) for i in range(41)]  # 1.00 .. 3.00
    RESERVES = [10, 30, 60]

    def test_fixture_is_the_real_run(self):
        self.assertEqual(len(JOBS), 35)
        j28 = next(j for j in JOBS if j["job"] == "w4(28)")
        self.assertEqual((j28["first_build_min"], j28["job_min"]), (171.9, 343.1))
        for j in JOBS:  # the round times add up to the measured build step
            self.assertAlmostEqual(j["first_build_min"] + sum(r["rebuild_min"] for r in j["rounds"]), j["build_step_min"], delta=3, msg=j["job"])

    def test_every_scaled_timeline_stays_inside_the_deadline_and_keeps_a_consistent_build(self):
        cases = 0
        for j in JOBS:
            for scale in self.SCALES:
                for reserve in self.RESERVES:
                    rp = Replay(j, scale, reserve)
                    res = rp.run()
                    cases += 1
                    self.assertLessEqual(rp.now, rp.deadline + 1e-9, (j["job"], scale, reserve))  # I1
                    last = res["last"]
                    self.assertIn(last, rp.built_from, (j["job"], scale, reserve))
                    self.assertEqual(rp.sources, rp.built_from[last], (j["job"], scale, reserve, res))  # I2
                    self.assertEqual(rp.undone, sum(1 for r in res["rounds"] if r.get("undone")))
        self.assertEqual(cases, 35 * 41 * 3)

    def test_jobs_that_fit_keep_every_round_they_ran(self):  # I3
        fit = 0
        for j in JOBS:
            rp = Replay(j)
            res = rp.run()
            real_end = j["before_min"] + j["build_step_min"]
            if real_end <= JOB_MIN - 30:
                fit += 1
                ran = [r["round"] for r in j["rounds"] if r["changed"]]
                self.assertIsNone(res["stopped"], j["job"])
                self.assertEqual([r["round"] for r in res["rounds"] if r["changed"]], ran, j["job"])
        self.assertEqual(fit, 34)  # every job but 28

    def test_job_28_keeps_its_first_portfolio_round_and_undoes_the_second(self):
        rp = Replay(next(j for j in JOBS if j["job"] == "w4(28)"))
        res = rp.run()
        self.assertEqual(res["last"], "p1")
        self.assertTrue(res["rounds"][-1]["undone"])
        self.assertEqual(res["rounds"][-1]["round"], "p2")
        self.assertEqual(rp.sources, {"version": "p1"})
        self.assertAlmostEqual(rp.now, JOB_MIN - 30)  # it stopped at the deadline: 30 minutes for Gate 2 and the rest, which took 2.3

    def test_mutant_without_put_back_is_caught(self):
        caught = 0
        for j in JOBS:
            for scale in self.SCALES:
                rp = Replay(j, scale, 30, put_back=False)
                res = rp.run()
                if rp.sources != rp.built_from[res["last"]]:
                    caught += 1
        self.assertGreater(caught, 100)

    def test_mutant_deadline_ignored_runs_past_the_limit(self):
        over = 0
        for j in JOBS:
            for scale in self.SCALES:
                rp = Replay(j, scale, 30)
                rp.deadline = float("inf")  # a build that is not stopped
                rp.run()
                over += rp.now > JOB_MIN - 30
        self.assertGreater(over, 100)

    def test_a_first_build_that_runs_out_keeps_what_it_built_and_tries_no_round(self):
        j = dict(JOBS[0], before_min=5, first_build_min=400)
        rp = Replay(j)
        res = rp.run()
        self.assertEqual(res["last"], "s0")
        self.assertEqual(res["rounds"], [])
        self.assertIn("first build", res["stopped"])

    def test_no_round_starts_after_the_deadline(self):
        calls = []
        res = br.run_rounds(lambda n: 0, lambda k, n, last: calls.append((k, n)) or True, lambda: None, lambda: None, 4, 3, clock=lambda: 100.0, deadline=50.0)
        self.assertEqual(calls, [])
        self.assertIn("not started", res["stopped"])

    def test_a_build_that_fails_stops_the_step(self):
        with self.assertRaises(SystemExit):
            br.run_rounds(lambda n: 1, lambda *a: True, lambda: None, lambda: None, 4, 3)


FAKE_LEAN = """#!/bin/sh
# lean --run DRIVER rel mod olean: sleeps as long as the module name says (T.Slow), then writes every output
echo "$4" >> "$FAKE_CALLS"
stem="${5%.olean}"
for s in .olean.server .olean.private .ilean .ir.sig .ir; do [ ! -e "$stem$s" ] || { echo "$3:1:0: error: an old $s was still there"; exit 2; }; done
case "$4" in *Slow*) echo half > "$5"; echo half > "$stem.ilean"; sleep 30;; esac  # killed half-way through writing
for s in .olean .olean.server .olean.private .ilean .ir.sig .ir; do echo "new $4" > "$stem$s"; done
exit 0
"""


def olean(lib, m):
    return lib / ".lake" / "build" / "lib" / "lean" / Path(*m.split(".")).with_suffix(".olean")


class Deadline(unittest.TestCase):
    """tolerant_build.py --deadline against a stand-in for lean"""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.t = Path(self.d.name)
        self.lib = self.t / "lib"
        (self.lib / "T").mkdir(parents=True)
        b = self.t / "bin"
        b.mkdir()
        lean = b / "lean"
        lean.write_text(FAKE_LEAN)
        lean.chmod(lean.stat().st_mode | stat.S_IEXEC)
        self.calls = self.t / "calls"
        self.env = {**os.environ, "PATH": f"{b}:{os.environ['PATH']}", "FAKE_CALLS": str(self.calls), "LEAN_PATH": ""}
        self.old = tb.lake_env
        tb.lake_env = lambda _lib: self.env

    def tearDown(self):
        tb.lake_env = self.old
        self.d.cleanup()

    def source(self, m, *imports):
        (self.lib / Path(*m.split("."))).with_suffix(".lean").write_text("".join(f"import {d}\n" for d in imports) + "theorem x : True := trivial\n")

    def build(self, deadline, jobs=1):
        b = tb.Builder(argparse.Namespace(lib=str(self.lib), roots="T", cache=str(self.lib / ".bump-cache"), timeout=1, jobs=jobs, modules="", own="", deadline=deadline))
        return b.run()

    def test_a_module_running_at_the_deadline_is_stopped_and_left_unbuilt(self):  # I4
        import time

        self.source("T.A")
        self.source("T.Slow", "T.A")
        self.source("T.C", "T.Slow")
        t0 = time.time()
        r = self.build(time.time() + 3)
        self.assertLess(time.time() - t0, 20)  # stopped, not left to sleep its 30 s
        self.assertEqual(r["status"]["T.A"]["state"], "clean")
        self.assertTrue(r["status"]["T.Slow"]["out_of_time"])
        self.assertEqual(r["out_of_time"], ["T.Slow"])
        self.assertEqual(r["status"]["T.C"]["state"], "blocked")
        stem = str(olean(self.lib, "T.Slow"))[: -len(".olean")]
        for s in tb.SUFFIXES:
            self.assertFalse(Path(stem + s).exists(), s)
        self.assertFalse((self.lib / ".bump-cache" / "T.Slow.key").exists())
        self.assertTrue((self.lib / ".bump-cache" / "T.A.key").exists())

    def test_nothing_starts_after_the_deadline(self):
        self.source("T.A")
        r = self.build(1.0)  # 1970
        self.assertFalse(self.calls.exists())
        self.assertTrue(r["status"]["T.A"]["out_of_time"])

    def test_no_deadline_builds_everything(self):
        self.source("T.A")
        self.source("T.B", "T.A")
        r = self.build(0)
        self.assertEqual(r["out_of_time"], [])
        self.assertEqual({m: s["state"] for m, s in r["status"].items()}, {"T.A": "clean", "T.B": "clean"})

    def test_every_old_output_is_gone_before_lean_writes(self):  # I5: the fake lean fails when an old output is still there
        self.source("T.A")
        stem = str(olean(self.lib, "T.A"))[: -len(".olean")]
        Path(stem).parent.mkdir(parents=True)
        for s in tb.SUFFIXES:
            Path(stem + s).write_text("old")
        r = self.build(0)
        self.assertEqual(r["status"]["T.A"]["state"], "clean")
        self.assertEqual(Path(stem + ".ilean").read_text().strip(), "new T.A")

    def test_the_command_exits_3_when_the_deadline_stopped_it(self):
        self.source("T.A")
        tool = BUMP / "tolerant_build.py"
        env = {**self.env, "PYTHONPATH": str(BUMP)}
        # lake env is not on this machine: run main with lake_env replaced
        code = (
            "import sys,os;sys.argv=sys.argv[1:];import tolerant_build as tb;"
            "tb.lake_env=lambda _l: dict(os.environ);tb.main()"
        )
        r = subprocess.run([sys.executable, "-c", code, str(tool), "--lib", str(self.lib), "--roots", "T", "--deadline", "1", "--log", str(self.t / "b.log"), "--report", str(self.t / "tb.json"),
                            "--cache", str(self.lib / ".bump-cache")], env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 3, r.stdout + r.stderr)
        r = subprocess.run([sys.executable, "-c", code, str(tool), "--lib", str(self.lib), "--roots", "T", "--log", str(self.t / "b.log"), "--report", str(self.t / "tb.json"),
                            "--cache", str(self.lib / ".bump-cache")], env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


def tree(root: Path) -> dict[str, str]:
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.rglob("*")) if p.is_file()}


class SaveAndPutBack(unittest.TestCase):
    """build_rounds.save / put_back on real files, for module names taken from the real FLT plan"""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.t = Path(self.d.name)
        self.lib = self.t / "lib"
        self.mods = ["Theorems.Thm_A", "P2M.Sol.«S_1102.4662».B", "Definitions.Def_C"]
        for m in self.mods:
            src = self.lib / Path(*tb.split_mod(m)).with_suffix(".lean")
            src.parent.mkdir(parents=True, exist_ok=True)
            src.write_text(f"-- {m}\n")
        self.paths = br.module_paths(self.lib, ["Theorems", "P2M", "Definitions"], self.mods)
        # the first two built, the third not
        for m in self.mods[:2]:
            stem = br.OUT.joinpath(*tb.split_mod(m))
            for s in tb.SUFFIXES:
                f = self.lib / f"{stem}{s}"
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(f"built {m}{s}")
            (self.lib / ".bump-cache").mkdir(exist_ok=True)
            (self.lib / ".bump-cache" / f"{m}.key").write_text("k")
            (self.lib / ".bump-cache" / f"{m}.log.json").write_text("{}")
        self.extra = [self.t / "moves.json", self.t / "state.json"]
        self.extra[0].write_text('{"moves":{}}')

    def tearDown(self):
        self.d.cleanup()

    def test_paths_cover_source_outputs_and_cache_for_each_module(self):
        self.assertEqual(len(self.paths), len(set(self.paths)))
        self.assertEqual(len(self.paths), 3 * (1 + len(tb.SUFFIXES) + 2))
        self.assertIn("P2M/Sol/S_1102.4662/B.lean", self.paths)
        self.assertIn(".lake/build/lib/lean/P2M/Sol/S_1102.4662/B.ir.sig", self.paths)
        self.assertTrue(all(not p.startswith("/") for p in self.paths))

    def test_a_round_is_undone_exactly(self):  # I2 on files
        before = tree(self.lib)
        extra_before = [f.read_text() if f.exists() else None for f in self.extra]
        snap = self.t / "snap"
        br.save(self.lib, self.paths, self.extra, snap)
        # what a round does: edit sources in place, rebuild (remove every output, write new ones), build a module that had no olean, write state
        for m in self.mods:
            (self.lib / Path(*tb.split_mod(m)).with_suffix(".lean")).write_text("edited\n")
        for m in self.mods:
            stem = br.OUT.joinpath(*tb.split_mod(m))
            for s in tb.SUFFIXES:
                f = self.lib / f"{stem}{s}"
                f.unlink(missing_ok=True)
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text("half")
            (self.lib / ".bump-cache" / f"{m}.key").write_text("new key")
        self.extra[1].write_text("{}")
        br.put_back(self.lib, snap)
        self.assertEqual(tree(self.lib), before)
        self.assertEqual([f.read_text() if f.exists() else None for f in self.extra], extra_before)

    def test_hard_linked_outputs_keep_their_content_when_rebuilt_by_unlink(self):
        snap = self.t / "snap"
        br.save(self.lib, self.paths, [], snap)
        rel = next(p for p in self.paths if p.endswith(".ilean") and (self.lib / p).exists())
        self.assertEqual(os.stat(self.lib / rel).st_ino, os.stat(snap / "lib" / rel).st_ino)  # linked, not copied
        (self.lib / rel).unlink()
        (self.lib / rel).write_text("new")
        self.assertTrue((snap / "lib" / rel).read_text().startswith("built"))

    def test_mutant_in_place_write_would_corrupt_a_linked_copy(self):  # why I5 is needed
        snap = self.t / "snap"
        br.save(self.lib, self.paths, [], snap)
        rel = next(p for p in self.paths if p.endswith(".olean") and (self.lib / p).exists())
        (self.lib / rel).write_text("written in place")
        self.assertEqual((snap / "lib" / rel).read_text(), "written in place")

    def test_sources_and_cache_entries_are_copied_not_linked(self):
        snap = self.t / "snap"
        br.save(self.lib, self.paths, [], snap)
        for rel in self.paths:
            if (self.lib / rel).exists() and not br.linkable(rel):
                self.assertNotEqual(os.stat(self.lib / rel).st_ino, os.stat(snap / "lib" / rel).st_ino, rel)

    def test_real_plan_module_names(self):
        """every target module of the real FLT plan: each name gives its own files, none shared with another module, all inside the library"""
        import gzip

        names = gzip.open(HERE / "fixtures" / "flt_plan_targets.txt.gz", "rt").read().split()
        self.assertGreater(len(names), 30000)
        lib = self.t / "real"
        for m in names:
            f = lib / Path(*tb.split_mod(m)).with_suffix(".lean")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("")
        roots = sorted({tb.split_mod(m)[0] for m in names})
        paths = br.module_paths(lib, roots, names)
        self.assertEqual(len(paths), len(names) * (1 + len(tb.SUFFIXES) + 2))
        self.assertEqual(len(set(paths)), len(paths))
        self.assertTrue(all(not p.startswith("/") and ".." not in Path(p).parts for p in paths))
        self.assertEqual(sum(br.linkable(p) for p in paths), len(names) * len(tb.SUFFIXES))
        with self.assertRaises(SystemExit):  # a module whose source is not found is a pipeline error, not a module left unsaved
            br.module_paths(lib, roots, ["Theorems.NoSuchModule"])


class Workflow(unittest.TestCase):
    """bump-shard.yml's clock (I6)"""

    @classmethod
    def setUpClass(cls):
        cls.text = (ROOT / ".github" / "workflows" / "bump-shard.yml").read_text()
        cls.doc = yaml.safe_load(cls.text)
        cls.job = cls.doc["jobs"]["shard"]

    def step(self, start):
        return next(s for s in self.job["steps"] if s.get("name", "").startswith(start))

    def test_job_min_is_the_jobs_timeout(self):
        self.assertEqual(int(self.job["env"]["JOB_MIN"]), int(self.job["timeout-minutes"]))

    def test_the_clock_starts_in_the_first_step(self):
        self.assertIn('echo "JOB_T0=$(date +%s)" >> "$GITHUB_ENV"', self.job["steps"][0]["run"])

    def test_the_reserve_covers_the_measured_steps_after_the_build(self):
        reserve = int(self.doc[True]["workflow_call"]["inputs"]["round_reserve_min"]["default"])
        worst = max(j["after_min"] for j in JOBS)
        self.assertEqual(worst, 9.3)
        self.assertGreaterEqual(reserve, 3 * worst)

    def test_the_build_step_runs_build_rounds_with_the_deadline(self):
        run = self.step("Build this shard's modules")["run"]
        self.assertIn("scripts/bump/build_rounds.py", run)
        self.assertIn('--deadline "$(( JOB_T0 + (JOB_MIN - ROUND_RESERVE_MIN) * 60 ))"', run)
        self.assertIn("--own own.txt", run)
        self.assertNotIn("tolerant_build.py", run)  # one place builds: build_rounds.py

    def snippet(self, step, start):
        return next(ln for ln in self.step(step)["run"].splitlines() if ln.strip().startswith(start)).strip()

    def bash(self, line, env, out):
        r = subprocess.run(["bash", "-ec", f"{line}\necho ${out}"], env={**os.environ, **env}, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return int(r.stdout.split()[-1])

    def test_gate2_budget_stops_before_the_jobs_end(self):
        line = self.snippet("Batched Gate 2", "budget=")
        import time

        now = int(time.time())
        for used_min, cap, want in ((10, 150, 150), (300, 150, 345 - 300 - 15), (340, 150, 1), (200, 60, 60)):
            got = self.bash(line, {"JOB_T0": str(now - used_min * 60), "JOB_MIN": "345", "GATE2_BUDGET_MIN": str(cap)}, "budget")
            self.assertIn(got, (want, want - 1), (used_min, cap))  # a second may pass
        self.assertIn('--budget-min "$budget"', self.step("Batched Gate 2")["run"])

    def test_keep_step_deadline_stops_before_the_jobs_end(self):
        line = self.snippet("What the passed theorems", "deadline=")
        import time

        now = int(time.time())
        got = self.bash(line, {"JOB_T0": str(now - 300 * 60), "JOB_MIN": "345"}, "deadline")
        self.assertLessEqual(got, now - 300 * 60 + (345 - 8) * 60)
        got = self.bash(line, {"JOB_T0": str(now), "JOB_MIN": "345"}, "deadline")
        self.assertAlmostEqual(got, now + 120 * 60, delta=2)


if __name__ == "__main__":
    unittest.main()
