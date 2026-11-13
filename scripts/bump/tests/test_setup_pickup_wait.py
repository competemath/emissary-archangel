"""The setup pickup waits for runners instead of leaving a ready library to the next trigger, and does not count its own job as a busy runner (setup_pickup.py, bump_pickup.py).

The real case, 13 Nov 2026: batch 7 was registered with five libraries ready and no setup started for hours. The 14:50 run printed `5 ready, 0 runners free of the 10 needed: next run`, and nothing
started a later run: GitHub's cron fired 3 times in 16 hours and the long jobs that end (workflow_run) were all in other repositories' queues. At 17:20 a hand dispatch found 11 jobs running, one of them
its own, and printed `9 runners free of the 10 needed`: its own job made 10 free look like 9.

Real measurement used (17:14 UTC, run ids and jobs of every in-progress run of the four repositories): 9 jobs, plus the pickup's own run 43470891538 with 1.
Invariants: the asking run (its id in ITS repository) is never counted; every other run always is, a run of another repository with the same number too (cubic on #192); a look that fails in the middle of a wait does not end it, the first one failing does; a pickup that started nothing because of the runners looks again after POLL_SECONDS until its deadline, and only then; it does not wait
when nothing was ready, when something started, on a dry run, or with --wait-minutes 0; a wait never outlasts the deadline by more than one poll; the workflow's job timeout is longer than its wait.
Mutants (each must fail a check): the asking run counted; the run id matched in every repository; waiting for any reason; no deadline; a failing look ending the wait.
"""

import inspect
import json
import os
import random
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))

import bump_pickup as bp  # noqa: E402
import setup_pickup as sp  # noqa: E402
import yaml  # noqa: E402
from test_setup_pickup import BATCH6, NOW, OPEN, R, without_batch6  # noqa: E402

WF = HERE.parents[2] / ".github" / "workflows"
OWN = "43470891538"
# repo -> {run id: jobs in progress or queued}, as measured at 17:14 UTC on 13 Nov 2026 (the pickup's own run added)
BUSY = {
    "competemath/tengoku": {"43469883877": 1, "43469880695": 1, "43469615333": 1, "43464819698": 1, "43457936611": 1},
    "competemath/emissary-archangel": {"43450160202": 1, "43435939792": 1, "43237206258": 2, OWN: 1},
    "competemath/emissary-sandbox": {},
    "competemath/tengoku-sandbox": {},
}


def fake_gh(busy):
    def gh(*args):
        path = args[2]
        if "/jobs" in path:
            run = path.split("/runs/")[1].split("/")[0]
            repo = path.split("repos/")[1].split("/actions")[0]
            return [busy[repo][run]] if run in busy[repo] else []
        repo = path.split("repos/")[1].split("/actions")[0]
        return [int(r) for r in busy[repo]] if "status=in_progress" in path else []

    return gh


class OwnJob(unittest.TestCase):
    def test_the_real_measurement(self):
        self.assertEqual(bp.runners_in_use(fake_gh(BUSY), skip_run=""), 10)
        self.assertEqual(bp.runners_in_use(fake_gh(BUSY), skip_run=OWN), 9)

    def test_the_run_id_of_the_actions_environment_is_the_default(self):
        with mock.patch.dict(os.environ, {"GITHUB_RUN_ID": OWN}):
            self.assertEqual(bp.runners_in_use(fake_gh(BUSY)), 9)
        with mock.patch.dict(os.environ):
            os.environ.pop("GITHUB_RUN_ID", None)
            self.assertEqual(bp.runners_in_use(fake_gh(BUSY)), 10)

    def test_ten_free_starts_a_setup_and_nine_does_not(self):
        """what the 17:20 dispatch should have done: 11 jobs running with its own, 10 free for the others"""
        busy = {r: dict(v) for r, v in BUSY.items()}
        busy["competemath/tengoku"]["1"] = 1  # one more job: 11 with its own, 10 without
        free = lambda skip: bp.RUNNERS - bp.runners_in_use(fake_gh(busy), skip_run=skip)  # noqa: E731
        self.assertEqual(free(""), 9)
        self.assertEqual(free(OWN), 10)
        self.assertEqual(sp.plan(BATCH6[:1], {BATCH6[0]: ("x", "ok")}, free(OWN))[0], [(BATCH6[0], "x")])
        self.assertEqual(sp.plan(BATCH6[:1], {BATCH6[0]: ("x", "ok")}, free(""))[0], [])

    def test_5000_random_states(self):
        rng = random.Random(13)
        for _ in range(5000):
            busy = {r: {str(rng.randrange(10**11)): rng.randrange(1, 12) for _ in range(rng.randrange(0, 5))} for r in bp.REPOS}
            own = str(rng.randrange(10**11))
            n = rng.randrange(1, 12)
            busy[rng.choice(bp.REPOS)][own] = n
            total = sum(v for runs in busy.values() for v in runs.values())
            self.assertEqual(bp.runners_in_use(fake_gh(busy), skip_run=own), total - n)
            self.assertEqual(bp.runners_in_use(fake_gh(busy), skip_run=""), total)

    def test_a_run_of_another_repository_with_the_same_number_still_counts(self):
        """cubic on #192: a run id is unique only within its repository"""
        busy = {r: dict(v) for r, v in BUSY.items()}
        busy["competemath/tengoku"][OWN] = 3  # the same number in tengoku: 3 real jobs
        e = "competemath/emissary-archangel"
        self.assertEqual(bp.runners_in_use(fake_gh(busy), skip_run=OWN, skip_repo=e), 9 + 3)
        with mock.patch.dict(os.environ, {"GITHUB_RUN_ID": OWN, "GITHUB_REPOSITORY": e}):
            self.assertEqual(bp.runners_in_use(fake_gh(busy)), 9 + 3)

    def test_mutant_the_run_id_matched_in_every_repository(self):
        src = inspect.getsource(bp.runners_in_use)
        old = "if skip and str(run) == skip and (not skip_repo or repo == skip_repo):"
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(bp))
        exec(src.replace(old, "if skip and str(run) == skip:"), ns)
        busy = {r: dict(v) for r, v in BUSY.items()}
        busy["competemath/tengoku"][OWN] = 3
        self.assertEqual(ns["runners_in_use"](fake_gh(busy), skip_run=OWN, skip_repo="competemath/emissary-archangel"), 9)  # not 12

    def test_mutant_the_asking_run_counted(self):
        src = inspect.getsource(bp.runners_in_use)
        self.assertEqual(src.count("if skip and str(run) == skip and (not skip_repo or repo == skip_repo):"), 1)
        ns = dict(vars(bp))
        exec(src.replace("if skip and str(run) == skip and (not skip_repo or repo == skip_repo):", "if False:"), ns)
        self.assertEqual(ns["runners_in_use"](fake_gh(BUSY), skip_run=OWN), 10)  # not 9: the real measurement catches it


class Waiting(unittest.TestCase):
    def run_main(self, frees, wait=30, dry=False, mod=sp, runs=None, fail_looks=(), main=None):
        """main() over the real registry with batch 6 not yet started and `frees` runners free at each look; returns (dispatches, sleeps, looks)"""
        looks, sleeps, calls = [], [], []
        clock = [NOW]
        seen = [0]

        def runs_of(repo, since):
            seen[0] += 1
            if seen[0] - 1 in fail_looks:
                raise RuntimeError("HTTP 502")
            return runs if runs is not None else without_batch6(R["runs"])

        def run(args, **k):
            if args[:2] == ["git", "log"]:
                return subprocess.CompletedProcess(args, 0, R["log"], "")
            calls.append(args)
            return subprocess.CompletedProcess(args, 0, "", "")

        def in_use():
            i = len(looks)
            looks.append(clock[0])
            f = frees[min(i, len(frees) - 1)]
            return bp.RUNNERS - f

        def sleep(s):
            sleeps.append(s)
            clock[0] += s

        argv = ["setup_pickup.py", "--wait-minutes", str(wait)] + (["--dry-run"] if dry else [])
        with tempfile.TemporaryDirectory() as d:
            Path(d, "sources.json").write_text(json.dumps({"sources": R["sources"]}))
            for k in R["set_up"]:
                Path(d, "data", "exports", k).mkdir(parents=True)
                Path(d, "data", "exports", k, "setup.ci.json").write_text("{}")
            cwd = os.getcwd()
            os.chdir(d)
            try:
                with (
                    mock.patch.object(mod.subprocess, "run", run),
                    mock.patch.object(mod, "setup_runs", runs_of),
                    mock.patch.object(mod, "records_prs", lambda tree: OPEN),
                    mock.patch.object(mod, "main_files", lambda tree, k, s: set()),
                    mock.patch.object(mod.bp, "runners_in_use", in_use),
                    mock.patch.object(mod.time, "time", lambda: clock[0]),
                    mock.patch.object(mod.time, "sleep", sleep),
                    mock.patch.object(sys, "argv", argv),
                ):
                    (main or mod.main)()
            finally:
                os.chdir(cwd)
        return [c[c.index("-f") + 1] for c in calls], sleeps, looks

    def test_it_waits_until_the_runners_are_free_then_starts(self):
        """the real morning: five minutes after 9 free, 11 are free: one start (the first of batch 6), with nothing started before"""
        started, sleeps, looks = self.run_main([0, 4, 9, 9, 11])
        self.assertEqual(sleeps, [sp.POLL_SECONDS] * 4)
        self.assertEqual(len(looks), 5)
        self.assertEqual(started, [f"key={BATCH6[0]}"])

    def test_it_stops_at_the_deadline(self):
        started, sleeps, looks = self.run_main([0], wait=20)
        self.assertEqual(started, [])
        self.assertLessEqual(sum(sleeps), 20 * 60)
        self.assertGreater(sum(sleeps) + sp.POLL_SECONDS, 20 * 60)  # no early give-up: it used the time it was given
        self.assertEqual(len(looks), len(sleeps) + 1)

    def test_no_wait_when_something_started(self):
        started, sleeps, _ = self.run_main([20])
        self.assertEqual(len(started), 4)  # the four of batch 6 with 20 free: no reason to look again
        self.assertEqual(sleeps, [])

    def test_no_wait_with_zero_minutes_or_on_a_dry_run(self):
        for kw in ({"wait": 0}, {"dry": True}):
            started, sleeps, looks = self.run_main([0], **kw)
            self.assertEqual((started, sleeps, len(looks)), ([], [], 1), kw)

    def test_no_wait_when_nothing_is_ready(self):
        """every library of the real registry has a setup (or is before the window): nothing waits for runners, so nothing is waited for"""
        runs = [{"displayTitle": f"setup-auto {k} (auto)", "createdAt": "2026-11-13T17:00:00Z"} for k in R["sources"]]
        started, sleeps, _ = self.run_main([0], runs=runs)
        self.assertEqual((started, sleeps), ([], []))

    def test_waits_for_runners_truth_table(self):
        self.assertTrue(sp.waits_for_runners([], 5, 9))  # the real 14:50 case had 0 free; 17:20 had 9
        self.assertTrue(sp.waits_for_runners([], 1, 0))
        self.assertFalse(sp.waits_for_runners([], 0, 0))  # nothing ready: the runners are not the reason
        self.assertFalse(sp.waits_for_runners([("a", "")], 3, 4))  # something started
        self.assertFalse(sp.waits_for_runners([], 5, bp.NEED_FREE))  # enough runners: plan would have started one

    def test_5000_random_plans_wait_exactly_when_the_runners_are_the_reason(self):
        rng = random.Random(7)
        for _ in range(5000):
            keys = [f"k{i}" for i in range(rng.randrange(0, 7))]
            refs = {k: (None, "no records") if rng.random() < 0.4 else ("", "ok") for k in keys}
            free = rng.randrange(0, 21)
            starts, notes = sp.plan(keys, refs, free)
            ready = [k for k in keys if refs[k][0] is not None]
            waits = sp.waits_for_runners(starts, len(ready), free)
            self.assertEqual(waits, bool(ready) and free < bp.NEED_FREE)
            self.assertEqual(waits, not starts and bool(ready))  # the same as what plan decided, without reading its words
            self.assertEqual(waits, any("runners free of the" in n for n in notes) and not starts)

    def test_a_look_that_fails_in_the_middle_does_not_end_the_wait(self):
        """cubic on #192: a 502 of gh at minute 10 of the wait; the next looks go on and the setup starts when the runners are free"""
        started, sleeps, looks = self.run_main([0, 0, 0, 12], fail_looks={1})
        self.assertEqual(started, [f"key={BATCH6[0]}"])
        self.assertGreaterEqual(len(sleeps), 3)

    def test_the_first_look_failing_is_a_failure(self):
        with self.assertRaises(RuntimeError):
            self.run_main([20], fail_looks={0})

    def test_mutant_a_failing_look_ends_the_wait(self):
        src = inspect.getsource(sp.main)
        self.assertEqual(src.count("        except Exception as e:"), 1)
        ns = dict(vars(sp))
        exec(src.replace("        except Exception as e:", "        except KeyboardInterrupt as e:"), ns)
        with self.assertRaises(RuntimeError):
            self.run_main([0, 0, 0, 12], fail_looks={1}, main=ns["main"])

    def test_mutant_waiting_for_any_reason(self):
        ns = dict(vars(sp))
        src = inspect.getsource(sp.waits_for_runners).replace("not starts and ready > 0 and free < bp.NEED_FREE", "True")
        exec(src, ns)
        with mock.patch.object(sp, "waits_for_runners", ns["waits_for_runners"]):
            runs = [{"displayTitle": f"setup-auto {k} (auto)", "createdAt": "2026-11-13T17:00:00Z"} for k in R["sources"]]
            _, sleeps, _ = self.run_main([0], runs=runs)
        self.assertNotEqual(sleeps, [])  # waited with nothing ready (the structured test fails it too)
        self.assertTrue(ns["waits_for_runners"]([], 0, 0))  # the mutant waits for nothing: test_no_wait_when_nothing_is_ready fails it

    def test_mutant_no_deadline_never_ends(self):
        src = inspect.getsource(sp.main)
        self.assertEqual(src.count("or time.time() + POLL_SECONDS > deadline"), 1)
        ns = dict(vars(sp))
        exec(src.replace("or time.time() + POLL_SECONDS > deadline", ""), ns)
        n = [0]

        def sleep(s):
            n[0] += 1
            if n[0] > 50:
                raise RuntimeError("never ends")

        with self.assertRaises(RuntimeError), mock.patch.object(sp, "main", ns["main"]):
            self.run_main_with_sleep(sleep)

    def run_main_with_sleep(self, sleep):
        with tempfile.TemporaryDirectory() as d:
            Path(d, "sources.json").write_text(json.dumps({"sources": R["sources"]}))
            for k in R["set_up"]:
                Path(d, "data", "exports", k).mkdir(parents=True)
                Path(d, "data", "exports", k, "setup.ci.json").write_text("{}")
            cwd = os.getcwd()
            os.chdir(d)
            try:
                with (
                    mock.patch.object(sp.subprocess, "run", lambda args, **k: subprocess.CompletedProcess(args, 0, R["log"] if args[:2] == ["git", "log"] else "", "")),
                    mock.patch.object(sp, "setup_runs", lambda repo, since: without_batch6(R["runs"])),
                    mock.patch.object(sp, "records_prs", lambda tree: OPEN),
                    mock.patch.object(sp, "main_files", lambda tree, k, s: set()),
                    mock.patch.object(sp.bp, "runners_in_use", lambda: 20),
                    mock.patch.object(sp.time, "time", lambda: NOW),
                    mock.patch.object(sp.time, "sleep", sleep),
                    mock.patch.object(sys, "argv", ["setup_pickup.py", "--wait-minutes", "30"]),
                ):
                    sp.main()
            finally:
                os.chdir(cwd)


class Workflow(unittest.TestCase):
    def test_the_job_waits_and_its_timeout_is_longer_than_the_wait(self):
        y = yaml.safe_load((WF / "setup-pickup.yml").read_text())
        job = y["jobs"]["pickup"]
        run = "\n".join(s.get("run", "") for s in job["steps"])
        self.assertIn("--wait-minutes 30", run)
        self.assertIn("--dry-run", run)
        self.assertGreaterEqual(job["timeout-minutes"], 30 + sp.POLL_SECONDS // 60 + 5)
        self.assertLessEqual(job["timeout-minutes"], 60)  # LANE_ENABLED is read when the job starts: a waiting run must not outlive a flipped kill switch for long (cubic on #192)
        self.assertEqual(y["concurrency"], {"group": "setup-pickup", "cancel-in-progress": False})  # a waiting run is never cancelled by the next trigger

    def test_a_dry_run_gets_no_wait(self):
        text = (WF / "setup-pickup.yml").read_text()
        line = [ln for ln in text.splitlines() if "setup_pickup.py" in ln and "run:" in ln][0]
        self.assertIn('[ "$DRY" = true ] && echo --dry-run || echo --wait-minutes 30', line)


if __name__ == "__main__":
    unittest.main()
