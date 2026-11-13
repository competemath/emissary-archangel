"""bump-pickup waits for runners as setup-pickup does (bump_pickup.py), on the real case of 13 Nov 2026.

palomar-qseries-row-factorization's setup finished at 18:11:32 UTC (its real record: 40 modules, 40 exported, 0 failed; the exports commit `exports: palomar-qseries-row-factorization (runner)` is
timestamped 18:11:52). The workflow_run of setup-sharded started bump-pickup at 18:12, which printed `1 ready, 0 runners free of the 10 needed: next hour`: the runners were full of pull-request checks,
and the next hourly cron is not to be counted on (it fired 3 times in 16 hours). The bump started only because a person dispatched bump-pickup at 18:55.

Invariants: with the runners full it waits (looks again every POLL_SECONDS until the deadline) and starts the bump on the first look with NEED_FREE free; it does not wait when nothing is ready, when a bump
started, on a dry run, or with --wait-minutes 0; a look that fails after the first does not end the wait; the decision is made from numbers (key, ready, free), not from the words of the notes (cubic on #192);
decide() is the same as before the split into classify() (5,000 random states against the old function's text kept here as an oracle).
Mutants (each must fail a check): waiting for any reason; no deadline; a failing look ending the wait.
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

import bump_pickup as bp  # noqa: E402
import yaml  # noqa: E402

WF = HERE.parents[2] / ".github" / "workflows"
KEY = "palomar-qseries-row-factorization"
RECORD = {"exported": 40, "modules": 40}  # setup.ci.json of 13 Nov 2026, finishedAt 18:11:32Z
PUBLISHED = 1794593512  # 2026-11-13 18:11:52 UTC, the exports commit
NOW = PUBLISHED + 20 * 60


def old_decide(published, records, bumps, parts, free, since=bp.FIRST_SETUP, refs=None):
    """decide() as it was before classify() was split out of it (the oracle)"""
    notes, ready = [], []
    for key, when in sorted(published.items()):
        rec = records.get(key)
        if when < since:
            continue
        if bumps.get(key, 0) >= when:
            continue
        if not rec:
            notes.append(f"{key}: no setup record")
        elif rec["exported"] < 1:
            notes.append(f"{key}: exported nothing")
        elif rec["modules"] > bp.MAX_MODULES:
            notes.append(f"{key}: {rec['modules']} modules, too big for a plain bump")
        elif key in parts:
            notes.append(f"{key}: a part is open on the tree")
        elif refs is not None and refs.get(key, (None, "records not looked for"))[0] is None:
            notes.append(f"{key}: {refs.get(key, (None, 'records not looked for'))[1]}")
        else:
            ready.append((rec["modules"], key))
    if ready and free < bp.NEED_FREE:
        notes.append(f"{len(ready)} ready, {free} runners free of the {bp.NEED_FREE} needed: next hour")
        return None, notes
    ready.sort()
    return (ready[0][1] if ready else None), notes + [f"{k}: waits for the next run" for _, k in ready[1:]]


class Decision(unittest.TestCase):
    def test_the_real_case_with_full_runners_waits_and_with_free_ones_starts(self):
        for free, key, waits in ((0, None, True), (9, None, True), (10, KEY, False), (12, KEY, False)):
            got, notes = bp.decide({KEY: PUBLISHED}, {KEY: RECORD}, {}, set(), free)
            self.assertEqual(got, key, free)
            _, ready = bp.classify({KEY: PUBLISHED}, {KEY: RECORD}, {}, set())
            self.assertEqual(bp.waits_for_runners(got, len(ready), free), waits, free)
        self.assertIn("1 ready, 0 runners free of the 10 needed: next hour", bp.decide({KEY: PUBLISHED}, {KEY: RECORD}, {}, set(), 0)[1])  # the real 18:12 line

    def test_truth_table(self):
        self.assertTrue(bp.waits_for_runners(None, 1, 0))
        self.assertFalse(bp.waits_for_runners(None, 0, 0))  # nothing ready
        self.assertFalse(bp.waits_for_runners("a", 2, 4))  # something started
        self.assertFalse(bp.waits_for_runners(None, 3, bp.NEED_FREE))

    def test_5000_random_states_decide_as_before_and_wait_exactly_for_the_runners(self):
        rng = random.Random(13)
        for _ in range(5000):
            keys = [f"k{i}" for i in range(rng.randrange(0, 6))]
            published = {k: rng.choice([bp.FIRST_SETUP - 5, bp.FIRST_SETUP + rng.randrange(0, 10**6)]) for k in keys}
            records = {k: {"exported": rng.choice([0, 5, 40]), "modules": rng.choice([3, 40, bp.MAX_MODULES + 1])} for k in keys if rng.random() < 0.9}
            bumps = {k: published[k] + rng.choice([-5, 5]) for k in keys if rng.random() < 0.3}
            parts = {k for k in keys if rng.random() < 0.2}
            refs = {k: (None, "no records") if rng.random() < 0.3 else ("", "ok") for k in keys} if rng.random() < 0.5 else None
            free = rng.randrange(0, 21)
            key, notes = bp.decide(published, records, bumps, parts, free, bp.FIRST_SETUP, refs)
            self.assertEqual((key, notes), old_decide(published, records, bumps, parts, free, bp.FIRST_SETUP, refs))
            _, ready = bp.classify(published, records, bumps, parts, bp.FIRST_SETUP, refs)
            waits = bp.waits_for_runners(key, len(ready), free)
            self.assertEqual(waits, bool(ready) and free < bp.NEED_FREE)
            self.assertEqual(waits, any("runners free of the" in n for n in notes))  # the same as the note says, without reading it

    def test_mutant_waiting_for_any_reason(self):
        ns = dict(vars(bp))
        exec(inspect.getsource(bp.waits_for_runners).replace("key is None and ready > 0 and free < NEED_FREE", "True"), ns)
        self.assertTrue(ns["waits_for_runners"]("a", 0, 20))  # the truth table would refuse this


class Loop(unittest.TestCase):
    def setUp(self):
        p = mock.patch.dict(os.environ)
        p.start()
        self.addCleanup(p.stop)
        os.environ.pop("GITHUB_RUN_ID", None)
        os.environ.pop("GITHUB_REPOSITORY", None)

    def run_main(self, frees, wait=30, dry=False, fail_looks=(), main=None, bumped=False, dispatch_fails=False):
        looks, sleeps, calls = [], [], []
        clock = [NOW]
        seen = [0]
        git_log = f"@{PUBLISHED}\texports: {KEY} (runner)\n\ndata/exports/{KEY}/setup.ci.json\n"

        def run(args, **k):
            if args[:2] == ["git", "log"]:
                return subprocess.CompletedProcess(args, 0, git_log, "")
            calls.append(args)
            if dispatch_fails:
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, "", "")

        def in_use():
            i = len(looks)
            looks.append(clock[0])
            return bp.RUNNERS - frees[min(i, len(frees) - 1)]

        def bump_runs(repo, since):
            seen[0] += 1
            if seen[0] - 1 in fail_looks:
                raise RuntimeError("HTTP 502")
            return [{"displayTitle": f"bump-sharded {KEY}", "createdAt": "2026-11-13T18:30:00Z"}] if bumped else []

        def sleep(s):
            sleeps.append(s)
            if len(sleeps) > 50:
                raise RuntimeError("never ends")  # a wait with no deadline
            clock[0] += s

        import tree_records as tr

        argv = ["bump_pickup.py", "--wait-minutes", str(wait)] + (["--dry-run"] if dry else [])
        with tempfile.TemporaryDirectory() as d:
            Path(d, "sources.json").write_text(json.dumps({"sources": {KEY: {"repo": "x", "commit": "y"}}}))
            Path(d, "data", "exports", KEY).mkdir(parents=True)
            Path(d, "data", "exports", KEY, "setup.ci.json").write_text(json.dumps({**RECORD, "modules": 40}))
            cwd = os.getcwd()
            os.chdir(d)
            try:
                with (
                    mock.patch.object(bp.subprocess, "run", run),
                    mock.patch.object(bp, "bump_runs", bump_runs),
                    mock.patch.object(bp, "runners_in_use", in_use),
                    mock.patch.object(bp, "open_titles", lambda tree: []),
                    mock.patch.object(tr, "records_prs", lambda tree: []),
                    mock.patch.object(tr, "main_files", lambda tree, k, s: {"x"}),
                    mock.patch.object(tr, "records_ref", lambda k, s, m, p, t, **kw: ("", "on main")),
                    mock.patch.object(bp.time, "time", lambda: clock[0]),
                    mock.patch.object(bp.time, "sleep", sleep),
                    mock.patch.object(sys, "argv", argv),
                ):
                    (main or bp.main)()
            finally:
                os.chdir(cwd)
        return [c for c in calls if "bump-sharded.yml" in c], sleeps, looks

    def test_the_real_morning_it_waits_and_starts_when_the_runners_free(self):
        started, sleeps, looks = self.run_main([0, 3, 9, 12])
        self.assertEqual(sleeps, [bp.POLL_SECONDS] * 3)
        self.assertEqual(len(looks), 4)
        self.assertEqual(len(started), 1)
        self.assertIn(f"key={KEY}", started[0])

    def test_it_stops_at_the_deadline(self):
        started, sleeps, looks = self.run_main([0], wait=20)
        self.assertEqual(started, [])
        self.assertLessEqual(sum(sleeps), 20 * 60)
        self.assertGreater(sum(sleeps) + bp.POLL_SECONDS, 20 * 60)

    def test_no_wait_when_it_started_or_zero_minutes_or_dry_or_nothing_ready(self):
        for kw in ({"frees": [20]}, {"frees": [0], "wait": 0}, {"frees": [0], "dry": True}, {"frees": [0], "bumped": True}):
            started, sleeps, _ = self.run_main(**kw)
            self.assertEqual(sleeps, [], kw)
        self.assertEqual(len(self.run_main([20])[0]), 1)

    def test_a_look_that_fails_in_the_middle_does_not_end_the_wait(self):
        started, _, _ = self.run_main([0, 0, 0, 12], fail_looks={1})
        self.assertEqual(len(started), 1)

    def test_the_first_look_failing_is_a_failure(self):
        with self.assertRaises(RuntimeError):
            self.run_main([20], fail_looks={0})

    def test_mutant_no_deadline_never_ends(self):
        src = inspect.getsource(bp.main)
        old = "if a.dry_run or not waits or time.time() + POLL_SECONDS > deadline:"
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(bp))
        exec(src.replace(old, "if a.dry_run or not waits:"), ns)
        with self.assertRaises(RuntimeError):
            self.run_main([0], main=ns["main"])

    def test_a_look_failing_when_no_further_look_fits_fails_the_job(self):
        """cubic on #192: a failure at the last look must not end quietly after saying the next look is in five minutes"""
        with self.assertRaises(RuntimeError):
            self.run_main([0, 0], wait=5, fail_looks={1})

    def test_a_failed_dispatch_is_not_retried(self):
        """cubic on #192: gh may report an error for a request GitHub accepted; the next look would start the bump twice"""
        seen = []
        real = bp.dispatch
        with mock.patch.object(bp, "dispatch", lambda args: (seen.append(args), real(args))[1]), self.assertRaises(bp.DispatchError):
            self.run_main([0, 20, 20, 20], dispatch_fails=True)
        self.assertEqual(len(seen), 1)

    def test_mutant_a_failed_dispatch_is_retried(self):
        src = inspect.getsource(bp.main)
        old = "        except DispatchError:\n            raise  # not retried: the request may have been accepted\n"
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(bp))
        exec(src.replace(old, ""), ns)
        seen = []
        real = bp.dispatch
        with mock.patch.object(bp, "dispatch", lambda args: (seen.append(args), real(args))[1]), self.assertRaises(Exception):
            self.run_main([0, 20, 20, 20], dispatch_fails=True, main=ns["main"])
        self.assertGreater(len(seen), 1)

    def test_mutant_a_failure_at_the_last_look_ends_quietly(self):
        src = inspect.getsource(bp.main)
        old = "if first or time.time() + POLL_SECONDS > deadline:"
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(bp))
        exec(src.replace(old, "if first:"), ns)
        self.run_main([0, 0], wait=5, fail_looks={1}, main=ns["main"])

    def test_mutant_a_failing_look_ends_the_wait(self):
        src = inspect.getsource(bp.main)
        self.assertEqual(src.count("        except Exception as e:"), 1)
        ns = dict(vars(bp))
        exec(src.replace("        except Exception as e:", "        except KeyboardInterrupt as e:"), ns)
        with self.assertRaises(RuntimeError):
            self.run_main([0, 0, 0, 12], fail_looks={1}, main=ns["main"])


class Workflow(unittest.TestCase):
    def test_the_job_waits_and_its_timeout_is_longer_than_the_wait(self):
        y = yaml.safe_load((WF / "bump-pickup.yml").read_text())
        job = y["jobs"]["pickup"]
        run = "\n".join(s.get("run", "") for s in job["steps"])
        self.assertIn('[ "$DRY" = true ] && echo --dry-run || echo --wait-minutes 30', run)
        self.assertGreaterEqual(job["timeout-minutes"], 30 + bp.POLL_SECONDS // 60 + 5)
        self.assertLessEqual(job["timeout-minutes"], 60)
        self.assertEqual(y["concurrency"], {"group": "bump-pickup", "cancel-in-progress": False})


if __name__ == "__main__":
    unittest.main()
