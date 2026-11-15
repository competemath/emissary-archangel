"""waves_watch.py cancels and resumes a bump-waves run whose build chain is dead, on the REAL run that was (fixtures/real-flt-waves-run-43237206258.json: its 69 jobs with their start, end, result and failed
steps, as GitHub listed them at 23:46 UTC on 13 Nov 2026; fixtures/real-flt-plan-*-run-43529754609.json: the settings its resume was dispatched with).

The real case: job 93 of wave 15 lost its runner at 19:14 (failure, no failed step), jobs 92 and 94 of the same wave ran on until 22:58 and 23:03, waves 16 and 17 then failed at the restore step within 9 to 20
minutes each, and a person noticed at 23:44. Replayed minute by minute, the rule fires at 23:32 (the first job of a second later wave to fail at the restore step; two jobs of wave 16 had failed at 23:12 and 23:13, which could be a transient), never before, and from then on.
Invariants: never while the failed job's wave still has running jobs; never on one failed job, on failures of the same wave, or on failures of ONE later wave; never on a cancelled job; once fired it stays fired; the resume is dispatched for the
cancelled run with the settings its plan recorded and nothing else; a value that is not a plain setting is refused; a chain longer than MAX_CHAIN, a plan without its settings, a run that does not end after its cancel, and a dry run dispatch
nothing; a failed dispatch is never retried.
Mutants (each must fail a check): the later-wave condition dropped (fires at 19:14), one later failure enough (fires at 23:12), cancelled jobs counted, the chain guard dropped, the cancel not waited for.
"""

import contextlib
import inspect
import io
import json
import os
import random
import subprocess
import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path
from unittest import mock

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import waves_watch as ww  # noqa: E402

FX = HERE / "fixtures"
RUN = json.loads((FX / "real-flt-waves-run-43237206258.json").read_text())
INPUTS = json.loads((FX / "real-flt-plan-inputs-run-43529754609.json").read_text())
LANE = json.loads((FX / "real-flt-plan-lane-run-43529754609.json").read_text())
WF = HERE.parents[2] / ".github" / "workflows"


def at(iso: str) -> float:
    return datetime.fromisoformat(iso.replace("Z", "+00:00")).timestamp()


def slice_at(t: float, jobs=RUN["jobs"]) -> list[dict]:
    """the job list as GitHub would have shown it at time t: a job exists from its start; it has its result only from its end"""
    out = []
    for j in jobs:
        if not j["started_at"] or at(j["started_at"]) > t:
            continue
        done = j["completed_at"] and at(j["completed_at"]) <= t
        out.append({"name": j["name"], "status": "completed" if done else "in_progress", "conclusion": j["conclusion"] if done else None, "failed_steps": j["failed_steps"] if done else []})
    return out


T0, T1 = at("2026-11-13T14:26:00Z"), at("2026-11-13T23:46:00Z")
FIRST = None
for minute in range(int(T0), int(T1), 60):
    if ww.doomed(slice_at(minute)):
        FIRST = minute
        break


def hhmm(t: float) -> str:
    return datetime.fromtimestamp(t, timezone.utc).strftime("%H:%M")


class RealRun(unittest.TestCase):
    def test_the_fixture_is_the_real_case(self):
        sh = {int(ww.SHARD.match(j["name"]).group(2)): j for j in RUN["jobs"] if ww.SHARD.match(j["name"])}
        self.assertEqual(sh[93]["conclusion"], "failure")
        self.assertEqual(sh[93]["failed_steps"], [])  # a runner lost: no failed step
        self.assertEqual((sh[92]["conclusion"], sh[94]["conclusion"]), ("success", "success"))
        for n in (95, 96, 97, 98, 99, 100, 101, 102, 103):
            self.assertEqual(sh[n]["conclusion"], "failure", n)
            self.assertTrue(any(s.startswith(ww.RESTORE_STEP) for s in sh[n]["failed_steps"]), n)
        self.assertEqual({sh[n]["conclusion"] for n in (104, 105, 106)}, {"cancelled"})

    def test_it_fires_at_the_second_later_failure_and_not_before(self):
        self.assertIsNotNone(FIRST)
        self.assertEqual(hhmm(FIRST), "23:32")  # the first job of a second later wave (w17) failed at 23:31:39; two jobs of w16 had at 23:12 and 23:13
        # a person noticed at 23:44: 12 minutes later
        self.assertLessEqual(FIRST, at("2026-11-13T23:33:00Z"))
        self.assertLess(FIRST, at("2026-11-13T23:44:00Z"))

    def test_never_while_the_failed_jobs_wave_still_runs(self):
        for t in range(int(at("2026-11-13T19:14:20Z")), int(at("2026-11-13T22:58:00Z")), 60):
            jobs = slice_at(t)
            self.assertTrue(any(j["status"] == "in_progress" and j["name"].startswith("w15") for j in jobs), hhmm(t))
            self.assertIsNone(ww.doomed(jobs), hhmm(t))

    def test_once_fired_it_stays_fired_to_the_end(self):
        for t in range(FIRST, int(T1), 60):
            d = ww.doomed(slice_at(t))
            self.assertIsNotNone(d, hhmm(t))
            self.assertEqual((d["wave"], d["failed"]), (15, [93]))
        d = ww.doomed(slice_at(T1))
        self.assertEqual(d["later"], [95, 96, 97, 98, 99, 100, 101, 102, 103])

    def test_no_run_before_wave_15_ever_fires(self):
        for t in range(int(T0), int(at("2026-11-13T19:14:00Z")), 300):
            self.assertIsNone(ww.doomed(slice_at(t)))


class Rule(unittest.TestCase):
    def job(self, wave, shard, conclusion, restore=False):
        return {"name": f"w{wave} ({shard}) / shard", "status": "completed", "conclusion": conclusion, "failed_steps": [ww.RESTORE_STEP + " (a build-once; before any code"] if restore else []}

    def test_one_failed_job_alone_or_one_later_failure_is_not_dead(self):
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure")]))
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure"), self.job(4, 11, "failure", True)]))
        self.assertIsNotNone(ww.doomed([self.job(3, 10, "failure"), self.job(4, 11, "failure", True), self.job(5, 12, "failure", True)]))

    def test_two_failures_of_one_later_wave_are_not_dead(self):
        """cubic on #195: two jobs of one wave failing to restore may be a transient fetch failure"""
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure"), self.job(4, 11, "failure", True), self.job(4, 12, "failure", True)]))
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure")] + [self.job(4, 11 + i, "failure", True) for i in range(9)]))
        self.assertIsNotNone(ww.doomed([self.job(3, 10, "failure"), self.job(4, 11, "failure", True), self.job(5, 12, "failure", True)]))

    def test_failures_of_the_same_wave_or_earlier_waves_do_not_count(self):
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure"), self.job(3, 11, "failure", True), self.job(3, 12, "failure", True)]))
        self.assertIsNone(ww.doomed([self.job(4, 10, "failure"), self.job(3, 11, "failure", True), self.job(2, 12, "failure", True)]))

    def test_cancelled_jobs_and_failures_of_other_steps_do_not_count(self):
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure"), self.job(4, 11, "cancelled", True), self.job(4, 12, "cancelled", True)]))
        self.assertIsNone(ww.doomed([self.job(3, 10, "cancelled"), self.job(4, 11, "failure", True), self.job(4, 12, "failure", True)]))
        self.assertIsNone(ww.doomed([self.job(3, 10, "failure"), self.job(4, 11, "failure"), self.job(4, 12, "failure")]))

    def test_5000_random_runs_against_the_rule_written_apart(self):
        rng = random.Random(14)
        for _ in range(5000):
            jobs, n = [], 0
            for w in range(rng.randrange(1, 8)):
                for _ in range(rng.randrange(0, 5)):
                    n += 1
                    c = rng.choice(["success", "success", "failure", "cancelled", None])
                    jobs.append(self.job(w, n, c, restore=rng.random() < 0.5 and c == "failure"))
            if rng.random() < 0.3:
                jobs.append({"name": "plan", "status": "completed", "conclusion": "failure", "failed_steps": []})
            fails = [j for j in jobs if j["conclusion"] == "failure" and ww.SHARD.match(j["name"])]
            wv = lambda j: int(ww.SHARD.match(j["name"]).group(1))  # noqa: E731
            want = False
            if fails:
                w0 = min(map(wv, fails))
                want = len({wv(j) for j in fails if wv(j) > w0 and j["failed_steps"]}) >= 2
            self.assertEqual(ww.doomed(jobs) is not None, want)

    def test_mutant_the_later_wave_condition_dropped_fires_at_the_first_failure(self):
        src = inspect.getsource(ww.doomed)
        old = 'later = [s for s in roots if s["wave"] > first and any(x.startswith(RESTORE_STEP) for x in s["steps"])]'
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(ww))
        exec(src.replace(old, 'later = [s for s in roots if any(x.startswith(RESTORE_STEP) for x in s["steps"])]'), ns)
        t = int(at("2026-11-13T20:00:00Z"))
        self.assertIsNone(ww.doomed(slice_at(t)))
        self.assertIsNotNone(ns["doomed"](slice_at(int(at("2026-11-13T23:40:00Z")))))  # control: the mutant fires late too
        same_wave = [self.job(3, 10, "failure"), self.job(3, 11, "failure", True), self.job(4, 12, "failure", True)]
        self.assertIsNotNone(ns["doomed"](same_wave))  # the mutant counts a restore failure of the failed job's own wave as a later one: it cancels a wave that is still running
        self.assertIsNone(ww.doomed(same_wave))

    def test_mutant_one_later_failure_is_enough_fires_early(self):
        src = inspect.getsource(ww.doomed)
        old = 'if len({s["wave"] for s in later}) < LATER_FAILURES:'
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(ww))
        exec(src.replace(old, "if len(later) < 1:"), ns)
        early = int(at("2026-11-13T23:12:30Z"))
        self.assertIsNone(ww.doomed(slice_at(early)))
        self.assertIsNotNone(ns["doomed"](slice_at(early)))

    def test_mutant_jobs_counted_instead_of_waves(self):
        src = inspect.getsource(ww.doomed)
        old = 'if len({s["wave"] for s in later}) < LATER_FAILURES:'
        ns = dict(vars(ww))
        exec(src.replace(old, "if len(later) < LATER_FAILURES:"), ns)
        one_wave = [self.job(3, 10, "failure"), self.job(4, 11, "failure", True), self.job(4, 12, "failure", True)]
        self.assertIsNone(ww.doomed(one_wave))
        self.assertIsNotNone(ns["doomed"](one_wave))
        self.assertIsNotNone(ns["doomed"](slice_at(at("2026-11-13T23:14:00Z"))))  # the real run, 18 minutes early

    def test_mutant_cancelled_jobs_counted(self):
        src = inspect.getsource(ww.doomed)
        old = 'roots = [s for s in shards if s["conclusion"] == "failure"]'
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(ww))
        exec(src.replace(old, 'roots = [s for s in shards if s["conclusion"] in ("failure", "cancelled")]'), ns)
        jobs = [self.job(3, 10, "cancelled"), self.job(4, 11, "failure", True), self.job(5, 12, "failure", True)]
        self.assertIsNone(ww.doomed(jobs))
        self.assertIsNotNone(ns["doomed"](jobs))


class Dispatch(unittest.TestCase):
    def test_the_real_resume_is_what_was_dispatched_by_hand(self):
        args = ww.dispatch_args("flt-anthropic", 43237206258, INPUTS, LANE)
        self.assertEqual(args[:9], ["gh", "workflow", "run", "bump-waves.yml", "-R", "competemath/emissary-archangel", "--ref", "main", "-f"])
        fields = dict(a.split("=", 1) for a in args[9:] if "=" in a)
        self.assertEqual(fields["key"], "flt-anthropic")
        self.assertEqual(fields["reuse_from"], "43237206258")
        self.assertEqual(fields["from_tree"], "true")  # without it the plan step stops: numbered differently
        self.assertEqual({k: fields[k] for k in ("imports", "swap_gb", "build_timeout_min", "mathlib", "toolchain")}, {"imports": "faithful", "swap_gb": "48", "build_timeout_min": "170", "mathlib": "v4.34.0-rc2", "toolchain": "leanprover/lean4:v4.34.0-rc2"})
        self.assertNotIn("tengoku_ref", fields)  # empty: the default

    def test_a_value_that_is_not_a_plain_setting_is_refused(self):
        for bad in ("a b", "x;rm", "$(id)", "`id`", "a\nb", "x\n", "x'y", 'x"y'):
            with self.assertRaises(ww.WatchError, msg=bad):
                ww.dispatch_args("flt-anthropic", 1, {**INPUTS, "tengoku_ref": bad}, LANE)
        for bad in ("Flt", "a b", "-x", "", "a;b", "flt-anthropic\n"):
            with self.assertRaises(ww.WatchError, msg=bad):
                ww.dispatch_args(bad, 1, INPUTS, LANE)
        with self.assertRaises(ww.WatchError):
            ww.dispatch_args("flt-anthropic", 1, INPUTS, {"from_tree": "maybe"})
        with self.assertRaises(ValueError):
            ww.dispatch_args("flt-anthropic", "1; x", INPUTS, LANE)

    def test_a_plan_without_its_settings_is_refused_before_anything_is_cancelled(self):
        """cubic on #195: missing settings would be dispatched as empty and the resume's plan step would stop on the mismatch"""
        for k in ww.SETTINGS:
            with self.assertRaises(ww.WatchError, msg=k):
                ww.dispatch_args("flt-anthropic", 1, {a: b for a, b in INPUTS.items() if a != k}, LANE)
        with self.assertRaises(ww.WatchError):
            ww.dispatch_args("flt-anthropic", 1, INPUTS, {})
        _, calls = Flow().run_incomplete()
        self.assertEqual(calls, [])

    def test_the_chain_length_follows_the_lanes(self):
        lanes = {"2": {"reuse_from": "1"}, "1": {}}
        self.assertEqual(ww.chain_length({"reuse_from": "2"}, lanes.get), 3)
        self.assertEqual(ww.chain_length({}, lanes.get), 1)
        self.assertGreater(ww.chain_length({"reuse_from": "2"}, {"2": {"reuse_from": "2"}}.get), ww.MAX_CHAIN)  # a loop is never resumed


class Flow(unittest.TestCase):
    def run_main(self, argv=(), chain=1, ends=True, dispatch_fails=False, jobs=None, mutate=None, runs=1):
        """main() with the world faked; `mutate=(old, new)` runs a broken copy of main() instead (its functions are looked up in a copy of the module, so the fakes go there)"""
        calls = []
        self.last_calls = calls
        jobs = jobs if jobs is not None else slice_at(at("2026-11-13T23:40:00Z"))

        def run(args, **k):
            calls.append(list(args))
            if args[:3] == ["gh", "workflow", "run"] and dispatch_fails:
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, "", "")

        fake_sub = mock.Mock(run=run, CalledProcessError=subprocess.CalledProcessError)
        lane = {"from_tree": "true", **({"reuse_from": "7"} if chain > 1 else {})}
        fakes = {
            "running": lambda: [{"id": 43237206258 + i, "title": "bump-waves flt-anthropic"} for i in range(runs)],
            "jobs_of": lambda r: jobs,
            "plan_files": lambda r, k: (INPUTS, lane),
            "chain_length": lambda lane_, lanes: chain,
            "ended": lambda r, **k: ends,
        }
        if mutate:
            src = inspect.getsource(ww.look)
            self.assertEqual(src.count(mutate[0]), 1, mutate[0])
            ns = dict(vars(ww))
            ns.update(fakes)
            ns["subprocess"] = fake_sub
            exec(src.replace(*mutate), ns)
            ns["look"](False)
            rc = 0
        else:
            with contextlib.ExitStack() as st:
                for k, v in fakes.items():
                    st.enter_context(mock.patch.object(ww, k, v))
                st.enter_context(mock.patch.object(ww, "subprocess", fake_sub))
                rc = ww.main(list(argv))
        return rc, calls

    def run_incomplete(self):
        """a dead run whose plan has no settings: nothing is cancelled"""
        calls = []
        fake_sub = mock.Mock(run=lambda args, **k: calls.append(list(args)), CalledProcessError=subprocess.CalledProcessError)
        with contextlib.ExitStack() as st:
            st.enter_context(mock.patch.object(ww, "running", lambda: [{"id": 5, "title": "bump-waves flt-anthropic"}]))
            st.enter_context(mock.patch.object(ww, "jobs_of", lambda r: slice_at(at("2026-11-13T23:40:00Z"))))
            st.enter_context(mock.patch.object(ww, "plan_files", lambda r, k: ({}, {})))
            st.enter_context(mock.patch.object(ww, "chain_length", lambda lane_, lanes: 1))
            st.enter_context(mock.patch.object(ww, "subprocess", fake_sub))
            with self.assertRaises(ww.WatchError):
                ww.main([])
        return None, calls

    def test_a_dead_run_is_cancelled_then_resumed(self):
        rc, calls = self.run_main()
        self.assertEqual(rc, 0)
        self.assertEqual([c[:3] for c in calls], [["gh", "run", "cancel"], ["gh", "workflow", "run"]])
        self.assertIn("reuse_from=43237206258", calls[1])
        self.assertIn("from_tree=true", calls[1])

    def test_a_queued_run_counts_as_alive_and_is_not_judged(self):
        """cubic on #197: a run that was just requested is queued; the watch must not end before it starts"""
        calls = []
        with (
            mock.patch.object(ww, "running", lambda: [{"id": 7, "title": "bump-waves flt-anthropic", "status": "queued"}]),
            mock.patch.object(ww, "jobs_of", lambda r: calls.append(r) or []),
        ):
            self.assertEqual(ww.look(False), (1, 0))
        self.assertEqual(calls, [])  # its jobs are not read: there are none

    def test_running_lists_queued_runs_too_without_a_run_twice(self):
        seen = []

        def fake_gh(*args):
            seen.append(args[1].split("status=")[1].split("&")[0])
            ids = [1, 2] if "in_progress" in args[1] else [2, 3]
            return json.dumps({"workflow_runs": [{"id": i, "display_title": f"bump-waves k{i}"} for i in ids]})

        with mock.patch.object(ww, "gh", fake_gh):
            got = ww.running()
        self.assertEqual(seen, ["in_progress", "queued"])
        self.assertEqual([(r["id"], r["status"]) for r in got], [(1, "in_progress"), (2, "in_progress"), (3, "queued")])

    def test_read_wraps_failures_of_reading_and_nothing_else(self):
        def boom():
            raise subprocess.CalledProcessError(1, ["gh"])

        def bad_json():
            return json.loads("{")

        def refusal():
            raise ww.WatchError("a refusal")

        with self.assertRaises(ww.ReadFailure):
            ww.read(boom)
        with self.assertRaises(ww.ReadFailure):
            ww.read(bad_json)
        with self.assertRaises(ww.WatchError):
            ww.read(refusal)
        self.assertEqual(ww.read(lambda x: x + 1, 1), 2)

    def test_the_cap_is_per_look_not_per_job(self):
        """cubic on #197: a third dead run is resumed by the next look, not five hours later"""
        _, calls = self.run_main(runs=3)
        self.assertEqual(len([c for c in calls if c[:3] == ["gh", "workflow", "run"]]), ww.MAX_RESUMES)
        _, calls2 = self.run_main(runs=1)
        self.assertEqual(len([c for c in calls2 if c[:3] == ["gh", "workflow", "run"]]), 1)  # a look of its own starts at zero

    def test_an_alive_run_is_left_alone(self):
        rc, calls = self.run_main(jobs=slice_at(at("2026-11-13T20:00:00Z")))
        self.assertEqual(calls, [])

    def test_a_dry_run_changes_nothing(self):
        _, calls = self.run_main(argv=["--dry-run"])
        self.assertEqual(calls, [])

    def test_a_long_chain_is_left_to_a_person(self):
        _, calls = self.run_main(chain=ww.MAX_CHAIN + 1)
        self.assertEqual(calls, [])
        _, calls = self.run_main(chain=ww.MAX_CHAIN)  # the resume would be the MAX_CHAIN + 1st run (cubic on #201)
        self.assertEqual(calls, [])
        _, calls = self.run_main(chain=ww.MAX_CHAIN - 1)
        self.assertEqual(len(calls), 2)

    def test_a_run_that_does_not_end_is_not_resumed(self):
        with self.assertRaises(ww.WatchError):
            self.run_main(ends=False)

    def test_a_failed_dispatch_is_not_retried(self):
        """cubic on #195: two dead runs; the first dispatch fails; exactly one dispatch was tried and the second run was not touched"""
        calls = []
        try:
            self.run_main(dispatch_fails=True, runs=2)
        except subprocess.CalledProcessError:
            pass
        else:
            self.fail("a failed dispatch must end the look")
        for _ in range(1):
            calls = self.last_calls
        self.assertEqual(len([c for c in calls if c[:3] == ["gh", "workflow", "run"]]), 1)
        self.assertEqual(len([c for c in calls if c[:3] == ["gh", "run", "cancel"]]), 1)

    def test_at_most_two_runs_are_resumed_in_one_look(self):
        _, calls = self.run_main(runs=3)
        self.assertEqual(len([c for c in calls if c[:3] == ["gh", "workflow", "run"]]), ww.MAX_RESUMES)

    def test_every_run_in_progress_is_looked_at_not_the_first_page(self):
        pages = []

        def fake_gh(*args):
            page = int(args[1].rsplit("page=", 1)[1])
            pages.append(page)
            n = 100 if page < 3 else 7
            return json.dumps({"workflow_runs": [{"id": page * 1000 + i, "display_title": "bump-waves k"} for i in range(n)]})

        with mock.patch.object(ww, "gh", fake_gh):
            got = ww.running()
        self.assertEqual((pages, len(got)), ([1, 2, 3, 1, 2, 3], 207))  # three pages of each status; the ids repeat, so each run is listed once

    def test_mutant_the_chain_guard_dropped(self):
        _, calls = self.run_main(chain=ww.MAX_CHAIN, mutate=("if n >= MAX_CHAIN:", "if False:"))
        self.assertEqual(len(calls), 2)  # the mutant resumes a chain that test_a_long_chain_is_left_to_a_person leaves alone

    def test_mutant_the_cancel_not_waited_for(self):
        _, calls = self.run_main(ends=False, mutate=('if not ended(r["id"]):', "if False:"))
        self.assertEqual(len(calls), 2)  # dispatched while the old run still ran: test_a_run_that_does_not_end_is_not_resumed refuses it


class Loop(unittest.TestCase):
    """the watch of a run: looks every LOOK_SECONDS while one is in progress, up to --wait-minutes, then dispatches itself once more"""

    def run_loop(self, argv, alive=(1,), fail_looks=(), dispatch_fails=False, mutate=None, hard_fail_looks=()):
        clock = [1000.0]
        looks, sleeps, calls = [], [], []
        self.looks, self.sleeps, self.calls = looks, sleeps, calls  # readable after a raise

        def look(dry, so_far=0):
            i = len(looks)
            looks.append(clock[0])
            if i in fail_looks:
                raise ww.ReadFailure("HTTP 502")
            if i in hard_fail_looks:
                raise subprocess.CalledProcessError(1, ["gh", "run", "cancel"])
            return alive[min(i, len(alive) - 1)], 0

        def run(args, **k):
            calls.append(list(args))
            if dispatch_fails:
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, "", "")

        def sleep(s_):
            sleeps.append(s_)
            clock[0] += s_

        fake_sub = mock.Mock(run=run, CalledProcessError=subprocess.CalledProcessError)
        if mutate:
            src = inspect.getsource(ww.main)
            self.assertEqual(src.count(mutate[0]), 1, mutate[0])
            ns = dict(vars(ww))
            ns.update(look=look, subprocess=fake_sub)
            exec(src.replace(*mutate), ns)
            ns["main"](list(argv), sleep=sleep, clock=lambda: clock[0])
        else:
            with mock.patch.object(ww, "look", look), mock.patch.object(ww, "subprocess", fake_sub):
                ww.main(list(argv), sleep=sleep, clock=lambda: clock[0])
        return calls

    def test_it_keeps_looking_while_a_run_lives_and_stops_when_none_does(self):
        self.run_loop(["--wait-minutes", "60"], alive=(1, 1, 1, 1, 0))
        self.assertEqual(self.sleeps, [ww.LOOK_SECONDS] * 4)
        self.assertEqual(len(self.looks), 5)
        self.assertEqual(self.calls, [])  # nothing left to watch: no new job

    def test_at_the_end_of_its_time_it_dispatches_itself_once(self):
        calls = self.run_loop(["--wait-minutes", "30"], alive=(1,))
        self.assertEqual(len(self.looks), 7)  # 0, 5, ... 30 minutes
        self.assertEqual(sum(self.sleeps), 30 * 60)
        self.assertEqual(calls, [["gh", "workflow", "run", "waves-watch.yml", "-R", "competemath/emissary-archangel", "--ref", "main", "-f", "dry_run=false"]])

    def test_no_wait_means_one_look_and_no_new_job(self):
        calls = self.run_loop([], alive=(1,))
        self.assertEqual((len(self.looks), self.sleeps, calls), (1, [], []))
        calls = self.run_loop(["--dry-run", "--wait-minutes", "60"], alive=(1,))
        self.assertEqual((len(self.looks), self.sleeps, calls), (1, [], []))

    def test_a_look_that_fails_in_the_middle_does_not_end_the_watch(self):
        self.run_loop(["--wait-minutes", "30"], alive=(1,), fail_looks={2})
        self.assertEqual(len(self.looks), 7)

    def test_the_first_look_and_the_last_look_failing_are_failures(self):
        with self.assertRaises(ww.ReadFailure):
            self.run_loop(["--wait-minutes", "30"], fail_looks={0})
        with self.assertRaises(ww.ReadFailure):
            self.run_loop(["--wait-minutes", "30"], alive=(1,), fail_looks={6})

    def test_only_a_failed_read_is_tolerated(self):
        """cubic on #197: a cancel or a dispatch that fails (after a run was cancelled, no resume) ends the watch with the error, in the middle of the loop too"""
        with self.assertRaises(subprocess.CalledProcessError):
            self.run_loop(["--wait-minutes", "30"], alive=(1,), hard_fail_looks={2})
        self.assertEqual(len(self.looks), 3)

    def test_a_failed_self_dispatch_is_not_retried(self):
        with self.assertRaises(subprocess.CalledProcessError):
            self.run_loop(["--wait-minutes", "30"], alive=(1,), dispatch_fails=True)
        self.assertEqual(len([c for c in self.calls if c[:3] == ["gh", "workflow", "run"]]), 1)

    def test_mutant_it_looks_once_and_stops(self):
        self.run_loop(["--wait-minutes", "30"], alive=(1,), mutate=("        sleep(LOOK_SECONDS)\n", "        break\n"))
        self.assertEqual(len(self.looks), 1)  # test_it_keeps_looking... needs 5

    def test_mutant_it_never_dispatches_itself(self):
        self.run_loop(["--wait-minutes", "30"], alive=(1,), mutate=('subprocess.run(["gh", "workflow", "run", "waves-watch.yml", "-R", REPO, "--ref", "main", "-f", "dry_run=false"], check=True)', "pass"))
        self.assertEqual(self.calls, [])  # the watch would end at the first job's end: test_at_the_end_of_its_time... needs the dispatch


ENDED = json.loads((FX / "real-flt-waves-run-43587360841.json").read_text())


def ended_jobs(last="failure_at_restore") -> list[dict]:
    """the job list of that run: REAL as listed after its cancel, except that job 110 (cancelled while it waited at its restore step) is what it would have become, a failure at that step (the run then ENDS failed)"""
    out = []
    for j in ENDED["jobs"]:
        d = {"name": j["name"], "status": "completed", "conclusion": j["conclusion"], "failed_steps": list(j["failed_steps"])}
        if j["name"] == "w20 (110) / shard" and last == "failure_at_restore":
            d.update(conclusion="failure", failed_steps=[ww.RESTORE_STEP + " (a build-once; before any code of the library runs, the one step with a token)"])
        out.append(d)
    return out


RUN_ENDED = 43587360841
NOW = at("2026-11-14T23:50:00Z")


class EndedRun(unittest.TestCase):
    """14 Nov 2026, run 43587360841: shard 109 of wave 19 lost its runner after 55 minutes; the one job after it (110, wave 20) could not restore its pack; the run ENDS failed. The rule of a run in progress (two later waves) never fires and
    a watch of runs in progress never sees an ended run, so a person resumed it by hand (23:33). A run that ended failed with a shard job that failed and one that succeeded is resumed (reuse_from), once."""

    def run_look(self, dry=False, budget=2, jobs=None, continues=False, chain=3, runs=None, dispatch_fails=False, mutate=None):
        calls = []
        self.calls = calls

        def run(args, **k):
            calls.append(list(args))
            if args[:3] == ["gh", "workflow", "run"] and dispatch_fails:
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, "", "")

        fake_sub = mock.Mock(run=run, CalledProcessError=subprocess.CalledProcessError)
        jobs = jobs if jobs is not None else ended_jobs()
        runs = runs if runs is not None else [{"id": RUN_ENDED, "title": "bump-waves flt-anthropic"}]
        fakes = {
            "failed_runs": lambda: runs,
            "jobs_of": lambda r: jobs,
            "continued": lambda r, k: continues,
            "plan_files": lambda r, k: (INPUTS, {"from_tree": "true", "reuse_from": "43529754609"}),
            "chain_length": lambda lane_, lanes: chain,
        }
        if mutate:
            src = inspect.getsource(ww.look_ended) if mutate[0] != "ended_dead" else inspect.getsource(ww.ended_dead)
            self.assertEqual(src.count(mutate[1]), 1, mutate[1])
            ns = dict(vars(ww))
            ns.update(fakes)
            ns["subprocess"] = fake_sub
            exec(src.replace(mutate[1], mutate[2]), ns)
            if mutate[0] == "ended_dead":
                fakes_ns = ns["ended_dead"]
                ns2 = dict(vars(ww))
                ns2.update(fakes)
                ns2["ended_dead"] = fakes_ns
                ns2["subprocess"] = fake_sub
                exec(inspect.getsource(ww.look_ended), ns2)
                return ns2["look_ended"](dry, budget), calls
            return ns["look_ended"](dry, budget), calls
        with contextlib.ExitStack() as st:
            for k, v in fakes.items():
                st.enter_context(mock.patch.object(ww, k, v))
            st.enter_context(mock.patch.object(ww, "subprocess", fake_sub))
            return ww.look_ended(dry, budget), calls

    def test_the_fixture_is_the_real_case(self):
        sh = {int(ww.SHARD.match(j["name"]).group(2)): j for j in ENDED["jobs"] if ww.SHARD.match(j["name"])}
        self.assertEqual((sh[109]["conclusion"], sh[109]["failed_steps"]), ("failure", []))  # a runner lost: no failed step
        self.assertEqual({sh[n]["conclusion"] for n in (99, 100, 101, 102, 103, 104, 105, 106, 107, 108)}, {"success"})
        self.assertEqual(sh[110]["conclusion"], "cancelled")
        self.assertIsNone(ww.doomed(ended_jobs()), "the rule of a run in progress needs TWO later waves: one is not enough")

    def test_the_real_run_is_resumed_with_the_settings_of_its_plan_and_without_a_cancel(self):
        n, calls = self.run_look()
        self.assertEqual(n, 1)
        self.assertEqual([c[:3] for c in calls], [["gh", "workflow", "run"]])
        self.assertIn(f"reuse_from={RUN_ENDED}", calls[0])
        self.assertIn("from_tree=true", calls[0])
        self.assertIn("swap_gb=48", calls[0])

    def test_the_cancelled_job_of_the_real_list_is_resumed_too(self):
        n, calls = self.run_look(jobs=ended_jobs("cancelled"))
        self.assertEqual(n, 1)

    def test_a_run_that_made_no_progress_is_not_resumed_again(self):
        jobs = [j for j in ended_jobs() if j["conclusion"] != "success"]
        self.assertEqual(self.run_look(jobs=jobs), (0, []))

    def test_a_run_without_a_failed_shard_is_not_resumed(self):
        jobs = [dict(j, conclusion="success") if j["conclusion"] == "failure" else dict(j) for j in ended_jobs()]
        self.assertEqual(self.run_look(jobs=jobs), (0, []))
        jobs = [dict(j, conclusion="cancelled") if j["conclusion"] == "failure" else dict(j) for j in ended_jobs()]
        self.assertEqual(self.run_look(jobs=jobs), (0, []))  # a cancelled job is no failure

    def test_a_run_that_a_newer_run_continues_is_left_alone(self):
        self.assertEqual(self.run_look(continues=True), (0, []))

    def test_a_long_chain_is_left_to_a_person(self):
        self.assertEqual(self.run_look(chain=ww.MAX_CHAIN + 1), (0, []))
        self.assertEqual(self.run_look(chain=ww.MAX_CHAIN), (0, []))  # the resume would be the MAX_CHAIN + 1st run (cubic on #201)
        self.assertEqual(self.run_look(chain=ww.MAX_CHAIN - 1)[0], 1)

    def test_a_dry_run_changes_nothing(self):
        self.assertEqual(self.run_look(dry=True), (0, []))

    def test_a_dry_run_previews_no_more_than_the_budget_allows(self):
        runs = [{"id": RUN_ENDED + i, "title": "bump-waves flt-anthropic"} for i in range(5)]
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            n, calls = self.run_look(dry=True, runs=runs, budget=2)
        self.assertEqual((n, calls), (0, []))  # nothing dispatched, and not reported as resumed
        self.assertEqual(out.getvalue().count("dry run: would dispatch"), 2)  # what a real look with this budget would do (cubic on #201)
        self.assertIn("the rest is left to the next look", out.getvalue())

    def test_at_most_the_budget_is_resumed(self):
        runs = [{"id": RUN_ENDED + i, "title": "bump-waves flt-anthropic"} for i in range(3)]
        self.assertEqual(self.run_look(runs=runs, budget=2)[0], 2)
        self.assertEqual(self.run_look(runs=runs, budget=0)[0], 0)

    def test_a_failed_dispatch_is_not_retried(self):
        with self.assertRaises(subprocess.CalledProcessError):
            self.run_look(dispatch_fails=True)
        self.assertEqual(len(self.calls), 1)

    def test_a_title_without_a_source_key_is_refused(self):
        with self.assertRaises(ww.WatchError):
            self.run_look(runs=[{"id": 5, "title": "something else"}])

    def test_failed_runs_lists_only_failures_of_the_last_hours(self):
        def clock():
            return NOW

        listing = {
            "workflow_runs": [
                {"id": 3, "conclusion": "failure", "updated_at": "2026-11-14T23:30:00Z", "display_title": "bump-waves flt-anthropic"},
                {"id": 2, "conclusion": "cancelled", "updated_at": "2026-11-14T23:31:00Z", "display_title": "bump-waves flt-anthropic"},
                {"id": 1, "conclusion": "success", "updated_at": "2026-11-14T23:32:00Z", "display_title": "bump-waves flt-anthropic"},
                {"id": 0, "conclusion": "failure", "updated_at": "2026-11-13T09:00:00Z", "display_title": "bump-waves flt-anthropic"},
            ]
        }
        with mock.patch.object(ww, "gh", lambda *a: json.dumps(listing)):
            self.assertEqual([r["id"] for r in ww.failed_runs(clock)], [3])

    def test_continued_reads_the_lane_of_newer_runs_of_the_same_source_only(self):
        listing = {"workflow_runs": [
            {"id": 12, "status": "in_progress", "display_title": "bump-waves flt-anthropic"},
            {"id": 11, "status": "completed", "display_title": "bump-waves hironaka"},
            {"id": 9, "status": "completed", "display_title": "bump-waves flt-anthropic"},
        ]}
        lanes = {12: {"reuse_from": "10"}, 11: {"reuse_from": "10"}, 9: {"reuse_from": "10"}}
        read_runs = []

        def plan(run, key):
            read_runs.append(run)
            return {}, lanes[int(run)]

        with mock.patch.object(ww, "gh", lambda *a: json.dumps(listing)), mock.patch.object(ww, "plan_files", plan), mock.patch.object(ww, "has_plan", lambda run, key: True):
            self.assertTrue(ww.continued(10, "flt-anthropic"))
            self.assertEqual(read_runs, [12])  # newer and the same source: 11 is another source, 9 is older
            lanes[12] = {"reuse_from": "8"}
            self.assertFalse(ww.continued(10, "flt-anthropic"))

    def test_a_newer_run_with_no_plan_does_not_abort_the_look(self):
        """cubic on #201: a queued run, or one that failed before its plan step, has no plan artifact: `gh run download` fails on it, and that used to raise out of the whole look."""
        listing = {"workflow_runs": [
            {"id": 13, "status": "queued", "display_title": "bump-waves flt-anthropic"},
            {"id": 12, "status": "completed", "display_title": "bump-waves flt-anthropic"},
        ]}
        plans = {13: False, 12: False}
        downloads = []

        def plan(run, key):
            downloads.append(int(run))
            raise AssertionError("a plan that is not there must not be downloaded")

        with mock.patch.object(ww, "gh", lambda *a: json.dumps(listing)), mock.patch.object(ww, "has_plan", lambda run, key: plans[int(run)]), mock.patch.object(ww, "plan_files", plan):
            self.assertTrue(ww.continued(10, "flt-anthropic"))  # 13 may be the resume that was just dispatched: wait for the next look, never a second resume
            self.assertEqual(downloads, [])  # no download of a plan that is not there
            listing["workflow_runs"] = listing["workflow_runs"][1:]
            self.assertFalse(ww.continued(10, "flt-anthropic"))  # 12 ended without a plan: it continues nothing, and the run is not blocked for ever
            self.assertEqual(downloads, [])

    def test_a_failed_read_of_a_plan_that_exists_is_a_failed_read(self):
        listing = {"workflow_runs": [{"id": 12, "status": "completed", "display_title": "bump-waves flt-anthropic"}]}

        def plan(run, key):
            raise subprocess.CalledProcessError(1, ["gh", "run", "download"])

        with mock.patch.object(ww, "gh", lambda *a: json.dumps(listing)), mock.patch.object(ww, "has_plan", lambda run, key: True), mock.patch.object(ww, "plan_files", plan):
            with self.assertRaises(ww.ReadFailure):  # tolerated by a later look, never read as "not continued"
                ww.continued(10, "flt-anthropic")

    def test_has_plan_asks_for_this_sources_plan_artifact_and_ignores_expired_ones(self):
        asked = []

        def gh(*a):
            asked.append(a)
            return json.dumps({"artifacts": [{"name": "plan-flt-anthropic", "expired": True}]})

        with mock.patch.object(ww, "gh", gh):
            self.assertFalse(ww.has_plan(7, "flt-anthropic"))
        self.assertIn("runs/7/artifacts?name=plan-flt-anthropic", asked[0][1])
        with mock.patch.object(ww, "gh", lambda *a: json.dumps({"artifacts": [{"name": "plan-flt-anthropic", "expired": False}]})):
            self.assertTrue(ww.has_plan(7, "flt-anthropic"))
        with mock.patch.object(ww, "gh", lambda *a: json.dumps({"artifacts": []})):
            self.assertFalse(ww.has_plan(7, "flt-anthropic"))

    def test_the_listings_read_every_page_not_the_first_30(self):
        """cubic on #201: `per_page=30` looked at the newest 30 runs of any source; a failure or a continuation on a later page was missed."""
        title = "bump-waves flt-anthropic"
        others = [{"id": 1000 - i, "status": "completed", "conclusion": "success", "created_at": "2026-11-14T10:00:00Z", "updated_at": "2026-11-14T11:00:00Z", "display_title": "bump-waves tda-lib"} for i in range(100)]
        page2 = [{"id": 800, "status": "completed", "conclusion": "failure", "created_at": "2026-11-14T08:00:00Z", "updated_at": "2026-11-14T22:00:00Z", "display_title": title},
                 {"id": 790, "status": "completed", "conclusion": "failure", "created_at": "2026-11-14T07:00:00Z", "updated_at": "2026-11-14T08:00:00Z", "display_title": title}]
        pages = {1: others, 2: page2}
        asked = []

        def gh(*a):
            asked.append(a[1])
            page = int(a[1].rsplit("page=", 1)[1])
            return json.dumps({"workflow_runs": pages.get(page, [])})

        with mock.patch.object(ww, "gh", gh):
            got = ww.failed_runs(lambda: NOW)
            self.assertEqual([r["id"] for r in got], [800, 790])  # both pages read; 790 failed 15 hours before NOW
            self.assertEqual(len(asked), 2)
            asked.clear()
            pages[2] = [{"id": 1100, "status": "in_progress", "display_title": title}, {"id": 900, "status": "completed", "display_title": title}, {"id": 700, "status": "completed", "display_title": title}]
            pages[1] = [{"id": 1200 - i, "status": "completed", "display_title": "bump-waves tda-lib"} for i in range(100)]
            self.assertEqual(ww.newer_runs(800, "flt-anthropic"), [(1100, "in_progress"), (900, "completed")])  # a continuation on page 2; 700 is older than the run: the listing stops there
        self.assertEqual(len(asked), 2)

    def test_a_listing_stops_at_the_lookback(self):
        old = {"id": 5, "conclusion": "failure", "created_at": "2026-10-01T00:00:00Z", "updated_at": "2026-11-14T23:00:00Z", "display_title": "bump-waves flt-anthropic"}
        pages = [json.dumps({"workflow_runs": [dict(old, id=100 - i, created_at="2026-11-14T00:00:00Z") for i in range(100)]}), json.dumps({"workflow_runs": [old] * 100}), "never read"]
        asked = []

        def gh(*a):
            asked.append(a[1])
            return pages[len(asked) - 1]

        with mock.patch.object(ww, "gh", gh):
            ww.failed_runs(lambda: NOW)
        self.assertEqual(len(asked), 2)  # page 2 starts with a run created before the lookback: the listing ends, page 3 is never asked for

    def test_5000_random_job_lists_against_the_rule_written_apart(self):
        rng = random.Random(14112026)
        for _ in range(5000):
            jobs = []
            for w in range(14, 21):
                for sh in range(w * 5, w * 5 + rng.randint(1, 4)):
                    jobs.append({"name": f"w{w} ({sh}) / shard", "status": "completed", "conclusion": rng.choice(["success", "success", "failure", "cancelled", "skipped", None]), "failed_steps": []})
            rng.shuffle(jobs)
            conclusions = [j["conclusion"] for j in jobs]
            want = "failure" in conclusions and "success" in conclusions
            self.assertEqual(ww.ended_dead(jobs) is not None, want, conclusions)

    def test_mutant_a_run_without_progress_is_resumed_again(self):
        jobs = [j for j in ended_jobs() if j["conclusion"] != "success"]
        n, calls = self.run_look(jobs=jobs, mutate=("ended_dead", "if not failed or not ok:", "if not failed:"))
        self.assertEqual(n, 1)  # the mutant dispatches: the test above fails on it

    def test_mutant_the_newer_run_check_dropped_resumes_it_twice(self):
        n, calls = self.run_look(continues=True, mutate=("look_ended", "if continued(r[\"id\"], key):", "if False:"))
        self.assertEqual(n, 1)

    def test_mutant_the_chain_guard_dropped(self):
        n, calls = self.run_look(chain=ww.MAX_CHAIN, mutate=("look_ended", "if length >= MAX_CHAIN:", "if False:"))
        self.assertEqual(n, 1)

    def test_mutant_a_cancelled_job_counts_as_failed(self):
        jobs = [dict(j, conclusion="cancelled") if j["conclusion"] == "failure" else dict(j) for j in ended_jobs()]
        n, calls = self.run_look(jobs=jobs, mutate=("ended_dead", 's["conclusion"] == "failure")', 's["conclusion"] in ("failure", "cancelled"))'))
        self.assertEqual(n, 1)

    def test_main_resumes_ended_runs_only_with_the_flag(self):
        seen = []

        def look(dry, so_far=0):
            return 0, 0

        def look_ended(dry, budget):
            seen.append(budget)
            return 1

        clock = [1000.0]
        with mock.patch.object(ww, "look", look), mock.patch.object(ww, "look_ended", look_ended), mock.patch.object(ww, "subprocess", mock.Mock(run=lambda *a, **k: None, CalledProcessError=subprocess.CalledProcessError)):
            ww.main([], sleep=lambda s_: None, clock=lambda: clock[0])
            self.assertEqual(seen, [])
            ww.main(["--resume-ended"], sleep=lambda s_: None, clock=lambda: clock[0])
            self.assertEqual(seen, [ww.MAX_RESUMES])  # one look (no --wait-minutes): the watch ends after it

    def test_the_watch_goes_on_looking_at_what_it_dispatched(self):
        """cubic on #201: alive was 0 and the resume dispatched is a run in progress: with --wait-minutes there is a second look (the first test names what it checks: one look without the flag)."""
        budgets, sleeps = [], []
        answers = iter([1, 0])  # the first look dispatches a resume, the second finds nothing to do

        def look_ended(dry, budget):
            budgets.append(budget)
            return next(answers)

        clock = [1000.0]

        def sleep(s_):
            sleeps.append(s_)
            clock[0] += s_

        # look() sees no run in progress at both looks: only the resume this watch dispatched keeps it looking
        with mock.patch.object(ww, "look", lambda dry, so_far=0: (0, 0)), mock.patch.object(ww, "look_ended", look_ended), mock.patch.object(ww, "subprocess", mock.Mock(run=lambda *a, **k: None, CalledProcessError=subprocess.CalledProcessError)):
            ww.main(["--resume-ended", "--wait-minutes", "60"], sleep=sleep, clock=lambda: clock[0])
        self.assertEqual(budgets, [ww.MAX_RESUMES, ww.MAX_RESUMES])  # two looks
        self.assertEqual(sleeps, [ww.LOOK_SECONDS])

    def test_the_workflow_passes_the_flag_in_both_branches(self):
        text = (WF / "waves-watch.yml").read_text()
        self.assertIn("scripts/bump/waves_watch.py --resume-ended $([", text)
        self.assertIn("--dry-run || echo --wait-minutes 300", text)


class Docs(unittest.TestCase):
    def test_the_module_says_how_often_it_looks(self):
        self.assertIn("every LOOK_SECONDS (five minutes)", ww.__doc__)
        self.assertEqual(ww.LOOK_SECONDS, 300)


class Workflow(unittest.TestCase):
    def test_shape(self):
        y = yaml.safe_load((WF / "waves-watch.yml").read_text())
        on = y[True]
        self.assertEqual(on["workflow_run"], {"workflows": ["setup-sharded", "bump-sharded", "bump-waves"], "types": ["requested", "completed"], "branches": ["main"]})  # `requested`: a run is watched from the moment it is requested
        self.assertEqual(on["workflow_dispatch"]["inputs"]["dry_run"]["default"], "true")
        self.assertIn("schedule", on)
        self.assertEqual(y["permissions"], {})
        self.assertEqual(y["concurrency"], {"group": "waves-watch", "cancel-in-progress": False})
        job = y["jobs"]["watch"]
        self.assertEqual(job["permissions"], {"actions": "write", "contents": "read"})
        for s in ("vars.LANE_ENABLED == 'true'", "github.ref == 'refs/heads/main'", "github.repository == 'competemath/emissary-archangel'"):
            self.assertIn(s, job["if"])
        run = "\n".join(s.get("run", "") for s in job["steps"])
        self.assertIn("python3 scripts/bump/waves_watch.py", run)
        self.assertNotIn("${{", run)
        for wf in on["workflow_run"]["workflows"]:
            self.assertEqual(yaml.safe_load((WF / f"{wf}.yml").read_text())["name"], wf)
        self.assertLessEqual(job["timeout-minutes"], 345)  # 15 minutes under a hosted job's own limit of 360: the job ends by itself and dispatches its successor (cubic on #197)
        self.assertGreaterEqual(job["timeout-minutes"] * 60, 300 * 60 + ww.MAX_RESUMES * (ww.ENDED_WITHIN_SECONDS + 300))  # the 300 minutes of looking, and every recovery of a look waiting for its cancel
        self.assertIn("--wait-minutes 300", run)
        self.assertIn("github.event.action != 'requested' || github.event.workflow_run.name == 'bump-waves'", job["if"])  # `requested` of setup-sharded or bump-sharded starts no watch
        self.assertIn('echo --dry-run ||', run)  # a dry run does not wait

    def test_it_never_runs_a_pull_requests_code(self):
        text = (WF / "waves-watch.yml").read_text()
        self.assertNotIn("pull_request", text)
        self.assertIn('checkout -q "$GITHUB_SHA"', text)


if __name__ == "__main__":
    unittest.main()
