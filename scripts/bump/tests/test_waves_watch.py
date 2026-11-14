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
            ns["look"](False, 0)
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

    def test_an_alive_run_is_left_alone(self):
        rc, calls = self.run_main(jobs=slice_at(at("2026-11-13T20:00:00Z")))
        self.assertEqual(calls, [])

    def test_a_dry_run_changes_nothing(self):
        _, calls = self.run_main(argv=["--dry-run"])
        self.assertEqual(calls, [])

    def test_a_long_chain_is_left_to_a_person(self):
        _, calls = self.run_main(chain=ww.MAX_CHAIN + 1)
        self.assertEqual(calls, [])
        _, calls = self.run_main(chain=ww.MAX_CHAIN)
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
        self.assertEqual((pages, len(got)), ([1, 2, 3], 207))

    def test_mutant_the_chain_guard_dropped(self):
        _, calls = self.run_main(chain=ww.MAX_CHAIN + 1, mutate=("if n > MAX_CHAIN:", "if False:"))
        self.assertEqual(len(calls), 2)  # the mutant resumes a chain that test_a_long_chain_is_left_to_a_person leaves alone

    def test_mutant_the_cancel_not_waited_for(self):
        _, calls = self.run_main(ends=False, mutate=('if not ended(r["id"]):', "if False:"))
        self.assertEqual(len(calls), 2)  # dispatched while the old run still ran: test_a_run_that_does_not_end_is_not_resumed refuses it


class Loop(unittest.TestCase):
    """the watch of a run: looks every LOOK_SECONDS while one is in progress, up to --wait-minutes, then dispatches itself once more"""

    def run_loop(self, argv, alive=(1,), fail_looks=(), dispatch_fails=False, mutate=None):
        clock = [1000.0]
        looks, sleeps, calls = [], [], []
        self.looks, self.sleeps, self.calls = looks, sleeps, calls  # readable after a raise

        def look(dry, so_far=0):
            i = len(looks)
            looks.append(clock[0])
            if i in fail_looks:
                raise RuntimeError("HTTP 502")
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
        with self.assertRaises(RuntimeError):
            self.run_loop(["--wait-minutes", "30"], fail_looks={0})
        with self.assertRaises(RuntimeError):
            self.run_loop(["--wait-minutes", "30"], alive=(1,), fail_looks={6})

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
        self.assertLessEqual(job["timeout-minutes"], 360)  # a hosted job's own limit
        self.assertGreaterEqual(job["timeout-minutes"] * 60, 300 * 60 + ww.MAX_RESUMES * (ww.ENDED_WITHIN_SECONDS + 300))  # the 300 minutes of looking, and every recovery of a look waiting for its cancel
        self.assertIn("--wait-minutes 300", run)
        self.assertIn('echo --dry-run ||', run)  # a dry run does not wait

    def test_it_never_runs_a_pull_requests_code(self):
        text = (WF / "waves-watch.yml").read_text()
        self.assertNotIn("pull_request", text)
        self.assertIn('checkout -q "$GITHUB_SHA"', text)


if __name__ == "__main__":
    unittest.main()
