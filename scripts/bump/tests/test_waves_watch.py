"""waves_watch.py cancels and resumes a bump-waves run whose build chain is dead, on the REAL run that was (fixtures/real-flt-waves-run-43237206258.json: its 69 jobs with their start, end, result and failed
steps, as GitHub listed them at 23:46 UTC on 13 Nov 2026; fixtures/real-flt-plan-*-run-43529754609.json: the settings its resume was dispatched with).

The real case: job 93 of wave 15 lost its runner at 19:14 (failure, no failed step), jobs 92 and 94 of the same wave ran on until 22:58 and 23:03, waves 16 and 17 then failed at the restore step within 9 to 20
minutes each, and a person noticed at 23:44. Replayed minute by minute, the rule fires at 23:14 (the second job of a later wave to fail at the restore step), never before, and from then on.
Invariants: never while the failed job's wave still has running jobs; never on one failed job or on failures of the same wave; never on a cancelled job; once fired it stays fired; the resume is dispatched for the
cancelled run with the settings its plan recorded and nothing else; a value that is not a plain setting is refused; a chain longer than MAX_CHAIN, a run that does not end after its cancel, and a dry run dispatch
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
        self.assertEqual(hhmm(FIRST), "23:14")  # the second later failure ended at 23:13:30
        # a person noticed at 23:44: 31 minutes later
        self.assertLessEqual(FIRST, at("2026-11-13T23:14:00Z"))

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
                want = sum(1 for j in fails if wv(j) > w0 and j["failed_steps"]) >= 2
            self.assertEqual(ww.doomed(jobs) is not None, want)

    def test_mutant_the_later_wave_condition_dropped_fires_at_the_first_failure(self):
        src = inspect.getsource(ww.doomed)
        old = 'later = [s for s in roots if s["wave"] > first and any(x.startswith(RESTORE_STEP) for x in s["steps"])]'
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(ww))
        exec(src.replace(old, 'later = [s for s in roots if any(x.startswith(RESTORE_STEP) for x in s["steps"])]'), ns)
        t = int(at("2026-11-13T20:00:00Z"))
        self.assertIsNone(ww.doomed(slice_at(t)))
        self.assertIsNotNone(ns["doomed"](slice_at(int(at("2026-11-13T23:20:00Z")))))  # control: the mutant fires late too
        same_wave = [self.job(3, 10, "failure"), self.job(3, 11, "failure", True), self.job(3, 12, "failure", True)]
        self.assertIsNotNone(ns["doomed"](same_wave))  # the mutant cancels a wave that is still running
        self.assertIsNone(ww.doomed(same_wave))

    def test_mutant_one_later_failure_is_enough_fires_early(self):
        src = inspect.getsource(ww.doomed)
        self.assertEqual(src.count("if len(later) < LATER_FAILURES:"), 1)
        ns = dict(vars(ww))
        exec(src.replace("if len(later) < LATER_FAILURES:", "if len(later) < 1:"), ns)
        early = int(at("2026-11-13T23:12:30Z"))
        self.assertIsNone(ww.doomed(slice_at(early)))
        self.assertIsNotNone(ns["doomed"](slice_at(early)))

    def test_mutant_cancelled_jobs_counted(self):
        src = inspect.getsource(ww.doomed)
        old = 'roots = [s for s in shards if s["conclusion"] == "failure"]'
        self.assertEqual(src.count(old), 1)
        ns = dict(vars(ww))
        exec(src.replace(old, 'roots = [s for s in shards if s["conclusion"] in ("failure", "cancelled")]'), ns)
        jobs = [self.job(3, 10, "cancelled"), self.job(4, 11, "failure", True), self.job(4, 12, "failure", True)]
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
        for bad in ("a b", "x;rm", "$(id)", "`id`", "a\nb", "x'y", 'x"y'):
            with self.assertRaises(ww.WatchError, msg=bad):
                ww.dispatch_args("flt-anthropic", 1, {**INPUTS, "tengoku_ref": bad}, LANE)
        for bad in ("Flt", "a b", "-x", "", "a;b"):
            with self.assertRaises(ww.WatchError, msg=bad):
                ww.dispatch_args(bad, 1, INPUTS, LANE)
        with self.assertRaises(ww.WatchError):
            ww.dispatch_args("flt-anthropic", 1, INPUTS, {"from_tree": "maybe"})
        with self.assertRaises(ValueError):
            ww.dispatch_args("flt-anthropic", "1; x", INPUTS, LANE)

    def test_the_chain_length_follows_the_lanes(self):
        lanes = {"2": {"reuse_from": "1"}, "1": {}}
        self.assertEqual(ww.chain_length({"reuse_from": "2"}, lanes.get), 3)
        self.assertEqual(ww.chain_length({}, lanes.get), 1)
        self.assertGreater(ww.chain_length({"reuse_from": "2"}, {"2": {"reuse_from": "2"}}.get), ww.MAX_CHAIN)  # a loop is never resumed


class Flow(unittest.TestCase):
    def run_main(self, argv=(), chain=1, ends=True, dispatch_fails=False, jobs=None, mutate=None):
        """main() with the world faked; `mutate=(old, new)` runs a broken copy of main() instead (its functions are looked up in a copy of the module, so the fakes go there)"""
        calls = []
        jobs = jobs if jobs is not None else slice_at(at("2026-11-13T23:20:00Z"))

        def run(args, **k):
            calls.append(list(args))
            if args[:3] == ["gh", "workflow", "run"] and dispatch_fails:
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, "", "")

        fake_sub = mock.Mock(run=run, CalledProcessError=subprocess.CalledProcessError)
        lane = {"from_tree": "true", **({"reuse_from": "7"} if chain > 1 else {})}
        fakes = {
            "running": lambda dry=False: [{"id": 43237206258, "title": "bump-waves flt-anthropic"}],
            "jobs_of": lambda r: jobs,
            "plan_files": lambda r, k: (INPUTS, lane),
            "chain_length": lambda lane_, lanes: chain,
            "ended": lambda r, **k: ends,
        }
        if mutate:
            src = inspect.getsource(ww.main)
            self.assertEqual(src.count(mutate[0]), 1, mutate[0])
            ns = dict(vars(ww))
            ns.update(fakes)
            ns["subprocess"] = fake_sub
            exec(src.replace(*mutate), ns)
            rc = ns["main"](list(argv))
        else:
            with contextlib.ExitStack() as st:
                for k, v in fakes.items():
                    st.enter_context(mock.patch.object(ww, k, v))
                st.enter_context(mock.patch.object(ww, "subprocess", fake_sub))
                rc = ww.main(list(argv))
        return rc, calls

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
        with self.assertRaises(subprocess.CalledProcessError):
            self.run_main(dispatch_fails=True)

    def test_mutant_the_chain_guard_dropped(self):
        _, calls = self.run_main(chain=ww.MAX_CHAIN + 1, mutate=("if n > MAX_CHAIN:", "if False:"))
        self.assertEqual(len(calls), 2)  # the mutant resumes a chain that test_a_long_chain_is_left_to_a_person leaves alone

    def test_mutant_the_cancel_not_waited_for(self):
        _, calls = self.run_main(ends=False, mutate=('if not ended(r["id"]):', "if False:"))
        self.assertEqual(len(calls), 2)  # dispatched while the old run still ran: test_a_run_that_does_not_end_is_not_resumed refuses it


class Workflow(unittest.TestCase):
    def test_shape(self):
        y = yaml.safe_load((WF / "waves-watch.yml").read_text())
        on = y[True]
        self.assertEqual(on["workflow_run"], {"workflows": ["setup-sharded", "bump-sharded", "bump-waves"], "types": ["completed"], "branches": ["main"]})
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
        self.assertLess(job["timeout-minutes"] * 60, 3600)
        self.assertGreater(job["timeout-minutes"] * 60, ww.ENDED_WITHIN_SECONDS + 300)

    def test_it_never_runs_a_pull_requests_code(self):
        text = (WF / "waves-watch.yml").read_text()
        self.assertNotIn("pull_request", text)
        self.assertIn('checkout -q "$GITHUB_SHA"', text)


if __name__ == "__main__":
    unittest.main()
