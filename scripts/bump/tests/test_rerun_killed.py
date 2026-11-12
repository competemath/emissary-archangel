"""A bump with a shard killed for memory starts itself again with swap, once (the `rerun-with-swap` job of bump-sharded.yml, rerun_killed.py).

Real cases: fixtures/real-failed-shards.json.gz, all 53 failed shard jobs of 12 failed bumps (31 Oct to 8 Nov 2026 and earlier), with their failed steps and error lines; 5,000 random mixes of them.
Invariants: a run starts again exactly when every failed shard was killed; the started run has the same inputs, the swap settings the plan accepts and no resume; it can never start another; every
input it sends is one the workflow declares; it is started once, on main; nothing runs on a fork, a branch or in the sandbox campaign; the job holds no more permission than it needs."""

import gzip
import json
import random
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import plan_inputs  # noqa: E402
import rerun_killed as rk  # noqa: E402

import yaml  # noqa: E402

CASES = json.loads(gzip.open(HERE / "fixtures" / "real-failed-shards.json.gz").read())
WORKFLOW = yaml.safe_load((HERE.parents[2] / ".github" / "workflows" / "bump-sharded.yml").read_text(encoding="utf-8"))
JOB = WORKFLOW["jobs"]["rerun-with-swap"]
DECLARED = WORKFLOW[True]["workflow_dispatch"]["inputs"]


def as_job(c):
    return ({"name": c["name"], "conclusion": "failure", "steps": [{"name": s, "conclusion": "failure"} for s in c["failed_steps"]]}, "\n".join(c["log"]))


def by_run():
    runs = {}
    for c in CASES:
        runs.setdefault(c["run"], []).append(as_job(c))
    return runs


INPUTS = {k: str(v.get("default", "")) for k, v in DECLARED.items()} | {"key": "leanbridge", "parallel": "2", "parts": "300"}


class RealFailures(unittest.TestCase):
    def test_the_cases_are_the_real_ones(self):
        self.assertEqual((len(CASES), len({c["run"] for c in CASES})), (53, 12))

    def test_each_real_run(self):
        want = {42483241941: True, 39433734018: True, 39033626778: True, 38008649083: True}
        got = {}
        for run, jobs in by_run().items():
            got[run] = rk.decide(jobs)[0]
        self.assertEqual({r for r, g in got.items() if g}, set(want))

    def test_the_library_not_building_is_never_started_again(self):
        for c in CASES:
            if c["failed_steps"] and c["failed_steps"][0].startswith(("The library at its pinned commit", "The old exports", "elan")):
                self.assertFalse(rk.killed(*as_job(c)), c)

    def test_leanbridge_exit_137(self):
        c = next(x for x in CASES if x["run"] == 42483241941)
        self.assertTrue(rk.killed(*as_job(c)))

    def test_mixes(self):
        rnd = random.Random(20261108)
        for _ in range(5000):
            mix = rnd.sample(CASES, rnd.randint(1, 8))
            want = all(rk.killed(*as_job(c)) for c in mix)
            self.assertEqual(rk.decide([as_job(c) for c in mix])[0], want)

    def test_no_failed_shard(self):
        self.assertFalse(rk.decide([({"name": "shard (0) / shard", "conclusion": "success", "steps": []}, "")])[0])

    def test_a_failed_job_that_is_no_shard_does_not_count(self):
        self.assertFalse(rk.decide([({"name": "plan", "conclusion": "failure", "steps": []}, "exit code 137")])[0])


class TheRunItStarts(unittest.TestCase):
    def test_same_inputs_and_swap(self):
        out = rk.payload(INPUTS)
        self.assertEqual(out["heavy"], rk.SWAP)
        self.assertEqual({k: v for k, v in out.items() if k != "heavy"}, {k: v for k, v in INPUTS.items() if k != "heavy" and k not in rk.RESUME_INPUTS})

    def test_no_resume(self):
        out = rk.payload(INPUTS | {"only_shards": "6", "fill_from": "1", "fill_unrecorded": "true"})
        self.assertFalse(set(rk.RESUME_INPUTS) & set(out))

    def test_the_plan_accepts_the_settings(self):
        h = plan_inputs.parse_heavy(rk.SWAP)
        self.assertEqual((h["swap_gb"], h["build_timeout_min"]), ("48", "170"))

    def test_every_input_is_declared_and_a_string(self):
        out = rk.payload(INPUTS)
        self.assertLessEqual(set(out), set(DECLARED))
        self.assertTrue(all(isinstance(v, str) for v in out.values()))
        self.assertLessEqual(len(out), 25)


class Fake:
    def __init__(self, jobs, logs, post_failures=0, notes=None):
        self.jobs, self.logs, self.posts, self.post_failures, self.tries = jobs, logs, [], post_failures, 0
        self.asked: list[int] = []
        self.notes = notes or {}  # job id -> annotations (a list of dicts), or None: the call fails
        self.note_calls: list[list[str]] = []

    def __call__(self, args, stdin=None, must=False):
        if "--method" in args and args[args.index("--method") + 1] == "POST":
            self.tries += 1
            if self.tries <= self.post_failures:
                if must:
                    raise RuntimeError("HTTP 500")
                return ""
            self.posts.append((args, json.loads(stdin)))
            return ""
        if args[1].endswith("/annotations"):
            self.note_calls.append(args)
            got = self.notes.get(int(args[1].split("/")[-2]), [])
            if got is None:
                return ""
            if "--paginate" not in args:  # GitHub's first page only
                got = got[:30]
            return "\n".join(a["message"] for a in got)  # what `--jq .[].message` prints
        if args[1].endswith("/logs"):
            self.asked.append(int(args[1].split("/")[-2]))
            log = self.logs.get(int(args[1].split("/")[-2]), "")
            return log.pop(0) if isinstance(log, list) else log  # a list: what each ask gets, in turn (GitHub stores a log a little after its job ends)
        return json.dumps({"jobs": self.jobs})


AINTLIB_TAIL = '2026-11-09T22:32:37.5815825Z   ROOTS: ModularCurves,BernoulliRegular,HasseWeil,DedekindResidue,LutzNagell\n2026-11-09T22:32:37.5816363Z ##[endgroup]\n2026-11-09T23:15:48.7473340Z ##[error]The runner has received a shutdown signal. This can happen when the runner service is stopped, or a manually started runner is canceled.\n2026-11-09T23:15:48.7480858Z ##[error]Process completed with exit code 143.\n'


class Main(unittest.TestCase):
    def job(self, i, name, steps=()):
        return {"id": i, "name": name, "conclusion": "failure", "steps": [{"conclusion": "failure", "name": s} for s in steps]}

    def test_killed_starts_it_once_on_main(self):
        f = Fake([self.job(1, "shard (6) / shard", ["Gate 2"])], {1: "##[error]Process completed with exit code 137."})
        self.assertEqual(rk.run("o/r", "9", INPUTS, f, lambda _: None), 0)
        self.assertEqual(len(f.posts), 1)
        args, body = f.posts[0]
        self.assertIn("repos/o/r/actions/workflows/bump-sharded.yml/dispatches", args)
        self.assertEqual((body["ref"], body["inputs"]["heavy"], body["inputs"]["key"]), ("main", rk.SWAP, "leanbridge"))

    def test_another_failure_starts_nothing(self):
        f = Fake([self.job(1, "shard (0) / shard", ["The library at its pinned commit"])], {1: "##[error]Process completed with exit code 1."})
        self.assertEqual(rk.run("o/r", "9", INPUTS, f, lambda _: None), 0)
        self.assertEqual(f.posts, [])

    def test_one_killed_and_one_not_starts_nothing(self):
        f = Fake([self.job(1, "shard (0) / shard", ["Gate"]), self.job(2, "shard (1) / shard", ["elan"])], {1: "exit code 137", 2: "exit code 1"})
        rk.run("o/r", "9", INPUTS, f, lambda _: None)
        self.assertEqual(f.posts, [])

    def test_a_lost_runner_has_no_log_at_all(self):
        f = Fake([self.job(1, "shard (0) / shard")], {})
        rk.run("o/r", "9", INPUTS, f, lambda _: None)
        self.assertEqual(len(f.posts), 1)

    def test_a_log_that_is_not_stored_yet_is_waited_for(self):
        """aintlib, 9 Nov 2026: asked 3 seconds after the runner was shut down, the log was empty; the real log, read later, ends like this"""
        waits = []
        f = Fake([self.job(1, "shard (16) / shard", ["Build this shard's modules, repair, rebuild"])], {1: ["", "", AINTLIB_TAIL]})
        self.assertEqual(rk.run("o/r", "9", INPUTS, f, waits.append), 0)
        self.assertEqual(len(f.posts), 1)
        self.assertEqual(waits, [rk.LOG_WAIT, rk.LOG_WAIT])

    def test_a_log_that_never_comes_is_a_lost_runner_after_every_try(self):
        waits = []
        f = Fake([self.job(1, "shard (0) / shard")], {1: [""] * rk.LOG_TRIES})
        rk.run("o/r", "9", INPUTS, f, waits.append)
        self.assertEqual(len(waits), rk.LOG_TRIES - 1)
        self.assertEqual(len(f.posts), 1)

    def test_many_late_logs_cost_one_wait_per_round(self):
        waits = []
        jobs = [self.job(i, f"shard ({i}) / shard", ["Build this shard's modules, repair, rebuild"]) for i in range(1, 21)]
        f = Fake(jobs, {i: ["", AINTLIB_TAIL] for i in range(1, 21)})
        rk.run("o/r", "9", INPUTS, f, waits.append)
        self.assertEqual(waits, [rk.LOG_WAIT])
        self.assertEqual(len(f.posts), 1)

    def test_a_log_already_read_is_not_asked_for_again(self):
        jobs = [self.job(1, "shard (1) / shard", ["Build this shard's modules, repair, rebuild"]), self.job(2, "shard (2) / shard", ["Build this shard's modules, repair, rebuild"])]
        f = Fake(jobs, {1: [AINTLIB_TAIL], 2: ["", "", AINTLIB_TAIL]})
        rk.run("o/r", "9", INPUTS, f, lambda _: None)
        self.assertEqual(sorted(f.asked), [1, 2, 2, 2])

    def test_the_reading_fits_the_job(self):
        wf = yaml.safe_load((HERE.parents[2] / ".github" / "workflows" / "bump-sharded.yml").read_text())
        # the deadline, one call that may run on past it (gh's own limit), and two minutes for the checkout and the dispatch
        self.assertLessEqual(rk.LOG_DEADLINE + 120 + 120, wf["jobs"]["rerun-with-swap"]["timeout-minutes"] * 60)

    def test_slow_calls_and_waits_stop_at_the_deadline(self):
        """32 failed shards (aintlib's bump had 32), every call slow and every log late: the reading ends at the deadline and the job still decides"""
        now = [0.0]

        def clock():
            return now[0]

        class Slow(Fake):
            def __call__(self, args, stdin=None, must=False):
                if args[1].endswith("/logs"):
                    now[0] += 60
                return super().__call__(args, stdin, must)

        def sleep(s):
            now[0] += s

        jobs = [self.job(i, f"shard ({i}) / shard", ["Build this shard's modules, repair, rebuild"]) for i in range(32)]
        f = Slow(jobs, {})
        self.assertEqual(rk.run("o/r", "9", INPUTS, f, sleep, clock), 0)
        self.assertLessEqual(now[0], rk.LOG_DEADLINE + 60)
        self.assertEqual(len(f.asked), rk.LOG_DEADLINE // 60)

    def test_no_wait_that_would_end_past_the_deadline(self):
        now = [0.0]
        ends = []

        class Slow(Fake):
            def __call__(self, args, stdin=None, must=False):
                if args[1].endswith("/logs"):
                    now[0] += 55
                return super().__call__(args, stdin, must)

        def sleep(s):
            now[0] += s
            ends.append(now[0])

        f = Slow([self.job(1, "shard (1) / shard", ["Build"])], {1: [""] * rk.LOG_TRIES})
        rk.run("o/r", "9", INPUTS, f, sleep, lambda: now[0])
        self.assertTrue(ends and all(e <= rk.LOG_DEADLINE for e in ends), ends)
        self.assertLess(len(ends), rk.LOG_TRIES - 1)

    def test_a_log_there_at_once_is_not_waited_for(self):
        waits = []
        f = Fake([self.job(1, "shard (6) / shard", ["Gate 2"])], {1: "exit code 137"})
        rk.run("o/r", "9", INPUTS, f, waits.append)
        self.assertEqual(waits, [])

    def test_jobs_that_cannot_be_read_are_an_error(self):
        self.assertEqual(rk.run("o/r", "9", INPUTS, lambda a, stdin=None, must=False: "", lambda _: None), 1)

    def test_a_dispatch_that_fails_is_a_failure_not_a_rerun_and_is_not_sent_twice(self):
        """accepted but reported as failed: a second dispatch would run the whole plan twice"""
        f = Fake([self.job(1, "shard (6) / shard", ["Gate 2"])], {1: "exit code 137"}, post_failures=1)
        self.assertEqual((rk.run("o/r", "9", INPUTS, f, lambda _: None), f.tries, f.posts), (1, 1, []))

    def test_the_real_gh_raises_when_a_post_fails(self):
        with self.assertRaises(RuntimeError):
            rk.gh(["no-such-gh-command-for-this-test"], must=True)
        self.assertEqual(rk.gh(["no-such-gh-command-for-this-test"]), "")


class Workflow(unittest.TestCase):
    def test_it_can_never_start_another(self):
        for guard in ("inputs.heavy == ''", "inputs.only_shards == ''", "inputs.fill_from == ''", "inputs.recut_from == ''"):
            self.assertIn(guard, JOB["if"])
        self.assertNotEqual(rk.SWAP, "")

    def test_only_on_main_in_the_real_repository(self):
        self.assertIn("github.ref == 'refs/heads/main'", JOB["if"])
        self.assertIn("github.repository == 'competemath/emissary-archangel'", JOB["if"])

    def test_only_after_a_failed_shard(self):
        self.assertIn("needs.shard.result == 'failure'", JOB["if"])
        self.assertIn("!cancelled()", JOB["if"])

    def test_permissions(self):
        # checks: read is for the jobs' annotations, the only trace a runner lost under its job leaves when no log is stored (etingofrepresentationtheory, 12 Nov 2026)
        self.assertEqual(JOB["permissions"], {"actions": "write", "checks": "read", "contents": "read"})

    def test_inputs_never_reach_a_shell_as_expressions(self):
        for step in JOB["steps"]:
            self.assertNotIn("${{", step["run"], step["name"])

    def test_the_script_is_in_the_sparse_checkout(self):
        self.assertIn('"/scripts/bump/"', JOB["steps"][0]["run"])


LOST = json.loads((HERE / "fixtures" / "etingof_lost_runner_2026-11-12.json").read_text())


class LostRunner(unittest.TestCase):
    """The real case: EtingofRepresentationTheory's shard 2 (run 43292037870): the build step marked failed, no log stored, one annotation that the runner lost communication."""

    def test_the_fixture_is_the_real_job(self):
        failed = [s["name"] for s in LOST["job"]["steps"] if s["conclusion"] == "failure"]
        self.assertEqual(failed, ["Build this shard's modules, repair, rebuild"])
        self.assertEqual(LOST["log"], "")
        self.assertTrue(any("lost communication with the server" in a["message"] for a in LOST["annotations"]))

    def test_its_note_makes_it_killed_and_the_plan_runs_again_once(self):
        job = dict(LOST["job"], id=LOST["job"]["id"])
        f = Fake([job], {}, notes={job["id"]: LOST["annotations"]})
        self.assertEqual(rk.run("o/r", "43292037870", INPUTS, f, lambda _: None), 0)
        self.assertEqual(len(f.posts), 1)
        self.assertEqual(f.posts[0][1]["inputs"]["heavy"], rk.SWAP)

    def test_mutant_without_the_note_it_reads_as_a_build_that_fails(self):
        # the bug as it was: log and steps alone
        self.assertFalse(rk.killed(LOST["job"], LOST["log"]))
        self.assertTrue(rk.killed(LOST["job"], LOST["log"], "\n".join(a["message"] for a in LOST["annotations"])))
        f = Fake([dict(LOST["job"])], {}, notes={})
        rk.run("o/r", "43292037870", INPUTS, f, lambda _: None)
        self.assertEqual(f.posts, [])

    def test_annotations_that_cannot_be_read_start_nothing(self):
        f = Fake([dict(LOST["job"])], {}, notes={LOST["job"]["id"]: None})
        rk.run("o/r", "43292037870", INPUTS, f, lambda _: None)
        self.assertEqual(f.posts, [])

    def test_another_note_is_not_a_kill(self):
        for msg in ("Process completed with exit code 1.", "Process completed with exit code 2.", "The job running on runner X has exceeded the maximum execution time of 345 minutes.",
                    "Canceling since a higher priority waiting request for 'x' exists"):
            self.assertFalse(rk.killed(LOST["job"], "", msg), msg)

    def test_a_lost_runner_beside_a_real_failure_starts_nothing(self):
        other = {"id": 2, "name": "shard (0) / shard", "conclusion": "failure", "steps": [{"name": "The library at its pinned commit", "conclusion": "failure"}]}
        f = Fake([dict(LOST["job"]), other], {2: "##[error]Process completed with exit code 1."}, notes={LOST["job"]["id"]: LOST["annotations"]})
        rk.run("o/r", "43292037870", INPUTS, f, lambda _: None)
        self.assertEqual(f.posts, [])

    def test_the_real_mixes_with_the_lost_runner(self):
        # every real run of the fixture, with the lost runner added: started exactly when every other failed shard was killed too
        rng = random.Random(1112)
        n = 0
        for run, jobs in by_run().items():
            for _ in range(20):
                mix = [(j, log) for j, log in jobs if rng.random() < 0.7] + [(LOST["job"], "", "\n".join(a["message"] for a in LOST["annotations"]))]
                go, _ = rk.decide(mix)
                expect = all(rk.killed(j, log) for j, log in [(m[0], m[1]) for m in mix[:-1]] if j.get("name", "").startswith("shard") and j.get("conclusion") == "failure")
                self.assertEqual(go, expect)
                n += 1
        self.assertGreaterEqual(n, 200)


class ReviewOn184(unittest.TestCase):
    """cubic on #184: every page of annotations, one deadline over them, a timeout is a failed call"""

    def test_a_note_beyond_the_first_page_counts(self):
        noise = [{"annotation_level": "warning", "message": f"Node.js 20 is deprecated ({i})"} for i in range(40)]
        f = Fake([dict(LOST["job"])], {}, notes={LOST["job"]["id"]: noise + LOST["annotations"]})
        rk.run("o/r", "1", INPUTS, f, lambda _: None)
        self.assertEqual(len(f.posts), 1)
        args = f.note_calls[0]
        self.assertIn("--paginate", args)
        self.assertEqual(args[args.index("--jq") + 1], ".[].message")
        self.assertEqual(args[args.index("--method") + 1], "GET")  # -F would otherwise make it a POST

    def test_mutant_first_page_only_misses_it(self):
        noise = [{"annotation_level": "warning", "message": f"note {i}"} for i in range(40)]
        f = Fake([dict(LOST["job"])], {}, notes={LOST["job"]["id"]: noise + LOST["annotations"]})
        real = rk.annotations
        try:
            rk.annotations = lambda api, repo, i: api(["api", f"repos/{repo}/check-runs/{i}/annotations", "--jq", ".[].message"]) or ""
            rk.run("o/r", "1", INPUTS, f, lambda _: None)
        finally:
            rk.annotations = real
        self.assertEqual(f.posts, [])

    def test_one_deadline_over_every_note(self):
        now = [0.0]

        class Slow(Fake):
            def __call__(self, args, stdin=None, must=False):
                if args[1].endswith("/annotations"):
                    now[0] += rk.NOTES_CALL
                return super().__call__(args, stdin, must)

        jobs = [dict(LOST["job"], id=100 + i, name=f"shard ({i}) / shard") for i in range(32)]
        f = Slow(jobs, {}, notes={100 + i: LOST["annotations"] for i in range(32)})
        start = now[0]
        rk.run("o/r", "1", INPUTS, f, lambda s: None, lambda: now[0])
        self.assertLessEqual(len(f.note_calls), rk.NOTES_DEADLINE // rk.NOTES_CALL)
        self.assertLessEqual(now[0] - start, rk.NOTES_DEADLINE + rk.NOTES_CALL)
        self.assertEqual(f.posts, [])  # the shards not reached have no note: no kill on no evidence

    def test_the_budget_fits_the_job(self):
        self.assertLessEqual(rk.LOG_DEADLINE + 120 + rk.NOTES_DEADLINE + rk.NOTES_CALL + 60, JOB["timeout-minutes"] * 60)

    def test_a_timeout_is_a_failed_call_not_a_crash(self):
        import subprocess
        from unittest import mock

        def boom(*a, **k):
            raise subprocess.TimeoutExpired(cmd="gh", timeout=k.get("timeout"))

        with mock.patch.object(rk.subprocess, "run", boom):
            self.assertEqual(rk.gh(["api", "x"]), "")
            self.assertEqual(rk.gh_notes(["api", "x"]), "")
            self.assertEqual(rk.annotations(rk.gh_notes, "o/r", 1), "")
            with self.assertRaises(RuntimeError):
                rk.gh(["api", "x"], must=True)

    def test_the_real_gh_reads_annotations_with_the_short_timeout(self):
        from unittest import mock
        seen = []

        def fake_run(cmd, **k):
            seen.append(k.get("timeout"))
            return mock.Mock(returncode=0, stdout="The hosted runner lost communication with the server.\n", stderr="")

        with mock.patch.object(rk.subprocess, "run", fake_run):
            self.assertIn("lost communication", rk.annotations(rk.gh_notes, "o/r", 1))
        self.assertEqual(seen, [rk.NOTES_CALL])


if __name__ == "__main__":
    unittest.main()
