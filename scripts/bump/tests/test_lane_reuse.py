"""A build-once that goes on from an earlier run of itself (scripts/bump/lane_reuse.py, wave_pack.py fetch --reuse-*, bump-waves.yml reuse_from, bump-shard.yml reuse_*).

The real case: flt-anthropic's lane, run 42678283150 (fixtures/flt_plan_restore.json: its plan, 111 jobs in 21 waves, with what each job restores;
fixtures/flt_lane_artifacts_2026-11-11.json: its jobs and artifacts at 14:45 UTC on 11 Nov 2026). Jobs 43, 53 and 65 stopped at their time limit in Gate 2 after their
pack step; job 62 stopped inside its build, with no pack; 42 of the 55 jobs after it build on it. Every job uploads its packs even when stopped, so an artifact proves
nothing on its own.

Invariants:
  I1  a good pack's job packed (pack step succeeded), its pack is there, and every pack it restored is good: no pack built on a missing one is reused;
  I2  a reused job succeeded, its pack is good and its shard pack is there;
  I3  every job of the plan either is reused or runs, exactly once, in its own wave;
  I4  on the real run: 62 jobs kept, 49 run (43, 53, 62, 65 and waves 10-20); job 62's pack is not good and no pack built on it is;
  I5  a job of the new run fetches a good pack from the earlier run and any other from its own run;
  I6  the workflows: the plan job takes the earlier run's plan, compares the settings, passes the reused packs to every wave, and the bundle fills from the earlier run.
Mutants (each fails a test): a pack counted good without its sources; artifacts trusted instead of the job's result; every pack fetched from one run.
"""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
BUMP = HERE.parent
WF = BUMP.parents[1] / ".github" / "workflows"
sys.path.insert(0, str(BUMP))
import lane_reuse as lr  # noqa: E402
import plan_waves as pw  # noqa: E402
import wave_pack as wp  # noqa: E402

PLAN = json.loads((HERE / "fixtures" / "flt_plan_restore.json").read_text())
RUN = json.loads((HERE / "fixtures" / "flt_lane_artifacts_2026-11-11.json").read_text())
KEY = "flt-anthropic"
ART = set(RUN["artifacts"])
BY = {s["shard"]: s for s in PLAN["shards"]}


def decide(jobs=RUN["jobs"], artifacts=ART):
    good = lr.good_packs(PLAN, lr.packed(jobs), artifacts, KEY)
    keep = lr.reusable(PLAN, lr.succeeded(jobs), good, artifacts, KEY)
    return good, keep


def upstream(n: int) -> set[int]:
    """every job whose pack job n's build stands on, through restores"""
    seen, todo = set(), list(BY[n]["restore"])
    while todo:
        r = todo.pop()
        if r not in seen:
            seen.add(r)
            todo += BY[r]["restore"]
    return seen


class RealRun(unittest.TestCase):
    def test_the_fixture_is_the_real_run(self):
        self.assertEqual(len(PLAN["shards"]), 111)
        stopped = sorted(int(j["name"].split("(")[1].split(")")[0]) for j in RUN["jobs"] if j["conclusion"] == "cancelled")
        self.assertEqual(stopped, [43, 53, 62, 65])
        self.assertIn("wave-flt-anthropic-43", ART)  # a stopped job still uploads its packs
        self.assertIn("shard-flt-anthropic-43", ART)

    def test_good_packs_stand_only_on_good_packs(self):  # I1
        good, _ = decide()
        packed = lr.packed(RUN["jobs"])
        for n in good:
            self.assertIn(n, packed)
            self.assertIn(f"wave-{KEY}-{n}", ART)
            self.assertLessEqual(upstream(n), good, n)
        self.assertNotIn(62, good)
        for n in BY:
            if 62 in upstream(n):
                self.assertNotIn(n, good, n)

    def test_reused_jobs_succeeded_with_both_packs(self):  # I2
        good, keep = decide()
        ok = lr.succeeded(RUN["jobs"])
        for n in keep:
            self.assertIn(n, ok)
            self.assertIn(n, good)
            self.assertIn(f"shard-{KEY}-{n}", ART)

    def test_every_job_runs_or_is_kept_exactly_once_in_its_wave(self):  # I3
        good, keep = decide()
        out = lr.outputs(PLAN, keep, good)
        ran = []
        for w in range(pw.MAX_WAVES):
            for n in json.loads(out[f"w{w}"]):
                self.assertEqual(BY[n]["wave"], w)
                ran.append(n)
        self.assertEqual(len(ran), len(set(ran)))
        self.assertEqual(set(ran) | keep, set(BY))
        self.assertFalse(set(ran) & keep)
        self.assertEqual(out["packs"], ",".join(str(n) for n in sorted(good)))

    def test_the_real_numbers(self):  # I4
        good, keep = decide()
        run = sorted(set(BY) - keep)
        self.assertEqual(len(keep), 62)
        self.assertEqual(len(run), 49)
        self.assertEqual([n for n in run if BY[n]["wave"] <= 9], [43, 53, 62, 65])
        self.assertEqual({BY[n]["wave"] for n in run if BY[n]["wave"] > 9}, set(range(10, PLAN["waves"])))
        self.assertTrue({43, 53, 65} <= good)  # stopped in Gate 2 after the pack: their packs stay, they are judged again

    def test_mutant_without_the_sources_check_reuses_a_pack_built_on_job_62(self):
        jobs = [dict(j, conclusion="success", pack_step="success") if j["conclusion"] is None else j for j in RUN["jobs"]]  # wave 10 finished, built around 62's hole
        arts = ART | {f"{k}-{KEY}-{n}" for n in range(66, 75) for k in ("wave", "shard")}
        good, keep = decide(jobs, arts)
        hole = {n for n in range(66, 75) if 62 in upstream(n)}
        self.assertTrue(hole)
        self.assertFalse(hole & good)
        self.assertFalse(hole & keep)
        naive = {n for n in BY if n in lr.packed(jobs) and f"wave-{KEY}-{n}" in arts}  # the mutant: no look at the sources
        self.assertTrue(hole & naive)

    def test_an_artifact_without_a_pack_step_is_no_pack(self):
        """job 62 left no artifact; had its upload found anything (a partial directory, an older attempt), the pack step that never ran still says it is no pack"""
        arts = ART | {f"wave-{KEY}-62", f"shard-{KEY}-62"}
        good, keep = decide(RUN["jobs"], arts)
        self.assertNotIn(62, good)
        self.assertNotIn(62, keep)
        self.assertEqual(next(j for j in RUN["jobs"] if j["name"] == "w9 (62) / shard")["pack_step"], "skipped")

    def test_mutant_trusting_artifacts_reuses_the_stopped_jobs(self):
        _, keep = decide()
        naive = {n for n in BY if f"wave-{KEY}-{n}" in ART and f"shard-{KEY}-{n}" in ART}
        self.assertTrue({43, 53, 65} & naive)
        self.assertFalse({43, 53, 62, 65} & keep)


class FromTree(unittest.TestCase):
    """a resume numbers its parts like the run it goes on from (cubic, #174)"""

    def test_the_real_earlier_run_ran_from_the_tree(self):
        log = (HERE / "fixtures" / "flt_lane_plan_log_head.txt").read_text()
        self.assertEqual(lr.earlier_from_tree(None, log), "true")
        self.assertEqual(lr.earlier_from_tree({"from_tree": "false"}, log), "false")  # lane.json, when there, says it
        self.assertIsNone(lr.earlier_from_tree(None, ""))
        self.assertIsNone(lr.earlier_from_tree(None, log + log.replace("FROM_TREE: true", "FROM_TREE: false")))  # two values: unknown

    def test_a_different_from_tree_stops_the_run(self):
        import subprocess
        import tempfile

        with tempfile.TemporaryDirectory() as t:
            d = Path(t)
            (d / "plan.json").write_text(json.dumps(PLAN))
            (d / "jobs.json").write_text(json.dumps(RUN["jobs"]))
            (d / "arts.json").write_text(json.dumps(RUN["artifacts"]))
            (d / "plan.log").write_text((HERE / "fixtures" / "flt_lane_plan_log_head.txt").read_text())
            base = [sys.executable, str(BUMP / "lane_reuse.py"), "--plan", str(d / "plan.json"), "--jobs", str(d / "jobs.json"), "--artifacts", str(d / "arts.json"), "--key", KEY, "--plan-log", str(d / "plan.log")]
            ok = subprocess.run([*base, "--from-tree", "true"], capture_output=True, text=True)
            self.assertEqual(ok.returncode, 0, ok.stderr)
            self.assertIn("packs=", ok.stdout)
            bad = subprocess.run([*base, "--from-tree", "false"], capture_output=True, text=True)
            self.assertNotEqual(bad.returncode, 0)
            self.assertIn("from_tree=true", bad.stderr)
            unknown = subprocess.run([*base[:-2], "--from-tree", "true"], capture_output=True, text=True)
            self.assertNotEqual(unknown.returncode, 0)

    def test_the_earlier_plan_log_is_fetched_with_curl(self):
        """gh refuses to write a job log (its colour codes: "the response contains terminal escape sequences"), and the resume of run 42678283150 stopped on an empty
        log (run 43066356910): the log is fetched with curl, and the real log, colour codes and all, still gives from_tree"""
        r = next(s for s in yaml.safe_load((WF / "bump-waves.yml").read_text())["jobs"]["plan"]["steps"] if s.get("id") == "r")
        self.assertIn('curl -sSfL --retry 5 -H "Authorization: Bearer $GH_TOKEN"', r["run"])
        self.assertIn('/actions/jobs/$plan_job/logs" -o "$d/plan.log"', r["run"])  # every run of the chain (test_lane_chain.py)
        self.assertNotIn('gh api "repos/$GITHUB_REPOSITORY/actions/jobs/$plan_job/logs"', r["run"])
        log = (HERE / "fixtures" / "flt_lane_plan_log_head.txt").read_text()
        self.assertIn("\x1b[36;1m", log)  # the real log carries the colour codes gh refused
        self.assertEqual(lr.earlier_from_tree(None, log), "true")

    def test_a_new_plan_records_its_from_tree(self):
        steps = yaml.safe_load((WF / "bump-waves.yml").read_text())["jobs"]["plan"]["steps"]
        settings = next(s for s in steps if s.get("name", "").startswith("What the shards are built with"))
        self.assertIn('"$FROM_TREE" > ../plan/lane.json', settings["run"])
        r = next(s for s in steps if s.get("id") == "r")
        self.assertIn('--from-tree "$FROM_TREE" --lane ../plan/lane.json --plan-log "../reuse/$REUSE_FROM/plan.log"', r["run"])


class Fetch(unittest.TestCase):
    def test_a_good_pack_comes_from_the_earlier_run_any_other_from_this_one(self):  # I5
        good, _ = decide()
        asked = []

        def runner(cmd, check=False):
            asked.append((cmd[3], int(cmd[cmd.index("-n") + 1].rsplit("-", 1)[1])))
            return type("R", (), {"returncode": 0})()

        dl = wp.gh_download("o/r", "999", KEY, runner=runner, sleep=lambda s: None, reuse_run="42678283150", reuse_packs=frozenset(good))
        for n in sorted(BY):
            dl(n, Path("/nonexistent"))
        for run, n in asked:
            self.assertEqual(run, "42678283150" if n in good else "999", n)
        self.assertEqual(sum(1 for r, _ in asked if r == "999"), 111 - len(good))
        # without a reuse run every pack is this run's
        asked.clear()
        dl = wp.gh_download("o/r", "999", KEY, runner=runner, sleep=lambda s: None)
        dl(5, Path("/nonexistent"))
        self.assertEqual(asked, [("999", 5)])


class Workflows(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = (WF / "bump-waves.yml").read_text()
        cls.waves = yaml.safe_load(cls.text)
        cls.shard = yaml.safe_load((WF / "bump-shard.yml").read_text())

    def test_every_wave_passes_the_reuse_inputs(self):  # I6
        for w in range(pw.MAX_WAVES):
            job = self.waves["jobs"][f"w{w}"]
            self.assertEqual(job["with"]["reuse_run"], "${{ inputs.reuse_from }}")
            self.assertEqual(job["with"]["reuse_packs"], "${{ needs.plan.outputs.packs }}")
        for k in ("reuse_run", "reuse_packs"):
            self.assertIn(k, self.shard[True]["workflow_call"]["inputs"])

    def test_the_plan_job_takes_the_earlier_plan_and_checks_the_settings(self):
        steps = self.waves["jobs"]["plan"]["steps"]
        r = next(s for s in steps if s.get("id") == "r")
        self.assertEqual(r["if"], "${{ inputs.reuse_from != '' }}")
        self.assertIn('gh run download "$REUSE_FROM"', r["run"])
        self.assertIn("lane_reuse.py", r["run"])
        self.assertIn("bump-waves $KEY", r["run"])  # only a lane run of this key
        p = next(s for s in steps if s.get("id") == "p")
        self.assertEqual(p["if"], "${{ inputs.reuse_from == '' }}")
        settings = next(s for s in steps if s.get("name", "").startswith("What the shards are built with"))
        self.assertIn("cmp ../plan/inputs.json ../this-run-inputs.json", settings["run"])
        self.assertEqual(self.waves["jobs"]["plan"]["permissions"], {"contents": "read", "actions": "read"})
        for w in range(pw.MAX_WAVES):
            self.assertEqual(self.waves["jobs"]["plan"]["outputs"][f"w{w}"], f"${{{{ steps.p.outputs.w{w} || steps.r.outputs.w{w} }}}}")

    def test_the_bundle_fills_from_the_earlier_run(self):
        run = self.waves["jobs"]["bundle"]["steps"][0]["run"]
        self.assertIn('fill=(); [ -z "$REUSE_FROM" ] || fill=(-f fill_from="$FILL")', run)  # the whole chain, newest first (test_lane_chain.py)
        self.assertEqual(self.waves["jobs"]["bundle"]["env"]["FILL"], "${{ needs.plan.outputs.fill }}")
        self.assertIn('"${fill[@]}"', run)

    def test_the_shard_checks_the_reuse_inputs_and_hands_them_to_the_fetch(self):
        steps = self.shard["jobs"]["shard"]["steps"]
        self.assertIn('"$REUSE_RUN" =~', steps[0]["run"])
        fetch = next(s for s in steps if s.get("name", "").startswith("The work of the earlier jobs"))
        self.assertIn('--reuse-run "$REUSE_RUN" --reuse-packs "$REUSE_PACKS"', fetch["run"])


if __name__ == "__main__":
    unittest.main()
