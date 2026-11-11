"""A resume of a resume, and uploads that outlast an outage (bump-waves.yml reuse_from; lane_reuse.py chain_view / earlier_of; wave_pack.py parse_packs; fill_from.py;
bump-shard.yml).

The real case (fixtures/flt_chain_2026-11-11.json.gz): flt-anthropic's lane 42678283150 kept 63 jobs for its resume 43075875630, which ran the other 48. On 11 Nov 2026 at
20:39 UTC job 43 of the resume finished its build (2 h 16 min) and its uploads failed in a GitHub outage ("workflow run not found", then error pages): the job ended without
Gate 2. The resume's bundle needs every wave green, so it will not run. A resume of the resume must keep the 63 jobs whose packs and shard packs are in 42678283150, the jobs
the resume finished, and run job 43 again; before this change it took one earlier run, so it would have run everything the resume kept, two days of builds.

Invariants:
  I1  a chain of one run is the resume as it was: the same jobs kept, the same packs (the real 42678283150: 63 and 66; and every generated case);
  I2  a job's state is the one of the newest run in which it ran, and a kept job has its shard pack in that run;
  I3  a pack comes from the OLDEST run in which it is good: the one every later job was built on;
  I4  every pack handed on is built only on packs handed on;
  I5  the chain is read from the runs: lane.json, else the plan log (the real logs: 43075875630 -> 42678283150 -> none); two values refuse;
  I6  what the plan hands on (`N@RUN`) the shard reads back as the same map, and bump-shard.yml's check takes it; anything else is refused;
  I7  the bundle reads every run of the chain, newest first, never replacing a shard already there, and refuses a run with another plan or other settings;
  I8  an upload of a pack or a shard pack that fails is tried twice more, 5 and 15 minutes later; the last try fails the job.
The resume step itself runs here on the real runs (fake gh and curl serving the fixture): the plan's outputs are checked.
Mutants: the newest good pack instead of the oldest (fails I3); a job's state from the oldest run it ran in (fails I2).
Cases: 2,000 generated chains of 1-4 runs over generated plans, the real chain, 40 pack lists, 9 fill cases.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import random
import re
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import yaml

HERE = Path(__file__).resolve().parents[1]
WF = HERE.parents[1] / ".github" / "workflows"
sys.path.insert(0, str(HERE))
import fill_from as ff  # noqa: E402
import lane_reuse as lr  # noqa: E402
import wave_pack as wp  # noqa: E402

FX = json.loads(gzip.open(HERE / "tests" / "fixtures" / "flt_chain_2026-11-11.json.gz", "rt", encoding="utf-8").read())
PLAN = json.loads((HERE / "tests" / "fixtures" / "flt_plan_restore.json").read_text())
P, R = "42678283150", "43075875630"
KEY = "flt-anthropic"


def run_of_fx(run: str):
    r = FX["runs"][run]
    return run, r["jobs"], set(r["artifacts"])


def kept(view) -> set[int]:
    ok, source, shard_pack = view
    return {n for n in ok if n in source and n in shard_pack}


def finished(run_ran: list[int], failed: dict[int, str]) -> tuple[list[dict], set[str]]:
    """the resume as it will end: every job it ran succeeded with its uploads, but those in `failed` ("built": the build and pack step done, the uploads lost)"""
    wave = {s["shard"]: s["wave"] for s in PLAN["shards"]}
    jobs = [{"name": "plan", "conclusion": "success", "pack_step": None}]
    arts = {f"plan-{KEY}"}
    for n in run_ran:
        if n in failed:
            jobs.append({"name": f"w{wave[n]} ({n}) / shard", "conclusion": "failure", "pack_step": "success"})
            continue
        jobs.append({"name": f"w{wave[n]} ({n}) / shard", "conclusion": "success", "pack_step": "success"})
        arts |= {f"wave-{KEY}-{n}", f"shard-{KEY}-{n}"}
    return jobs, arts


class RealChain(unittest.TestCase):
    def test_a_chain_of_one_is_the_resume_as_it_was(self):  # I1
        run, jobs, arts = run_of_fx(P)
        good = lr.good_packs(PLAN, lr.packed(jobs), arts, KEY)
        old_keep = lr.reusable(PLAN, lr.succeeded(jobs), good, arts, KEY)
        view = lr.chain_view(PLAN, [(run, jobs, arts)], KEY)
        self.assertEqual((len(old_keep), len(good)), (63, 66))
        self.assertEqual(kept(view), old_keep)
        self.assertEqual(set(view[1]), good)
        self.assertEqual(set(view[1].values()), {P})

    def test_the_snapshot_keeps_what_the_earlier_run_kept_and_runs_job_43_again(self):  # I2
        view = lr.chain_view(PLAN, [run_of_fx(R), run_of_fx(P)], KEY)
        self.assertEqual(len(kept(view)), 63)
        self.assertNotIn(43, view[0])  # failed in the resume (it failed in 42678283150 too)
        self.assertEqual(view[1][43], P)  # its pack: good in 42678283150, which every later job of the resume restored

    def test_the_resume_as_it_will_end_leaves_only_job_43(self):  # I2, I3
        ran = sorted(set(range(len(PLAN["shards"]))) - kept(lr.chain_view(PLAN, [run_of_fx(P)], KEY)))
        self.assertEqual(len(ran), 48)
        jobs, arts = finished(ran, {43: "built"})
        view = lr.chain_view(PLAN, [(R, jobs, arts), run_of_fx(P)], KEY)
        self.assertEqual(sorted(set(range(len(PLAN["shards"]))) - kept(view)), [43])
        source = view[1]
        _, pj, pa = run_of_fx(P)
        p_good = lr.good_packs(PLAN, lr.packed(pj), pa, KEY)
        for n, run in source.items():  # I3: a pack that was good in 42678283150 stays there; the resume's own packs are the ones that were not
            self.assertEqual(run, P if n in p_good else R, n)
        self.assertEqual(source[53], P)  # rebuilt by the resume too, but its later jobs were built on 42678283150's
        self.assertEqual(source[62], R)  # 42678283150 has no pack of 62 (stopped inside its build)

    def test_mutant_the_newest_good_pack(self):  # I3 fails
        # a resume in which job 43 kept its uploads too: 53 was rebuilt there, but every later job was built on 42678283150's pack of 53
        ran = sorted(set(range(len(PLAN["shards"]))) - kept(lr.chain_view(PLAN, [run_of_fx(P)], KEY)))
        jobs, arts = finished(ran, {})
        chain = [(R, jobs, arts), run_of_fx(P)]
        source = lr.chain_view(PLAN, chain, KEY)[1]
        self.assertEqual(source[53], P)
        self.assertTrue(i3_holds(PLAN, chain, source, KEY))
        mutant = {n: next(r for r, j, a in chain if n in lr.packed(j) and f"wave-{KEY}-{n}" in a) for n in source}  # the newest run with the pack
        self.assertEqual(mutant[53], R)
        self.assertFalse(i3_holds(PLAN, chain, mutant, KEY))

    def test_mutant_a_jobs_state_from_the_oldest_run(self):  # I2 fails
        ran = sorted(set(range(len(PLAN["shards"]))) - kept(lr.chain_view(PLAN, [run_of_fx(P)], KEY)))
        jobs, arts = finished(ran, {43: "built"})
        oldest_first = lr.chain_view(PLAN, [run_of_fx(P), (R, jobs, arts)], KEY)  # the same view with the runs the wrong way round
        self.assertNotEqual(kept(oldest_first), set(range(len(PLAN["shards"]))) - {43})

    def test_the_chain_is_read_from_the_real_plan_logs(self):  # I5
        self.assertEqual(lr.earlier_of(None, FX["runs"][R]["plan_log"]), P)
        self.assertEqual(lr.earlier_of(None, FX["runs"][P]["plan_log"]), "")
        self.assertEqual(lr.earlier_of({"from_tree": "true", "reuse_from": "77"}, FX["runs"][R]["plan_log"]), "77")  # lane.json first
        self.assertEqual(lr.earlier_of({"from_tree": "true"}, FX["runs"][R]["plan_log"]), P)  # a lane.json of before this change says nothing of it
        with self.assertRaises(ValueError):
            lr.earlier_of(None, "2026-11-11T18:14:40.1Z   REUSE_FROM: 1\n2026-11-11T18:14:41.1Z   REUSE_FROM: 2\n")
        self.assertEqual(lr.earlier_of(None, "2026-11-11T18:14:40.1Z   REUSE_FROM: \n"), "")  # a run started from wave 0 since reuse_from exists


def i3_holds(plan: dict, chain, source: dict[int, str], key: str) -> bool:
    """every pack handed on is packed and there in its run, and good in no older run of the chain (I3)"""
    order = [r for r, _, _ in chain]  # newest first
    for n, run in source.items():
        _, j, a = chain[order.index(run)]
        if n not in lr.packed(j) or f"wave-{key}-{n}" not in a:
            return False
        for r, j2, a2 in chain[order.index(run) + 1:]:  # the older runs
            restores = plan["shards"][n]["restore"]
            if n in lr.packed(j2) and f"wave-{key}-{n}" in a2 and all(x in source and order.index(source[x]) >= order.index(r) for x in restores):
                return False
    return True


def gen_plan(rng: random.Random) -> dict:
    n = rng.randint(3, 40)
    waves = sorted(rng.randint(0, min(n - 1, 9)) for _ in range(n))
    waves[0] = 0
    shards = []
    for i, w in enumerate(waves):
        earlier = [j for j in range(i) if waves[j] < w]
        shards.append({"shard": i, "wave": w, "restore": sorted(rng.sample(earlier, rng.randint(0, len(earlier))))})
    return {"shards": shards, "waves": max(waves) + 1}


def gen_run(rng: random.Random, plan: dict, shards: list[int], key: str = "k") -> tuple[list[dict], set[str]]:
    jobs, arts = [], set()
    for n in shards:
        w = plan["shards"][n]["wave"]
        fate = rng.choice(["success", "success", "success", "gate2", "build", "never", "lost"])
        if fate == "never":
            continue
        packed_ok = fate in ("success", "gate2", "lost")
        jobs.append({"name": f"w{w} ({n}) / shard", "conclusion": "success" if fate == "success" else "failure", "pack_step": "success" if packed_ok else "failure"})
        if packed_ok and fate != "lost":
            arts.add(f"wave-{key}-{n}")
        if fate == "success" or (fate == "gate2" and rng.random() < 0.5):
            arts.add(f"shard-{key}-{n}")
    return jobs, arts


class Generated(unittest.TestCase):
    def test_two_thousand_chains(self):  # I1 I2 I3 I4
        rng = random.Random(20261111)
        for case in range(2000):
            plan = gen_plan(rng)
            chain: list[tuple[str, list[dict], set[str]]] = []
            todo = [s["shard"] for s in plan["shards"]]
            for k in range(rng.randint(1, 4)):
                jobs, arts = gen_run(rng, plan, todo)
                chain.insert(0, (str(1000 + k), jobs, arts))
                ok, source, shard_pack = view = lr.chain_view(plan, chain, "k")
                keep = kept(view)
                if k == 0:  # I1
                    self.assertEqual(keep, lr.reusable(plan, lr.succeeded(jobs), lr.good_packs(plan, lr.packed(jobs), arts, "k"), arts, "k"), case)
                    self.assertEqual(set(source), lr.good_packs(plan, lr.packed(jobs), arts, "k"), case)
                for s in plan["shards"]:  # I4
                    if s["shard"] in source:
                        self.assertTrue(all(r in source for r in s["restore"]), case)
                self.assertTrue(i3_holds(plan, chain, source, "k"), case)  # I3
                for n in keep:  # I2: the newest run that ran it says success, and holds its shard pack
                    r, j, a = next(c for c in chain if any((m := lr.JOB.match(x["name"])) and int(m.group(2)) == n for x in c[1]))
                    self.assertTrue(any(x["name"].endswith(f"({n}) / shard") and x["conclusion"] == "success" for x in j), case)
                    self.assertIn(f"shard-k-{n}", a, case)
                todo = [s["shard"] for s in plan["shards"] if s["shard"] not in keep]
                if not todo:
                    break


class Packs(unittest.TestCase):
    def test_what_the_plan_hands_on_the_shard_reads_back(self):  # I6
        ran = sorted(set(range(len(PLAN["shards"]))) - kept(lr.chain_view(PLAN, [run_of_fx(P)], KEY)))
        jobs, arts = finished(ran, {43: "built"})
        _, source, _ = view = lr.chain_view(PLAN, [(R, jobs, arts), run_of_fx(P)], KEY)
        out = lr.chain_outputs(PLAN, kept(view), source, [R, P])
        self.assertEqual(wp.parse_packs(out["packs"], R), source)
        self.assertEqual(out["fill"], f"{R},{P}")
        self.assertEqual(json.loads(out["w7"]), [43])
        for n, run in source.items():
            self.assertEqual(wp.run_of(n, "999", R, wp.parse_packs(out["packs"], R)), run)
        self.assertEqual(wp.run_of(43 + 1000, "999", R, source), "999")  # no pack handed on: this run's

    def test_bad_lists_are_refused(self):  # I6
        for bad in ("x", "1@0", "1@", "@5", "1,1", "1@5,1@6", "12345", "1@1234567890123456"):
            with self.assertRaises(ValueError, msg=bad):
                wp.parse_packs(bad, "77")
        with self.assertRaises(ValueError):
            wp.parse_packs("3", "")  # a plain N needs reuse_run
        self.assertEqual(wp.parse_packs("3,4@9", "77"), {3: "77", 4: "9"})  # the lists of before this change still read
        self.assertEqual(wp.parse_packs("", ""), {})

    def test_bump_shard_takes_what_the_plan_hands_on(self):  # I6: the shell check itself
        step = yaml.safe_load((WF / "bump-shard.yml").read_text())["jobs"]["shard"]["steps"][0]["run"]
        check = next(ln for ln in step.splitlines() if "REUSE_PACKS" in ln and "=~" in ln)
        ran = sorted(set(range(len(PLAN["shards"]))) - kept(lr.chain_view(PLAN, [run_of_fx(P)], KEY)))
        jobs, arts = finished(ran, {43: "built"})
        _, source, _ = view = lr.chain_view(PLAN, [(R, jobs, arts), run_of_fx(P)], KEY)
        good = lr.chain_outputs(PLAN, kept(view), source, [R, P])["packs"]
        for packs, want in ((good, 0), ("", 0), ("1,2,3", 0), ("1@5", 0), ("1@5;rm -rf /", 1), ("1@0", 1), ("a", 1), ("1,,2", 1)):
            r = subprocess.run(["bash", "-c", check], env={"REUSE_RUN": R, "REUSE_PACKS": packs, "PATH": "/usr/bin:/bin"}, capture_output=True, text=True)
            self.assertEqual(r.returncode != 0, bool(want), (packs, r.stdout))


def fake_gh(store: dict[str, dict[str, dict[str, str]]], fail_first: int = 0):
    """gh run download / gh api .../artifacts over `store` {run: {artifact: {relpath: text}}}; the first `fail_first` calls fail (a 502)"""
    calls = []

    def runner(cmd, capture_output=True, text=True, check=False):
        calls.append(cmd)
        if len(calls) <= fail_first:
            return subprocess.CompletedProcess(cmd, 1, "", "HTTP 502")
        if cmd[1:3] == ["run", "download"]:
            run, name, dest = cmd[3], cmd[cmd.index("-n") + 1], Path(cmd[cmd.index("-D") + 1])
            if name not in store.get(run, {}):
                return subprocess.CompletedProcess(cmd, 1, "", "no artifact")
            for rel, body in store[run][name].items():
                f = dest / rel
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(body)
            return subprocess.CompletedProcess(cmd, 0, "", "")
        if cmd[1] == "api":
            run = re.search(r"/runs/(\d+)/artifacts", cmd[3]).group(1)
            return subprocess.CompletedProcess(cmd, 0, "\n".join(store.get(run, {})) + "\n", "")
        raise AssertionError(cmd)

    return runner, calls


def real_store(plan_old: dict | None = None, inputs_old: str = '{"x": 1}') -> dict:
    plan_text = json.dumps(plan_old or PLAN)
    store = {}
    for run in (R, P):
        names = set(FX["runs"][run]["artifacts"]) | ({f"shard-{KEY}-53", f"shard-{KEY}-62", f"wave-{KEY}-62"} if run == R else set())
        store[run] = {n: ({"shard-pack/src/marker": run} if n.startswith("shard-") else {"x": run}) for n in names}
        store[run][f"plan-{KEY}"] = {"plan.json": plan_text, **({"inputs.json": inputs_old} if inputs_old else {})}
    return store


class Fill(unittest.TestCase):
    def setUp(self):
        self.t = Path(tempfile.mkdtemp())
        (self.t / "plan-new").mkdir()
        (self.t / "plan-new" / "plan.json").write_text(json.dumps(PLAN))
        (self.t / "plan-new" / "inputs.json").write_text('{"x": 1}')
        (self.t / "shards" / f"shard-{KEY}-43" / "shard-pack" / "src").mkdir(parents=True)
        (self.t / "shards" / f"shard-{KEY}-43" / "shard-pack" / "src" / "marker").write_text("here")

    def fill(self, store, runs=(R, P), **kw):
        runner, calls = fake_gh(store, kw.pop("fail_first", 0))
        got = ff.fill_from("o/r", KEY, list(runs), self.t / "shards", self.t / "work", self.t / "plan-new", runner=runner, sleep=lambda s: None, **kw)
        return got, calls

    def marker(self, n: int) -> str:
        return (self.t / "shards" / f"shard-{KEY}-{n}" / "shard-pack" / "src" / "marker").read_text()

    def test_every_run_newest_first_never_replacing(self):  # I7
        got, calls = self.fill(real_store())
        self.assertEqual(self.marker(43), "here")  # built by the run being cut
        self.assertEqual(self.marker(53), R)  # in both: the newer copy
        self.assertEqual(self.marker(0), P)
        n_p = sum(1 for n in FX["runs"][P]["artifacts"] if re.fullmatch(rf"shard-{KEY}-\d+", n))
        self.assertEqual(sum(got.values()) + 1, len({p.name for p in (self.t / "shards").iterdir()}))
        self.assertEqual(got[R], 2)
        self.assertEqual(got[P], n_p - 1 - (1 if f"shard-{KEY}-43" in FX["runs"][P]["artifacts"] else 0))  # 53 came from the resume
        downloaded = [c[c.index("-n") + 1] for c in calls if c[1:3] == ["run", "download"]]
        self.assertFalse([d for d in downloaded if d.startswith("wave-")])  # packs are not shards

    def test_another_plan_is_refused(self):  # I7
        other = dict(PLAN, waves=PLAN["waves"] + 1)
        with self.assertRaises(SystemExit) as e:
            self.fill(real_store(plan_old=other))
        self.assertIn(R, str(e.exception))

    def test_other_settings_are_refused(self):  # I7
        with self.assertRaises(SystemExit):
            self.fill(real_store(inputs_old='{"x": 2}'))

    def test_a_run_without_settings_needs_a_vouch(self):  # I7
        with self.assertRaises(SystemExit):
            self.fill(real_store(inputs_old=""))
        got, _ = self.fill(real_store(inputs_old=""), unrecorded=True)
        self.assertTrue(got)

    def test_a_502_is_tried_again(self):
        got, calls = self.fill(real_store(), fail_first=2)
        self.assertTrue(got)

    def test_the_finish_job_fills_without_the_plan(self):
        runner, _ = fake_gh(real_store())
        got = ff.fill_from("o/r", KEY, [R, P], self.t / "shards", self.t / "work2", None, runner=runner, sleep=lambda s: None)
        self.assertTrue(got)

    def test_run_lists(self):
        self.assertEqual(ff.runs_of(f"{R},{P}"), [R, P])
        for bad in ("", "0", "1,1", "a", ",".join(str(i) for i in range(1, 10)), "1;2"):
            with self.assertRaises(ValueError, msg=bad):
                ff.runs_of(bad)

    def test_only_this_keys_shards(self):
        self.assertEqual(ff.shard_names(["shard-k-2", "shard-k-10", "shard-kk-1", "wave-k-1", "plan-k", "shard-k-x", "shard-k-1"], "k"), ["shard-k-1", "shard-k-2", "shard-k-10"])


class WorkflowText(unittest.TestCase):
    def setUp(self):
        self.shard = yaml.safe_load((WF / "bump-shard.yml").read_text())["jobs"]["shard"]["steps"]

    def uploads(self, prefix: str) -> list[dict]:
        return [s for s in self.shard if "upload-artifact" in s.get("uses", "") and prefix in json.dumps(s.get("with", {}))]

    def test_each_pack_upload_is_tried_three_times(self):  # I8
        for prefix, first in (("wave-${{ inputs.key }}", "wave_up"), ("shard-${{ inputs.key }}", "shard_up")):
            ups = self.uploads(prefix)
            self.assertEqual(len(ups), 3, prefix)
            self.assertEqual([u.get("id") for u in ups], [f"{first}1", f"{first}2", None])
            self.assertTrue(ups[0]["continue-on-error"] and ups[1]["continue-on-error"])
            self.assertNotIn("continue-on-error", ups[2])  # the last try fails the job: a pack that is not there must not read as handed on
            for u in ups:
                self.assertIs(u["with"]["overwrite"], True)
            self.assertIn(f"steps.{first}1.outcome == 'failure'", ups[1]["if"])
            self.assertIn(f"steps.{first}2.outcome == 'failure'", ups[2]["if"])
            waits = [s for s in self.shard if s.get("run", "").startswith("sleep") and first in s.get("if", "")]
            self.assertEqual([w["run"] for w in waits], ["sleep 300", "sleep 900"])

    def test_the_pack_step_is_still_what_lane_reuse_reads(self):
        names = [s.get("name", "") for s in self.shard]
        self.assertTrue(any(n.startswith("This job's work, for the jobs after it") for n in names))


class ResumeStep(unittest.TestCase):
    """bump-waves.yml's RESUME step, run on the real runs: fake `gh` and `curl` serve the fixture"""

    def test_the_step_walks_the_real_chain(self):  # I2 I3 I5 I6 end to end
        step = next(s for s in yaml.safe_load((WF / "bump-waves.yml").read_text())["jobs"]["plan"]["steps"] if s.get("id") == "r")
        t = Path(tempfile.mkdtemp())
        (t / "emissary" / "scripts" / "bump").mkdir(parents=True)
        for f in ("lane_reuse.py", "plan_waves.py"):
            (t / "emissary" / "scripts" / "bump" / f).symlink_to(HERE / f)
        for f in HERE.glob("*.py"):
            if not (t / "emissary" / "scripts" / "bump" / f.name).exists():
                (t / "emissary" / "scripts" / "bump" / f.name).symlink_to(f)
        ran = sorted(set(range(len(PLAN["shards"]))) - kept(lr.chain_view(PLAN, [run_of_fx(P)], KEY)))
        jobs, arts = finished(ran, {43: "built"})
        runs = {R: {"jobs": jobs, "artifacts": sorted(arts), "log": FX["runs"][R]["plan_log"], "id": 1},
                P: {"jobs": FX["runs"][P]["jobs"], "artifacts": FX["runs"][P]["artifacts"], "log": FX["runs"][P]["plan_log"], "id": 2}}
        (t / "fx.json").write_text(json.dumps({"runs": runs, "plan": PLAN, "key": KEY}))
        bin_ = t / "bin"
        bin_.mkdir()
        (bin_ / "gh").write_text(f"""#!{sys.executable}
import json, sys, os, pathlib, re
fx = json.load(open({str(t / "fx.json")!r}))
a = sys.argv[1:]
if a[:2] == ["run", "download"]:
    d = pathlib.Path(a[a.index("-D") + 1]); d.mkdir(parents=True, exist_ok=True)
    (d / "plan.json").write_text(json.dumps(fx["plan"])); (d / "inputs.json").write_text("{{}}")
    sys.exit(0)
url = next(x for x in a if x.startswith("repos/"))
run = re.search(r"/runs/(\\d+)", url).group(1)
jq = a[a.index("--jq") + 1] if "--jq" in a else ""
if url.endswith("/runs/" + run):
    print(".github/workflows/bump-waves.yml | bump-waves " + fx["key"])
elif "/jobs" in url and 'select(.name == "plan")' in jq:
    print(fx["runs"][run]["id"])
elif "/jobs" in url:
    for j in fx["runs"][run]["jobs"]: print(json.dumps(j))
elif "/artifacts" in url:
    for n in fx["runs"][run]["artifacts"]: print(n)
""")
        (bin_ / "curl").write_text(f"""#!{sys.executable}
import json, sys
fx = json.load(open({str(t / "fx.json")!r}))
a = sys.argv[1:]
url = next(x for x in a if x.startswith("https://"))
jid = int(url.rstrip("/").split("/")[-2])
run = next(r for r, v in fx["runs"].items() if v["id"] == jid)
open(a[a.index("-o") + 1], "w").write(fx["runs"][run]["log"])
""")
        for f in ("gh", "curl"):
            (bin_ / f).chmod((bin_ / f).stat().st_mode | stat.S_IEXEC)
        (t / "out").write_text("")
        env = {"PATH": f"{bin_}:{Path(sys.executable).parent}:/usr/bin:/bin:/usr/local/bin", "REUSE_FROM": R, "KEY": KEY, "FROM_TREE": "true", "GH_TOKEN": "x",
               "GITHUB_REPOSITORY": "o/r", "GITHUB_OUTPUT": str(t / "out")}
        script = step["run"].replace("python3 ", f"{sys.executable} ").replace("sleep $((i * 20))", "true")
        r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script], cwd=t / "emissary", env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        out = dict(ln.split("=", 1) for ln in (t / "out").read_text().splitlines() if "=" in ln)
        self.assertEqual(out["fill"], f"{R},{P}")
        self.assertEqual(sum(len(json.loads(out[f"w{w}"])) for w in range(lr.MAX_WAVES)), 1)  # job 43 alone
        self.assertEqual(json.loads(out["w7"]), [43])
        packs = wp.parse_packs(out["packs"], R)
        self.assertEqual(packs[43], P)
        self.assertEqual(packs[62], R)
        self.assertIn("reused from the earlier run: 110 of 111", r.stderr)


if __name__ == "__main__":
    unittest.main()
