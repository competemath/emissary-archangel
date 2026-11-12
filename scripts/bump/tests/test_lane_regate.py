"""A shard whose Gate 2 ran out of budget is judged again on its own build, and its pack takes the new verdicts (shard_pack.py regate; bump-shard.yml regate).

The real case (fixtures/flt_shard43_pack_2026-11-12.json.gz): flt-anthropic's job 43 in run 43146942669 (12 Nov 2026) built for 3 h 02 min, so its Gate 2 had 139 of the
job's 345 minutes: 288 theorems judged, 125 passed, and 114 target modules left without a verdict (gate2-killed.json). Nothing in the lane judged them again, and the
bundle cuts a module without a verdict with everything that imports it: those theorems could never ship.

Invariants:
  I1  the new pack is the old one plus the new verdicts: sources, ranges, the build's errors, the earlier passes and their keep lines unchanged;
  I2  a target judged now leaves the killed list; one the new job could not judge stays; nothing else changes on it;
  I3  the counts add up (checked, passes, fail reasons), and the regate is recorded;
  I4  only the old killed targets may be judged: a pass credited to another module, a target that had a verdict, or a new killed module that was not asked is refused;
  I5  through the bundle's own merge (shard_pack.py merge) the judged modules are no longer killed, so compose keeps them;
  I6  the regate plan (regate_plan.py) picks the shards whose own targets include a killed module, reading the packs as the bundle does (this run first, then the
      runs it resumes, each the lane's own run of the same library), and hands the jobs the runs to find the packs in;
  I7  the shard job's REGATE step (bump-shard.yml), run on the real pack and the real plan entry of shard 43: Gate 2 is asked exactly the 114, the shard's own pack is
      restored with the earlier jobs', every module of the build is restored, nothing is built, no wave pack is handed on;
  I8  bump-waves.yml: every wave passed, then the regate plan, the regate jobs, then the bundle, which a failed regate does not stop;
  I9  a regate never touches the shard's first pack: its pack is regate-KEY-N, uploaded only when it was made whole, and whatever reads the packs takes it in the
      shard pack's place (fill_from.py pack_names, promote; the bundle's compose and finish) (cubic, #180).
Mutant: handing the new verdicts in as a second pack instead (the merge takes the union of the killed lists) leaves all 114 killed (fails I5).
Cases: the real pack with all 114 judged and with 34 still killed, 6 refusals, 1,000 generated splits of the real killed list, the real plan entry of shard 43, 7 input checks.
"""

from __future__ import annotations

import argparse
import contextlib
import gzip
import io
import json
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import fill_from as ff  # noqa: E402
import shard_pack as sp  # noqa: E402

FX = json.loads(gzip.open(HERE / "tests" / "fixtures" / "flt_shard43_pack_2026-11-12.json.gz", "rt", encoding="utf-8").read())
KILLED = json.loads(FX["files"]["emissary/gate2-killed.json"])
OLD_PASSED = json.loads(FX["files"]["shard-pack/passed.json"])
OLD_RESULTS = json.loads(FX["files"]["shard-pack/gate2-results.json"])


def old_pack(root: Path) -> Path:
    art = root / "shard-flt-anthropic-43"
    for rel, text in FX["files"].items():
        f = art / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)
    return art


def new_verdicts(root: Path, asked: list[str], still: list[str], passes: dict[str, list[str]], fails: int = 0) -> dict[str, Path]:
    d = root / "new"
    d.mkdir(parents=True, exist_ok=True)
    (d / "asked.txt").write_text("\n".join(asked) + "\n")
    (d / "killed.json").write_text(json.dumps(still))
    (d / "passed.json").write_text(json.dumps(passes))
    n = sum(len(v) for v in passes.values())
    (d / "results.json").write_text(json.dumps({"checked": n + fails, "pass": n, "pass_equal": n, "pass_entails": 0, "pass_private_not_records": 0,
                                                 "fail_reasons": {"uses_sorry": fails} if fails else {}, "pass_unattributed": []}))
    (d / "gate2.log").write_text("".join(f"GATE2B_PASS old={x} new={x} via=equal\n" for v in passes.values() for x in v) + "some other line\n")
    (d / "keep.log").write_text("x:1:0: info: BUNDLE_KEEP " + json.dumps([[m, x] for m, v in passes.items() for x in v]) + " BUNDLE_END\n")
    return {k: d / f for k, f in (("asked", "asked.txt"), ("killed", "killed.json"), ("passed", "passed.json"), ("results", "results.json"), ("gate2", "gate2.log"), ("keep", "keep.log"))}


def regate(root: Path, art: Path, v: dict[str, Path]) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "regate", "--old", str(art), "--asked", str(v["asked"]), "--gate2", str(v["gate2"]), "--passed", str(v["passed"]),
                           "--results", str(v["results"]), "--killed", str(v["killed"]), "--keep", str(v["keep"]), "--out", str(root / "out" / "shard-pack"),
                           "--out-emissary", str(root / "out" / "emissary")], capture_output=True, text=True)


def passes_for(mods: list[str], k: int = 2) -> dict[str, list[str]]:
    return {m: [f"{m}.thm{i}" for i in range(k)] for m in mods}


class RealShard43(unittest.TestCase):
    def setUp(self):
        self.t = Path(tempfile.mkdtemp())
        self.art = old_pack(self.t)

    def test_the_fixture_is_the_real_case(self):
        self.assertEqual(len(KILLED), 114)
        self.assertEqual(OLD_RESULTS["checked"], 288)
        self.assertEqual(OLD_RESULTS["pass"], 125)
        self.assertEqual(sum(len(v) for v in OLD_PASSED.values()), 125)
        self.assertFalse(set(KILLED) & set(OLD_PASSED))  # a killed target has no passes

    def test_every_target_judged(self):  # I1 I2 I3
        passed_mods = KILLED[:30]
        v = new_verdicts(self.t, KILLED, [], passes_for(passed_mods), fails=40)
        r = regate(self.t, self.art, v)
        self.assertEqual(r.returncode, 0, r.stderr)
        out = self.t / "out"
        self.assertEqual(json.loads((out / "emissary" / "gate2-killed.json").read_text()), [])
        merged = json.loads((out / "shard-pack" / "passed.json").read_text())
        for m, ns in OLD_PASSED.items():
            self.assertEqual(merged[m], ns)  # the earlier passes, as they were
        self.assertEqual(set(merged) - set(OLD_PASSED), set(passed_mods))
        res = json.loads((out / "shard-pack" / "gate2-results.json").read_text())
        self.assertEqual(res["checked"], 288 + 60 + 40)
        self.assertEqual(res["pass"], 125 + 60)
        self.assertEqual(res["fail_reasons"]["uses_sorry"], OLD_RESULTS["fail_reasons"]["uses_sorry"] + 40)
        self.assertEqual(res["regate"], {"asked": 114, "judged": 114, "still_killed": 0})
        self.assertEqual(json.loads((out / "emissary" / "gate2-results.json").read_text()), res)
        keep = (out / "shard-pack" / "bundle-deps.log").read_text()
        self.assertTrue(keep.startswith(FX["files"]["shard-pack/bundle-deps.log"]))  # the earlier keep lines first, as they were
        self.assertEqual(keep.count("BUNDLE_KEEP"), 2)
        for rel, text in FX["files"].items():
            if rel.startswith(("shard-pack/src/", "shard-pack/ranges/")) or rel == "shard-pack/errors.log":
                self.assertEqual((out / rel).read_text(), text, rel)  # the build is the first job's
        log = (out / "shard-pack" / "gate2.log").read_text()
        self.assertTrue(log.startswith(FX["files"]["shard-pack/gate2.log"].rstrip("\n")))
        self.assertNotIn("some other line", log)  # only verdict lines, as pack keeps them

    def test_some_targets_still_without_a_verdict(self):  # I2
        still = KILLED[80:]
        v = new_verdicts(self.t, KILLED, still, passes_for(KILLED[:10]))
        r = regate(self.t, self.art, v)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(json.loads((self.t / "out" / "emissary" / "gate2-killed.json").read_text()), sorted(still))
        self.assertEqual(json.loads((self.t / "out" / "shard-pack" / "gate2-results.json").read_text())["regate"], {"asked": 114, "judged": 80, "still_killed": 34})

    def test_refusals(self):  # I4
        a_passed_module = next(iter(OLD_PASSED))
        cases = {
            "asked a module that had a verdict": dict(asked=KILLED + [a_passed_module], still=[], passes={}),
            "a pass in a module not asked": dict(asked=KILLED[:10], still=[], passes=passes_for([KILLED[20]])),
            "a pass in a module still killed": dict(asked=KILLED[:10], still=KILLED[:2], passes=passes_for(KILLED[:1])),
            "killed but not asked": dict(asked=KILLED[:10], still=[KILLED[50]], passes={}),
            "nothing asked": dict(asked=[], still=[], passes={}),
            "a pass in a module of the first pack": dict(asked=KILLED[:10], still=[], passes=passes_for([a_passed_module])),
        }
        for why, c in cases.items():
            t = Path(tempfile.mkdtemp())
            art = old_pack(t)
            v = new_verdicts(t, c["asked"], c["still"], c["passes"])
            self.assertNotEqual(regate(t, art, v).returncode, 0, why)
            self.assertFalse((t / "out" / "emissary" / "gate2-killed.json").exists(), why)  # nothing written


class ThroughTheBundlesMerge(unittest.TestCase):
    def merge(self, shards: Path) -> dict:
        logs = shards.parent / "logs"
        logs.mkdir(exist_ok=True)
        r = subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "merge", "--shards", str(shards), "--out", str(shards.parent / "merged"), "--logs", str(logs)],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return {"killed": json.loads((logs / "gate2-killed.json").read_text()), "passed": json.loads((logs / "passed.json").read_text())}

    def test_the_judged_modules_reach_compose(self):  # I5
        t = Path(tempfile.mkdtemp())
        art = old_pack(t)
        v = new_verdicts(t, KILLED, KILLED[100:], passes_for(KILLED[:30]))
        self.assertEqual(regate(t, art, v).returncode, 0)
        shards = t / "shards" / "shard-flt-anthropic-43"
        shutil.copytree(t / "out", shards)
        got = self.merge(t / "shards")
        self.assertEqual(sorted(got["killed"]), sorted(KILLED[100:]))
        self.assertEqual(set(got["passed"]), set(OLD_PASSED) | set(KILLED[:30]))

    def test_mutant_a_second_pack(self):  # I5 fails: the union of the killed lists keeps all 114
        t = Path(tempfile.mkdtemp())
        art = old_pack(t)
        shards = t / "shards"
        shutil.copytree(art, shards / "shard-flt-anthropic-43")
        second = shards / "shard-flt-anthropic-43-regate"
        (second / "shard-pack" / "src").mkdir(parents=True)
        (second / "emissary").mkdir()
        (second / "emissary" / "gate2-killed.json").write_text("[]")
        (second / "shard-pack" / "passed.json").write_text(json.dumps(passes_for(KILLED[:30])))
        got = self.merge(shards)
        self.assertEqual(len(got["killed"]), 114)


class Generated(unittest.TestCase):
    def test_a_thousand_splits_of_the_real_killed_list(self):  # I2 I3 I4
        rng = random.Random(20261112)
        base = Path(tempfile.mkdtemp())
        art = old_pack(base)
        for case in range(1000):
            with contextlib.redirect_stdout(io.StringIO()):
                asked = sorted(rng.sample(KILLED, rng.randint(1, len(KILLED))))
                still = sorted(rng.sample(asked, rng.randint(0, len(asked))))
                judged = [m for m in asked if m not in still]
                passed = rng.sample(judged, rng.randint(0, len(judged))) if judged else []
                t = base / f"c{case}"
                v = new_verdicts(t, asked, still, passes_for(passed, rng.randint(1, 3)), fails=rng.randint(0, 50))
                sp.regate(argparse.Namespace(old=str(art), asked=str(v["asked"]), gate2=str(v["gate2"]), passed=str(v["passed"]), results=str(v["results"]), killed=str(v["killed"]),
                                             keep=str(v["keep"]), keep_drops="", out=str(t / "out" / "shard-pack"), out_emissary=str(t / "out" / "emissary")))  # in process: 1,000 cases
                killed = json.loads((t / "out" / "emissary" / "gate2-killed.json").read_text())
                self.assertEqual(set(killed), (set(KILLED) - set(asked)) | set(still), case)
                merged = json.loads((t / "out" / "shard-pack" / "passed.json").read_text())
                self.assertEqual(set(merged), set(OLD_PASSED) | set(passed), case)
                self.assertFalse(set(merged) & set(killed), case)  # no module both passed and without a verdict
                res = json.loads((t / "out" / "shard-pack" / "gate2-results.json").read_text())
                new = json.loads(v["results"].read_text())
                self.assertEqual(res["pass"], OLD_RESULTS["pass"] + new["pass"], case)
                self.assertEqual(res["checked"], OLD_RESULTS["checked"] + new["checked"], case)
                shutil.rmtree(t)



PLAN43 = json.loads(gzip.open(HERE / "tests" / "fixtures" / "flt_plan_shard43.json.gz", "rt", encoding="utf-8").read())
WF = HERE.parents[1] / ".github" / "workflows"


class Plan(unittest.TestCase):
    """regate_plan.py: the shards whose own targets include a killed module (I6)"""

    def setUp(self):
        sys.path.insert(0, str(HERE))
        import regate_plan

        self.rp = regate_plan
        self.t = Path(tempfile.mkdtemp())
        old_pack(self.t / "shards")
        (self.t / "shards" / "shard-flt-anthropic-43").rename(self.t / "shards" / "shard-flt-anthropic-43")

    def plan(self, extra: list[dict] | None = None) -> dict:
        return {"shards": [{"shard": 43, "targets": PLAN43["targets"]}] + (extra or []), "waves": 21}

    def test_the_real_shard_is_judged_again_with_all_114(self):
        shards, counts = self.rp.to_regate(self.plan(), self.t / "shards", "flt-anthropic")
        self.assertEqual(shards, [43])
        self.assertEqual(counts, {43: 114})
        self.assertLessEqual(set(KILLED), set(PLAN43["targets"]))  # every killed module is one of the shard's own targets

    def test_a_shard_with_nothing_killed_or_no_pack_or_no_targets_is_left(self):
        art = self.t / "shards" / "shard-flt-anthropic-44" / "emissary"
        art.mkdir(parents=True)
        (art / "gate2-killed.json").write_text("[]")
        extra = [{"shard": 44, "targets": ["A"]}, {"shard": 45, "targets": ["B"]}, {"shard": 46, "targets": []}]
        shards, _ = self.rp.to_regate(self.plan(extra), self.t / "shards", "flt-anthropic")
        self.assertEqual(shards, [43])

    def test_a_killed_module_another_shard_targets_is_not_this_ones(self):
        plan = {"shards": [{"shard": 43, "targets": PLAN43["targets"][:5]}], "waves": 21}
        shards, counts = self.rp.to_regate(plan, self.t / "shards", "flt-anthropic")
        self.assertEqual(counts.get(43, 0), len(set(PLAN43["targets"][:5]) & set(KILLED)))

    def test_a_bad_killed_list_is_refused(self):
        (self.t / "shards" / "shard-flt-anthropic-43" / "emissary" / "gate2-killed.json").write_text('{"a": 1}')
        with self.assertRaises(SystemExit):
            self.rp.to_regate(self.plan(), self.t / "shards", "flt-anthropic")


class ShardStep(unittest.TestCase):
    """bump-shard.yml's REGATE step on the real pack and the real plan entry of shard 43 (I7): Gate 2 asked exactly the killed targets, the shard's own pack
    restored with the earlier ones, every module of the build restored, the files where Gate 2 reads them"""

    def run_step(self, killed: list[str] | None = None) -> tuple[subprocess.CompletedProcess, Path]:
        import yaml

        step = next(s for s in yaml.safe_load((WF / "bump-shard.yml").read_text())["jobs"]["shard"]["steps"] if s.get("name", "").startswith("REGATE - the shard's pack, and"))
        t = Path(tempfile.mkdtemp())
        art = old_pack(t / "store")
        if killed is not None:
            (art / "emissary" / "gate2-killed.json").write_text(json.dumps(killed))
        (t / "emissary").mkdir()
        (t / "targets.txt").write_text("\n".join(PLAN43["targets"]) + "\n")
        build = PLAN43["own"] + PLAN43["build_minus_own_sample"]
        (t / "build.txt").write_text("\n".join(build) + "\n")
        (t / "own.txt").write_text("\n".join(PLAN43["own"]) + "\n")
        (t / "restore.txt").write_text(",".join(str(x) for x in PLAN43["restore"]))
        bin_ = t / "bin"
        bin_.mkdir()
        (bin_ / "gh").write_text(f"""#!{sys.executable}
import shutil, sys
a = sys.argv[1:]
run = a[2]
if run != "222":
    sys.exit(1)  # only the second run of regate_from holds the pack
shutil.copytree({str(art)!r}, a[a.index("-D") + 1])
""")
        (bin_ / "gh").chmod(0o755)
        env = {"PATH": f"{bin_}:{Path(sys.executable).parent}:/usr/bin:/bin", "REGATE_FROM": "111,222", "KEY": "flt-anthropic", "SHARD": "43", "GITHUB_REPOSITORY": "o/r", "GH_TOKEN": "x"}
        r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step["run"].replace("python3 ", f"{sys.executable} ")], cwd=t, env=env, capture_output=True, text=True)
        return r, t

    def test_the_real_shard(self):
        r, t = self.run_step()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("the pack of shard 43 is run 222's", r.stdout)
        asked = (t / "asked.txt").read_text().split()
        self.assertEqual(sorted(asked), sorted(KILLED))
        self.assertEqual((t / "emissary" / "targets.txt").read_text().split(), asked)  # Gate 2 reads it there, and judges only these
        self.assertEqual((t / "closure.txt").read_text().split(), (t / "build.txt").read_text().split())  # every module of the build is restored
        restore = (t / "restore.txt").read_text().split(",")
        self.assertEqual(restore, [str(x) for x in PLAN43["restore"]] + ["43"])  # the shard's own pack too
        for f in ("build", "own"):
            self.assertEqual((t / "emissary" / f"{f}.txt").read_text(), (t / f"{f}.txt").read_text())

    def test_nothing_killed_stops_the_job(self):
        r, _ = self.run_step(killed=[])
        self.assertNotEqual(r.returncode, 0)


class Wiring(unittest.TestCase):
    """bump-waves.yml (I8): every wave passed, then the regate plan, the regate jobs, then the bundle, which a failed regate does not stop"""

    def setUp(self):
        import yaml

        self.waves = yaml.safe_load((WF / "bump-waves.yml").read_text())["jobs"]
        self.shard = yaml.safe_load((WF / "bump-shard.yml").read_text())

    def test_the_order(self):
        self.assertEqual(set(self.waves["regate-plan"]["needs"]), {"plan", "lane-done"})
        self.assertEqual(set(self.waves["regate"]["needs"]), {"plan", "regate-plan"})
        self.assertEqual(set(self.waves["bundle"]["needs"]), {"plan", "lane-done", "regate-plan", "regate"})

    def test_a_failed_regate_does_not_stop_the_bundle(self):
        cond = self.waves["bundle"]["if"]
        self.assertIn("!cancelled()", cond)
        self.assertNotIn("contains(needs.*.result", cond)  # that would count the regate jobs too
        self.assertNotIn("needs.regate.result", cond)

    def test_the_regate_jobs(self):
        j = self.waves["regate"]
        w = j["with"]
        self.assertEqual((w["build_once"], w["regate"]), ("true", "true"))
        self.assertEqual(w["regate_from"], "${{ needs.regate-plan.outputs.from }}")
        self.assertEqual(w["reuse_packs"], "${{ needs.plan.outputs.packs }}")
        self.assertEqual(int(w["gate2_budget_min"]), 300)
        self.assertEqual(j["strategy"]["matrix"]["shard"], "${{ fromJSON(needs.regate-plan.outputs.shards) }}")
        self.assertIn("needs.regate-plan.outputs.shards != '[]'", j["if"])
        self.assertLessEqual(set(w), set(self.shard[True]["workflow_call"]["inputs"]))

    def test_a_regate_builds_nothing_and_hands_on_no_wave_pack(self):
        steps = self.shard["jobs"]["shard"]["steps"]
        by = {s.get("name", ""): s for s in steps}
        self.assertEqual(by["Build this shard's modules, repair, rebuild"]["if"], "inputs.regate != 'true'")
        self.assertEqual(by["Pack this shard"]["if"], "inputs.regate != 'true'")
        for s in steps:
            if "wave-" in json.dumps(s.get("with", {})) or "wave_pack.py pack" in s.get("run", ""):
                self.assertIn("inputs.regate != 'true'", s["if"], s.get("name"))
        merge = by["REGATE - the shard's pack with the new verdicts"]
        self.assertEqual(merge["if"], "inputs.regate == 'true'")
        self.assertIn("shard_pack.py regate --old ../old-shard --asked ../asked.txt", merge["run"])
        names = [s.get("name", "") for s in steps]
        self.assertLess(names.index("REGATE - the shard's pack, and the targets its Gate 2 gave no verdict"), names.index("The work of the earlier jobs (a build-once; before any code of the library runs, the one step with a token)"))
        self.assertLess(names.index("Batched Gate 2 over the declarations of this shard's targets"), names.index("REGATE - the shard's pack with the new verdicts"))

    def test_the_inputs_are_checked(self):
        check = self.shard["jobs"]["shard"]["steps"][0]["run"]
        line = next(ln for ln in check.splitlines() if "REGATE_FROM" in ln)
        for regate, frm, once, ok in (("false", "", "false", True), ("true", "1,2", "true", True), ("true", "", "true", False), ("true", "1", "false", False),
                                      ("maybe", "", "false", False), ("true", "1;rm", "true", False), ("false", "1,,2", "false", False)):
            r = subprocess.run(["bash", "-c", line], env={"REGATE": regate, "REGATE_FROM": frm, "BUILD_ONCE": once, "PATH": "/usr/bin:/bin"}, capture_output=True, text=True)
            self.assertEqual(r.returncode == 0, ok, (regate, frm, once))


class PlanEndToEnd(unittest.TestCase):
    """regate_plan.py as the regate-plan job runs it: fake gh serves this run (its plan, no shard 43) and the run it resumes (the real pack of shard 43), both
    the lane's own runs of the same library (I6)"""

    def run_plan(self, earlier_branch: str = "main") -> subprocess.CompletedProcess:
        t = Path(tempfile.mkdtemp())
        art = old_pack(t / "store")
        (t / "emissary" / "data" / "exports" / "flt-anthropic").mkdir(parents=True)
        setup = {"repo": "https://github.com/anthropics/fermats-last-theorem", "commit": "a" * 40, "roots": ["Theorems", "Definitions"]}
        (t / "emissary" / "data" / "exports" / "flt-anthropic" / "setup.ci.json").write_text(json.dumps(setup))
        (t / "emissary" / "sources.json").write_text(json.dumps({"sources": {"flt-anthropic": {}}}))
        plan = {"shards": [{"shard": 43, "wave": 7, "targets": PLAN43["targets"], "restore": []}], "waves": 21}
        fx = {"plan": plan, "pack": str(art), "setup": setup, "branch": {"900": "main", "800": earlier_branch}}
        (t / "fx.json").write_text(json.dumps(fx))
        bin_ = t / "bin"
        bin_.mkdir()
        (bin_ / "gh").write_text(f"""#!{sys.executable}
import base64, json, pathlib, re, shutil, sys
fx = json.load(open({str(t / "fx.json")!r}))
a = sys.argv[1:]
if a[:2] == ["run", "download"]:
    run, name, dest = a[2], a[a.index("-n") + 1], pathlib.Path(a[a.index("-D") + 1])
    if name.startswith("plan-"):
        dest.mkdir(parents=True, exist_ok=True); (dest / "plan.json").write_text(json.dumps(fx["plan"])); sys.exit(0)
    if run == "800" and name == "shard-flt-anthropic-43":
        shutil.copytree(fx["pack"], dest); sys.exit(0)
    sys.exit(1)
url = a[1] if a[0] == "api" and a[1] != "--paginate" else a[2]
m = re.search(r"/runs/(\\d+)$", url)
if m:
    run = m.group(1)
    print(json.dumps({{"head_sha": "b" * 40, "path": ".github/workflows/bump-waves.yml", "display_title": "bump-waves flt-anthropic", "head_branch": fx["branch"][run], "event": "workflow_dispatch", "head_repo": "o/r"}}))
elif "/contents/sources.json" in url:
    print(base64.b64encode(json.dumps({{"sources": {{"flt-anthropic": {{}}}}}}).encode()).decode())
elif "/contents/" in url:
    print(base64.b64encode(json.dumps(fx["setup"]).encode()).decode())
elif url.endswith("/runs/800/artifacts?per_page=100"):
    print("shard-flt-anthropic-43\\nwave-flt-anthropic-43\\nplan-flt-anthropic")
elif "/artifacts" in url:
    print("plan-flt-anthropic")
""")
        (bin_ / "gh").chmod(0o755)
        env = {"PATH": f"{bin_}:{Path(sys.executable).parent}:/usr/bin:/bin"}
        return subprocess.run([sys.executable, str(HERE / "regate_plan.py"), "--repo", "o/r", "--key", "flt-anthropic", "--run", "900", "--fill", "800",
                               "--library-from", str(t / "emissary"), "--work", str(t / "work")], env=env, capture_output=True, text=True)

    def test_the_real_shard_in_the_run_it_resumes(self):
        r = self.run_plan()
        self.assertEqual(r.returncode, 0, r.stderr)
        out = dict(ln.split("=", 1) for ln in r.stdout.splitlines())
        self.assertEqual(json.loads(out["shards"]), [43])
        self.assertEqual(out["from"], "900,800")  # this run first: a regated pack lands here and wins

    def test_a_run_not_of_the_lane_on_main_is_refused(self):
        r = self.run_plan(earlier_branch="feature")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("may not hand its artifacts", r.stderr + r.stdout)


class OwnName(unittest.TestCase):
    """I9: the regate pack has its own name, is uploaded only when whole, and takes the shard pack's place where the packs are read"""

    def test_the_pack_names(self):
        names = ["shard-k-1", "shard-k-2", "regate-k-2", "regate-k-3", "wave-k-1", "plan-k", "regate-kk-1", "regate-k-x", "shard-k-10"]
        self.assertEqual(ff.pack_names(names, "k"), {"shard-k-1": "shard-k-1", "shard-k-2": "regate-k-2", "shard-k-3": "regate-k-3", "shard-k-10": "shard-k-10"})
        self.assertEqual(ff.pack_names(["regate-k-2", "shard-k-2"], "k"), {"shard-k-2": "regate-k-2"})  # whatever the order of the listing

    def test_the_uploads(self):
        import yaml

        steps = yaml.safe_load((WF / "bump-shard.yml").read_text())["jobs"]["shard"]["steps"]
        shard_ups = [s for s in steps if "upload-artifact" in s.get("uses", "") and str(s.get("with", {}).get("name", "")).startswith("shard-")]
        regate_ups = [s for s in steps if "upload-artifact" in s.get("uses", "") and str(s.get("with", {}).get("name", "")).startswith("regate-")]
        self.assertEqual((len(shard_ups), len(regate_ups)), (3, 3))
        for u in shard_ups:
            self.assertIn("inputs.regate != 'true'", u["if"])  # a regate never uploads shard-KEY-N
        for u in regate_ups:
            self.assertTrue(u["if"].startswith("inputs.regate == 'true' && steps.regate_merge.outcome == 'success'"), u["if"])  # only a whole pack
        self.assertEqual([("continue-on-error" in u) for u in regate_ups], [True, True, False])
        self.assertEqual(next(s for s in steps if s.get("id") == "regate_merge")["if"], "inputs.regate == 'true'")

    def test_the_bundle_takes_the_regate_packs(self):
        import yaml

        jobs = yaml.safe_load((WF / "bump-sharded.yml").read_text())["jobs"]
        for job in ("compose", "finish"):
            st = jobs[job]["steps"]
            down = next(i for i, s in enumerate(st) if s.get("with", {}).get("path") == "shards" and "pattern" in s.get("with", {}))
            prom = next(i for i, s in enumerate(st) if "--promote-from" in s.get("run", ""))
            merge = next(i for i, s in enumerate(st) if "shard_pack.py merge" in s.get("run", ""))
            self.assertLess(down, prom, job)
            self.assertLess(prom, merge, job)
            self.assertEqual(st[prom]["env"]["RUN"], "${{ inputs.recut_from || github.run_id }}")

    def test_promote_puts_a_whole_regate_pack_in_place(self):
        t = Path(tempfile.mkdtemp())
        shards = t / "shards"
        old_pack(shards)
        regated = t / "store"
        v = new_verdicts(t, KILLED, [], passes_for(KILLED[:5]))
        self.assertEqual(regate(t, old_pack(regated), v).returncode, 0)
        def runner(cmd, capture_output=True, text=True, check=False):
            if cmd[1] == "api":
                return subprocess.CompletedProcess(cmd, 0, "shard-flt-anthropic-43\nregate-flt-anthropic-43\nwave-flt-anthropic-43\n", "")
            shutil.copytree(t / "out", cmd[cmd.index("-D") + 1])
            return subprocess.CompletedProcess(cmd, 0, "", "")
        done = ff.promote("o/r", "flt-anthropic", "5", shards, t / "work", runner, lambda s: None)
        self.assertEqual(done, ["shard-flt-anthropic-43"])
        self.assertEqual(json.loads((shards / "shard-flt-anthropic-43" / "emissary" / "gate2-killed.json").read_text()), [])
        def broken(cmd, capture_output=True, text=True, check=False):  # a regate artifact without a whole pack is refused, the first pack kept
            if cmd[1] == "api":
                return subprocess.CompletedProcess(cmd, 0, "regate-flt-anthropic-43\n", "")
            Path(cmd[cmd.index("-D") + 1]).mkdir(parents=True)
            return subprocess.CompletedProcess(cmd, 0, "", "")
        with self.assertRaises(SystemExit):
            ff.promote("o/r", "flt-anthropic", "5", shards, t / "work2", broken, lambda s: None)
        self.assertTrue((shards / "shard-flt-anthropic-43" / "shard-pack" / "src").is_dir())

    def test_nine_runs_for_a_resume_at_the_deepest(self):  # cubic, #180: this run and the 8 a resume may name
        chain = ",".join(str(1000 + i) for i in range(9))
        self.assertEqual(len(ff.runs_of(chain, most=ff.MAX_RUNS + 1)), 9)
        with self.assertRaises(ValueError):
            ff.runs_of(chain)


class DefinitionsAndControls(unittest.TestCase):
    def test_the_new_jobs_checks_are_counted(self):  # cubic, #180: shard_pack.merge sums definitions.by_result and counts controls.wrongly_passed
        t = Path(tempfile.mkdtemp())
        art = old_pack(t)
        v = new_verdicts(t, KILLED, [], passes_for(KILLED[:3]))
        r = json.loads(v["results"].read_text())
        r["definitions"] = {"by_result": {"identical": 7, "drift": 1}, "drifted": {"Def.X": "a -> b"}}
        r["controls"] = {"checked": 4, "wrongly_passed": ["Ctl.y"]}
        v["results"].write_text(json.dumps(r))
        self.assertEqual(regate(t, art, v).returncode, 0)
        res = json.loads((t / "out" / "shard-pack" / "gate2-results.json").read_text())
        self.assertEqual(res["definitions"]["by_result"], {"identical": OLD_RESULTS["definitions"]["by_result"]["identical"] + 7, "drift": 1})
        self.assertEqual(res["definitions"]["drifted"]["Def.X"], "a -> b")
        self.assertEqual(res["controls"]["checked"], OLD_RESULTS["controls"]["checked"] + 4)
        self.assertIn("Ctl.y", res["controls"]["wrongly_passed"])


if __name__ == "__main__":
    unittest.main()
