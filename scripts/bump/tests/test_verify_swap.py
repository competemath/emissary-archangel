"""verify builds with the swap its shards were built with (bump-sharded.yml compose -> verify; plan_inputs.py swap).

The real case (fixtures/verify_swap_2026-11-12.json): prime-gaps-186, run 42549840777. Its shard added 48 GB of swap (heavy: swap_gb=48) and built the library's one new module
in 64 minutes. verify freed the disk, turned every swap off, seeded the tree (89 GB free after it) and built the same module with none: the runner was lost 16 minutes into the build,
on 9 Nov and again on 12 Nov, with no log (out/disk.log went with the runner). flt-anthropic's lane (bump-waves run 43146942669) records the same swap_gb=48, and its bundle recuts it
through the same verify job, so the final theorem's modules would have died the same way.

Invariants:
  1. plan_inputs.py swap reads the swap a plan's shards were built with: the record's swap_gb, or "0" when the record leaves it out (a run on the defaults); anything else is an error,
     and the CLI's stdout (which is $GITHUB_OUTPUT) holds exactly one line `swap_gb=N`, or nothing on an error. No record at all (a recut older than the plan's 14 days) is "0", said.
  2. The round trip: for every setting the plan can record, swap_of(record(env)) is the SWAP_GB the shards were given.
  3. The workflow: compose reads the plan of the run whose shards it merges (recut_from || this run), exposes swap_gb; verify takes it in its env, adds the swap with add-swap.sh
     after the tree is seeded (the size comes from what is really free) and before the first `lake build`, and not when the shards had none. The disk and memory sampler writes to the
     job's log too. Each broken version (mutant) is caught.
  4. End to end on the real numbers: the real plans give 48; the step runs; the real add-swap.sh on the real free space after seeding (89 GB) adds 48 GB and keeps 40.
"""

import copy
import json
import os
import random
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import plan_inputs as pi  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]
WF = ROOT / ".github" / "workflows" / "bump-sharded.yml"
FX = json.loads((Path(__file__).parent / "fixtures" / "verify_swap_2026-11-12.json").read_text())
SCRIPT = HERE / "plan_inputs.py"


def jobs(text: str) -> dict:
    return yaml.safe_load(text)["jobs"]


def problems(text: str) -> list[str]:
    """what is wrong with the verify job's swap in bump-sharded.yml (empty: nothing)"""
    out = []
    j = jobs(text)
    comp, ver = j["compose"], j["verify"]
    if comp.get("outputs", {}).get("swap_gb") != "${{ steps.built.outputs.swap_gb }}":
        out.append("compose does not expose the swap the shards were built with")
    steps = comp["steps"]
    built = next((i for i, s in enumerate(steps) if s.get("id") == "built"), None)
    dl = next((i for i, s in enumerate(steps) if (s.get("with") or {}).get("path") == "plan-built"), None)
    if built is None or dl is None or dl > built:
        out.append("compose does not download the plan before it reads the swap")
    else:
        w = steps[dl]["with"]
        if w.get("name") != "plan-${{ inputs.key }}" or w.get("run-id") != "${{ inputs.recut_from || github.run_id }}":
            out.append("compose reads the plan of another run than the one whose shards it merges")
        if "continue-on-error" in steps[dl]:
            out.append("a failed download of the plan reads as no swap")
        rec = next((i for i, s in enumerate(steps) if s.get("id") == "planrec"), None)
        if rec is None or rec > dl or steps[dl].get("if") != "${{ steps.planrec.outputs.kept == 'true' }}":
            out.append("the plan is not looked up before it is downloaded")
        else:
            r = steps[rec]["run"]
            if "select(.expired | not)" not in r or '[ -z "$RECUT" ]' not in r or "|| echo" in r or "|| true" in r:
                out.append("the lookup does not tell an expired plan from a failure")
        if steps[built].get("run") != 'python3 emissary/scripts/bump/plan_inputs.py swap plan-built/inputs.json >> "$GITHUB_OUTPUT"':
            out.append("compose does not read swap_gb with plan_inputs.py swap")
    if "compose" not in ([ver["needs"]] if isinstance(ver["needs"], str) else ver["needs"]):
        out.append("verify does not need compose")
    if ver.get("env", {}).get("SWAP_GB") != "${{ needs.compose.outputs.swap_gb }}":
        out.append("verify's SWAP_GB is not compose's")
    vs = ver["steps"]
    sw = [i for i, s in enumerate(vs) if 'add-swap.sh "$SWAP_GB" 40' in (s.get("run") or "")]
    seed = [i for i, s in enumerate(vs) if "scripts/cache.sh get" in (s.get("run") or "")]
    builds = [i for i, s in enumerate(vs) if any("lake build" in l and not l.lstrip().startswith("#") for l in (s.get("run") or "").splitlines())]  # comments say `lake build` too
    freeing = [i for i, s in enumerate(vs) if "swapoff -a" in (s.get("run") or "")]
    if len(sw) != 1:
        out.append(f"verify adds the swap {len(sw)} times")
    else:
        i = sw[0]
        if vs[i].get("if") != "${{ needs.compose.outputs.swap_gb != '0' && needs.compose.outputs.swap_gb != '' }}":
            out.append("the swap step does not run exactly when the shards had swap")
        if not seed or i < max(seed):
            out.append("the swap is sized before the tree's cache is unpacked")
        if not builds or i > min(builds):
            out.append("a lake build runs before the swap is there")
        if not freeing or i < max(freeing):
            out.append("the disk freeing turns the swap off again")
        if "swapon --show --noheadings" not in vs[i]["run"] or "exit 1" not in vs[i]["run"]:
            out.append("a build runs without swap when none could be added")
    sampler = [s for s in vs if "mem_avail_kb" in (s.get("run") or "")]
    if len(sampler) != 1 or "| tee -a ../out/disk.log" not in sampler[0]["run"] or "swap_used_kb" not in sampler[0]["run"]:
        out.append("the sampler does not reach the job's log with the swap")
    return out


def cli(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(SCRIPT), *args], capture_output=True, text=True)


class SwapRecord(unittest.TestCase):
    def test_the_real_plans_say_48(self):
        self.assertEqual(pi.swap_of(FX["prime_gaps_inputs"]), "48")
        self.assertEqual(pi.swap_of(FX["flt_lane_inputs"]), "48")
        # and what the shard really added, from its log
        self.assertIn("heavy: swap_gb=48;build_timeout_min=170", FX["shard_log"][0])
        self.assertTrue(any("add-swap.sh: 48 GB of swap" in l for l in FX["shard_log"]))
        self.assertTrue(any("shutdown signal" in l for l in FX["verify_log"]))

    def test_round_trip_over_every_setting(self):
        rng = random.Random(20261112)
        n = 0
        swaps = ["0", "1", "8", "16", "47", "48", "64", "100", "999"] + [str(rng.randint(1, 999)) for _ in range(300)]
        for sw in swaps:
            for bt in ("90", "150", "170", "300"):
                for tg in ("", "registry/x"):
                    env = {"MATHLIB": "v4.34.0-rc2", "TOOLCHAIN": "leanprover/lean4:v4.34.0-rc2", "IMPORTS": rng.choice(["faithful", "full"]), "TENGOKU_REF": tg,
                           "SWAP_GB": sw, "BUILD_TIMEOUT_MIN": bt}
                    rec = json.loads(pi.dump(pi.record(env)))
                    self.assertEqual(pi.swap_of(rec), sw)
                    self.assertEqual("swap_gb" in rec, sw != "0")  # the default is left out of the record, and still reads as 0
                    n += 1
        self.assertGreaterEqual(n, 2400)

    def test_malformed_is_an_error(self):
        for bad in ("-1", "48.5", "048", "1000", "", " 48", "48;rm", 48, None, ["48"]):
            with self.assertRaises(ValueError, msg=repr(bad)):
                pi.swap_of({"swap_gb": bad})
        for rec in ([], ["swap_gb"], "48", 48, None, True):  # valid JSON that is not a record (cubic, #182): an error, never a traceback
            with self.assertRaises(ValueError, msg=repr(rec)):
                pi.swap_of(rec)

    def test_cli(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "inputs.json"
            p.write_text(json.dumps(FX["prime_gaps_inputs"]))
            r = cli("swap", str(p))
            self.assertEqual((r.returncode, r.stdout), (0, "swap_gb=48\n"))
            p.write_text(pi.dump(pi.record({"MATHLIB": "m", "TOOLCHAIN": "t", "IMPORTS": "faithful", "TENGOKU_REF": ""})))
            self.assertEqual(cli("swap", str(p)).stdout, "swap_gb=0\n")
            r = cli("swap", str(Path(d) / "missing.json"))
            self.assertEqual((r.returncode, r.stdout), (0, "swap_gb=0\n"))
            self.assertIn("::warning::", r.stderr)
            for bad in ('{"swap_gb": "48;rm -rf /"}', "{not json", "[]", '"48"', "null"):
                p.write_text(bad)
                r = cli("swap", str(p))
                self.assertEqual((r.returncode, r.stdout), (1, ""), bad)  # nothing reaches $GITHUB_OUTPUT
                self.assertIn("::error::", r.stderr)


class Workflow(unittest.TestCase):
    TEXT = WF.read_text()

    def test_the_real_workflow(self):
        self.assertEqual(problems(self.TEXT), [])

    def test_mutants_are_caught(self):
        t = self.TEXT
        a = t.index("      - name: Swap, as the shards were built with")
        step = t[a:t.index("      - name: ", a + 10)]  # the whole step, as the workflow has it
        self.assertIn(step, t)
        build_anchor = "      - name: Build them (the queue's own command)\n"
        seed_anchor = "      - name: The tree, seeded from the newest published cache (verified), as the merge queue seeds it\n"
        mutants = {
            "no swap step (main before the fix)": t.replace(step, ""),
            "swap after the first build": t.replace(step, "").replace("      - name: Give the declarations that ran out of heartbeats room", step + "      - name: Give the declarations that ran out of heartbeats room"),
            "swap before the seeding": t.replace(step, "").replace(seed_anchor, step + seed_anchor),
            "swap always": t.replace(step, step.replace("${{ needs.compose.outputs.swap_gb != '0' && needs.compose.outputs.swap_gb != '' }}", "${{ always() }}")),
            "swap when none was asked for": t.replace(step, step.replace(" && needs.compose.outputs.swap_gb != ''", "")),
            "the plan of this run on a recut": t.replace('path: plan-built, run-id: "${{ inputs.recut_from || github.run_id }}"', 'path: plan-built, run-id: "${{ github.run_id }}"'),
            "a failed download passes": t.replace("        if: ${{ steps.planrec.outputs.kept == 'true' }}\n", "        if: ${{ steps.planrec.outputs.kept == 'true' }}\n        continue-on-error: true\n"),
            "no lookup before the download": t.replace("        if: ${{ steps.planrec.outputs.kept == 'true' }}\n", ""),
            "expired plans counted as kept": t.replace("[.artifacts[] | select(.expired | not)] | length", "[.artifacts[]] | length"),
            "a failing query reads as no record": t.replace("--jq '[.artifacts[] | select(.expired | not)] | length')", "--jq '[.artifacts[] | select(.expired | not)] | length' || echo 0)"),
            "no check that the swap is there": t.replace('          [ -n "$(swapon --show --noheadings)" ] ||', '          true ||'),
            "compose output dropped": t.replace("      swap_gb: ${{ steps.built.outputs.swap_gb }}\n", ""),
            "verify env dropped": t.replace(', SWAP_GB: "${{ needs.compose.outputs.swap_gb }}" }', " }"),
            "sampler only in out/": t.replace("| tee -a ../out/disk.log; done ) &", ">> ../out/disk.log; done ) &"),
        }
        for name, m in mutants.items():
            self.assertNotEqual(m, t, name)
            self.assertNotEqual(problems(m), [], name)
        self.assertEqual(len(mutants), 14)

    def test_the_condition_on_real_and_default_plans(self):
        cond = jobs(self.TEXT)["verify"]["steps"]
        cond = next(s["if"] for s in cond if 'add-swap.sh "$SWAP_GB"' in (s.get("run") or ""))
        expr = re.fullmatch(r"\$\{\{ needs\.compose\.outputs\.swap_gb != '0' && needs\.compose\.outputs\.swap_gb != '' \}\}", cond)
        self.assertIsNotNone(expr)
        runs = lambda v: v != "0" and v != ""  # the expression above
        self.assertTrue(runs(pi.swap_of(FX["prime_gaps_inputs"])))
        self.assertTrue(runs(pi.swap_of(FX["flt_lane_inputs"])))
        self.assertFalse(runs(pi.swap_of({"mathlib": "m"})))


def step_run(job: str, pred) -> str:
    return next(s["run"] for s in jobs(WF.read_text())[job]["steps"] if pred(s))


def fakes(d: Path, scripts: dict) -> dict:
    for name, body in scripts.items():
        (d / name).write_text("#!/bin/sh\n" + body)
        os.chmod(d / name, 0o755)
    return {**os.environ, "PATH": f"{d}:{os.environ['PATH']}"}


class PlanLookup(unittest.TestCase):
    """the compose step that decides whether the plan of the shards' run is still kept, run as bash with a fake gh"""

    def run_step(self, recut: str, gh_body: str):
        with tempfile.TemporaryDirectory() as d:
            env = fakes(Path(d), {"gh": gh_body})
            out = Path(d) / "out"
            out.write_text("")
            env.update(GITHUB_OUTPUT=str(out), GITHUB_REPOSITORY="competemath/emissary-archangel", KEY="prime-gaps-186", RECUT=recut,
                       RUN=recut or "43237206258", GH_TOKEN="x")
            r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step_run("compose", lambda s: s.get("id") == "planrec")], capture_output=True, text=True, env=env)
            return r.returncode, out.read_text(), r.stdout + r.stderr

    def test_cases(self):
        kept = "echo 1\n"
        cases = {
            ("", "echo called >&2; exit 9\n"): (0, "kept=true\n"),  # this run's own plan: gh is never asked
            ("42549840777", kept): (0, "kept=true\n"),
            ("42549840777", "echo 0\n"): (0, "kept=false\n"),  # expired or never uploaded
            ("42549840777", "echo 'HTTP 502' >&2; exit 1\n"): (1, ""),  # a failing query stops the job, never 'no record'
            ("42549840777", "echo oops\n"): (1, ""),
            ("42549840777 ; rm", kept): (1, ""),
            ("0", kept): (1, ""),
        }
        for (recut, gh), (code, out) in cases.items():
            got = self.run_step(recut, gh)
            self.assertEqual(got[:2], (code, out), (recut, gh, got[2]))
            if recut == "":
                self.assertNotIn("called", got[2])


class SwapStep(unittest.TestCase):
    """verify's swap step, run as bash with the real add-swap.sh and fake df, sudo, free, swapon"""

    def run_step(self, avail_gb: int):
        with tempfile.TemporaryDirectory() as d:
            b = Path(d)
            (b / "emissary").symlink_to(ROOT)
            env = fakes(b, {"df": f"echo Avail\necho {avail_gb * 1073741824}\n", "sudo": f'echo "$*" >> {d}/sudo.log\n', "free": "exit 0\n",
                            "swapon": f'grep -q "^swapon /swapfile" {d}/sudo.log 2>/dev/null && echo "/swapfile file 48G 0B -2"\nexit 0\n'})
            env["SWAP_GB"] = pi.swap_of(FX["prime_gaps_inputs"])
            r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step_run("verify", lambda s: 'add-swap.sh "$SWAP_GB" 40' in (s.get("run") or ""))],
                               capture_output=True, text=True, env=env, cwd=d)
            return r.returncode, r.stdout + r.stderr

    def test_real_free_space_adds_it(self):
        code, out = self.run_step(89)  # after seeding, prime-gaps-186's verify of 12 Nov
        self.assertEqual(code, 0, out)
        self.assertIn("48 GB of swap", out)

    def test_no_room_stops_the_job_and_says_why(self):
        for avail in (0, 40, 45, 47):  # under 8 GB to spare after the 40 kept
            code, out = self.run_step(avail)
            self.assertEqual(code, 1, (avail, out))
            self.assertIn("under 8 GB to spare", out)
            self.assertIn("::error::the shards were built with 48 GB of swap and none could be added here", out)


class EndToEndOnTheRealNumbers(unittest.TestCase):
    def test_add_swap_on_the_real_free_space_after_seeding(self):
        seeded = next(l for l in FX["verify_log"] if "/dev/root" in l and "56G" in l)
        avail_gb = int(re.search(r"\s(\d+)G\s+\d+%", seeded).group(1))
        self.assertEqual(avail_gb, 89)
        with tempfile.TemporaryDirectory() as d:
            b = Path(d)
            (b / "df").write_text(f"#!/bin/sh\necho Avail\necho {avail_gb * 1073741824}\n")
            (b / "sudo").write_text(f"#!/bin/sh\necho \"$*\" >> {d}/sudo.log\n")
            (b / "free").write_text("#!/bin/sh\nexit 0\n")
            for f in ("df", "sudo", "free"):
                os.chmod(b / f, 0o755)
            swap = pi.swap_of(FX["prime_gaps_inputs"])
            r = subprocess.run(["sh", str(ROOT / "scripts" / "add-swap.sh"), swap, "40"], capture_output=True, text=True, env={**os.environ, "PATH": f"{d}:{os.environ['PATH']}"})
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn("add-swap.sh: 48 GB of swap (89 GB were free, 40 kept, at most 48)", r.stdout)
            self.assertIn("fallocate -l 48G /swapfile", (b / "sudo.log").read_text())


if __name__ == "__main__":
    unittest.main()
