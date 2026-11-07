"""lake_fetch.py: `lake update` and `lake exe cache get` under a time limit, tried again when they fail or hang.

The real case: evm-asm's bump (2026-11-07, run 42336062605). Shard 30 failed in this step with Lake's own line "error: mathlib: failed to fetch cache"; shard 28 hung in it for 5 h 43 min until
the job's limit cancelled it; the compose that needed both shards died. Here a stand-in `lake` plays each of those: the real error line, a hang (with a child process, as lake has),
and the success after them. Invariants: both commands succeed -> exit 0; a failure or a hang is tried again, at most --tries times, and a hang is killed WITH its children; a command
that never succeeds -> exit 1 with an error line naming it, and `cache get` is never run after `update` failed for good; the bump workflows call the helper and nothing else fetches.
"""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = Path(__file__).resolve().parents[3]
SCRIPT = HERE / "lake_fetch.py"

FAKE_LAKE = r'''#!/usr/bin/env python3
import os, subprocess, sys, time
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
cmd = " ".join(sys.argv[1:])
with open(state / "calls", "a") as f:
    f.write(cmd + "\n")
n = sum(1 for l in open(state / "calls") if l.strip() == cmd)
plan = os.environ.get("FAKE_" + ("UPDATE" if cmd == "update" else "CACHE"), "ok").split(",")
step = plan[min(n, len(plan)) - 1]
if step == "fail":
    print("error: mathlib: failed to fetch cache")
    sys.exit(1)
if step == "hang":
    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(600)"])
    (state / "child").write_text(str(child.pid))
    time.sleep(600)
print("done " + cmd)
'''


class LakeFetch(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        (self.tmp / "bin").mkdir()
        (self.tmp / "state").mkdir()
        (self.tmp / "lib").mkdir()
        lake = self.tmp / "bin" / "lake"
        lake.write_text(FAKE_LAKE)
        lake.chmod(lake.stat().st_mode | stat.S_IEXEC)

    def fetch(self, update="ok", cache="ok", tries=4, minutes=0.03, budget=5.0):
        env = {**os.environ, "PATH": f"{self.tmp / 'bin'}:{os.environ['PATH']}", "FAKE_STATE": str(self.tmp / "state"), "FAKE_UPDATE": update, "FAKE_CACHE": cache}
        p = subprocess.run([sys.executable, str(SCRIPT), str(self.tmp / "lib"), "--tries", str(tries), "--minutes", str(minutes), "--budget-minutes", str(budget), "--pause", "0"], env=env, capture_output=True, text=True, timeout=120)
        calls = (self.tmp / "state" / "calls").read_text().splitlines() if (self.tmp / "state" / "calls").exists() else []
        return p, calls

    def test_both_succeed_at_once(self):
        p, calls = self.fetch()
        self.assertEqual(p.returncode, 0, p.stdout)
        self.assertEqual(calls, ["update", "exe cache get"])

    def test_a_cache_fetch_that_fails_twice_is_tried_again(self):
        p, calls = self.fetch(cache="fail,fail,ok")
        self.assertEqual(p.returncode, 0, p.stdout)
        self.assertEqual(calls, ["update", "exe cache get", "exe cache get", "exe cache get"])
        self.assertEqual(p.stdout.count("::warning::lake exe cache get exited 1"), 2)
        self.assertIn("failed to fetch cache", p.stdout)  # the reason is in the log

    def test_a_hang_is_killed_with_its_children_and_tried_again(self):
        t0 = time.time()
        p, calls = self.fetch(cache="hang,ok", minutes=0.05)
        self.assertEqual(p.returncode, 0, p.stdout)
        self.assertLess(time.time() - t0, 60)  # not the 600 s the hang would take
        self.assertEqual(calls, ["update", "exe cache get", "exe cache get"])
        self.assertIn("ran out of time", p.stdout)
        child = int((self.tmp / "state" / "child").read_text())
        for _ in range(50):
            try:
                os.kill(child, 0)
            except ProcessLookupError:
                break
            time.sleep(0.1)
        else:
            os.kill(child, 9)
            self.fail("the hung command's child was left running")

    def test_a_command_that_never_succeeds_stops_the_step(self):
        p, calls = self.fetch(cache="fail", tries=3)
        self.assertEqual(p.returncode, 1)
        self.assertIn("::error::lake exe cache get did not succeed in 3 tries", p.stdout)
        self.assertEqual(calls.count("exe cache get"), 3)

    def test_cache_get_is_not_run_after_update_failed_for_good(self):
        p, calls = self.fetch(update="fail", tries=2)
        self.assertEqual(p.returncode, 1)
        self.assertEqual(calls, ["update", "update"])
        self.assertIn("::error::lake update did not succeed in 2 tries", p.stdout)

    def test_the_whole_step_fits_its_budget(self):
        # every try hangs: without the budget, 4 tries of 0.05 min (12 s); with a budget of 0.1 min (6 s) the step ends near 6 s, saying the budget is spent
        t0 = time.time()
        p, calls = self.fetch(cache="hang", tries=4, minutes=0.05, budget=0.1)
        took = time.time() - t0
        self.assertEqual(p.returncode, 1)
        self.assertLess(took, 10, took)
        self.assertIn("budget of this step is spent", p.stdout)
        child = int((self.tmp / "state" / "child").read_text())
        try:
            os.kill(child, 0)
            os.kill(child, 9)
            self.fail("a hung try's child was left running at the end of the budget")
        except ProcessLookupError:
            pass

    def test_a_verbose_command_keeps_only_its_last_lines(self):
        lake = self.tmp / "bin" / "lake"
        lake.write_text("#!/usr/bin/env python3\nimport sys\nfor i in range(200000): print('line', i)\nprint('the end')\n")
        p, _ = self.fetch()
        self.assertEqual(p.returncode, 0)
        self.assertIn("the end", p.stdout)
        self.assertNotIn("line 100\n", p.stdout)
        self.assertLess(len(p.stdout), 2000)

    def test_bad_arguments_are_refused(self):
        for args in (["--tries", "0"], ["--minutes", "0"], ["--pause", "-1"], ["--minutes", "inf"], ["--minutes", "nan"], ["--pause", "inf"], ["--pause", "nan"], ["--budget-minutes", "inf"], ["--budget-minutes", "0"]):
            # with the stand-in lake (one that fails at once), so that a value let through can never start the real one
            env = {**os.environ, "PATH": f"{self.tmp / 'bin'}:{os.environ['PATH']}", "FAKE_STATE": str(self.tmp / "state"), "FAKE_UPDATE": "fail", "FAKE_CACHE": "fail"}
            p = subprocess.run([sys.executable, str(SCRIPT), str(self.tmp / "lib"), "--tries", "1", *args], env=env, capture_output=True, text=True, timeout=60)
            self.assertNotEqual(p.returncode, 0, args)
            self.assertIn("all finite numbers", p.stderr, args)  # refused for the value, not failed for the fetch


class Workflows(unittest.TestCase):
    """The bump workflows fetch through the helper and nothing else: every `run` of their steps, comments left out, holds the helper call and no direct Lake fetch."""

    @staticmethod
    def runs(wf: str) -> list[str]:
        import yaml

        doc = yaml.safe_load((ROOT / ".github" / "workflows" / wf).read_text())
        out = []
        for job in doc["jobs"].values():
            for step in job.get("steps", []):
                if "run" in step:
                    out.append("\n".join(ln.split(" #")[0] for ln in step["run"].splitlines() if not ln.strip().startswith("#")))
        return out

    def test_the_bump_workflows_fetch_through_the_helper_only(self):
        import re

        for wf in ("bump-shard.yml", "bump-library.yml"):
            code = "\n".join(self.runs(wf))
            self.assertIn("python3 scripts/bump/lake_fetch.py lib", code, wf)
            self.assertIsNone(re.search(r"\blake\s+update\b", code), wf)
            self.assertIsNone(re.search(r"\blake\s+exe\s+cache\s+get\b", code), wf)

    def test_a_direct_fetch_would_be_caught(self):
        import re

        code = "\n".join(self.runs("bump-shard.yml")).replace("python3 scripts/bump/lake_fetch.py lib", "(cd lib && lake update && lake exe cache get)")
        self.assertIsNotNone(re.search(r"\blake\s+update\b", code))



class PinnedCommit(unittest.TestCase):
    """padic-l-functions (bump run 42408598866, 7 Nov): its manifest pins LeanModularForms at 512911ce, a commit no branch holds; Lake's clone lacks it and `lake update` failed four
    times with "fatal: unable to read tree (512911ce…)". The real git case: an upstream whose pinned commit is on no branch (it serves a commit named by hash, as GitHub does), a clone
    made over the transport (which is shown to lack it), and a stand-in `lake` that prints Lake's real lines until the clone has the commit."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        g = lambda *a, cwd: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "init.defaultBranch=main", *a], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()
        up = self.tmp / "up"
        up.mkdir()
        g("init", "-q", cwd=up)
        (up / "A.lean").write_text("def a := 1\n")
        g("add", "-A", cwd=up)
        g("commit", "-qm", "main", cwd=up)
        g("checkout", "-qb", "work", cwd=up)
        (up / "B.lean").write_text("def b := 2\n")
        g("add", "-A", cwd=up)
        g("commit", "-qm", "pinned", cwd=up)
        self.rev = g("rev-parse", "HEAD", cwd=up)
        g("checkout", "-q", "main", cwd=up)
        g("branch", "-qD", "work", cwd=up)
        g("config", "uploadpack.allowAnySHA1InWant", "true", cwd=up)
        self.lib = self.tmp / "lib"
        clone = self.lib / ".lake" / "packages" / "LeanModularForms"
        clone.parent.mkdir(parents=True)
        g("clone", "-q", "--no-local", str(up), str(clone), cwd=self.tmp)
        self.clone = clone
        (self.tmp / "bin").mkdir()
        lake = self.tmp / "bin" / "lake"
        lake.write_text(f"""#!/bin/sh
echo "$@" >> {self.tmp}/calls
if [ "$1" = update ] && ! git -C {clone} cat-file -e {self.rev}^{{commit}} 2>/dev/null; then
  echo "info: LeanModularForms: checking out revision '{self.rev}'"
  echo "info: stderr:"
  echo "fatal: unable to read tree ({self.rev})"
  echo "error: external command 'git' exited with code 128"
  exit 1
fi
echo ok
""")
        lake.chmod(0o755)

    def fetch(self, tries="1"):
        env = {**os.environ, "PATH": f"{self.tmp / 'bin'}:{os.environ['PATH']}"}
        return subprocess.run([sys.executable, str(SCRIPT), str(self.lib), "--tries", tries, "--minutes", "1", "--pause", "0"], env=env, capture_output=True, text=True, timeout=120)

    def test_the_fixture_lacks_the_commit(self):
        r = subprocess.run(["git", "-C", str(self.clone), "cat-file", "-e", f"{self.rev}^{{commit}}"], capture_output=True)
        self.assertNotEqual(r.returncode, 0)  # the clone was made over the transport: the commit on no branch is not in it

    def test_the_commit_is_fetched_by_hash_and_the_try_does_not_count(self):
        p = self.fetch("1")  # one try only: the repair must not use it up
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("fetched it by its hash", p.stdout)
        calls = (self.tmp / "calls").read_text().split("\n")
        self.assertEqual([c for c in calls if c], ["update", "update", "exe cache get"])

    def test_a_commit_the_remote_does_not_have_is_an_ordinary_failure(self):
        lake = self.tmp / "bin" / "lake"
        lake.write_text(lake.read_text().replace(self.rev, "0" * 40))  # Lake asks for a commit nobody has
        p = self.fetch("2")
        self.assertEqual(p.returncode, 1)
        self.assertIn("did not succeed in 2 tries", p.stdout)
        self.assertNotIn("fetched it by its hash", p.stdout)

    def test_the_repair_leaves_every_try_for_other_failures(self):
        # after the repair, `lake update` fails once more for another reason (the network), then succeeds: with 2 tries that is still a success, because the repair was free
        lake = self.tmp / "bin" / "lake"
        text = lake.read_text().replace("echo ok\n", f"""if [ "$1" = update ] && [ ! -e {self.tmp}/flaked ]; then : > {self.tmp}/flaked; echo "error: network"; exit 1; fi
echo ok
""")
        lake.write_text(text)
        p = self.fetch("2")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        calls = [c for c in (self.tmp / "calls").read_text().split("\n") if c]
        self.assertEqual(calls, ["update", "update", "update", "exe cache get"])  # repaired, failed once, succeeded


class RepairLimits(unittest.TestCase):
    """cubic on emissary#156: a repair's fetch must stay inside the step's budget (a slow origin neither outruns it nor crashes the step), the free repairs are five for the
    whole step (both commands together), and the tests of this file run when it is executed directly."""

    def test_the_free_repairs_are_five_for_the_whole_step(self):
        import importlib.util

        spec = importlib.util.spec_from_file_location("lake_fetch_mod", SCRIPT)
        lf = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(lf)
        calls = {"update": 0, "cache": 0, "repairs": 0}

        def run(cmd, cwd, seconds):
            key = "update" if cmd[1] == "update" else "cache"
            calls[key] += 1
            if key == "update" and calls["update"] > 3:
                return 0, "ok"
            return 1, "fatal: unable to read tree (" + "a" * 40 + ")"

        def repair(directory, output, deadline=None):
            calls["repairs"] += 1
            return ["Pkg"]

        lf.run, lf.repair_pins, lf.time.sleep = run, repair, (lambda s: None)
        ok = lf.fetch("lib", tries=1, minutes=1, pause=0, budget_minutes=5)
        self.assertFalse(ok)
        self.assertEqual(calls["repairs"], 5)  # 3 during update, 2 left for cache get (the old counter gave cache get 5 more)
        self.assertEqual(calls["cache"], 3)  # 2 repaired tries and the one counted try

    def test_a_slow_fetch_stays_inside_the_budget(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp, True)
        clone = tmp / "lib" / ".lake" / "packages" / "Slow"
        clone.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(clone)], check=True)
        (tmp / "bin").mkdir()
        real_git = shutil.which("git")
        # git that hangs on `fetch` (a slow origin) and is itself otherwise
        (tmp / "bin" / "git").write_text(f'#!/bin/sh\ncase " $* " in *" fetch "*) exec sleep 60;; esac\nexec {real_git} "$@"\n')
        (tmp / "bin" / "lake").write_text("#!/bin/sh\necho 'fatal: unable to read tree (" + "b" * 40 + ")'\nexit 1\n")
        for f in ("git", "lake"):
            (tmp / "bin" / f).chmod(0o755)
        env = {**os.environ, "PATH": f"{tmp / 'bin'}:{os.environ['PATH']}"}
        t0 = time.time()
        p = subprocess.run([sys.executable, str(SCRIPT), str(tmp / "lib"), "--tries", "2", "--minutes", "1", "--budget-minutes", "0.1", "--pause", "0"], env=env, capture_output=True, text=True, timeout=120)
        took = time.time() - t0
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertNotIn("Traceback", p.stderr)  # a fetch that runs out of time is a failed repair, not a crash
        self.assertLess(took, 20, took)  # the 6-second budget, not the 60-second fetch

    def test_this_file_runs_every_test_when_executed_directly(self):
        import ast

        tree = ast.parse(Path(__file__).read_text())
        last = tree.body[-1]
        self.assertIsInstance(last, ast.If)  # the `__main__` guard is the last statement: no test class is defined after unittest.main()
        self.assertIn("__main__", ast.unparse(last.test))


if __name__ == "__main__":
    unittest.main()
