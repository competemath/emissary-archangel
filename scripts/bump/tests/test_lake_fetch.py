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

    def fetch(self, update="ok", cache="ok", tries=4, minutes=0.03):
        env = {**os.environ, "PATH": f"{self.tmp / 'bin'}:{os.environ['PATH']}", "FAKE_STATE": str(self.tmp / "state"), "FAKE_UPDATE": update, "FAKE_CACHE": cache}
        p = subprocess.run([sys.executable, str(SCRIPT), str(self.tmp / "lib"), "--tries", str(tries), "--minutes", str(minutes), "--pause", "0"], env=env, capture_output=True, text=True, timeout=120)
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
        self.assertIn("ran out of 0.05 min", p.stdout)
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

    def test_bad_arguments_are_refused(self):
        for args in (["--tries", "0"], ["--minutes", "0"], ["--pause", "-1"]):
            p = subprocess.run([sys.executable, str(SCRIPT), str(self.tmp / "lib"), *args], capture_output=True, text=True)
            self.assertNotEqual(p.returncode, 0, args)


class Workflows(unittest.TestCase):
    def test_the_bump_workflows_fetch_through_the_helper_only(self):
        for wf in ("bump-shard.yml", "bump-library.yml"):
            text = (ROOT / ".github" / "workflows" / wf).read_text()
            self.assertIn("python3 scripts/bump/lake_fetch.py lib", text, wf)
            self.assertNotIn("lake exe cache get 2>&1", text, wf)  # the old unguarded fetch


if __name__ == "__main__":
    unittest.main()
