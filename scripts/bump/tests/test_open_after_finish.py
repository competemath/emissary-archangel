"""A finished bump starts the opener (the `open` job of bump-sharded.yml and bump-library.yml).

The real case: intake-open.yml's schedule says "every 10 minutes" (cron 3-59/10), but GitHub ran it at 18:12, 21:47 and 00:55 on 7-8 Nov 2026, so a finished bump waited hours
for its pull requests; padic-l-functions, zeta-3-irrational and primecert were opened by hand (intake-open runs 42444625597, 42445304275, 42446068096), twelve more bumps were in flight.

The opener keeps one pending run (concurrency group intake-open, cancel-in-progress false), and GitHub replaces a pending run with a newer one: a dispatch for one key could be
dropped (cubic, #158). So the job starts the opener for every library with a finished bundle; whichever run survives opens them all.

Invariants, on both workflows:
  * the job runs only after the job that publishes the archive succeeded (bump-sharded: finish; bump-library: attest), only when parts were cut (`parts` neither empty nor 0:
    the opener opens part archives only), only for a run on main (the opener ignores bump runs of other branches), and only in the factory itself, never in a rehearsal (the
    sandbox campaign must never open pull requests in the tree);
  * its only permission is `actions: write`, and it runs nothing of the run and takes nothing from it: no checkout, no artifact, no `uses:` step, no `${{ }}` and no input
    variable in its shell;
  * the real `run:` text, executed by bash with a fake `gh`, starts intake-open.yml exactly once, on main, with target competemath/tengoku and dry_run=false and no `keys`
    (every library); whatever the run's key, the dispatch is the same: checked for every registered key of sources.json (the real registry) and for hostile values;
  * the inputs it passes are inputs intake-open.yml declares, and `keys` defaults to every library there, so a change in the opener cannot silently break the dispatch;
  * intake-open still has the one-pending concurrency this design answers.
"""

from __future__ import annotations

import json
import os
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

REPO = Path(__file__).resolve().parents[3]
WF = REPO / ".github" / "workflows"
SOURCES = json.loads((REPO / "sources.json").read_text(encoding="utf-8"))["sources"]

FAKE_GH = """#!/bin/bash
printf '%s\\n' "$@" > "$GH_CALLS/call-$(ls "$GH_CALLS" | wc -l | tr -d ' ')"
"""


def load(name: str) -> dict:
    return yaml.safe_load((WF / name).read_text(encoding="utf-8"))


class OpenAfterFinish(unittest.TestCase):
    CASES = [("bump-sharded.yml", "finish"), ("bump-library.yml", "attest")]

    def job(self, wf: str) -> dict:
        jobs = load(wf)["jobs"]
        self.assertIn("open", jobs, f"{wf} has no open job")
        return jobs["open"]

    def run_step(self, job: dict, key: str) -> tuple[int, str, list[list[str]]]:
        script = job["steps"][0]["run"]
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            (t / "bin").mkdir()
            (t / "calls").mkdir()
            gh = t / "bin" / "gh"
            gh.write_text(FAKE_GH)
            gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
            (t / "step.sh").write_text(script)
            env = {"PATH": f"{t / 'bin'}:{os.environ['PATH']}", "KEY": key, "PARTS": key, "GH_TOKEN": "x", "GITHUB_REPOSITORY": "competemath/emissary-archangel", "GH_CALLS": str(t / "calls")}
            r = subprocess.run(["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", str(t / "step.sh")], env=env, capture_output=True, text=True, check=False)
            calls = [(t / "calls" / c).read_text().splitlines() for c in sorted(os.listdir(t / "calls"))]
            return r.returncode, r.stdout + r.stderr, calls

    def assert_the_dispatch(self, calls: list[list[str]], what: str) -> None:
        self.assertEqual(len(calls), 1, what)
        c = calls[0]
        self.assertEqual(c[:5], ["workflow", "run", "intake-open.yml", "-R", "competemath/emissary-archangel"], what)
        self.assertEqual(c[c.index("--ref") + 1], "main", what)
        fields = sorted(c[i + 1] for i, a in enumerate(c) if a == "-f")
        self.assertEqual(fields, ["dry_run=false", "target=competemath/tengoku"], f"{what}: {c}")

    def test_runs_only_after_the_archive_is_published_with_parts_on_main_in_the_factory(self):
        for wf, after in self.CASES:
            j = self.job(wf)
            self.assertEqual(j["needs"], [after], wf)
            cond = j["if"]
            for part in (f"needs.{after}.result == 'success'", "inputs.parts != ''", "inputs.parts != '0'", "github.ref == 'refs/heads/main'",
                         "github.repository == 'competemath/emissary-archangel'", "!cancelled()"):
                self.assertIn(part, cond, wf)

    def test_only_the_dispatch_permission_and_nothing_of_the_run(self):
        for wf, _ in self.CASES:
            j = self.job(wf)
            self.assertEqual(j["permissions"], {"actions": "write"}, wf)
            self.assertEqual(len(j["steps"]), 1, wf)
            self.assertNotIn("uses", j["steps"][0], wf)
            self.assertEqual(set(j.get("env", {})), {"GH_TOKEN"}, wf)  # no input of the run reaches the job
            text = j["steps"][0]["run"]
            for word in ("checkout", "download-artifact", "git clone", "${{", "$KEY", "$PARTS", "inputs."):
                self.assertNotIn(word, text, f"{wf}: {word}")

    def test_one_dispatch_for_every_library_whatever_the_key(self):
        keys = sorted(SOURCES)
        self.assertGreater(len(keys), 100)
        hostile = ["", "a;b", "$(id)", "Foo", "../x", "a b", "-x", "x" * 65, "a\nb", "padic-l-functions;rm -rf ~"]
        for wf, _ in self.CASES:
            j = self.job(wf)
            for key in keys + hostile:
                code, out, calls = self.run_step(j, key)
                self.assertEqual(code, 0, f"{wf} {key!r}: {out}")
                self.assert_the_dispatch(calls, f"{wf} {key!r}")

    def test_the_opener_takes_these_inputs_and_keeps_one_pending_run(self):
        d = load("intake-open.yml")
        inputs = d[True]["workflow_dispatch"]["inputs"]  # YAML reads the key `on` as True
        for name in ("target", "dry_run", "keys"):
            self.assertIn(name, inputs)
        self.assertEqual(inputs["keys"].get("default", ""), "")  # no keys: every library with a finished bundle
        self.assertEqual(d["concurrency"], {"group": "intake-open", "cancel-in-progress": False})


if __name__ == "__main__":
    unittest.main()
