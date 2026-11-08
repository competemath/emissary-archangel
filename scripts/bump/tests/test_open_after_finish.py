"""A finished bump starts the opener for its own library (the `open` job of bump-sharded.yml and bump-library.yml).

The real case: intake-open.yml's schedule says "every 10 minutes" (cron 3-59/10), but GitHub ran it at 18:12, 21:47 and 00:55 on 7-8 Nov 2026, so a finished bump waited hours
for its pull requests; padic-l-functions' re-bump (run 42441872493) was opened by hand (intake-open run 42444625597), and twelve more bumps were in flight.

Invariants, on both workflows:
  * the job runs only after the job that publishes the archive succeeded (bump-sharded: finish; bump-library: attest), only when parts are cut (the opener opens part archives
    only), and only in the factory itself, never in a rehearsal (the sandbox campaign must never open pull requests in the tree);
  * its only permission is `actions: write` (the dispatch), and it runs nothing of the run: no checkout, no artifact, no `uses:` step;
  * the real `run:` text, executed by bash with a fake `gh`, starts intake-open.yml once with target competemath/tengoku, keys = exactly this key, dry_run=false, on main;
    for every registered key of sources.json (the real registry);
  * a malformed key (a shell word, an upper-case name, empty, a path) is refused before `gh` is called;
  * the inputs it passes are inputs intake-open.yml declares (target, keys, dry_run), so a rename there cannot silently break the dispatch.
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
            env = {"PATH": f"{t / 'bin'}:{os.environ['PATH']}", "KEY": key, "GH_TOKEN": "x", "GITHUB_REPOSITORY": "competemath/emissary-archangel", "GH_CALLS": str(t / "calls")}
            r = subprocess.run(["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", str(t / "step.sh")], env=env, capture_output=True, text=True, check=False)
            calls = [(t / "calls" / c).read_text().splitlines() for c in sorted(os.listdir(t / "calls"))]
            return r.returncode, r.stdout + r.stderr, calls

    def test_runs_only_after_the_archive_is_published_with_parts_and_only_in_the_factory(self):
        for wf, after in self.CASES:
            j = self.job(wf)
            self.assertEqual(j["needs"], [after], wf)
            cond = j["if"]
            for part in (f"needs.{after}.result == 'success'", "inputs.parts != '0'", "github.repository == 'competemath/emissary-archangel'", "!cancelled()"):
                self.assertIn(part, cond, wf)

    def test_only_the_dispatch_permission_and_nothing_of_the_run(self):
        for wf, _ in self.CASES:
            j = self.job(wf)
            self.assertEqual(j["permissions"], {"actions": "write"}, wf)
            self.assertEqual(len(j["steps"]), 1, wf)
            self.assertNotIn("uses", j["steps"][0], wf)
            text = j["steps"][0]["run"]
            for word in ("checkout", "download-artifact", "git clone", "${{"):
                self.assertNotIn(word, text, f"{wf}: {word}")

    def test_every_registered_key_starts_the_opener_for_that_key_only(self):
        keys = sorted(SOURCES)
        self.assertGreater(len(keys), 100)
        for wf, _ in self.CASES:
            j = self.job(wf)
            for key in keys:
                code, out, calls = self.run_step(j, key)
                self.assertEqual(code, 0, f"{wf} {key}: {out}")
                self.assertEqual(len(calls), 1, f"{wf} {key}")
                c = calls[0]
                self.assertEqual(c[:4], ["workflow", "run", "intake-open.yml", "-R"], f"{wf} {key}")
                self.assertEqual(c[4], "competemath/emissary-archangel")
                fields = [c[i + 1] for i, a in enumerate(c) if a == "-f"]
                self.assertEqual(sorted(fields), sorted(["target=competemath/tengoku", f"keys={key}", "dry_run=false"]), f"{wf} {key}: {c}")
                self.assertEqual(c[c.index("--ref") + 1], "main")

    def test_a_malformed_key_is_refused_before_gh(self):
        for wf, _ in self.CASES:
            j = self.job(wf)
            for key in ["", "a;b", "$(id)", "Foo", "../x", "a b", "-x", "x" * 65, "a\nb", "padic-l-functions;rm -rf ~"]:
                code, out, calls = self.run_step(j, key)
                self.assertNotEqual(code, 0, f"{wf} {key!r}")
                self.assertEqual(calls, [], f"{wf} {key!r}: gh was called")
                self.assertIn("nothing was opened", out)

    def test_the_inputs_passed_are_inputs_of_the_opener(self):
        inputs = load("intake-open.yml")[True]["workflow_dispatch"]["inputs"]  # YAML reads the key `on` as True
        for name in ("target", "keys", "dry_run"):
            self.assertIn(name, inputs)


if __name__ == "__main__":
    unittest.main()
