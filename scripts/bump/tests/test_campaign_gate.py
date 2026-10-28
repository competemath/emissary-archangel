"""campaign-gate.yml: a change to the pipeline is trusted only with an attested campaign run in the sandbox.

What must hold of the workflow itself (it is the enforcement, and a pull request must not be able to weaken it):
  * it runs from the BASE branch (pull_request_target), checks out nothing of the pull request, and holds no more than `contents: read`;
  * the attestation is verified against the sandbox's own workflow on its main branch;
  * the verdict step is the decision, and it is tested HERE by running the very text of the workflow's python on fixtures: wrong commit, wrong repository, a stale expectation, a failed campaign.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[3]
WF = ROOT / ".github" / "workflows" / "campaign-gate.yml"
TEXT = WF.read_text()
DOC = yaml.safe_load(TEXT)


def verdict_script() -> str:
    m = re.search(r"python3 - <<'PY'\n(.*?)\n\s*PY\n", TEXT, re.S)
    assert m
    return "\n".join(line[10:] if line.startswith("          ") else line for line in m.group(1).splitlines())


def run_verdict(result: dict, expected_sha: str, sha: str):
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        (t / "result").mkdir()
        (t / "result" / "result.json").write_text(json.dumps(result))
        (t / "expected.sha256").write_text(expected_sha + "\n")
        r = subprocess.run([sys.executable, "-c", verdict_script()], cwd=t, env={**os.environ, "SHA": sha}, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr


GOOD = {"emissary_repo": "competemath/emissary-archangel", "emissary_sha": "a" * 40, "expected_sha256": "e" * 64, "ok": True, "verdict": {"ok": True, "enforced": ["baseline"], "skipped": [], "failures": []}}


class Workflow(unittest.TestCase):
    def test_it_runs_from_the_base_branch_and_checks_nothing_of_the_pull_request_out(self):
        self.assertIn("pull_request_target", DOC[True])
        self.assertNotIn("pull_request", DOC[True])
        self.assertNotIn("actions/checkout", TEXT)
        self.assertNotIn("github.head_ref", TEXT.replace("github.event.pull_request.head.sha", ""))

    def test_it_holds_nothing_beyond_read(self):
        self.assertEqual(DOC["permissions"], {})
        self.assertEqual(DOC["jobs"]["gate"]["permissions"], {"contents": "read"})

    def test_the_attestation_is_the_sandboxs_own_workflow_on_its_main_branch(self):
        self.assertIn('--signer-workflow "$SANDBOX/.github/workflows/campaign.yml"', TEXT)
        self.assertIn("--source-ref refs/heads/main", TEXT)
        self.assertIn("gh attestation verify result/result.json", TEXT)

    def test_it_covers_the_same_paths_the_sandbox_polls(self):
        paths = DOC[True]["pull_request_target"]["paths"]
        self.assertEqual(sorted(paths), sorted(["scripts/**", "lib/**", "gate2/**", "public/local-claude-bridge.mjs", ".github/workflows/**", "sources.json"]))

    def test_the_wait_has_two_limits_and_a_sha_check(self):
        self.assertIn("1800", TEXT)
        self.assertIn("5700", TEXT)
        self.assertIn("[[ \"$SHA\" =~ ^[0-9a-f]{40}$ ]]", TEXT)


class Verdict(unittest.TestCase):
    def test_a_good_result_passes(self):
        code, out = run_verdict(GOOD, "e" * 64, "a" * 40)
        self.assertEqual(code, 0, out)

    def test_every_way_of_not_being_good_fails_with_its_reason(self):
        cases = {
            "another commit": (dict(GOOD, emissary_sha="b" * 40), "e" * 64, "a" * 40, "not"),
            "another repository": (dict(GOOD, emissary_repo="someone/else"), "e" * 64, "a" * 40, "someone/else"),
            "a stale expectation": (GOOD, "f" * 64, "a" * 40, "changed since"),
            "a failed campaign": (dict(GOOD, ok=False, verdict={"ok": False, "failures": ["vendor: module X is 'errors'"]}), "e" * 64, "a" * 40, "module X"),
            "a failed campaign without a reason": (dict(GOOD, ok=False, verdict={}), "e" * 64, "a" * 40, "no reason recorded"),
            "no ok field at all": ({k: v for k, v in GOOD.items() if k != "ok"}, "e" * 64, "a" * 40, "campaign failed"),
        }
        for name, (res, exp, sha, needle) in cases.items():
            code, out = run_verdict(res, exp, sha)
            self.assertNotEqual(code, 0, name)
            self.assertIn(needle, out, name)

    def test_a_result_that_is_ok_only_in_its_verdict_is_not_ok(self):
        # the top-level `ok` is the campaign's (it includes the run job's result); a verdict that says ok alone is not enough
        code, _ = run_verdict(dict(GOOD, ok=False), "e" * 64, "a" * 40)
        self.assertNotEqual(code, 0)


if __name__ == "__main__":
    unittest.main()
