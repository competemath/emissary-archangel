"""The scheduled opener (.github/workflows/intake-open.yml) holds the intake App's key and opens pull requests on tengoku unattended. What it must never do is pinned here:
run only when the lane is switched on, reach only the two repositories the App is installed on, take nothing from an input into a shell line, use pinned actions, and arm
the merge queue only on request."""

from __future__ import annotations

import re
import unittest
from pathlib import Path

import yaml

PATH = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "intake-open.yml"
TEXT = PATH.read_text(encoding="utf-8")
DOC = yaml.safe_load(TEXT)
JOB = DOC["jobs"]["open"]


def run_blocks() -> list[str]:
    return [s["run"] for s in JOB["steps"] if "run" in s]


class IntakeOpenWorkflow(unittest.TestCase):
    def test_it_runs_only_when_the_lane_is_on_or_a_person_starts_it(self):
        self.assertIn("vars.LANE_ENABLED == 'true'", JOB["if"])
        self.assertIn("workflow_dispatch", JOB["if"])
        self.assertIn("schedule", DOC[True])  # `on:` is read as True by YAML 1.1

    def test_no_permission_beyond_reading_and_no_default_permissions(self):
        self.assertEqual(DOC["permissions"], {})
        self.assertEqual(JOB["permissions"], {"contents": "read", "actions": "read", "attestations": "read"})

    def test_every_action_is_pinned_to_a_commit(self):
        uses = [s["uses"] for s in JOB["steps"] if "uses" in s]
        self.assertTrue(uses)
        for u in uses:
            self.assertRegex(u, r"@[0-9a-f]{40}$", u)

    def test_an_input_reaches_a_shell_line_only_through_the_environment(self):
        for block in run_blocks():
            self.assertNotIn("${{", block)  # the run blocks hold no expression at all: inputs come in as $TARGET, $KEYS, $DRY_RUN
        for name in ("TARGET", "KEYS", "DRY_RUN"):
            self.assertIn("inputs.", JOB["env"][name])

    def test_the_target_is_one_of_the_two_repositories_the_app_is_installed_on(self):
        first = run_blocks()[0]
        self.assertIn("competemath/tengoku|competemath/tengoku-sandbox)", first)
        self.assertRegex(first, r"\*\) .*exit 1")

    def test_the_apps_token_is_scoped_to_the_target_and_reaches_only_the_opener_step(self):
        app = next(s for s in JOB["steps"] if s.get("id") == "app")
        self.assertEqual(app["with"]["repositories"], "${{ env.REPO_NAME }}")
        self.assertEqual(app["with"]["owner"], "competemath")
        holders = [s["name"] for s in JOB["steps"] if "TENGOKU_TOKEN" in s.get("env", {})]
        self.assertEqual(holders, ["Open the next pull requests"])
        self.assertEqual(JOB["steps"][-1]["env"]["GH_TOKEN"], "${{ github.token }}")  # the factory's token, not the App's, for the factory's runs

    def test_auto_merge_is_armed_only_when_the_variable_says_so_and_a_dry_run_opens_nothing(self):
        step = run_blocks()[-1]
        self.assertRegex(step, r'\[ "\$AUTOMERGE" = "true" \] && args\+=\(--auto-merge\)')
        self.assertRegex(step, r'\[ "\$DRY_RUN" = "true" \] && args\+=\(--dry-run\)')
        self.assertEqual(DOC[True]["workflow_dispatch"]["inputs"]["dry_run"]["default"], "true")  # a hand-started run is a dry run unless the person says otherwise

    def test_one_run_at_a_time_and_never_cancelled_halfway_through_opening_a_pr(self):
        self.assertEqual(DOC["concurrency"], {"group": "intake-open", "cancel-in-progress": False})

    def test_the_script_it_calls_exists_and_the_pace_default_is_the_documented_one(self):
        self.assertIn("scripts/bump/intake_open.py", run_blocks()[-1])
        self.assertTrue((PATH.parents[2] / "scripts" / "bump" / "intake_open.py").exists())
        self.assertTrue(re.search(r"--pace\", type=int, default=90", (PATH.parents[2] / "scripts" / "bump" / "intake_open.py").read_text()))


if __name__ == "__main__":
    unittest.main()
