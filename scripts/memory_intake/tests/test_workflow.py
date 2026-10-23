"""memory-intake.yml: a job that is meant to run on a schedule names a cron that exists (a cron changed in one place and not in the other would skip every run, silently), and the
App's token is minted where it is meant to be and nowhere else."""

import re
import unittest
from pathlib import Path

import yaml

WF = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "memory-intake.yml"
DOC = yaml.safe_load(WF.read_text(encoding="utf-8"))
TRIGGERS = DOC.get("on") or DOC[True]  # PyYAML reads the key `on` as the boolean True
CRONS = {c["cron"] for c in TRIGGERS["schedule"]}


def named(job):
    return set(re.findall(r"github\.event\.schedule == '([^']+)'", str(job.get("if", ""))))


class Schedule(unittest.TestCase):
    def test_every_cron_a_job_names_exists_and_every_cron_is_named(self):
        used = set()
        for name, job in DOC["jobs"].items():
            missing = named(job) - CRONS
            self.assertEqual(missing, set(), f"{name} waits for a cron that is not scheduled")
            used |= named(job)
        self.assertEqual(CRONS - used, set(), "a cron no job runs on")

    def test_the_intake_is_hourly_and_the_report_and_the_settle_run_every_half_hour(self):
        self.assertEqual(named(DOC["jobs"]["collect"]), {"17 * * * *"})
        self.assertEqual(named(DOC["jobs"]["report"]), {"7,37 * * * *"})
        self.assertEqual(named(DOC["jobs"]["settle"]), {"7,37 * * * *"})

    def test_nothing_scheduled_runs_without_the_kill_switch(self):
        for name in ("collect", "report", "settle"):
            self.assertIn("vars.LEAK_INTAKE_ENABLED == '1'", DOC["jobs"][name]["if"], name)


class Checkout(unittest.TestCase):
    def test_the_test_job_checks_out_the_workflow_this_file_reads(self):
        """CodeRabbit on emissary#102: memory-intake-tests.yml checked out scripts/memory_intake only, so this module failed on import in CI."""
        tests = yaml.safe_load((WF.parent / "memory-intake-tests.yml").read_text(encoding="utf-8"))
        checkout = next(s for s in tests["jobs"]["unit"]["steps"] if "actions/checkout" in s.get("uses", ""))
        self.assertIn(".github/workflows", checkout["with"]["sparse-checkout"].split("\n"))


class Token(unittest.TestCase):
    def test_the_apps_token_is_minted_in_open_and_settle_only(self):
        minters = {n for n, j in DOC["jobs"].items() if any("create-github-app-token" in s.get("uses", "") for s in j["steps"])}
        self.assertEqual(minters, {"open", "settle"})

    def test_settle_has_no_write_permission_of_its_own_and_runs_after_the_report(self):
        job = DOC["jobs"]["settle"]
        self.assertEqual(job["permissions"], {"contents": "read", "id-token": "write"})
        self.assertEqual(job["needs"], "report")

    def test_settle_closes_before_it_tells_the_site(self):
        runs = [s.get("run", "") for s in DOC["jobs"]["settle"]["steps"]]
        close = next(i for i, r in enumerate(runs) if "run settle" in r)
        post = next(i for i, r in enumerate(runs) if "run post" in r)
        self.assertLess(close, post)

    def test_a_dry_run_mints_no_token_and_posts_nothing(self):
        steps = DOC["jobs"]["settle"]["steps"]
        app = next(s for s in steps if s.get("id") == "app")
        self.assertIn("inputs.dry_run != 'true'", app["if"])
        post = next(s for s in steps if "run post" in s.get("run", ""))
        self.assertIn("inputs.dry_run != 'true'", post["if"])


if __name__ == "__main__":
    unittest.main()
