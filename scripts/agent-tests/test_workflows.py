"""The workflows that carry the agent jail, and the pinning rules every workflow here follows.

Reads the YAML with PyYAML when it is installed (it is on the runners; bump-tests relies on it too), else through Ruby.
"""
import glob
import json
import os
import re
import shutil
import subprocess
import unittest

import _load

WORKFLOWS = os.path.join(_load.ROOT, ".github", "workflows")
USES = re.compile(r"^\s*-?\s*uses:\s*(\S+?)\s*(#.*)?$")


def load_yaml(path):
    try:
        import yaml

        with open(path, encoding="utf-8") as fh:
            return yaml.safe_load(fh)
    except ImportError:
        if not shutil.which("ruby"):
            raise unittest.SkipTest("neither PyYAML nor ruby is available")
        res = subprocess.run(["ruby", "-ryaml", "-rjson", "-e", "puts JSON.generate(YAML.load_file(ARGV[0]))", path], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, universal_newlines=True, check=True)
        return json.loads(res.stdout)


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def workflow_files():
    return sorted(glob.glob(os.path.join(WORKFLOWS, "*.yml")))


def steps(doc, job):
    return doc["jobs"][job]["steps"]


def step_named(doc, job, fragment):
    found = [s for s in steps(doc, job) if fragment in str(s.get("name", ""))]
    assert len(found) == 1, (fragment, [s.get("name") for s in steps(doc, job)])
    return found[0]


def index_of(doc, job, fragment):
    return [i for i, s in enumerate(steps(doc, job)) if fragment in str(s.get("name", s.get("uses", "")))][0]


class Pinning(unittest.TestCase):
    def test_every_action_is_a_full_commit_sha_with_a_version_comment(self):
        bad = []
        for path in workflow_files():
            for n, line in enumerate(read(path).split("\n"), 1):
                m = USES.match(line)
                if not m or m.group(1).startswith("./"):
                    continue
                if not re.fullmatch(r"[\w.-]+/[\w./-]+@[0-9a-f]{40}", m.group(1)) or not re.match(r"#\s*v\d", m.group(2) or ""):
                    bad.append("%s:%d: %s %s" % (os.path.basename(path), n, m.group(1), m.group(2) or ""))
        self.assertEqual(bad, [])

    def test_no_installer_is_piped_into_a_shell(self):
        bad = []
        for path in workflow_files():
            for n, line in enumerate(read(path).split("\n"), 1):
                if re.search(r"(curl|wget)\b[^#\n]*\|\s*(sudo\s+)?(sh|bash)\b", line):
                    bad.append("%s:%d" % (os.path.basename(path), n))
        self.assertEqual(bad, [], "download to a file, check its sha256, then run it")

    def test_every_elan_installer_is_at_a_commit_and_checked_against_its_digest(self):
        for path in workflow_files():
            text = read(path)
            for m in re.finditer(r"elan/([^/\s]+)/elan-init\.sh", text):
                self.assertRegex(m.group(1), r"^[0-9a-f]{40}$", "%s fetches elan-init.sh from %s" % (os.path.basename(path), m.group(1)))
            n_fetch = len(re.findall(r"elan/[0-9a-f]{40}/elan-init\.sh", text))
            n_check = len(re.findall(r"echo \"[0-9a-f]{64}  [^\"]*elan-init\.sh\" \| sha256sum -c -", text))
            self.assertEqual(n_fetch, n_check, "%s: each fetch of elan-init.sh needs its sha256sum -c" % os.path.basename(path))

    def test_global_npm_installs_name_an_exact_version(self):
        for path in workflow_files():
            for n, line in enumerate(read(path).split("\n"), 1):
                if "npm install" in line and " -g" in line:
                    self.assertRegex(line, r"@anthropic-ai/claude-code@(\$\{?CLAUDE_CODE_VERSION\}?|\"\$CLAUDE_CODE_VERSION\"|\d+\.\d+\.\d+)", "%s:%d" % (os.path.basename(path), n))

    def test_the_pinned_agent_version_is_one_exact_version_everywhere(self):
        versions = set()
        for path in workflow_files():
            versions |= set(re.findall(r'CLAUDE_CODE_VERSION: "([^"]+)"', read(path)))
        self.assertEqual(len(versions), 1, versions)
        self.assertRegex(versions.pop(), r"^\d+\.\d+\.\d+$")


class Translate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.path = os.path.join(WORKFLOWS, "translate.yml")
        cls.doc = load_yaml(cls.path)
        cls.text = read(cls.path)

    def test_harden_runner_is_first_in_audit_mode_in_the_jobs_that_hold_tokens(self):
        for job in ("translate", "finish"):
            first = steps(self.doc, job)[0]
            self.assertEqual(first["uses"], "step-security/harden-runner@e14015d583714f6e62063499dc959a02595150a1")
            self.assertEqual(first["with"]["egress-policy"], "audit")
        self.assertIn("--from-audit", self.text, "the way to turn the observed endpoints into `block` is written next to the step")

    def test_the_jail_is_proven_before_the_agent_can_start_and_the_gate_runs_after(self):
        order = [index_of(self.doc, "translate", f) for f in ("The agent (agent mode only)", "The agent's jail", "Translate this shard", "Audit the agent's trace", "Take the jail down", "Redact secrets")]
        self.assertEqual(order, sorted(order))
        self.assertEqual(len(set(order)), len(order))
        for frag in ("The agent (agent mode only)", "The agent's jail", "Audit the agent's trace", "Take the jail down"):
            self.assertIn("inputs.mode == 'agent'", step_named(self.doc, "translate", frag)["if"], frag)

    def test_mechanical_mode_does_not_touch_the_jail(self):
        translate = step_named(self.doc, "translate", "Translate this shard")
        run = translate["run"]
        self.assertIn('if [ "$JAIL" != 1 ]', run)
        self.assertRegex(run, r'agent_env=\(EMISSARY_JAIL=1 CLAUDE_BIN="\$PWD/scripts/agent-run\.py" EMISSARY_TRACE_DIR="\$PWD/out/trace"\)')
        self.assertIn("EMISSARY_NO_AGENT=\"$noagent\"", run)

    def test_the_jail_step_falls_back_instead_of_failing_the_shard(self):
        run = step_named(self.doc, "translate", "The agent's jail")["run"]
        self.assertIn("agent-jail.py setup", run)
        self.assertIn("agent-jail.py ready", run)
        self.assertIn("::warning::", run)
        self.assertIn("jail=0", run)
        self.assertIn("--traverse lean", run, "the Lean services' user must keep its way through the closed runner home")

    def test_the_agent_is_installed_root_owned_at_one_exact_version(self):
        step = step_named(self.doc, "translate", "The agent (agent mode only)")
        self.assertRegex(step["env"]["CLAUDE_CODE_VERSION"], r"^\d+\.\d+\.\d+$")
        self.assertIn("chown -R root:root /opt/agent-tools", step["run"])

    def test_artifacts_are_redacted_before_upload_and_kept_three_days(self):
        redact = step_named(self.doc, "translate", "Redact secrets")
        self.assertEqual(redact["id"], "redact")
        upload = steps(self.doc, "translate")[-1]
        self.assertTrue(upload["uses"].startswith("actions/upload-artifact@"))
        self.assertIn("steps.redact.outcome == 'success'", upload["if"])
        self.assertEqual(upload["with"]["retention-days"], 3)

    def test_the_finish_job_pushes_with_a_lease_not_a_blind_loop(self):
        run = step_named(self.doc, "finish", "Fold the shards")["run"]
        self.assertIn("scripts/safe-push.py", run)
        self.assertNotIn("pull -q --rebase", run)
        self.assertNotIn("git push", run)

    def test_no_secret_reaches_the_steps_that_run_the_installers(self):
        for frag in ("elan", "The agent (agent mode only)"):
            self.assertNotIn("secrets.", json.dumps(step_named(self.doc, "translate", frag)))


class SelfTestWorkflow(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.path = os.path.join(WORKFLOWS, "agent-selftest.yml")
        cls.doc = load_yaml(cls.path)
        cls.text = read(cls.path)

    def test_manual_only_short_and_without_secrets_lean_or_the_model(self):
        on = self.doc.get("on") or self.doc.get(True) or self.doc.get("true")  # YAML 1.1 reads the key `on` as a boolean
        self.assertEqual(list(on), ["workflow_dispatch"])
        self.assertEqual(self.doc["permissions"], {})
        job = self.doc["jobs"]["battery"]
        self.assertEqual(job["timeout-minutes"], 10)
        self.assertEqual(job["permissions"], {"contents": "read"})
        self.assertNotIn("${{ secrets.", self.text)
        self.assertNotRegex(self.text, r"lake|elan|npm install|CLAUDE_CODE_OAUTH_TOKEN")
        self.assertEqual(steps(self.doc, "battery")[0]["uses"], "step-security/harden-runner@e14015d583714f6e62063499dc959a02595150a1")

    def test_it_builds_the_same_jail_as_translate(self):
        translate = read(os.path.join(WORKFLOWS, "translate.yml"))
        for needle in ("agent-jail.py setup", "agent-jail.py ready", "--ports 4125,7871,7872"):
            self.assertIn(needle, self.text)
            self.assertIn(needle, translate)


class EveryWorkflow(unittest.TestCase):
    def test_top_level_permissions_are_empty_or_read_only(self):
        for path in workflow_files():
            doc = load_yaml(path)
            perms = doc.get("permissions")
            self.assertIsNotNone(perms, os.path.basename(path) + " has no top-level permissions")
            self.assertTrue(perms == {} or set(perms.values()) <= {"read"}, os.path.basename(path))

    def test_every_workflow_parses(self):
        for path in workflow_files():
            self.assertIn("jobs", load_yaml(path), path)


if __name__ == "__main__":
    unittest.main()
