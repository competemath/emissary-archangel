"""scripts/agent-jail.py builds the jail and proves it. Here: the commands it would run, read but not executed, and the
decision logic of `ready` with a fake runner. A real run is the agent-selftest workflow."""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import types
import unittest

import _load

jail_cli = _load.load_script("agent-jail")
agent_run = _load.load_script("agent-run")
inner = _load.load_script("agent-selftest-inner")


def bash_syntax_ok(text):
    res = subprocess.run(["bash", "-n"], input=text, universal_newlines=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return res.returncode == 0, res.stdout


class SetupScript(unittest.TestCase):
    def setUp(self):
        self.script = jail_cli.setup_script(runner_user="runner", runner_home="/home/runner")

    def test_it_is_valid_bash(self):
        ok, out = bash_syntax_ok(self.script)
        self.assertTrue(ok, out)
        ok, out = bash_syntax_ok(jail_cli.teardown_script())
        self.assertTrue(ok, out)

    def test_the_agent_user_comes_from_warden_and_fails_closed(self):
        self.assertIn("set -euo pipefail", self.script)
        self.assertIn("useradd --system", self.script)
        self.assertIn("hidepid=2", self.script)
        self.assertIn("chmod o-rwx", self.script)
        self.assertIn("not allowed to run sudo", self.script)
        self.assertEqual(self.script.count("#!"), 1, "one shebang")

    def test_egress_rules_name_exactly_the_allowed_loopback_ports_and_reject_the_rest(self):
        accepts = sorted(int(p) for p in re.findall(r"-p tcp -d 127\.0\.0\.1/32 --dport (\d+) -j ACCEPT", self.script))
        self.assertEqual(accepts, [4125, 7871, 7872, 8899])
        self.assertIn("-j REJECT", self.script)
        self.assertIn("ip6tables", self.script)
        self.assertIn("169.254.169.254/32", self.script)
        self.assertIn("--uid-owner $AGENT_UID", self.script)

    def test_the_proxy_runs_as_its_own_user_and_allows_the_model_api_only(self):
        proxy = [l for l in self.script.split("\n") if "egress-proxy" in l]
        self.assertEqual(len(proxy), 1)
        self.assertIn("sudo -n -u egress env -i", proxy[0])
        self.assertEqual(re.findall(r"--allow (\S+)", proxy[0]), ["api.anthropic.com:443"])
        self.assertIn("--listen 127.0.0.1:8899", proxy[0])

    def test_user_namespaces_are_switched_off_and_the_code_is_installed_root_owned(self):
        self.assertIn("sysctl -w user.max_user_namespaces=0", self.script)
        self.assertIn("chown -R root:root /opt/emissary-jail", self.script)
        for name in ("agent-supervise.py", "agent-selftest-inner.py"):
            self.assertIn("/opt/emissary-jail/" + name, self.script)

    def test_what_the_hosted_image_leaves_writable_is_closed_and_the_agents_path_has_no_writable_directory(self):
        script = jail_cli.setup_script(runner_user="runner", runner_home="/home/runner", harden_path="/usr/local/bin:/usr/bin:/opt/hostedtoolcache/node/22/x64/bin")
        self.assertTrue(bash_syntax_ok(script)[0])
        self.assertIn("for d in /opt /usr/local /usr/local/bin", script)
        self.assertIn("chmod go-w", script)
        self.assertIn("RUNNER_PATH=/usr/local/bin:/usr/bin:/opt/hostedtoolcache/node/22/x64/bin", script)
        self.assertIn("find -L", script)
        self.assertIn("chmod o-rwx /run/dbus/system_bus_socket", script)
        self.assertNotIn("RUNNER_PATH", self.script, "without --harden-path nothing walks a PATH")
        self.assertNotIn("/usr/local/bin", jail_cli.AGENT_PATH.split(":"), "the image leaves /usr/local/bin writable by everyone")
        self.assertTrue(all(d.startswith(("/opt/agent-tools", "/usr/bin", "/bin")) for d in jail_cli.AGENT_PATH.split(":")))

    def test_the_lean_services_user_keeps_its_way_through_the_closed_home(self):
        script = jail_cli.setup_script(runner_user="runner", runner_home="/home/runner", traverse=["lean"])
        self.assertIn("setfacl -m u:lean:x /home/runner", script)
        self.assertTrue(bash_syntax_ok(script)[0])
        self.assertNotIn("setfacl", self.script)
        for bad in ("root", "agent", "bad user", "-x"):
            with self.assertRaises(Exception):
                jail_cli.setup_script(runner_user="runner", runner_home="/home/runner", traverse=[bad])

    def test_workspace_and_home_must_not_collide_with_the_runner(self):
        with self.assertRaises(Exception):
            jail_cli.setup_script(workspace="/home/runner/agent", runner_home="/home/runner")
        with self.assertRaises(Exception):
            jail_cli.setup_script(agent_user="runner", runner_user="runner")


class SelftestCommand(unittest.TestCase):
    def test_it_runs_as_the_agent_with_the_agents_environment_and_every_input_set(self):
        argv = jail_cli.selftest_argv(
            agent_user="agent", agent_uid=1003, workspace="/home/agent", runner_home="/home/runner", canaries=["/a", "/b"], decoy_pid=4242,
            egress_canary="10.1.2.3:5555", ports=[4125, 7871, 7872], report="/home/agent/selftest.json", github_files=["/gh/env"],
        )
        self.assertEqual(argv[:6], ["sudo", "-n", "-u", "agent", "env", "-i"])
        text = " ".join(argv)
        for needle in ("--require-linux", "--expect-uid 1003", "--bridge-pid 4242", "--egress-canary 10.1.2.3:5555", "--canary-file /a", "--canary-file /b",
                       "--github-file /gh/env", "--allow-port 8899", "--allow-port 4125", "--home /home/runner", "PATH=" + jail_cli.AGENT_PATH, "HOME=/home/agent"):
            self.assertIn(needle, text)
        self.assertNotRegex(text, r"TOKEN|SECRET|sk-ant")

    def test_the_inner_battery_skips_only_what_a_uid_jail_cannot_answer(self):
        self.assertEqual(inner.SKIPPED, jail_cli.SKIPPED_PROBES)
        from warden import selftest

        names = {p.name for p in selftest.default_probes()}
        kept = {p.name for p in selftest.default_probes() if p.name not in inner.SKIPPED}
        self.assertEqual(names - kept, {"userns_differs_from_host"})
        self.assertTrue({"sudo_denied", "tcp_egress_canary_denied", "read_host_canary", "read_bridge_environ", "nested_userns_denied", "unix_sockets_denied"} <= kept)


class FakeRunner:
    """Stands in for subprocess.run: records every command and answers by what it is."""

    def __init__(self, report, battery_rc=0):
        self.calls = []
        self.report = report
        self.battery_rc = battery_rc
        self.marker = None

    def __call__(self, argv, input_text=None, timeout=300, check=False):
        self.calls.append((list(argv), input_text))
        text = " ".join(argv)
        out = types.SimpleNamespace(returncode=0, stdout="")
        if argv[:3] == ["id", "-u", "agent"]:
            out.stdout = "1003\n"
        elif "agent-selftest-inner.py" in text:
            out.returncode = self.battery_rc
            out.stdout = "PASS: 33 denied\n"
        elif argv[-2:] == ["cat", "/home/agent/selftest.json"]:
            out.stdout = json.dumps(self.report)
        elif argv[:3] == ["sudo", "-n", "tee"]:
            self.marker = input_text
        return out


def good_report(**over):
    rep = {"ok": True, "linux": True, "uid": 1003, "failed": [], "results": [{"name": "p%d" % i} for i in range(33)]}
    rep.update(over)
    return rep


class Ready(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.claude = os.path.join(self.tmp, "claude")
        with open(self.claude, "w") as fh:
            fh.write("#!/bin/sh\n")
        os.chmod(self.claude, 0o755)
        self.saved_ip = jail_cli.primary_ip
        jail_cli.primary_ip = lambda: "10.9.8.7"
        self.addCleanup(setattr, jail_cli, "primary_ip", self.saved_ip)

    def ready(self, runner, **over):
        args = types.SimpleNamespace(
            agent_user="agent", workspace="/home/agent", ports="4125,7871,7872", proxy_port=8899, runner_home="/home/runner", real_claude=self.claude,
            agent_path=jail_cli.AGENT_PATH, max_usd=20.0, max_turns=400, wall_seconds=3600, report=os.path.join(self.tmp, "report.json"),
        )
        for k, v in over.items():
            setattr(args, k, v)
        return jail_cli.cmd_ready(args, runner=runner)

    def test_a_passing_battery_writes_a_marker_the_wrapper_accepts(self):
        runner = FakeRunner(good_report())
        self.assertEqual(self.ready(runner), 0)
        marker = json.loads(runner.marker)
        self.assertEqual((marker["agent_uid"], marker["ok"], marker["version"]), (1003, True, 1))
        self.assertEqual(marker["ports"], [4125, 7871, 7872, 8899])
        self.assertEqual(marker["real_claude"], self.claude)
        # the marker is written after the stale one is removed, and made root-owned
        argvs = [c[0] for c in runner.calls]
        self.assertEqual(argvs[0], ["sudo", "-n", "rm", "-f", jail_cli.MARKER])
        self.assertIn(["sudo", "-n", "chown", "root:root", jail_cli.MARKER], argvs)
        # and what it wrote is exactly what agent-run.py loads
        d = os.path.join(self.tmp, "jail")
        os.mkdir(d, 0o755)
        path = os.path.join(d, "ready.json")
        with open(path, "w") as fh:
            fh.write(runner.marker)
        os.chmod(path, 0o644)
        self.assertEqual(agent_run.load_ready(path, trusted_uid=os.getuid())["agent_user"], "agent")

    def test_a_failing_battery_writes_nothing(self):
        for runner in (FakeRunner(good_report(ok=False, failed=["sudo_denied"])), FakeRunner(good_report(), battery_rc=1),
                       FakeRunner(good_report(linux=False)), FakeRunner(good_report(uid=0)), FakeRunner({})):
            self.assertEqual(self.ready(runner), 1)
            self.assertIsNone(runner.marker)
            self.assertFalse([c for c in runner.calls if c[0][:3] == ["sudo", "-n", "tee"]])

    def test_without_the_agent_binary_it_refuses_before_running_anything_as_the_agent(self):
        runner = FakeRunner(good_report())
        self.assertEqual(self.ready(runner, real_claude=os.path.join(self.tmp, "missing")), 1)
        self.assertFalse([c for c in runner.calls if "agent-selftest-inner.py" in " ".join(c[0])])

    def test_the_canaries_are_cleaned_up(self):
        runner = FakeRunner(good_report())
        self.ready(runner)
        battery = [c[0] for c in runner.calls if "agent-selftest-inner.py" in " ".join(c[0])][0]
        for f in [battery[i + 1] for i, a in enumerate(battery) if a == "--canary-file"]:
            self.assertFalse(os.path.exists(f))


if __name__ == "__main__":
    unittest.main()
