"""scripts/agent-run.py (the wrapper) and scripts/agent-supervise.py (the process that runs as the agent user).

Nothing here needs sudo or Linux: the wrapper's decisions are pure functions of (argv, the ready file, the environment), and the
supervisor is run as the current user with a workspace of its own.
"""
import io
import json
import os
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest

import _load

run = _load.load_script("agent-run")
sup = _load.load_script("agent-supervise")

SUPERVISOR = os.path.join(_load.SCRIPTS, "agent-supervise.py")


def slurp(path):
    with open(path) as fh:
        return fh.read()


def spit(path, text=""):
    with open(path, "w") as fh:
        fh.write(text)


def ready(**over):
    data = {
        "version": 1, "ok": True, "agent_user": "agent", "workspace": "/home/agent", "real_claude": "/opt/agent-tools/bin/claude",
        "path": "/opt/agent-tools/bin:/usr/bin:/bin", "ports": [4125, 7871, 7872, 8899], "proxy": "http://127.0.0.1:8899",
        "bash": False, "max_usd": 20.0, "max_turns": 400, "wall_seconds": 3600,
    }
    data.update(over)
    return data


def bridge_run_dir(*, mcp_url="http://127.0.0.1:7871/sse", extra_files=None):
    """What spawnProverStream leaves in its run directory: mcp.json, settings.json and the two hook scripts."""
    d = tempfile.mkdtemp(prefix="claude-tree-")
    with open(os.path.join(d, "mcp.json"), "w") as fh:
        json.dump({"mcpServers": {"Leak_IV": {"type": "sse", "url": mcp_url}, "architect": {"type": "sse", "url": "http://127.0.0.1:4125/gov/abc/sse?view=architect"}}}, fh)
    with open(os.path.join(d, "no-local-lean.mjs"), "w") as fh:
        fh.write("// hook\n")
    with open(os.path.join(d, "no-memory.mjs"), "w") as fh:
        fh.write("// hook\n")
    with open(os.path.join(d, "settings.json"), "w") as fh:
        json.dump({"hooks": {"PreToolUse": [{"matcher": "Bash", "hooks": [{"type": "command", "command": "node %s/no-local-lean.mjs" % d}]}]}}, fh)
    for name, content in (extra_files or {}).items():
        with open(os.path.join(d, name), "w") as fh:
            fh.write(content)
    return d


def bridge_argv(d, tools="--tools=", extra=()):
    return ["-p", "prove it", "--output-format", "stream-json", "--verbose", "--mcp-config", os.path.join(d, "mcp.json"), tools, "--strict-mcp-config",
            "--dangerously-skip-permissions", "--max-turns", "30", "--max-budget-usd", "5", "--settings", os.path.join(d, "settings.json"),
            "--append-system-prompt", "be careful"] + list(extra)


class ReadyFile(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        os.chmod(self.dir, 0o755)
        self.path = os.path.join(self.dir, "ready.json")
        self.addCleanup(shutil.rmtree, self.dir, True)

    def write(self, data, mode=0o644):
        with open(self.path, "w") as fh:
            json.dump(data, fh)
        os.chmod(self.path, mode)

    def test_a_good_file_loads(self):
        self.write(ready())
        self.assertEqual(run.load_ready(self.path, trusted_uid=os.getuid())["agent_user"], "agent")

    def test_missing_file_refuses_to_start(self):
        with self.assertRaisesRegex(run.Refused, "not ready"):
            run.load_ready(self.path, trusted_uid=os.getuid())

    def test_a_file_someone_else_could_write_or_own_is_refused(self):
        self.write(ready(), mode=0o664)
        with self.assertRaisesRegex(run.Refused, "only root can write"):
            run.load_ready(self.path, trusted_uid=os.getuid())
        self.write(ready())
        with self.assertRaisesRegex(run.Refused, "only root can write"):
            run.load_ready(self.path, trusted_uid=os.getuid() + 1)
        os.chmod(self.dir, 0o777)
        with self.assertRaisesRegex(run.Refused, "directory"):
            run.load_ready(self.path, trusted_uid=os.getuid())

    def test_malformed_or_not_ok_is_refused(self):
        for bad in (ready(ok=False), ready(version=2), ready(agent_user="root"), ready(workspace="relative"), ready(ports=[0]), ready(proxy="http://evil.example:3128"),
                    ready(max_usd=0), ready(max_turns=True), ready(bash="yes"), {}):
            self.write(bad)
            with self.assertRaises(run.Refused, msg=str(bad)):
                run.load_ready(self.path, trusted_uid=os.getuid())


class Planning(unittest.TestCase):
    def setUp(self):
        self.d = bridge_run_dir()
        self.addCleanup(shutil.rmtree, self.d, True)
        self.env = {"PATH": "/runner/bin", "LANG": "C.UTF-8", "CLAUDE_CODE_OAUTH_TOKEN": "sk-ant-oat01-" + "x" * 40, "BRIDGE_TOKEN": "bridge-secret",
                    "GH_TOKEN": "ghs_" + "a" * 36, "TENGOKU_BOT_TOKEN": "bot", "HOME": "/home/runner", "RANDOM": "1"}

    def plan(self, argv=None, ready_over=None, env=None, name="run.0123456789abcdef"):
        return run.plan_launch(argv if argv is not None else bridge_argv(self.d), ready(**(ready_over or {})), env if env is not None else self.env, name)

    def test_the_launch_is_staged_rewritten_and_run_as_the_agent(self):
        p = self.plan()
        work = "/home/agent/run.0123456789abcdef/work"
        self.assertEqual(p["sudo"][:7], ["sudo", "-n", "-u", "agent", "env", "-i", "PATH=/usr/bin:/bin"])
        self.assertEqual(p["sudo"][7:], ["/usr/bin/python3", "/opt/emissary-jail/agent-supervise.py"])
        argv = p["header"]["argv"]
        self.assertEqual(argv[0], "/opt/agent-tools/bin/claude")
        self.assertIn(work + "/mcp.json", argv)
        self.assertIn(work + "/settings.json", argv)
        self.assertFalse([a for a in argv if self.d in a], "no path of the bridge's temp directory is left in argv")
        files = {}
        with tarfile.open(fileobj=io.BytesIO(p["tar"])) as tar:
            for m in tar.getmembers():
                files[m.name] = tar.extractfile(m).read().decode()
        self.assertEqual(sorted(files), ["mcp.json", "no-local-lean.mjs", "no-memory.mjs", "settings.json"])
        self.assertIn(work + "/no-local-lean.mjs", files["settings.json"])
        self.assertNotIn(self.d, files["settings.json"])

    def test_the_environment_is_rebuilt_from_an_allowlist(self):
        p = self.plan()
        env = p["header"]["env"]
        for forbidden in ("BRIDGE_TOKEN", "GH_TOKEN", "TENGOKU_BOT_TOKEN", "RANDOM"):
            self.assertNotIn(forbidden, env)
        self.assertEqual(env["PATH"], ready()["path"], "the agent's PATH is the jail's, not the bridge's")
        self.assertEqual(env["HOME"], "/home/agent/run.0123456789abcdef/home")
        self.assertEqual(env["HTTPS_PROXY"], "http://127.0.0.1:8899")
        self.assertTrue(env["CLAUDE_CODE_OAUTH_TOKEN"].startswith("sk-ant-oat01-"))
        self.assertEqual(env["CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC"], "1")
        self.assertNotIn("sk-ant", " ".join(p["sudo"]), "the credential is never on a command line")
        self.assertNotIn("bridge-secret", json.dumps(p["header"]))

    def test_a_secret_in_an_allowed_variable_is_refused(self):
        with self.assertRaisesRegex(run.Refused, "environment refused"):
            self.plan(env=dict(self.env, LANG="ghp_" + "b" * 36))

    def test_caps_are_clamped_to_the_ceiling_and_added_when_missing(self):
        argv = self.plan(bridge_argv(self.d, extra=["--max-turns=99999"]), ready_over={"max_turns": 50, "max_usd": 7.5})["header"]["argv"]
        self.assertEqual(argv.count("--max-turns"), 1)
        self.assertEqual(argv[argv.index("--max-turns") + 1], "30", "the lowest of the requested values and the ceiling")
        self.assertEqual(argv[argv.index("--max-budget-usd") + 1], "5.0")
        bare = [a for a in bridge_argv(self.d) if a not in ("--max-turns", "30", "--max-budget-usd", "5")]
        argv = self.plan(bare, ready_over={"max_turns": 50, "max_usd": 7.5})["header"]["argv"]
        self.assertEqual(argv[argv.index("--max-turns") + 1], "50")
        self.assertEqual(argv[argv.index("--max-budget-usd") + 1], "7.5")

    def test_a_shell_needs_the_jail_to_have_been_proven_with_one(self):
        with self.assertRaisesRegex(run.Refused, "shell"):
            self.plan(bridge_argv(self.d, tools="--tools=Bash"))
        self.assertIn("--tools=Bash", self.plan(bridge_argv(self.d, tools="--tools=Bash"), ready_over={"bash": True})["header"]["argv"])

    def test_argv_the_tool_policy_refuses(self):
        base = ["-p", "x", "--mcp-config", os.path.join(self.d, "mcp.json")]
        cases = {
            "no tool set": base + ["--strict-mcp-config", "--dangerously-skip-permissions"],
            "deny-list only": base + ["--strict-mcp-config", "--dangerously-skip-permissions", "--disallowedTools", "WebSearch"],
            "default tools": base + ["--tools=default", "--strict-mcp-config", "--dangerously-skip-permissions"],
            "web tool": base + ["--tools=WebFetch", "--strict-mcp-config", "--dangerously-skip-permissions"],
            "write tool": base + ["--tools=Write", "--strict-mcp-config"],
            "no strict mcp": base + ["--tools="],
            "interactive": ["--mcp-config", os.path.join(self.d, "mcp.json"), "--tools=", "--strict-mcp-config"],
            "inline settings": base + ["--tools=", "--strict-mcp-config", "--settings", '{"hooks":{}}'],
        }
        for label, argv in cases.items():
            with self.assertRaises(run.Refused, msg=label):
                self.plan(argv)

    def test_mcp_config_that_would_run_a_program_or_leave_the_loopback_is_refused(self):
        for label, cfg in {
            "stdio": {"mcpServers": {"x": {"command": "sh", "args": ["-c", "id"]}}},
            "stdio typed": {"mcpServers": {"x": {"type": "stdio", "command": "sh"}}},
            "port": {"mcpServers": {"x": {"type": "sse", "url": "http://127.0.0.1:9999/sse"}}},
            "host": {"mcpServers": {"x": {"type": "sse", "url": "http://evil.example:7871/sse"}}},
            "https": {"mcpServers": {"x": {"type": "sse", "url": "https://127.0.0.1:7871/sse"}}},
            "headers": {"mcpServers": {"x": {"type": "sse", "url": "http://127.0.0.1:7871/sse", "headers": {"a": "b"}}}},
            "shape": {"servers": {}},
        }.items():
            d = bridge_run_dir()
            self.addCleanup(shutil.rmtree, d, True)
            with open(os.path.join(d, "mcp.json"), "w") as fh:
                json.dump(cfg, fh)
            with self.assertRaises(run.Refused, msg=label):
                self.plan(bridge_argv(d))

    def test_a_run_directory_that_is_not_plain_files_is_refused(self):
        for label, setup in {
            "symlink": lambda d: os.symlink("/etc/passwd", os.path.join(d, "link.json")),
            "subdirectory": lambda d: os.mkdir(os.path.join(d, "sub")),
            "odd name": lambda d: spit(os.path.join(d, "-rf")),
            "huge file": lambda d: spit(os.path.join(d, "big.json"), "x" * (run.MAX_STAGED_FILE + 1)),
        }.items():
            d = bridge_run_dir()
            self.addCleanup(shutil.rmtree, d, True)
            setup(d)
            with self.assertRaises(run.Refused, msg=label):
                self.plan(bridge_argv(d))

    def test_a_run_directory_outside_the_temp_directory_is_refused(self):
        with self.assertRaises(run.Refused):
            run.stage_directory(os.path.expanduser("~"), "/home/agent/run.x/work")

    def test_two_mcp_configs_or_an_inline_one_are_refused(self):
        with self.assertRaises(run.Refused):
            self.plan(bridge_argv(self.d, extra=["--mcp-config", os.path.join(self.d, "mcp.json")]))
        with self.assertRaises(run.Refused):
            self.plan(["-p", "x", "--mcp-config", '{"mcpServers":{}}', "--tools=", "--strict-mcp-config"])

    def test_no_ready_file_means_no_launch(self):
        self.assertEqual(run.main(["-p", "x"]), 2)


class Supervisor(unittest.TestCase):
    def setUp(self):
        self.ws = tempfile.mkdtemp(prefix="agent-ws-")
        self.addCleanup(shutil.rmtree, self.ws, True)

    def start(self, argv, *, files=None, env=None, wall=60, run_name="run.0123456789abcdef", run_dir=None):
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w") as tar:
            for name, text in (files or {}).items():
                info = tarfile.TarInfo(name)
                info.size = len(text)
                tar.addfile(info, io.BytesIO(text.encode()))
        header = {"run_dir": run_dir or os.path.join(self.ws, run_name), "argv": argv, "env": env or {"PATH": os.environ["PATH"]}, "wall": wall, "tar_len": len(buf.getvalue())}
        proc = subprocess.Popen([sys.executable, SUPERVISOR, "--workspace", self.ws], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        proc.stdin.write((json.dumps(header) + "\n").encode() + buf.getvalue())
        proc.stdin.flush()
        return proc, header["run_dir"]

    def finish(self, proc, timeout=20):
        """Read everything, wait, and only then close stdin: end of file on stdin means the launcher is gone."""
        out = proc.stdout.read()
        err = proc.stderr.read()
        proc.wait(timeout=timeout)
        proc.stdin.close()
        proc.stdout.close()
        proc.stderr.close()
        return out, err

    def test_runs_the_command_in_work_with_exactly_the_given_environment_and_cleans_up(self):
        code = "import os,sys; print(open('mcp.json').read(), os.getcwd().endswith('/work'), os.environ.get('ONLY'), 'BRIDGE_TOKEN' in os.environ, os.environ['HOME']); sys.exit(7)"
        proc, run_dir = self.start([sys.executable, "-c", code], files={"mcp.json": "{}"}, env={"PATH": os.environ["PATH"], "ONLY": "mine", "HOME": self.ws + "/run.0123456789abcdef/home"})
        out, err = self.finish(proc)
        self.assertEqual(proc.returncode, 7, err)
        self.assertEqual(out.decode().split(), ["{}", "True", "mine", "False", self.ws + "/run.0123456789abcdef/home"])
        self.assertFalse(os.path.exists(run_dir), "the run directory is removed")

    def test_the_launcher_going_away_kills_the_agent_and_its_children(self):
        marker = os.path.join(self.ws, "child.pid")
        code = "import os,subprocess,time; c=subprocess.Popen(['sleep','60']); open(%r,'w').write(str(c.pid)); time.sleep(60)" % marker
        proc, run_dir = self.start([sys.executable, "-c", code])
        for _ in range(100):
            if os.path.exists(marker) and slurp(marker):
                break
            time.sleep(0.1)
        pid = int(slurp(marker))
        proc.stdin.close()  # what SIGKILL of the wrapper looks like from here
        proc.wait(timeout=20)
        proc.stdout.close()
        proc.stderr.close()
        for _ in range(50):
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.1)
        else:
            self.fail("the grandchild is still running")
        self.assertFalse(os.path.exists(run_dir))

    def test_wall_clock_limit(self):
        t0 = time.time()
        proc, _ = self.start([sys.executable, "-c", "import time; time.sleep(60)"], wall=1)
        self.finish(proc, timeout=30)
        self.assertLess(time.time() - t0, 25)
        self.assertNotEqual(proc.returncode, 0)

    def test_sigterm_reaches_the_agent(self):
        proc, _ = self.start([sys.executable, "-c", "import time; time.sleep(60)"])
        time.sleep(1.0)
        proc.send_signal(signal.SIGTERM)
        self.finish(proc)
        self.assertEqual(proc.returncode, 128 + signal.SIGTERM)

    def test_a_header_that_points_elsewhere_is_refused(self):
        for run_dir in ("/tmp/run.0123456789abcdef", os.path.join(self.ws, "other"), os.path.join(self.ws, "run.0123456789abcdef", "..", "run.0123456789abcdef"), os.path.join(self.ws, "sub", "run.0123456789abcdef")):
            proc, _ = self.start([sys.executable, "-c", "print(1)"], run_dir=run_dir)
            _, err = self.finish(proc)
            self.assertEqual(proc.returncode, 97, (run_dir, err))

    def test_staged_entries_must_be_plain_files(self):
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w") as tar:
            info = tarfile.TarInfo("../escape")
            info.size = 1
            tar.addfile(info, io.BytesIO(b"x"))
        with self.assertRaises(sup.Refused):
            sup.extract_staged(buf.getvalue(), self.ws)
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w") as tar:
            info = tarfile.TarInfo("link")
            info.type = tarfile.SYMTYPE
            info.linkname = "/etc/passwd"
            tar.addfile(info)
        with self.assertRaises(sup.Refused):
            sup.extract_staged(buf.getvalue(), self.ws)


if __name__ == "__main__":
    unittest.main()
