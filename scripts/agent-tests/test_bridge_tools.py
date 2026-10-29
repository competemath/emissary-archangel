"""Regression test for the tool exposure of public/local-claude-bridge.mjs.

The bridge used to start the Claude CLI with --dangerously-skip-permissions and a deny-list (--disallowedTools WebSearch
WebFetch ...), with Bash on, the bridge's whole environment, and flags chosen by the page. This test fails if any spawn site
of the CLI goes back to that:

* warden's own scanner (`warden toolpolicy scan-source`) finds no bypass, allow-list or deny-list flag without a --tools set;
* every spawn of the CLI goes through spawnClaude, and every spawnClaude site takes its flags from claudeToolArgs (or buildArgs,
  which does) and names its kind;
* no deny-list, permission rule or permission-mode text is left in the code at all;
* the argv the bridge really builds, for every kind and every setting of the shell switches, passes warden's argv checker against
  the translator policy, and a shell appears only where the policy gives one.

BRIDGE_PATH=<file> runs the same checks on another copy of the bridge: on `git show origin/main:public/local-claude-bridge.mjs`
(the code before this change) every group below fails.
"""
import json
import os
import re
import subprocess
import sys
import unittest

import _load
import agent_policy
from warden import toolpolicy

BRIDGE = _load.BRIDGE
REGION_JS = os.path.join(_load.TESTS, "bridge-region.mjs")


def read_bridge():
    with open(BRIDGE, encoding="utf-8") as fh:
        return fh.read()


def code_only(text):
    """The source with comments blanked out (newlines kept), using warden's own lexer."""
    comments, _ = toolpolicy._lex(text, False)
    chars = list(text)
    for start, end in comments:
        for i in range(start, end):
            if chars[i] != "\n":
                chars[i] = " "
    return "".join(chars)


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def region_bounds(text):
    begin, end = text.find("// agent-jail:begin"), text.find("// agent-jail:end")
    return (begin, end) if 0 <= begin < end else (None, None)


def enclosing_function(code, pos):
    """Name and start of the top-level function declaration that contains ``pos`` (the bridge declares them at column 0)."""
    last = None
    for m in re.finditer(r"^(?:export\s+)?(?:async\s+)?function\s+(\w+)", code, re.M):
        if m.start() > pos:
            break
        last = m
    return (last.group(1), last.start()) if last else (None, 0)


def call_text(code, open_paren):
    depth = 0
    for i in range(open_paren, len(code)):
        if code[i] == "(":
            depth += 1
        elif code[i] == ")":
            depth -= 1
            if depth == 0:
                return code[open_paren : i + 1]
    return code[open_paren:]


class WardenScanner(unittest.TestCase):
    def test_scan_source_finds_nothing(self):
        env = dict(os.environ, PYTHONPATH=_load.SCRIPTS, PYTHONDONTWRITEBYTECODE="1")
        res = subprocess.run(
            [sys.executable, "-m", "warden", "toolpolicy", "scan-source", "--allow-skip-permissions", BRIDGE],
            env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, universal_newlines=True,
        )
        self.assertEqual(res.returncode, 0, "spawn sites without a --tools set:\n" + res.stdout)


class SpawnSites(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = read_bridge()
        cls.code = code_only(cls.text)
        cls.begin, cls.end = region_bounds(cls.text)

    def test_the_bridge_has_its_jail_region(self):
        self.assertIsNotNone(self.begin, "no agent-jail region: the spawn helpers are gone")

    def test_the_cli_is_started_in_one_place(self):
        raw = [m.start() for m in re.finditer(r"\bspawn\(\s*CLAUDE_BIN", self.code)]
        self.assertTrue(raw, "no spawn(CLAUDE_BIN ...) at all: spawnClaude is gone")
        outside = [line_of(self.code, p) for p in raw if not (self.begin is not None and self.begin < p < self.end)]
        self.assertEqual(outside, [], "spawn(CLAUDE_BIN ...) outside spawnClaude, at lines %s" % outside)
        self.assertEqual(len(raw), 1, "exactly one place may start the CLI")

    def test_nothing_else_executes_the_cli(self):
        bad = [line_of(self.code, m.start()) for m in re.finditer(r"\b(?:execFile|execFileAsync|exec|execSync|spawnSync)\(\s*CLAUDE_BIN", self.code)]
        self.assertEqual(bad, [])

    def test_every_spawn_site_takes_its_flags_from_claudeToolArgs_and_names_its_kind(self):
        sites = [m for m in re.finditer(r"\bspawnClaude\(", self.code) if not self.code[max(0, m.start() - 9) : m.start()].endswith("function ")]
        self.assertGreaterEqual(len(sites), 5, "expected the five spawn sites of the CLI plus --version")
        problems = []
        for m in sites:
            text = call_text(self.code, m.end() - 1)
            name, start = enclosing_function(self.code, m.start())
            where = "line %d (in %s)" % (line_of(self.code, m.start()), name)
            if re.search(r'\[\s*"--version"\s*\]', text):
                if 'kind: "version"' not in text:
                    problems.append("%s: --version without kind" % where)
                continue
            if not re.search(r"\bkind\s*[:,]", text):
                problems.append("%s: no kind" % where)
            body = self.code[start : m.start()]
            if re.match(r"(?:async\s+)?function\s+%s\(\s*args\b" % re.escape(name or ""), self.code[start : start + 200].replace("export ", "")):
                # the function receives its argv: every call of it must pass a buildArgs(...) result
                for call in re.finditer(r"\b%s\(" % re.escape(name), self.code):
                    if call.start() == start or self.code[max(0, call.start() - 9) : call.start()].endswith("function "):
                        continue
                    first = self.code[call.end() : call.end() + 120].lstrip()
                    if not first.startswith("buildArgs("):
                        problems.append("line %d: %s() is called with an argv that buildArgs did not build" % (line_of(self.code, call.start()), name))
            elif "claudeToolArgs(" not in body and "buildArgs(" not in body:
                problems.append("%s: its argv is not built with claudeToolArgs" % where)
        self.assertEqual(problems, [])

    def test_buildArgs_ends_every_argv_with_the_empty_tool_set(self):
        m = re.search(r"^function buildArgs\(.*?^}", self.code, re.M | re.S)
        self.assertIsNotNone(m)
        self.assertIn('claudeToolArgs("none")', m.group(0))
        for forbidden in ("allowedTools", "disallowedTools", "permissionMode", "strictMcpConfig"):
            self.assertNotIn(forbidden, m.group(0), "buildArgs still lets the caller choose %s" % forbidden)

    def test_no_deny_list_or_permission_rule_is_left(self):
        pat = re.compile(r"allowedTools|disallowedTools|allowed-tools|disallowed-tools|DISALLOWED_TOOLS|--permission-mode|bypassPermissions|PERMISSION_MODES")
        hits = ["line %d: %s" % (line_of(self.code, m.start()), m.group(0)) for m in pat.finditer(self.code)]
        self.assertEqual(hits, [])

    def test_the_permission_bypass_appears_only_inside_claudeToolArgs(self):
        names = {enclosing_function(self.code, m.start())[0] for m in re.finditer(r"--dangerously-skip-permissions", self.code)}
        self.assertEqual(names, {"claudeToolArgs"})

    def test_no_spawn_hands_the_bridge_environment_to_a_child(self):
        bad = [line_of(self.code, m.start()) for m in re.finditer(r"\.\.\.process\.env|env:\s*process\.env|shell:\s*true", self.code)]
        self.assertEqual(bad, [], "the bridge's environment (BRIDGE_TOKEN, GH_TOKEN, ...) must not be copied into a child")


class ArgvTheBridgeBuilds(unittest.TestCase):
    """What claudeToolArgs really returns, run in node, judged by warden.toolpolicy.check_claude_argv."""

    @classmethod
    def setUpClass(cls):
        res = subprocess.run(["node", REGION_JS, "tool-args"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, env=dict(os.environ, BRIDGE_PATH=BRIDGE))
        if res.returncode != 0:
            raise AssertionError("the jail region could not be loaded:\n" + res.stderr)
        cls.out = json.loads(res.stdout)

    def argv(self, flags, caps):
        return ["claude", "-p", "a prompt", "--output-format", "stream-json", "--verbose", "--mcp-config", "/run/mcp.json"] + flags + caps + ["--settings", "/run/settings.json"]

    def test_every_kind_passes_the_translator_policy_where_a_shell_is_allowed_and_only_there(self):
        expect_bash = {"plain": False, "allow_bash": True, "jail_with_wrapper": True, "jail_without_wrapper": False}
        for case, kinds in self.out.items():
            kinds = dict(kinds)
            caps = kinds.pop("caps")
            for kind, flags in kinds.items():
                shell = any(f.startswith("--tools=") and "Bash" in f for f in flags)
                self.assertEqual(shell, expect_bash[case] and kind in ("prover", "blind"), "%s/%s: tool flags %s" % (case, kind, flags))
                argv = self.argv(flags, caps)
                vs = toolpolicy.check_claude_argv(argv, agent_policy.argv_policy(bash=shell), run_dir="/run")
                self.assertEqual([str(v) for v in vs], [], "%s/%s: %s" % (case, kind, argv))
                if shell:
                    vs = toolpolicy.check_claude_argv(argv, agent_policy.argv_policy(bash=False), run_dir="/run")
                    self.assertIn("shell-tool", [v.rule for v in vs], "the no-shell policy must refuse a shell")

    def test_the_old_flag_combinations_are_refused(self):
        policy = agent_policy.argv_policy(bash=False)
        old = [
            ["claude", "-p", "x", "--mcp-config", "/run/mcp.json", "--strict-mcp-config", "--dangerously-skip-permissions"],
            ["claude", "-p", "x", "--mcp-config", "/run/mcp.json", "--strict-mcp-config", "--dangerously-skip-permissions", "--disallowedTools", "WebSearch", "WebFetch"],
            ["claude", "-p", "x", "--allowedTools", "Bash"],
            ["claude", "-p", "x", "--tools", "default", "--strict-mcp-config"],
        ]
        for argv in old:
            self.assertTrue(toolpolicy.check_claude_argv(argv, policy, run_dir="/run"), argv)

    def test_the_caps_are_in_every_argv(self):
        for case, kinds in self.out.items():
            self.assertEqual(kinds["caps"][0::2], ["--max-turns", "--max-budget-usd"], case)


if __name__ == "__main__":
    unittest.main()
