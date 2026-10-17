"""What the jailed translation agent may be and do: one place, read by the wrapper (agent-run.py) and the trace gate.

The bridge (public/local-claude-bridge.mjs, claudeToolArgs) decides which tools each spawn asks for; the wrapper refuses an
argv that asks for more than this module allows, and agent-trace-gate.py checks after the run that the agent used nothing
else. The three must agree, and scripts/agent-tests/test_bridge_tools.py checks that they do.

Credit: the Tau Ceti Project (TauCetiReview PR #123) for the lesson that a tool flag is not a tool set; see docs/agent-security.md.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from warden.toolpolicy import ToolPolicy  # noqa: E402

# MCP servers the translation run hands the agent (scripts/run-recurse.mjs) and the bridge's own architect server. The name of
# a tool is mcp__<server>__<tool>; a pattern names a whole server.
MCP_PATTERNS = ("mcp__Leak_IV", "mcp__Archangel_Emissary_0_0_1", "mcp__Leak_I", "mcp__architect")

# Built-in tools that can show up in a session that was started with an empty tool set because the CLI itself lists them next
# to MCP servers: read-only access to the resources the servers expose. Used only when auditing a trace; a launch may never
# ask for them. If a real run's trace shows another name, the gate fails and says which; add it here deliberately.
AUDIT_EXTRA_TOOLS = ("ListMcpResourcesTool", "ReadMcpResourceTool")

# Per-invocation ceilings. The bridge has the same numbers (AGENT_MAX_USD_DEFAULT, AGENT_MAX_TURNS_DEFAULT) and a test pins them.
DEFAULT_MAX_USD = 20.0
DEFAULT_MAX_TURNS = 400
DEFAULT_WALL_SECONDS = 21000


def bash_allowed(environ=None) -> bool:
    """A shell is allowed only inside the jail (EMISSARY_JAIL=1), never otherwise."""
    env = os.environ if environ is None else environ
    return env.get("EMISSARY_JAIL") == "1"


def argv_policy(bash: bool) -> ToolPolicy:
    """The policy a launch argv is checked against: MCP only, plus Bash inside the jail. The permission bypass is allowed
    because the MCP tools need it; check_claude_argv still demands a restricted --tools set next to it."""
    return ToolPolicy(
        "translator-shell" if bash else "translator",
        builtin_tools=("Bash",) if bash else (),
        mcp_patterns=MCP_PATTERNS,
        allow_shell=bash,
        allow_skip_permissions=True,
    )


def audit_policy(bash: bool, extra_tools=AUDIT_EXTRA_TOOLS) -> ToolPolicy:
    """The policy a finished trace is checked against: the launch policy plus the read-only MCP resource tools."""
    tools = (("Bash",) if bash else ()) + tuple(extra_tools)
    return ToolPolicy(
        "translator-audit-shell" if bash else "translator-audit",
        builtin_tools=tools,
        mcp_patterns=MCP_PATTERNS,
        allow_shell=bash,
        allow_skip_permissions=True,
    )
