#!/usr/bin/env python3
"""After the agent step: audit every trace the bridge tee'd (EMISSARY_TRACE_DIR) against the translator tool policy.

    python3 scripts/agent-trace-gate.py out/trace --out out/trace-report.json --results out/results.jsonl --quarantine out

Each file is the stdout of one Claude CLI run (stream-json lines). warden.toolpolicy.audit_trace_claude reads it and reports
every tool the session was given and every tool it called; a tool outside the policy, a web tool, a path outside the workspace
or a shell the policy does not allow is a violation. The policy is agent_policy.audit_policy: MCP tools of the translation
servers only, and Bash only when EMISSARY_JAIL=1 (the jail was proven, so the agent had one). When a shell is allowed, each
shell command is still counted in the report; it is not a violation, because the jail is what confines it.

Exit status: 0 clean, 1 at least one violation (or evidence missing), 2 bad input. With --quarantine DIR a failure also moves the
shard's bank, results and prefix cache into DIR/quarantine/, leaves empty files in their place and writes DIR/QUARANTINED, which
scripts/translate-finish.mjs reads: a shard whose agent did something outside the policy contributes nothing to the bank, and
its entries stay unsettled for the next run.

Missing evidence is a violation too: if results.jsonl records entries the agent worked on (outcome agentic or unresolved) but no
trace file exists, nobody can say what the agent did.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import agent_policy  # noqa: E402
from warden.toolpolicy import audit_trace_claude  # noqa: E402

AGENT_OUTCOMES = ("agentic", "unresolved")
QUARANTINE_FILES = ("bank.jsonl", "results.jsonl", "prefix-cache.json")


def trace_files(directory: str):
    if not os.path.isdir(directory):
        return []
    return sorted(os.path.join(directory, f) for f in os.listdir(directory) if f.endswith(".jsonl") and os.path.isfile(os.path.join(directory, f)))


def kind_of(path: str) -> str:
    parts = os.path.basename(path)[: -len(".jsonl")].split("-")
    return parts[2] if len(parts) >= 4 else "unknown"


def agent_entries(results_path):
    n = 0
    if results_path and os.path.isfile(results_path):
        with open(results_path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                try:
                    if json.loads(line).get("outcome") in AGENT_OUTCOMES:
                        n += 1
                except ValueError:
                    continue
    return n


def audit_directory(directory, *, bash: bool, workspace: str, results_path=None, extra_tools=agent_policy.AUDIT_EXTRA_TOOLS):
    """Pure-ish core: returns the report dict. ``bash`` says whether the policy allows a shell (the jail was proven)."""
    policy = agent_policy.audit_policy(bash, extra_tools)
    files = trace_files(directory)
    report = {"ok": True, "jail": bash, "policy": policy.name, "traces": [], "violations": [], "shell_commands": 0, "empty_traces": 0}
    for path in files:
        if os.path.getsize(path) == 0:
            report["empty_traces"] += 1  # the CLI printed nothing: no tool can have run
            report["traces"].append({"file": os.path.basename(path), "kind": kind_of(path), "ok": True, "empty": True})
            continue
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            rep = audit_trace_claude(fh, policy, [workspace])
        violations = [v for v in rep.violations if not (bash and v.rule == "shell-command")]
        report["shell_commands"] += sum(1 for v in rep.violations if v.rule == "shell-command") if bash else 0
        errors = [v for v in violations if v.severity == "error"]
        entry = {
            "file": os.path.basename(path), "kind": kind_of(path), "ok": not errors, "events": rep.events, "calls_by_tool": dict(sorted(rep.calls_by_tool.items())),
            "denied": rep.denied, "init_tools": rep.init_tools, "violations": [v.to_dict() for v in violations],
        }
        report["traces"].append(entry)
        for v in violations:
            d = v.to_dict()
            d["file"] = os.path.basename(path)
            report["violations"].append(d)
        if errors:
            report["ok"] = False
    worked = agent_entries(results_path)
    if worked and not files:
        report["ok"] = False
        report["violations"].append({
            "rule": "no-trace-for-agent-run", "severity": "error", "file": "",
            "message": "results.jsonl records %d entries the agent worked on, and there is no trace to audit" % worked, "detail": "",
        })
    report["trace_files"] = len(files)
    return report


def quarantine(out_dir: str, report: dict) -> list:
    """Move the shard's contributions aside and leave empty files; write the marker. Returns the moved names."""
    qdir = os.path.join(out_dir, "quarantine")
    os.makedirs(qdir, exist_ok=True)
    moved = []
    for name in QUARANTINE_FILES:
        src = os.path.join(out_dir, name)
        if os.path.isfile(src):
            shutil.move(src, os.path.join(qdir, name))
            moved.append(name)
        if name != "prefix-cache.json":
            open(src, "w").close()
    with open(os.path.join(out_dir, "QUARANTINED"), "w", encoding="utf-8") as fh:
        json.dump({"reason": "agent trace gate", "violations": report["violations"][:50], "moved": moved}, fh, indent=2, sort_keys=True)
        fh.write("\n")
    return moved


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("trace_dir")
    ap.add_argument("--out", help="write the JSON report here")
    ap.add_argument("--results", help="the shard's results.jsonl, to demand a trace when the agent worked")
    ap.add_argument("--workspace", default="/home/agent", help="the agent's workspace, for the path check")
    ap.add_argument("--quarantine", metavar="OUT_DIR", help="on failure, move this shard's bank/results/prefix cache aside")
    ap.add_argument("--allow-tool", action="append", help="a built-in tool the audit accepts in a session (default: %s)" % ", ".join(agent_policy.AUDIT_EXTRA_TOOLS))
    ns = ap.parse_args(argv)
    extra = tuple(ns.allow_tool) if ns.allow_tool else agent_policy.AUDIT_EXTRA_TOOLS
    try:
        report = audit_directory(ns.trace_dir, bash=agent_policy.bash_allowed(), workspace=ns.workspace, results_path=ns.results, extra_tools=extra)
    except (OSError, ValueError) as exc:
        print("agent-trace-gate: %s" % exc, file=sys.stderr)
        return 2
    if not report["ok"] and ns.quarantine:
        report["quarantined"] = quarantine(ns.quarantine, report)
    text = json.dumps(report, indent=2, sort_keys=True)
    if ns.out:
        os.makedirs(os.path.dirname(os.path.abspath(ns.out)), exist_ok=True)
        with open(ns.out, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
    calls = sum(sum(t.get("calls_by_tool", {}).values()) for t in report["traces"])
    print("agent-trace-gate: %s: %d trace(s), %d tool call(s), %d shell command(s), %d violation(s)%s" % (
        "ok" if report["ok"] else "VIOLATIONS", report["trace_files"], calls, report["shell_commands"], len(report["violations"]),
        " (policy %s)" % report["policy"]))
    for v in report["violations"][:20]:
        print("  [%s] %s (%s) %s" % (v["rule"], v["message"], v.get("file", ""), v.get("detail", "")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
