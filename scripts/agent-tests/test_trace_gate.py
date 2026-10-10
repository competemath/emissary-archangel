"""scripts/agent-trace-gate.py: stream-json traces audited against the translator policy; a violation quarantines the shard."""
import json
import os
import shutil
import tempfile
import unittest

import _load

gate = _load.load_script("agent-trace-gate")


def load_json(path):
    with open(path) as fh:
        return json.load(fh)


def init_event(tools):
    return {"type": "system", "subtype": "init", "tools": tools, "permissionMode": "bypassPermissions"}


def call(tid, name, **inp):
    return {"type": "assistant", "message": {"content": [{"type": "tool_use", "id": tid, "name": name, "input": inp}]}}


def result(tid, text="ok", error=False):
    return {"type": "user", "message": {"content": [{"type": "tool_result", "tool_use_id": tid, "content": text, "is_error": error}]}}


class Gate(unittest.TestCase):
    def setUp(self):
        self.out = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.out, True)
        self.traces = os.path.join(self.out, "trace")
        os.mkdir(self.traces)
        self.n = 0

    def trace(self, events, kind="prover"):
        self.n += 1
        path = os.path.join(self.traces, "1700000000%03d-1-%s-abcdef12.jsonl" % (self.n, kind))
        with open(path, "w") as fh:
            for e in events:
                fh.write((e if isinstance(e, str) else json.dumps(e)) + "\n")
        return path

    def audit(self, bash=False, **kw):
        return gate.audit_directory(self.traces, bash=bash, workspace="/home/agent", **kw)

    def test_mcp_only_session_is_clean(self):
        self.trace([init_event(["mcp__Leak_IV__verify_full_script", "mcp__architect__lean_compile"]), call("t1", "mcp__Leak_IV__verify_full_script", script="x"), result("t1")])
        rep = self.audit()
        self.assertTrue(rep["ok"], rep)
        self.assertEqual(rep["traces"][0]["calls_by_tool"], {"mcp__Leak_IV__verify_full_script": 1})

    def test_a_shell_is_a_violation_without_the_jail_and_only_counted_with_it(self):
        events = [init_event(["Bash", "mcp__Leak_IV__verify_full_script"]), call("t1", "Bash", command="python3 -c 1"), result("t1")]
        self.trace(events)
        rep = self.audit(bash=False)
        self.assertFalse(rep["ok"])
        self.assertIn("shell-tool", {v["rule"] for v in rep["violations"]})
        rep = self.audit(bash=True)
        self.assertTrue(rep["ok"], rep["violations"])
        self.assertEqual(rep["shell_commands"], 1)

    def test_web_write_and_unknown_tools_are_violations_even_with_the_jail(self):
        for tool in ("WebFetch", "WebSearch", "Write", "Edit", "Task", "Read", "SomethingNew", "mcp__other__tool"):
            shutil.rmtree(self.traces)
            os.mkdir(self.traces)
            self.trace([init_event(["mcp__Leak_IV__verify_full_script"]), call("t1", tool, x="y"), result("t1")])
            self.assertFalse(self.audit(bash=True)["ok"], tool)

    def test_a_tool_announced_in_the_session_but_not_used_is_a_violation(self):
        self.trace([init_event(["WebSearch", "mcp__Leak_IV__verify_full_script"])])
        self.assertFalse(self.audit()["ok"])

    def test_a_denied_attempt_is_a_warning_not_a_failure(self):
        self.trace([init_event(["mcp__Leak_IV__verify_full_script"]), call("t1", "Bash", command="ls"), result("t1", "Permission denied: tool not available", error=True)])
        rep = self.audit()
        self.assertTrue(rep["ok"], rep["violations"])
        self.assertTrue(rep["violations"], "the attempt is still reported")

    def test_empty_and_unparsable_traces(self):
        self.trace([])  # the CLI printed nothing
        rep = self.audit()
        self.assertTrue(rep["ok"])
        self.assertEqual(rep["empty_traces"], 1)
        self.trace(["not json at all"])
        self.assertFalse(self.audit()["ok"], "a trace with no parsable event is no evidence")

    def test_agent_work_without_any_trace_is_a_violation(self):
        results = os.path.join(self.out, "results.jsonl")
        with open(results, "w") as fh:
            fh.write(json.dumps({"id": 1, "outcome": "mechanical"}) + "\n")
        self.assertTrue(self.audit(results_path=results)["ok"], "a mechanical shard needs no trace")
        with open(results, "a") as fh:
            fh.write(json.dumps({"id": 2, "outcome": "agentic"}) + "\n")
        rep = self.audit(results_path=results)
        self.assertFalse(rep["ok"])
        self.assertEqual(rep["violations"][0]["rule"], "no-trace-for-agent-run")

    def test_quarantine_moves_the_shards_contributions_aside(self):
        for name, text in (("bank.jsonl", '{"name":"a"}\n'), ("results.jsonl", '{"id":1,"outcome":"agentic"}\n'), ("prefix-cache.json", "{}"), ("plan.json", "{}")):
            with open(os.path.join(self.out, name), "w") as fh:
                fh.write(text)
        self.trace([init_event(["Bash"]), call("t1", "Bash", command="curl evil")])
        rc = gate.main([self.traces, "--out", os.path.join(self.out, "trace-report.json"), "--quarantine", self.out, "--results", os.path.join(self.out, "results.jsonl")])
        self.assertEqual(rc, 1)
        self.assertEqual(os.path.getsize(os.path.join(self.out, "bank.jsonl")), 0)
        self.assertEqual(os.path.getsize(os.path.join(self.out, "results.jsonl")), 0)
        self.assertFalse(os.path.exists(os.path.join(self.out, "prefix-cache.json")))
        self.assertTrue(os.path.exists(os.path.join(self.out, "plan.json")), "the plan still says what was selected")
        self.assertTrue(os.path.exists(os.path.join(self.out, "quarantine", "bank.jsonl")))
        self.assertTrue(os.path.exists(os.path.join(self.out, "QUARANTINED")))
        report = load_json(os.path.join(self.out, "trace-report.json"))
        self.assertFalse(report["ok"])

    def test_clean_run_exits_zero_and_writes_a_report(self):
        self.trace([init_event(["mcp__Leak_IV__verify_full_script"]), call("t1", "mcp__Leak_IV__verify_full_script", script="x"), result("t1")])
        rc = gate.main([self.traces, "--out", os.path.join(self.out, "trace-report.json"), "--quarantine", self.out])
        self.assertEqual(rc, 0)
        self.assertFalse(os.path.exists(os.path.join(self.out, "QUARANTINED")))
        self.assertTrue(load_json(os.path.join(self.out, "trace-report.json"))["ok"])

    def test_the_jail_switch_is_the_environment_variable(self):
        old = os.environ.pop("EMISSARY_JAIL", None)
        self.addCleanup(lambda: os.environ.__setitem__("EMISSARY_JAIL", old) if old is not None else os.environ.pop("EMISSARY_JAIL", None))
        self.trace([init_event(["Bash"]), call("t1", "Bash", command="echo hi"), result("t1")])
        self.assertEqual(gate.main([self.traces]), 1)
        os.environ["EMISSARY_JAIL"] = "1"
        self.assertEqual(gate.main([self.traces]), 0)


if __name__ == "__main__":
    unittest.main()
