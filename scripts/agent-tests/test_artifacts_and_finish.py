"""scripts/agent-artifacts.py (redact before upload) and scripts/translate-finish.mjs (a quarantined shard contributes nothing)."""
import json
import os
import shutil
import subprocess
import tempfile
import unittest

import _load

artifacts = _load.load_script("agent-artifacts")
FINISH = os.path.join(_load.SCRIPTS, "translate-finish.mjs")
TOKEN = "ghp_" + "Ab3dE6gH9jK2mN5pQ8sT1vX4zC7fR0wY3bUa"[:36]
ANTHROPIC = "sk-ant-oat01-" + "Qw3Er5Ty7Ui9Op1As3Df5Gh7Jk9Lz1Xc3Vb5Nm7"


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        fh.write(text)


def read(path):
    with open(path) as fh:
        return fh.read()


class Artifacts(unittest.TestCase):
    def setUp(self):
        self.out = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.out, True)

    def test_a_clean_directory_is_untouched(self):
        write(os.path.join(self.out, "bridge.log"), "listening on 4125\n")
        write(os.path.join(self.out, "bank.jsonl"), '{"name":"a","proof":"by simp"}\n')
        self.assertEqual(artifacts.main([self.out]), 0)
        self.assertEqual(read(os.path.join(self.out, "bridge.log")), "listening on 4125\n")

    def test_secrets_in_logs_and_traces_are_redacted_in_place(self):
        write(os.path.join(self.out, "bridge.log"), "auth failed with %s for user\n" % TOKEN)
        write(os.path.join(self.out, "trace", "1-1-prover-ab.jsonl"), json.dumps({"type": "assistant", "text": "export CLAUDE_CODE_OAUTH_TOKEN=%s" % ANTHROPIC}) + "\n")
        self.assertEqual(artifacts.main([self.out]), 0)
        for rel in ("bridge.log", "trace/1-1-prover-ab.jsonl"):
            text = read(os.path.join(self.out, rel))
            self.assertNotIn(TOKEN, text)
            self.assertNotIn(ANTHROPIC, text)
            self.assertIn("[REDACTED:", text)
        json.loads(read(os.path.join(self.out, "trace", "1-1-prover-ab.jsonl")))

    def test_a_bank_record_with_a_secret_is_set_aside_and_the_others_stay(self):
        good = json.dumps({"name": "good", "proof": "by simp"})
        bad = json.dumps({"name": "bad", "proof": "-- key %s" % TOKEN})
        write(os.path.join(self.out, "bank.jsonl"), good + "\n" + bad + "\n")
        self.assertEqual(artifacts.main([self.out]), 0)
        self.assertEqual(read(os.path.join(self.out, "bank.jsonl")), good + "\n")
        rejected = read(os.path.join(self.out, "quarantine", "bank.rejected.jsonl"))
        self.assertIn('"bad"', rejected)
        self.assertNotIn(TOKEN, rejected)

    def test_json_files_still_parse_after_redaction(self):
        write(os.path.join(self.out, "results.jsonl"), json.dumps({"id": 1, "outcome": "unresolved", "error": "token was %s" % TOKEN}) + "\n")
        write(os.path.join(self.out, "prefix-cache.json"), json.dumps({"a.lean": {"note": "url https://user:hunter2hunter2@example.com/x"}}))
        self.assertEqual(artifacts.main([self.out]), 0)
        json.loads(read(os.path.join(self.out, "results.jsonl")))
        json.loads(read(os.path.join(self.out, "prefix-cache.json")))

    def test_a_file_too_large_to_scan_blocks_the_upload(self):
        write(os.path.join(self.out, "huge.log"), "x\n")
        saved = artifacts.MAX_BYTES
        artifacts.MAX_BYTES = 1
        self.addCleanup(setattr, artifacts, "MAX_BYTES", saved)
        write(os.path.join(self.out, "huge.log"), "xx\n")
        self.assertEqual(artifacts.main([self.out]), 1)

    def test_not_a_directory_is_bad_input(self):
        self.assertEqual(artifacts.main([os.path.join(self.out, "nope")]), 2)


@unittest.skipUnless(shutil.which("node"), "node is needed")
class Finish(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        self.shards = os.path.join(self.root, "shards")
        self.addCleanup(shutil.rmtree, self.root, True)

    def shard(self, n, name, *, marker=None, report=None):
        d = os.path.join(self.shards, "shard-%d" % n)
        write(os.path.join(d, "results.jsonl"), json.dumps({"id": n, "name": name, "outcome": "agentic"}) + "\n")
        write(os.path.join(d, "bank.jsonl"), json.dumps({"name": name, "statement": "theorem %s" % name}) + "\n")
        write(os.path.join(d, "plan.json"), json.dumps({"todo": 1, "limited": False}))
        write(os.path.join(d, "prefix-cache.json"), json.dumps({"f%d.lean" % n: {"checkedAt": "2026-10-09"}}))
        if marker:
            write(os.path.join(d, "QUARANTINED"), "{}")
        if report is not None:
            write(os.path.join(d, "trace-report.json"), report)

    def finish(self):
        env = dict(os.environ, TRANSLATE_FINISH_ROOT=self.root + "/")
        return subprocess.run(["node", FINISH, "lib", "42", self.shards, "agent", "1"], env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)

    def test_a_quarantined_shard_contributes_nothing_but_its_plan(self):
        self.shard(0, "good")
        self.shard(1, "marked", marker=True)
        self.shard(2, "failed_report", report=json.dumps({"ok": False}))
        self.shard(3, "unreadable_report", report="{not json")
        self.shard(4, "clean_report", report=json.dumps({"ok": True}))
        res = self.finish()
        self.assertEqual(res.returncode, 0, res.stderr)
        banked = read(os.path.join(self.root, "data", "bank", "lib", "42.jsonl"))
        self.assertEqual(sorted(json.loads(l)["name"] for l in banked.split("\n") if l), ["clean_report", "good"])
        ledger = [json.loads(l)["name"] for l in read(os.path.join(self.root, "data", "translate", "lib.jsonl")).split("\n") if l]
        self.assertEqual(sorted(ledger), ["clean_report", "good"])
        cache = json.loads(read(os.path.join(self.root, "data", "translate", "lib.prefix-cache.json")))
        self.assertEqual(sorted(cache), ["f0.lean", "f4.lean"])
        status = json.loads(read(os.path.join(self.root, "data", "translate", "lib.status.json")))["agent"]
        self.assertEqual(status["todo"], 5, "the quarantined shards' entries still count as selected")
        self.assertEqual(status["left"], 3, "...and as not settled, so the next run takes them")
        self.assertEqual(res.stdout.count("::warning::"), 3)


if __name__ == "__main__":
    unittest.main()
