"""One rule for the tentative record files of a library, on the REAL sources.json (every registered library) and on the real workflows.

flt-anthropic's bump (5 Nov 2026) planned 30,961 modules with 0 entries and stopped in compose: the bump workflows read data/tentative/<key>.jsonl and <key>/*.jsonl, but
flt-anthropic's records are the three files sources.json lists under `tentative`. The setup workflows had always read that list.
"""
import glob
import json
import os
import random
import re
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts" / "bump"))
import tentative_files as tf  # noqa: E402

SOURCES = json.load(open(ROOT / "sources.json"))
KEYS = sorted(SOURCES["sources"])


def setup_rule(key):
    """What the setup workflows read (their inline python: s.get('tentative', [KEY + '.jsonl']))."""
    return list(SOURCES["sources"][key].get("tentative", [key + ".jsonl"]))


def old_bump_rule(key, root):
    """What the bump workflows read before: <key>.jsonl and <key>/*.jsonl, whatever sources.json says."""
    return [f"{root}/data/tentative/{key}.jsonl", f"{root}/data/tentative/{key}/*.jsonl"]


class RealLibraries(unittest.TestCase):
    def test_the_registry_is_the_real_one(self):
        self.assertGreaterEqual(len(KEYS), 150)
        listed = [k for k in KEYS if "tentative" in SOURCES["sources"][k]]
        self.assertIn("flt-anthropic", listed)
        self.assertGreaterEqual(len(listed), 10)

    def test_the_bump_reads_every_file_the_setup_reads_for_every_library(self):
        for key in KEYS:
            want = {f"/data/tentative/{n}" for n in setup_rule(key)}
            self.assertTrue(want <= set(tf.sparse_paths(SOURCES, key)), key)
            self.assertIn(f"/data/tentative/{key}/", tf.sparse_paths(SOURCES, key), key)
            got = tf.globs(SOURCES, key, "T")
            for n in setup_rule(key):
                self.assertIn(f"T/data/tentative/{n}", got, (key, n))

    def test_on_disk_exactly_the_listed_files_that_exist_and_the_directory_are_found(self):
        rnd = random.Random(20261105)
        cases = 0
        with tempfile.TemporaryDirectory() as d:
            for key in KEYS:
                names = setup_rule(key)
                for variant in range(20):  # which of the listed files exist, and whether the directory holds files
                    base = Path(d) / f"{key}-{variant}" / "data" / "tentative"
                    (base / key).mkdir(parents=True)
                    exist = [n for n in names if rnd.random() < 0.7 or variant == 0]
                    for n in exist:
                        (base / n).write_text("{}\n")
                    inside = [f"part{i}.jsonl" for i in range(rnd.randint(0, 3))]
                    for n in inside:
                        (base / key / n).write_text("{}\n")
                    (base / key / "notes.txt").write_text("not a record file")
                    got = tf.files(SOURCES, key, str(Path(d) / f"{key}-{variant}"))
                    want = sorted(str(base / n) for n in exist) + sorted(str(base / key / n) for n in inside)
                    self.assertEqual(sorted(got), sorted(want), (key, variant))
                    cases += 1
        self.assertGreaterEqual(cases, 3000)
        print(f"tentative_files: {cases} real-library layouts checked ({len(KEYS)} libraries)")

    def test_the_old_bump_rule_is_caught_by_the_same_check(self):
        """The mutant: the rule the bump workflows had. It must miss files for the libraries that list their own."""
        missed = []
        with tempfile.TemporaryDirectory() as d:
            for key in KEYS:
                base = Path(d) / key / "data" / "tentative"
                base.mkdir(parents=True)
                for n in setup_rule(key):
                    (base / n).parent.mkdir(parents=True, exist_ok=True)
                    (base / n).write_text("{}\n")
                found = {p for pat in old_bump_rule(key, str(Path(d) / key)) for p in glob.glob(pat)}
                if found != {str(base / n) for n in setup_rule(key)}:
                    missed.append(key)
        def reachable_by_old_rule(key, n):
            return n == key + ".jsonl" or (n.startswith(key + "/") and n.endswith(".jsonl") and "/" not in n[len(key) + 1 :])

        expected = sorted(k for k in KEYS if not all(reachable_by_old_rule(k, n) for n in setup_rule(k)))
        self.assertIn("flt-anthropic", missed)
        self.assertGreaterEqual(len(missed), 2)
        self.assertEqual(sorted(missed), expected)

    def test_the_command_line_prints_what_the_functions_return(self):
        import subprocess

        for key in ("flt-anthropic", "azurite", "lean-pool"):
            out = subprocess.run([sys.executable, str(ROOT / "scripts" / "bump" / "tentative_files.py"), "sparse", str(ROOT / "sources.json"), key], capture_output=True, text=True, check=True).stdout.strip()
            self.assertEqual(out.split(" "), tf.sparse_paths(SOURCES, key))
            out = subprocess.run([sys.executable, str(ROOT / "scripts" / "bump" / "tentative_files.py"), "globs", str(ROOT / "sources.json"), key, "../tengoku"], capture_output=True, text=True, check=True).stdout.strip()
            self.assertEqual(out.split(","), tf.globs(SOURCES, key, "../tengoku"))
        bad = subprocess.run([sys.executable, str(ROOT / "scripts" / "bump" / "tentative_files.py"), "sparse", str(ROOT / "sources.json"), "no-such-library"], capture_output=True, text=True)
        self.assertEqual(bad.returncode, 1)


class RealWorkflows(unittest.TestCase):
    WF = ROOT / ".github" / "workflows"

    def test_no_bump_workflow_reads_only_key_jsonl(self):
        for name in ("bump-sharded.yml", "bump-shard.yml", "bump-library.yml"):
            text = (self.WF / name).read_text()
            self.assertNotIn('data/tentative/$KEY.jsonl', text, name)
            self.assertNotIn('tentative/{key}.jsonl', text, name)
            self.assertIn("tentative_files.py", text, name)

    def test_every_bump_job_that_reads_the_records_has_sources_json_and_the_script(self):
        # the sparse checkouts of the jobs that call tentative_files.py hold /scripts/ and /sources.json
        for name in ("bump-sharded.yml", "bump-shard.yml", "bump-library.yml"):
            text = (self.WF / name).read_text()
            self.assertRegex(text, r'"/scripts/"', name)
            self.assertRegex(text, r'"/sources\.json"|/sources\.json', name)

    def test_the_setup_workflows_still_use_the_listed_files(self):
        for name in ("setup-sharded.yml", "setup-auto.yml", "setup-libraries.yml"):
            text = (self.WF / name).read_text()
            self.assertTrue(re.search(r"s\.get\('tentative', \[os\.environ\['KEY'\] \+ '\.jsonl'\]\)", text), name)


if __name__ == "__main__":
    unittest.main()
