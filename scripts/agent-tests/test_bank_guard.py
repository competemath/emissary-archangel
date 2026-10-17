"""scripts/bank-guard.py against a real (local) git repository standing in for the tree."""
import json
import os
import shutil
import subprocess
import tempfile
import unittest

import _load

guard = _load.load_script("bank-guard")
POLICY = os.path.join(_load.SCRIPTS, "agent-paths.json")
GIT = ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false"]


def git(repo, *args):
    return subprocess.run(GIT + ["-C", repo] + list(args), check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True).stdout.strip()


def marker(target):
    return '<!--tengoku-target:v1 {"actor":"emissary-archangel","base":"main","target":"%s"}-->' % target


class Guard(unittest.TestCase):
    def setUp(self):
        self.repo = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.repo, True)
        git(self.repo, "init", "-q", "-b", "main")
        os.makedirs(os.path.join(self.repo, "data", "staging", "lib"))
        with open(os.path.join(self.repo, "data", "staging", "lib", "old.jsonl"), "w") as fh:
            fh.write('{"name":"old"}\n')
        with open(os.path.join(self.repo, "README"), "w") as fh:
            fh.write("x\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "base")
        git(self.repo, "branch", "origin_main")
        self.base = "origin_main"
        self.target = "emissary-archangel:stage/lib/20261009T000000Z-000"
        self.body = os.path.join(self.repo, "..", "body-%d.md" % os.getpid())
        self.addCleanup(lambda: os.path.exists(self.body) and os.unlink(self.body))
        self.write_body("Banked. \n\n" + marker(self.target))

    def write_body(self, text):
        with open(self.body, "w") as fh:
            fh.write(text)

    def commit(self, rel, content='{"name":"new","statement":"theorem new : True"}\n', mode=None):
        git(self.repo, "switch", "-q", "-C", "bank/lib/x", self.base)
        path = os.path.join(self.repo, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as fh:
            fh.write(content)
        if mode:
            os.chmod(path, mode)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "stage")
        return path

    def run_guard(self, path, title="Stage lib: 1 record (x)", **over):
        args = ["--title", title, "--body-file", self.body, "--branch", "bank/lib/x", "--base", "main", "--expect-target", self.target, "--file", path,
                "--repo-dir", self.repo, "--base-rev", self.base, "--head-rev", "HEAD", "--policy", POLICY]
        args += [a for k, v in over.items() for a in (k, v)]
        return guard.main(args)

    def test_a_staging_file_with_a_marker_passes(self):
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl")
        self.assertEqual(self.run_guard(path), 0)

    def test_a_secret_in_a_record_is_refused(self):
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl", '{"name":"n","proof":"-- ' + "ghp_" + "A1b2C3d4" * 5 + '"}\n')
        self.assertEqual(self.run_guard(path), 1)

    def test_a_secret_in_the_body_is_refused(self):
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl")
        self.write_body("token sk-ant-api03-" + "Zz9" * 20 + "\n\n" + marker(self.target))
        self.assertEqual(self.run_guard(path), 1)

    def test_marker_must_exist_and_name_the_expected_target(self):
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl")
        self.write_body("no marker here")
        self.assertEqual(self.run_guard(path), 1)
        self.write_body("x\n\n" + marker("emissary-archangel:stage/other/1"))
        self.assertEqual(self.run_guard(path), 1)
        self.write_body("x\n\n" + marker(self.target) + "\n" + marker(self.target))
        self.assertEqual(self.run_guard(path), 1)

    def test_paths_outside_the_policy_are_refused(self):
        for rel in ("data/trusted/lib.jsonl", "data/staging/lib.jsonl", "data/staging/lib/sub/x.jsonl", ".github/workflows/x.yml", "scripts/x.mjs", "data/staging/lib/x.txt"):
            path = self.commit(rel)
            self.assertEqual(self.run_guard(path), 1, rel)

    def test_a_second_file_a_deletion_an_executable_and_a_symlink_are_refused(self):
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl")
        with open(os.path.join(self.repo, "data", "staging", "lib", "b.jsonl"), "w") as fh:
            fh.write("{}\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "second")
        self.assertEqual(self.run_guard(path), 1, "two files")
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl", mode=0o755)
        self.assertEqual(self.run_guard(path), 1, "executable")
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl")
        git(self.repo, "rm", "-q", "data/staging/lib/old.jsonl")
        git(self.repo, "commit", "-q", "-m", "delete")
        self.assertEqual(self.run_guard(path), 1, "deletion")
        git(self.repo, "switch", "-q", "-C", "bank/lib/x", self.base)
        os.symlink("/etc/passwd", os.path.join(self.repo, "data", "staging", "lib", "20261009T000000Z-000.jsonl"))
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "link")
        self.assertEqual(self.run_guard(os.path.join(self.repo, "README")), 1, "symlink (mode 120000)")

    def test_nothing_to_check_is_a_refusal_and_a_dry_run_skips_only_scope(self):
        path = self.commit("data/staging/lib/20261009T000000Z-000.jsonl")
        self.assertEqual(guard.main(["--title", "t", "--body-file", self.body, "--branch", "b", "--expect-target", self.target]), 2)
        self.assertEqual(guard.main(["--title", "Stage", "--body-file", self.body, "--branch", "bank/lib/x", "--expect-target", self.target, "--file", path, "--skip-scope"]), 0)

    def test_bank_flush_builds_the_marker_the_way_the_guard_reads_it(self):
        with open(os.path.join(_load.SCRIPTS, "bank-flush.mjs"), encoding="utf-8") as fh:
            source = fh.read()
        self.assertIn('JSON.stringify({ actor: "emissary-archangel", base: "main", target })', source, "keys in sorted order, as safegit.make_marker writes them")
        built = json.dumps({"actor": "emissary-archangel", "base": "main", "target": self.target}, separators=(",", ":"))
        self.assertEqual("<!--tengoku-target:v1 %s-->" % built, marker(self.target))


if __name__ == "__main__":
    unittest.main()
