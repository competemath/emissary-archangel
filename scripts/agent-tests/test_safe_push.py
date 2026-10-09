"""scripts/safe-push.py against a real bare remote: it lands on a moved branch by rebasing, and it never overwrites."""
import os
import shutil
import subprocess
import tempfile
import unittest

import _load

safe = _load.load_script("safe-push")
GIT = ["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-c", "commit.gpgsign=false"]


def git(repo, *args, check=True):
    return subprocess.run(GIT + ["-C", repo] + list(args), check=check, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True).stdout.strip()


def commit_file(repo, name, text, message):
    with open(os.path.join(repo, name), "w") as fh:
        fh.write(text)
    git(repo, "add", name)
    git(repo, "commit", "-q", "-m", message)


class SafePush(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.root, True)
        self.bare = os.path.join(self.root, "remote.git")
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", self.bare], check=True)
        self.a = os.path.join(self.root, "a")
        self.b = os.path.join(self.root, "b")
        subprocess.run(["git", "clone", "-q", self.bare, self.a], check=True, stderr=subprocess.PIPE)
        commit_file(self.a, "base.txt", "base\n", "base")
        git(self.a, "branch", "-M", "main")
        git(self.a, "push", "-q", "origin", "main")
        subprocess.run(["git", "clone", "-q", self.bare, self.b], check=True, stderr=subprocess.PIPE)
        # the module builds a github.com URL; point the remote at the local bare repository instead
        self.saved = safe.remote_url
        safe.remote_url = lambda repo, token: self.bare
        self.addCleanup(setattr, safe, "remote_url", self.saved)

    def remote_head(self):
        return git(self.bare, "rev-parse", "main")

    def test_a_plain_push_lands(self):
        commit_file(self.b, "mine.txt", "x\n", "mine")
        self.assertEqual(safe.main(["--repo", self.b, "--remote-repo", "o/n", "--attempts", "1"]), 0)
        self.assertEqual(self.remote_head(), git(self.b, "rev-parse", "HEAD"))

    def test_when_the_branch_moved_it_rebases_onto_it_and_keeps_the_other_commit(self):
        commit_file(self.a, "other.txt", "o\n", "other shard")
        git(self.a, "push", "-q", "origin", "main")
        commit_file(self.b, "mine.txt", "x\n", "mine")
        self.assertEqual(safe.main(["--repo", self.b, "--remote-repo", "o/n", "--attempts", "1"]), 0)
        log = git(self.bare, "log", "--format=%s", "main").split("\n")
        self.assertEqual(log, ["mine", "other shard", "base"])

    def test_a_push_that_loses_the_race_between_fetch_and_push_is_refused_and_retried(self):
        commit_file(self.b, "mine.txt", "x\n", "mine")
        real_push_cas = safe.safegit.push_cas
        raced = []

        def racing(repo, remote, ref, new_sha, expected_old_sha, **kw):
            if not raced:  # another shard lands exactly between our fetch and our push
                raced.append(1)
                commit_file(self.a, "late.txt", "l\n", "late shard")
                git(self.a, "push", "-q", "origin", "main")
            return real_push_cas(repo, remote, ref, new_sha, expected_old_sha, **kw)

        safe.safegit.push_cas = racing
        self.addCleanup(setattr, safe.safegit, "push_cas", real_push_cas)
        sleeps = []
        self.assertEqual(safe.main(["--repo", self.b, "--remote-repo", "o/n", "--attempts", "3"], sleep=sleeps.append, rng=lambda: 0.0), 0)
        self.assertEqual(len(sleeps), 1, "one lost race, one retry")
        self.assertEqual(git(self.bare, "log", "--format=%s", "main").split("\n"), ["mine", "late shard", "base"])

    def test_it_never_force_pushes_over_a_rewritten_branch(self):
        # the remote branch is rewritten to an unrelated history between fetch and push: the lease must refuse, not overwrite
        commit_file(self.b, "mine.txt", "x\n", "mine")
        real_push_cas = safe.safegit.push_cas

        def rewriting(repo, remote, ref, new_sha, expected_old_sha, **kw):
            git(self.a, "reset", "-q", "--hard", "HEAD")
            commit_file(self.a, "evil.txt", "e\n", "rewritten")
            git(self.a, "push", "-q", "origin", "main", "--force")
            return real_push_cas(repo, remote, ref, new_sha, expected_old_sha, **kw)

        safe.safegit.push_cas = rewriting
        self.addCleanup(setattr, safe.safegit, "push_cas", real_push_cas)
        rc = safe.main(["--repo", self.b, "--remote-repo", "o/n", "--attempts", "1"], sleep=lambda s: None)
        self.assertEqual(rc, 1)
        self.assertEqual(git(self.bare, "log", "--format=%s", "main").split("\n")[0], "rewritten")
        self.assertNotIn("mine", git(self.bare, "log", "--format=%s", "main"))

    def test_nothing_to_push_is_success(self):
        self.assertEqual(safe.main(["--repo", self.b, "--remote-repo", "o/n", "--attempts", "1"]), 0)

    def test_bad_input(self):
        self.assertEqual(safe.main(["--repo", self.b, "--remote-repo", "nonsense"]), 2)
        self.assertEqual(safe.main(["--repo", self.b, "--remote-repo", "o/n", "--branch=-x"]), 2)


if __name__ == "__main__":
    unittest.main()
