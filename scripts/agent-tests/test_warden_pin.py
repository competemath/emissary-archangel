"""scripts/warden is a byte-for-byte copy of tengoku-warden, and PIN says which commit and which hashes.

A hand edit of a vendored file, a file added next to them, or a stale PIN fails here. Change tengoku-warden and run
scripts/warden/refresh.py instead.
"""
import hashlib
import os
import re
import unittest

import _load

WARDEN = os.path.join(_load.SCRIPTS, "warden")
NOT_VENDORED = {"PIN", "refresh.py", "__pycache__"}
NEEDED = {"toolpolicy", "envscrub", "jail", "selftest", "egress", "secretscan", "sanitize", "caps", "safegit", "scope", "audit", "untrusted", "verdict", "__init__", "__main__"}


def read_pin():
    commit, files = None, {}
    with open(os.path.join(WARDEN, "PIN"), encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            if line.startswith("commit "):
                commit = line.split(" ", 1)[1]
            elif line.startswith("repo "):
                continue
            else:
                digest, _, name = line.partition("  ")
                files[name] = digest
    return commit, files


class VendoredWarden(unittest.TestCase):
    def test_pin_names_a_full_commit(self):
        commit, _ = read_pin()
        self.assertRegex(commit or "", r"^[0-9a-f]{40}$")

    def test_every_vendored_file_matches_its_pinned_hash(self):
        _, files = read_pin()
        bad = []
        for name, digest in sorted(files.items()):
            path = os.path.join(WARDEN, name)
            with open(path, "rb") as fh:
                actual = hashlib.sha256(fh.read()).hexdigest()
            if actual != digest:
                bad.append("%s: pinned %s, found %s" % (name, digest[:12], actual[:12]))
        self.assertEqual(bad, [], "vendored files were edited; run scripts/warden/refresh.py <checkout> instead:\n" + "\n".join(bad))

    def test_pin_lists_exactly_the_files_that_are_there(self):
        _, files = read_pin()
        present = {f for f in os.listdir(WARDEN) if f not in NOT_VENDORED}
        self.assertEqual(sorted(present), sorted(files), "a file next to the vendored ones is not pinned, or a pinned file is missing")
        for digest in files.values():
            self.assertRegex(digest, r"^[0-9a-f]{64}$")

    def test_the_modules_the_jail_uses_are_all_vendored(self):
        _, files = read_pin()
        self.assertTrue({m + ".py" for m in NEEDED} <= set(files), sorted({m + ".py" for m in NEEDED} - set(files)))

    def test_refresh_script_agrees_with_the_list(self):
        with open(os.path.join(WARDEN, "refresh.py"), encoding="utf-8") as fh:
            src = fh.read()
        listed = set(re.findall(r'"([a-z_]+)"', re.search(r"VENDORED = \((.*?)\)", src, re.S).group(1)))
        self.assertEqual(listed, NEEDED)


if __name__ == "__main__":
    unittest.main()
