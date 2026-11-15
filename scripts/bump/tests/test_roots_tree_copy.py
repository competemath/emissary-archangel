"""scripts/bump/roots_tree.py is tengoku's scripts/roots_tree.py, byte for byte: the factory qualifies a bundle's root declarations with the script the tree's roots PRs are held to
(tengoku scripts/ci/roots_check.py recomputes them with it), so a form the tree learned is a form the factory knows. When tengoku changes the file, copy it and move the pin."""

import hashlib
import sys
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
WORKFLOWS = HERE.parents[2] / ".github" / "workflows"
sys.path.insert(0, str(HERE.parent))
import roots_tree  # noqa: E402
import scope_rewrite as sr  # noqa: E402

PIN = "d286e4525238d82263137d93fa5988bd9d3d5d976cdb1618fcc5d826c20caa48"  # sha256 of scripts/roots_tree.py in competemath/tengoku (main, 15 Nov 2026: through tengoku #835)
STEP = "Make the registrations that leak into other libraries local (RECUT), and move the root declarations to Tengoku.<Library> (every cut)"


def steps(name: str, job: str) -> list[dict]:
    return yaml.safe_load((WORKFLOWS / name).read_text())["jobs"][job]["steps"]


class Copy(unittest.TestCase):
    def test_the_copy_is_tengokus_file(self):
        self.assertEqual(hashlib.sha256((HERE.parent / "roots_tree.py").read_bytes()).hexdigest(), PIN, "scripts/bump/roots_tree.py is a verbatim copy of tengoku's scripts/roots_tree.py")

    def test_scope_rewrite_uses_it(self):
        self.assertIs(sr.roots_tree, roots_tree)
        self.assertEqual(roots_tree.NOTE.format(ns="Tengoku.X"), "-- Tengoku: root names of this library moved to Tengoku.X so they do not collide with other libraries (generated)\n")


class Workflows(unittest.TestCase):
    def test_the_recut_job_of_bump_library_fetches_the_copy_with_scope_rewrite(self):
        clones = [s["run"] for s in steps("bump-library.yml", "attest") if "sparse-checkout set" in s.get("run", "") and "/scripts/bump/scope_rewrite.py" in s.get("run", "")]
        self.assertTrue(clones)
        for clone in clones:
            self.assertIn("/scripts/bump/roots_tree.py", clone)

    def test_compose_and_finish_of_bump_sharded_make_the_same_edit(self):
        runs = []
        for job in ("compose", "finish"):
            found = [s for s in steps("bump-sharded.yml", job) if s.get("name") == STEP]
            self.assertEqual(len(found), 1, job)
            self.assertNotIn("if", found[0], f"{job}: the step runs on every cut")
            runs.append(found[0]["run"])
        self.assertEqual(runs[0], runs[1])
        self.assertIn("root_lines.py --merged merged --out roots.scope", runs[0])
        self.assertIn('--leaks "$SCOPE" --roots-file roots.scope --qualify-roots', runs[0])
        self.assertIn('[ -n "$SCOPE" ] || [ -s roots.scope ]', runs[0])

    def test_the_step_comes_after_the_bundle_is_cut_and_before_it_is_used(self):
        for job, after in (("compose", "The draft, for the tree's build"), ("finish", "Every module that ships was built in the tree, byte for byte")):
            names = [s.get("name") for s in steps("bump-sharded.yml", job)]
            self.assertLess(names.index("Merge the shards and cut the bundle"), names.index(STEP), job)
            self.assertLess(names.index(STEP), names.index(after), job)


if __name__ == "__main__":
    unittest.main()
