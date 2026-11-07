"""in_tree.py and the plan step that runs it: a fresh bump of a library whose parts are in the tree is cut from the tree, or it does not start.

The real case: foundation (2026-11-07). Tengoku records its part 002 (data/intake/foundation/parts/002.json); bump run 42370781841 ran without from_tree, its parts were numbered from
001, the opener skipped them ("every part is in the tree") and 108 passed theorems shipped nowhere until a recut by hand from the tree cut part 003 (run 42376189191). Fixtures: the
tree's real part listings of 7 Nov (foundation: 002; lean-pool: 002-016; formal-conjectures: none). Invariants: parts in the tree and no from_tree -> refused, naming from_tree=true and
the next part number; from_tree without parts -> refused; from_tree with parts -> runs; no part in the tree -> runs; another library's parts never count. The plan step itself runs on a
real git repository laid out like the tree.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import in_tree  # noqa: E402

FOUNDATION = ["data/intake/foundation/manifest.jsonl", "data/intake/foundation/parts/002.json", "data/intake/foundation/report.json"]
LANA = ["data/intake/lana-pi1/manifest.jsonl", "data/intake/lana-pi1/report.json"]  # merged in one part (#733): no parts/ directory
LEAN_POOL = ["data/intake/lean-pool/manifest.jsonl"] + [f"data/intake/lean-pool/parts/{n:03d}.json" for n in range(2, 17)]


class Verdict(unittest.TestCase):
    def test_a_library_in_the_tree_without_from_tree_is_refused(self):
        ok, why = in_tree.verdict(FOUNDATION, "foundation", "", "0")
        self.assertFalse(ok)
        self.assertIn("from_tree=true parts=300", why)
        self.assertIn("from part 003", why)
        ok, why = in_tree.verdict(LEAN_POOL, "lean-pool", "false", "300")
        self.assertFalse(ok)
        self.assertIn("from_tree=true parts=300", why)
        self.assertIn("from part 017", why)

    def test_a_library_merged_in_one_part_is_in_the_tree(self):
        # lana-pi1, ns-p23 and flt-anthropic (#740) were merged as 'part 1 of 1': the tree records the manifest and no parts/
        ok, why = in_tree.verdict(LANA, "lana-pi1", "", "0")
        self.assertFalse(ok)
        self.assertIn("from part 002", why)
        self.assertTrue(in_tree.verdict(LANA, "lana-pi1", "true", "300")[0])
        self.assertTrue(in_tree.verdict(["data/intake/lana-pi1/report.json"], "lana-pi1", "", "0")[0])  # a report alone is not a merge

    def test_from_tree_with_parts_runs(self):
        self.assertEqual(in_tree.verdict(FOUNDATION, "foundation", "true", "300")[0], True)
        self.assertIn("from part 017", in_tree.verdict(LEAN_POOL, "lean-pool", "true", "300")[1])

    def test_from_tree_without_parts_is_refused(self):
        for parts in ("0", "", " 0 "):
            ok, why = in_tree.verdict(FOUNDATION, "foundation", "true", parts)
            self.assertFalse(ok, parts)
            self.assertIn("no part would be cut", why)
        self.assertFalse(in_tree.verdict([], "formal-conjectures", "true", "0")[0])  # also for a library not in the tree
        self.assertFalse(in_tree.verdict([], "formal-conjectures", "", "x")[0])

    def test_a_library_not_in_the_tree_runs(self):
        for parts in ("0", "300"):
            self.assertTrue(in_tree.verdict([], "formal-conjectures", "", parts)[0])
        # another library's parts never count, nor a prefix of the key, nor a file that is not a part
        others = LEAN_POOL + ["data/intake/foundation-x/parts/001.json", "data/intake/formal-conjectures/records.json", "data/intake/formal-conjectures/parts/notes.md"]
        self.assertTrue(in_tree.verdict(others, "formal-conjectures", "", "0")[0])
        self.assertTrue(in_tree.verdict(others, "foundation", "", "0")[0])

    def test_every_combination(self):
        # 3 listings x 4 from_tree values x 4 parts values: the rule, stated once, holds for each
        listings = {"foundation": FOUNDATION, "lean-pool": LEAN_POOL, "lana-pi1": LANA, "formal-conjectures": []}
        n = 0
        for key, paths in listings.items():
            for ft in ("", "false", "true", "TRUE"):
                for parts in ("0", "", "1", "300"):
                    ok, _ = in_tree.verdict(paths, key, ft, parts)
                    want_ft, has_parts = ft == "true", int(parts or 0) > 0
                    expect = (has_parts if want_ft else not paths)
                    self.assertEqual(ok, expect, (key, ft, parts))
                    n += 1
        self.assertEqual(n, 64)


class PlanStep(unittest.TestCase):
    """The plan job's own step, read from the workflow and run with bash against a git repository laid out like the tree (main holds data/intake/foundation/parts/002.json)."""

    def setUp(self):
        import yaml

        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        tree = self.tmp / "tengoku"
        (tree / "data/intake/foundation/parts").mkdir(parents=True)
        (tree / "data/intake/foundation/parts/002.json").write_text("{}\n")
        (tree / "data/intake/foundation/manifest.jsonl").write_text("{}\n")
        (tree / "data/intake/lana-pi1").mkdir(parents=True)
        (tree / "data/intake/lana-pi1/manifest.jsonl").write_text("{}\n")
        (tree / "README.md").write_text("tree\n")
        git = ["git", "-C", str(tree), "-c", "user.name=t", "-c", "user.email=t@t", "-c", "init.defaultBranch=main"]
        subprocess.run(["git", "-c", "init.defaultBranch=main", "init", "-q", str(tree)], check=True)
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "tree"], check=True)
        (self.tmp / "emissary" / "scripts").mkdir(parents=True)
        (self.tmp / "emissary" / "scripts" / "bump").symlink_to(HERE)
        doc = yaml.safe_load((ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text())
        steps = doc["jobs"]["plan"]["steps"]
        names = [s.get("name") for s in steps]
        self.step = steps[names.index("A library in the tree is cut from the tree")]
        self.assertLess(names.index("A library in the tree is cut from the tree"), names.index("The library, its import graph, the plan"))  # before hours of work

    def run_step(self, key, from_tree, parts):
        env = {"PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin", "KEY": key, "FROM_TREE": from_tree, "PARTS": parts}
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", self.step["run"]], cwd=self.tmp / "emissary", env=env, capture_output=True, text=True)

    def test_the_step_refuses_foundation_without_from_tree(self):
        p = self.run_step("foundation", "", "0")
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("::error::foundation is in the tree already", p.stdout)

    def test_the_step_refuses_a_library_merged_in_one_part(self):
        p = self.run_step("lana-pi1", "", "0")
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("from part 002", p.stdout)

    def test_the_step_lets_the_right_dispatches_run(self):
        self.assertEqual(self.run_step("foundation", "true", "300").returncode, 0)
        p = self.run_step("formal-conjectures", "", "0")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)  # an empty listing: ls-tree prints nothing and succeeds

    def test_the_step_passes_the_inputs(self):
        self.assertEqual(self.step["env"], {"FROM_TREE": "${{ inputs.from_tree }}", "PARTS": "${{ inputs.parts }}"})
        self.assertEqual(self.step["working-directory"], "emissary")


if __name__ == "__main__":
    unittest.main()
