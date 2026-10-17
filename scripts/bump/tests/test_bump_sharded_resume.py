"""A shard whose job dies must not vanish, and it must be possible to run just that shard again.

2026-10-17, navier-stokes-euler (64 shards): shard 1, two thirds of the library's lines, died on a runner shutdown after 3h49m. `compose` ran anyway (`!cancelled() && plan
succeeded`), `shard_pack merge` read the 63 artifacts that were there ("0 modules without a Gate 2 verdict") and the bundle was cut without shard 1: 8,666 theorems that had
passed Gate 2 were left out because they import its modules, and Gate 2 never ran on the shard itself. Nothing said a shard was missing. Now: compose refuses a plan with a
shard that has no result, and a run can build only the shards named in `only_shards` and take the others from an earlier run (`fill_from`, same plan, checked).
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parents[1]
PATH = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "bump-sharded.yml"
DOC = yaml.safe_load(PATH.read_text(encoding="utf-8"))
JOBS = DOC["jobs"]
INPUTS = DOC[True]["workflow_dispatch"]["inputs"]


def pack(root: Path, n: int, key: str = "k", with_src: bool = True) -> None:
    d = root / f"shard-{key}-{n}" / "shard-pack"
    d.mkdir(parents=True)
    if with_src:
        (d / "src").mkdir()


def tool(*args: str):
    p = subprocess.run([sys.executable, str(HERE / "shard_pack.py"), *args], capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


class Complete(unittest.TestCase):
    def test_every_planned_shard_having_its_pack_passes(self):
        with tempfile.TemporaryDirectory() as d:
            for n in (0, 1, 2):
                pack(Path(d), n)
            rc, out = tool("complete", "--shards", d, "--key", "k", "--planned", "[0, 1, 2]")
            self.assertEqual(rc, 0, out)

    def test_a_shard_that_died_is_named_and_refused(self):
        with tempfile.TemporaryDirectory() as d:
            for n in (0, 2):
                pack(Path(d), n)
            rc, out = tool("complete", "--shards", d, "--key", "k", "--planned", "[0, 1, 2]")
            self.assertNotEqual(rc, 0)
            self.assertIn("[1]", out)
            self.assertIn("only_shards", out)  # the way out is in the message

    def test_an_artifact_without_a_pack_is_no_result(self):
        with tempfile.TemporaryDirectory() as d:
            pack(Path(d), 0)
            pack(Path(d), 1, with_src=False)
            self.assertNotEqual(tool("complete", "--shards", d, "--key", "k", "--planned", "[0, 1]")[0], 0)

    def test_another_librarys_shard_is_not_this_ones(self):
        with tempfile.TemporaryDirectory() as d:
            pack(Path(d), 0, key="other")
            self.assertNotEqual(tool("complete", "--shards", d, "--key", "k", "--planned", "[0]")[0], 0)


class Select(unittest.TestCase):
    def test_all_of_the_plan_when_nothing_is_named(self):
        self.assertEqual(json.loads(tool("select", "--planned", "[0, 1, 5]", "--only", "")[1]), [0, 1, 5])

    def test_only_the_named_ones_in_plan_order(self):
        self.assertEqual(json.loads(tool("select", "--planned", "[0, 1, 5]", "--only", "5, 1")[1]), [1, 5])
        self.assertEqual(json.loads(tool("select", "--planned", "[0, 1, 5]", "--only", "1")[1]), [1])

    def test_a_shard_that_is_not_in_the_plan_is_an_error(self):
        rc, out = tool("select", "--planned", "[0, 1, 5]", "--only", "1,7")
        self.assertNotEqual(rc, 0)
        self.assertIn("7", out)


class Fill(unittest.TestCase):
    def test_the_earlier_runs_shards_are_taken_where_this_run_has_none_and_never_replace_one(self):
        with tempfile.TemporaryDirectory() as d:
            shards, old = Path(d) / "shards", Path(d) / "old"
            pack(shards, 1)
            (shards / "shard-k-1" / "marker").write_text("new")
            for n in (0, 1, 2):
                pack(old, n)
                (old / f"shard-k-{n}" / "marker").write_text("old")
            rc, out = tool("fill", "--shards", str(shards), "--fill", str(old))
            self.assertEqual(rc, 0, out)
            self.assertEqual(sorted(p.name for p in shards.iterdir()), ["shard-k-0", "shard-k-1", "shard-k-2"])
            self.assertEqual((shards / "shard-k-1" / "marker").read_text(), "new")  # the shard built here wins
            self.assertEqual((shards / "shard-k-0" / "marker").read_text(), "old")

    def test_nothing_to_fill_from_is_fine(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(tool("fill", "--shards", d, "--fill", str(Path(d) / "absent"))[0], 0)


def steps(job: str) -> list[dict]:
    return JOBS[job]["steps"]


def index(job: str, needle: str) -> int:
    found = [i for i, s in enumerate(steps(job)) if needle in s.get("name", "") or needle in s.get("run", "")]
    assert len(found) >= 1, (job, needle)
    return found[0]


class Workflow(unittest.TestCase):
    def test_the_inputs_exist(self):
        self.assertIn("only_shards", INPUTS)
        self.assertIn("fill_from", INPUTS)
        self.assertIn("fill_unrecorded", INPUTS)

    def test_the_shard_matrix_is_the_shards_this_run_builds(self):
        self.assertIn("run_shards", JOBS["shard"]["strategy"]["matrix"]["shard"])
        self.assertIn("run_shards", JOBS["plan"]["outputs"])
        self.assertIn("select", next(s["run"] for s in steps("plan") if s.get("id") == "run"))

    def test_compose_refuses_a_plan_with_a_shard_that_has_no_result_before_it_merges(self):
        check = index("compose", "Every shard of the plan has its result")
        self.assertLess(check, index("compose", "shard_pack.py merge"))
        s = steps("compose")[check]
        self.assertEqual(s["if"], "${{ inputs.recut_from == '' }}")  # a recut has no plan: it merges what an earlier run left
        self.assertIn("needs.plan.outputs.shards", s["env"]["PLANNED"])
        self.assertIn("shard_pack.py complete", s["run"])

    def test_the_filled_in_shards_are_in_place_before_compose_and_finish_merge(self):
        for job, merge in (("compose", "shard_pack.py merge"), ("finish", "shard_pack.py merge")):
            fill = index(job, "shard_pack.py fill")
            self.assertLess(fill, index(job, merge), job)
            self.assertEqual(steps(job)[fill]["if"], "${{ inputs.fill_from != '' }}", job)
            down = steps(job)[fill - 1]["with"]
            self.assertEqual(down["run-id"], "${{ inputs.fill_from }}", job)
            self.assertEqual(down["path"], "shards-fill", job)  # not straight into shards/: a shard built here is never replaced by its old copy

    def test_the_earlier_runs_plan_must_be_this_runs_plan(self):
        cmp_step = steps("compose")[index("compose", "The earlier run planned the same shards")]
        self.assertIn("cmp plan-old/plan.json plan-new/plan.json", cmp_step["run"])
        # CodeRabbit: the plan alone does not say what the shards were built with
        self.assertIn("cmp plan-old/inputs.json plan-new/inputs.json", cmp_step["run"])
        self.assertIn("fill_unrecorded", cmp_step["env"]["UNRECORDED"])  # an old run without inputs.json needs an explicit vouch, never a silent pass
        record = next(s for s in steps("plan") if "What the shards are built with" in s.get("name", ""))
        for name in ("MATHLIB", "TOOLCHAIN", "IMPORTS", "TENGOKU_REF"):
            self.assertIn(name, record["env"], name)
        self.assertLess(steps("plan").index(record), next(i for i, s in enumerate(steps("plan")) if "upload-artifact" in s.get("uses", "")))
        self.assertLess(index("compose", "The earlier run planned the same shards"), index("compose", "Every shard of the plan has its result"))

    def test_a_resume_needs_no_new_permission(self):
        self.assertEqual(JOBS["compose"]["permissions"], {"contents": "read", "actions": "read"})
        self.assertIn("actions", JOBS["finish"]["permissions"])


if __name__ == "__main__":
    unittest.main()
