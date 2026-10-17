import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]


def shard(root: Path, name: str, killed: str | None, where: str = "artifact") -> None:
    """A shard artifact as bump-shard.yml uploads it: shard-pack/ and emissary/gate2-killed.json (`where=pack` puts the file in the pack instead; `killed=None` leaves it out)."""
    pack = root / name / "shard-pack"
    (pack / "src").mkdir(parents=True)
    (pack / "passed.json").write_text("{}")
    if killed is not None:
        target = (root / name / "emissary") if where == "artifact" else pack
        target.mkdir(parents=True, exist_ok=True)
        (target / "gate2-killed.json").write_text(killed)


def merge(root: Path):
    out, logs = root / "merged", root / "logs"
    out.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    p = subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "merge", "--shards", str(root / "shards"), "--out", str(out), "--logs", str(logs)], capture_output=True, text=True)
    return p, logs


class KilledOverShards(unittest.TestCase):
    """2026-10-17: gate2_driver.py writes gate2-killed.json per shard ("nothing of it reaches a bundle") and nothing downstream read it; merge now carries the union to compose, and refuses a shard without one."""

    def test_the_killed_modules_of_every_shard_are_merged(self):
        root = Path(tempfile.mkdtemp())
        shard(root / "shards", "shard-k-0", '["Euler.A", "Euler.B"]')
        shard(root / "shards", "shard-k-1", "[]")
        shard(root / "shards", "shard-k-2", '["Euler.B", "NS.C"]', where="pack")
        p, logs = merge(root)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual(json.loads((logs / "gate2-killed.json").read_text()), ["Euler.A", "Euler.B", "NS.C"])
        self.assertIn("3 modules without a Gate 2 verdict", p.stdout)

    def test_a_shard_with_no_killed_file_is_refused_not_read_as_none(self):
        root = Path(tempfile.mkdtemp())
        shard(root / "shards", "shard-k-0", "[]")
        shard(root / "shards", "shard-k-1", None)
        p, _ = merge(root)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("gate2-killed.json", p.stderr)
        self.assertIn("shard-k-1", p.stderr)

    def test_a_killed_file_that_is_not_a_list_of_names_is_refused(self):
        for text in ('{"a": 1}', "[1]", "null"):
            root = Path(tempfile.mkdtemp())
            shard(root / "shards", "shard-k-0", text)
            p, _ = merge(root)
            self.assertNotEqual(p.returncode, 0, text)


class WorkflowsPassTheList(unittest.TestCase):
    """Every place that composes a bundle hands compose the merged killed list; the argument is required, so a workflow that forgot it fails at once, and this pins that none does."""

    ROOT = HERE.parents[1]

    def test_every_compose_in_a_workflow_passes_gate2_killed(self):
        seen = 0
        for wf in ("bump-sharded.yml", "bump-library.yml"):
            text = (self.ROOT / ".github" / "workflows" / wf).read_text()
            for chunk in text.split("bundle.py compose")[1:]:
                seen += 1
                command = chunk.split("\n      - name:")[0].split("\n\n")[0]
                self.assertIn("--gate2-killed", command, wf)
        self.assertEqual(seen, 3)  # compose and finish of bump-sharded, the single job of bump-library

    def test_the_shard_artifact_carries_the_list(self):
        text = (self.ROOT / ".github" / "workflows" / "bump-shard.yml").read_text()
        self.assertIn("emissary/gate2-killed.json", text.split("upload-artifact")[1])


if __name__ == "__main__":
    unittest.main()
