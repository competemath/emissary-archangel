import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import plan_shards as ps  # noqa: E402


class Planner(unittest.TestCase):
    def test_shards_are_dependency_closed_and_cover_the_targets(self):
        imp = {"core": []}
        for i in range(40):
            imp[f"leaf{i}"] = ["core"] if i % 2 else []
        imp["All"] = [f"leaf{i}" for i in range(40)]  # an aggregator imports everything and has no entries
        wanted = {m for m in imp if m != "All"}
        p = ps.plan(imp, {m: 100 for m in imp}, 4, wanted=wanted)
        got = [m for s in p["shards"] for m in s["targets"]]
        self.assertEqual(sorted(got), sorted(wanted))  # every wanted module is a target of exactly one shard
        for s in p["shards"]:
            b = set(s["build"])
            self.assertTrue(set(s["targets"]) <= b)
            for m in b:
                self.assertTrue(set(imp[m]) <= b, f"shard {s['shard']}: {m} imports something that is not built with it")
        self.assertLess(max(s["lines"] for s in p["shards"]), 0.5 * p["lines"])  # the aggregator's closure is nobody's job

    def test_pack_and_merge_feed_bundle_compose(self):
        sys.path.insert(0, str(HERE / "tests"))
        import test_records as T

        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        (lib / "Toy" / "A.lean").write_text(T.A)
        (lib / "Toy" / "B.lean").write_text(T.B)
        la, lb = T.A.split("\n"), T.B.split("\n")
        ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
        rows = {"Toy/A": [["Toy.one", ln(la, "/-- the number one"), ln(la, "def one")], ["Toy.one_pos", ln(la, "theorem one_pos"), ln(la, "theorem one_pos")]],
                "Toy/B": [["Toy.uses_one_pos", ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos")]]}
        for m, r in rows.items():
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(r))
        (d / "gate2.log").write_text("noise\nGATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n")
        (d / "errors.log").write_text("error: Toy/A.lean:1:0: x\nwarning: y\n")
        (d / "passed.json").write_text(json.dumps({"Toy.B": ["Toy.uses_one_pos"]}))
        (d / "keep.log").write_text('BUNDLE_KEEP [["Toy.B","Toy.uses_one_pos"],["Toy.A","Toy.one_pos"],["Toy.A","Toy.one"]] BUNDLE_END\n')
        (d / "mods.txt").write_text("Toy.A\nToy.B\n")
        pk = d / "shards" / "shard-0"
        subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "pack", "--lib", str(lib), "--roots", "Toy", "--out", str(pk), "--gate2", str(d / "gate2.log"),
                        "--errors", str(d / "errors.log"), "--passed", str(d / "passed.json"), "--keep", str(d / "keep.log"), "--modules", str(d / "mods.txt")], check=True)
        merged, logs = d / "merged", d / "logs"
        merged.mkdir(); logs.mkdir()
        subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "merge", "--shards", str(d / "shards"), "--out", str(merged), "--logs", str(logs)], check=True)
        self.assertEqual(json.loads((logs / "passed.json").read_text()), {"Toy.B": ["Toy.uses_one_pos"]})
        self.assertNotIn("noise", (logs / "gate2.log").read_text())
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy", "commit": "c"}))
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--lib", str(merged), "--log", str(logs / "bundle-deps.log"), "--passed", str(logs / "passed.json"), "--meta", str(d / "setup.json"),
                        "--key", "toy", "--toolchain", "tc", "--errors", str(logs / "errors.log"), "--gate2", str(logs / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src")], check=True)
        self.assertIn("theorem uses_one_pos", (d / "bundle" / "Tengoku" / "Toy" / "Toy" / "B.lean").read_text())
        self.assertEqual(json.loads((d / "bundle" / "report.json").read_text())["theorems"], 1)


if __name__ == "__main__":
    unittest.main()
