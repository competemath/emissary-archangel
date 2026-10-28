"""explain_ejection.py puts each error of a rejected part in the class that names its cause."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import explain_ejection as ex  # noqa: E402

SRC_A = "import Mathlib\n\ntheorem bad_one : True := by\n  apply Finset.prod_le_prod₀\n\ntheorem good_one : True := trivial\n"
SRC_B = "import Mathlib\n\nlemma helper_thing : True := trivial\n\ntheorem user_one : True := by\n  simp only [helper_thing]\n"
SRC_C = "import Mathlib\n\n@[instance_reducible]\ndef bial : Nat := 1\n\ntheorem uses_bial : True := by\n  rw [bial]\n"


def write(root: Path, rel: str, text: str) -> None:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


class Explain(unittest.TestCase):
    def setup(self):
        shards, shipped = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp())
        sp = shards / "shard-lib-0" / "shard-pack"
        for rel, text in (("Lib/A.lean", SRC_A), ("Lib/B.lean", SRC_B), ("Lib/C.lean", SRC_C), ("Lib/D.lean", "import Mathlib\n\ntheorem d_one : 1 = 1 := rfl\n")):
            write(sp / "src", rel, text)
        # the factory's own build failed in bad_one only (line 4)
        (sp / "errors.log").write_text("error: Lib/A.lean:4:8: Unknown constant `Finset.prod_le_prod₀`\n")
        # shipped: A as it is (the failing declaration is still there, 2 lines up after pruning), B without helper_thing, C without its attribute, D as it is
        write(shipped, "Tengoku/Ns/Lib/A.lean", "import Tengoku\n\ntheorem bad_one : True := by\n  apply Finset.prod_le_prod₀\n")
        write(shipped, "Tengoku/Ns/Lib/B.lean", "import Tengoku\n\ntheorem user_one : True := by\n  simp only [helper_thing]\n")
        write(shipped, "Tengoku/Ns/Lib/C.lean", "import Tengoku\n\ndef bial : Nat := 1\n\ntheorem uses_bial : True := by\n  rw [bial]\n")
        write(shipped, "Tengoku/Ns/Lib/D.lean", "import Tengoku\n\ntheorem d_one : 1 = 1 := rfl\n")
        return shards, shipped

    def log(self, *errors):
        return "Some required targets logged failures:\n- Tengoku.Ns.Lib.A\n" + "".join(f"2026-10-11T10:00:00.0Z error: Tengoku/Ns/{rel}:{ln}:2: {msg}\n" for rel, ln, msg in errors)

    def run_one(self, rel, line, msg):
        shards, shipped = self.setup()
        r = ex.explain(self.log((rel, line, msg)), ex.Shipped(shipped), ex.Factory(shards))
        return r["modules"][rel][0]

    def test_A_a_declaration_that_failed_in_the_factory_and_was_shipped(self):
        e = self.run_one("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`")
        self.assertEqual(e["class"], "A")
        self.assertIn("bad_one", e["why"])

    def test_B_a_declaration_of_the_library_that_the_pruning_cut(self):
        e = self.run_one("Lib/B.lean", 4, "Unknown identifier `helper_thing`")
        self.assertEqual(e["class"], "B")
        self.assertIn("Lib/B.lean", e["why"])

    def test_E_a_name_declared_nowhere(self):
        e = self.run_one("Lib/D.lean", 3, "Unknown constant `Finset.zzz_missing_name`")
        self.assertEqual(e["class"], "E")

    def test_every_spelling_of_an_unknown_name_is_classified_the_same(self):
        for msg in ("Unknown constant `Finset.zzz_missing_name`", "unknown constant 'Finset.zzz_missing_name'", "unknown identifier 'zzz_missing_name'", "unknown namespace 'Zzz.Missing'", "invalid field 'zzz_missing_name', the environment does not contain 'Nat.zzz_missing_name'"):
            self.assertEqual(self.run_one("Lib/D.lean", 3, msg)["class"], "E", msg)
        self.assertEqual(self.run_one("Lib/B.lean", 4, "unknown identifier 'helper_thing'")["class"], "B")

    def test_C_attributes_the_packager_stripped(self):
        e = self.run_one("Lib/C.lean", 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern")
        self.assertEqual(e["class"], "C")
        self.assertIn("instance_reducible x1", e["why"])

    def test_D_unexplained_shows_the_shipped_lines(self):
        e = self.run_one("Lib/D.lean", 3, "failed to synthesize instance")
        self.assertEqual(e["class"], "D")
        self.assertIn("theorem d_one", e["why"])

    def test_the_summary_counts_failing_targets_and_classes_and_the_cli_reads_a_tar(self):
        import io
        import tarfile

        shards, shipped = self.setup()
        tar = Path(tempfile.mkdtemp()) / "part.tar"
        with tarfile.open(tar, "w") as t:
            for p in sorted(shipped.rglob("*.lean")):
                t.add(p, arcname=str(p.relative_to(shipped)))
        log = Path(tempfile.mkdtemp()) / "q.log"
        log.write_text(self.log(("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`"), ("Lib/B.lean", 4, "Unknown identifier `helper_thing`")))
        out = Path(tempfile.mkdtemp()) / "r.json"
        self.assertEqual(ex.main(["--queue-log", str(log), "--shards", str(shards), "--shipped", str(tar), "--json", str(out)]), 0)
        r = json.loads(out.read_text())
        self.assertEqual((r["failing_targets"], r["error_classes"]), (["Ns.Lib.A"], {"A": 1, "B": 1}))
        del io


if __name__ == "__main__":
    unittest.main()
