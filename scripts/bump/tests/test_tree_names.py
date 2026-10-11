"""tree_names.py gives compose the set tengoku's intake gate refuses a bundle theorem against: the names of data/trusted and data/intake, minus the library's own files."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import tree_names  # noqa: E402


def write(root: Path, rel: str, names: list[str]) -> None:
    f = root / rel
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text("".join('{"name": "%s", "statement": "x"}\n' % n for n in names))


class TreeNames(unittest.TestCase):
    def test_trusted_and_intake_names_without_the_librarys_own_files(self):
        root = Path(tempfile.mkdtemp())
        write(root, "data/trusted/mathlib-algebra.jsonl", ["A.one"])
        write(root, "data/trusted/lean-pool.jsonl", ["Own.trusted"])  # stem == lib
        write(root, "data/intake/other/manifest.jsonl", ["B.two"])
        write(root, "data/intake/other/parts/001.jsonl", ["B.three"])
        write(root, "data/intake/lean-pool/manifest.jsonl", ["Own.intake"])  # parent == lib
        write(root, "data/staging/other/s.jsonl", ["C.staged"])  # not in the tree
        self.assertEqual(tree_names.tree_names(root, "lean-pool"), {"A.one", "B.two", "B.three"})

    def test_the_cli_writes_one_name_per_line_and_refuses_an_empty_checkout(self):
        root, out = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp()) / "names.txt"
        write(root, "data/trusted/m.jsonl", ["B.b", "A.a"])
        r = subprocess.run([sys.executable, str(HERE / "tree_names.py"), "--root", str(root), "--lib", "x", "--out", str(out)], capture_output=True, text=True)
        self.assertEqual((r.returncode, out.read_text()), (0, "A.a\nB.b\n"), r.stderr)
        r = subprocess.run([sys.executable, str(HERE / "tree_names.py"), "--root", str(Path(tempfile.mkdtemp())), "--lib", "x", "--out", str(out)], capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)  # a wrong checkout must not mean 'no clash'
        self.assertIn("empty list would let every clash through", r.stderr)


if __name__ == "__main__":
    unittest.main()
