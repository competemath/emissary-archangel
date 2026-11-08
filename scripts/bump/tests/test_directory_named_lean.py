"""A DIRECTORY named like a Lean file is not a module (every walk of a library's sources keeps files only).

The real case: leanbridge (CBirkbeck/LeanBridge @ 4dffaca4) has the directory LeanBridge/Mathlib/Units.lean/, holding unitmk.lean. Its setup built fine; its bump (run 42474356030,
8 Nov 2026) died in the plan job: `rglob("*.lean")` returns directories too, and tolerant_build.module_files read it: "IsADirectoryError: [Errno 21] Is a directory:
'lib/LeanBridge/Mathlib/Units.lean'".

Fixture: that real layout (plus ordinary modules, one importing the file inside the directory, and a root that is a directory named Root.lean). Invariants: each function that walks a
library returns or reads the files, never the directory, and does not raise; the file INSIDE the directory is still found; a source-level check that every `rglob("*.lean")` in the
six files that walk a library's sources keeps files only, so a new walk cannot bring this back.
"""

from __future__ import annotations

import re
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import bundle  # noqa: E402
import engine  # noqa: E402
import tolerant_build as tb  # noqa: E402

WALKERS = ["adapters.py", "bundle.py", "engine.py", "gate2_batch.py", "tolerant_build.py", "vendor_deps.py"]
# bundle.py also walks the bundle it composed itself (out_dir, src_dir): those trees are written by the factory, file by file
FACTORY_TREES = ("src_dir", "tree_root")


class DirectoryNamedLean(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.lib = lib = Path(self.tmp.name) / "lib"
        (lib / "LeanBridge" / "Mathlib" / "Units.lean").mkdir(parents=True)
        (lib / "LeanBridge" / "Mathlib" / "Units.lean" / "unitmk.lean").write_text("theorem unitmk : True := trivial\n")
        (lib / "LeanBridge" / "Mathlib" / "Basic.lean").write_text("import Mathlib.Data.Nat.Basic\n\ntheorem basic : True := trivial\n")
        (lib / "LeanBridge" / "Top.lean").write_text("import LeanBridge.Mathlib.Basic\n\ntheorem top : True := trivial\n")
        (lib / "LeanBridge.lean").write_text("import LeanBridge.Top\n")
        (lib / "Root.lean").mkdir()  # a root that is a directory named like its file

    def test_module_files_keeps_the_files_and_not_the_directory(self):
        for follow in (False, True):
            found = tb.module_files(self.lib, ["LeanBridge", "Root"], follow_imports=follow)
            self.assertTrue(all(p.is_file() for p in found.values()), found)
            self.assertNotIn("LeanBridge.Mathlib.Units", found)
            self.assertNotIn("Root", found)
            self.assertIn("LeanBridge.Top", found)
            self.assertEqual([p.name for m, p in found.items() if "Units" in m], ["unitmk.lean"])  # the file inside the directory is a file of the library

    def test_engine_lean_files_keeps_the_files(self):
        files = engine.lean_files(self.lib, ["LeanBridge", "Root"])
        self.assertTrue(all(p.is_file() for p in files), files)
        self.assertIn(self.lib / "LeanBridge" / "Mathlib" / "Units.lean" / "unitmk.lean", files)
        self.assertNotIn(self.lib / "LeanBridge" / "Mathlib" / "Units.lean", files)

    def test_uses_mathlib_reads_past_the_directory(self):
        self.assertTrue(bundle.uses_mathlib(self.lib))

    def test_every_walk_of_a_library_keeps_files_only(self):
        for name in WALKERS:
            lines = (HERE / name).read_text(encoding="utf-8").split("\n")
            for i, line in enumerate(lines):
                if 'rglob("*.lean")' not in line or any(t in line for t in FACTORY_TREES):
                    continue
                self.assertTrue(re.search(r"is_file\(\)", " ".join(lines[i : i + 2])), f"{name}:{i + 1}: {line.strip()}")


if __name__ == "__main__":
    unittest.main()
