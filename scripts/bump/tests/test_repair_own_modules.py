"""engine.py repair never rewrites an import of the library's own module, under the roots or in another package of the library.

The real case: flt-anthropic's main bump (run 42001607075, 5 Nov 2026), shard 5. The roots were Theorems,Definitions; every Theorems module imports P2M.Util (the library's
tactics, `p2m_exact_reverting`) and its own P2M.Sol.S_* proof. The first build had 414 modules with a bad import (P2M had not been built), and the repair took P2M.Util and
P2M.Sol.* for modules that no longer exist: it replaced 828 imports with `import Mathlib`. Every theorem then failed with "unknown tactic" and an unknown solution, 426 of 572
modules, and the whole bump's count of modules with errors (29,651 of 60,474) was mostly this. #144 builds P2M now, but a P2M module that times out still gives its importers a
bad import, and the repair would cut them off from their proofs again.

Fixture: real module names and real import headers from the flt fixture (real-flt-imports.json.gz): 300 Theorems modules with their P2M.Util and P2M.Sol imports, the files of
those P2M modules, and one import of a module that really is gone. The log has a bad import line for every P2M import of every module (what shard 5's first build logged). Invariants: no import of a module the library
has a file for is touched, under the roots or not; an import of a module the library does not have is still repaired; the summary counts only that one.
"""

from __future__ import annotations

import gzip
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import engine  # noqa: E402

FIXTURE = HERE / "tests" / "fixtures" / "real-flt-imports.json.gz"


class RepairOwnModules(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        imports = json.load(gzip.open(FIXTURE))["imports"]
        thms = sorted(m for m in imports if m.startswith("Theorems.") and "P2M.Util" in imports[m] and any(i.startswith("P2M.Sol.") for i in imports[m]))[:300]
        self.assertEqual(len(thms), 300)
        self.lib = self.tmp / "lib"
        own: set[str] = set()
        log = []
        for m in thms:
            own.update(i for i in imports[m] if i.startswith("P2M."))
        for m in sorted(own) + thms:
            f = self.lib / Path(*m.split(".")).with_suffix(".lean")
            f.parent.mkdir(parents=True, exist_ok=True)
            header = "".join(f"import {i}\n" for i in imports.get(m, []))
            f.write_text(header + "\ntheorem t : True := trivial\n")
        # the one module that is really gone: an import the library does not have a file for
        gone = self.lib / "Theorems" / "Gone.lean"
        gone.write_text("import Mathlib.Old.Gone\nimport P2M.Util\n\ntheorem g : True := trivial\n")
        for m in thms:  # what the first build of shard 5 logged: P2M was not built, so each P2M import of a theorem was a bad import
            for i in imports[m]:
                if i.startswith("P2M."):
                    log.append(f"error: {Path(*m.split('.')).with_suffix('.lean')}: bad import '{i}'")
        log.append("error: Theorems/Gone.lean: bad import 'Mathlib.Old.Gone'")
        log.append("error: Theorems/Gone.lean: bad import 'P2M.Util'")
        (self.tmp / "build.log").write_text("\n".join(log) + "\n")
        self.thms, self.own = thms, own
        self.before = {p: p.read_text() for p in self.lib.rglob("*.lean")}

    def repair(self):
        r = subprocess.run([sys.executable, str(HERE / "engine.py"), "repair", "--lib", str(self.lib), "--log", str(self.tmp / "build.log"), "--roots", "Theorems,Definitions",
                            "--state", str(self.tmp / "state.json"), "--out", str(self.tmp / "repair.json")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads((self.tmp / "repair.json").read_text())

    def test_no_import_of_the_librarys_own_modules_is_touched(self):
        summary = self.repair()
        changed = [p for p, t in self.before.items() if p.read_text() != t]
        self.assertEqual([p.name for p in changed], ["Gone.lean"])  # 300 theorem files with P2M imports: none touched
        self.assertEqual(summary["moved_imports"], 1)  # only the module that is really gone
        text = (self.lib / "Theorems" / "Gone.lean").read_text()
        self.assertIn("import P2M.Util\n", text)  # its own import stays, in the same file that was repaired
        self.assertNotIn("Mathlib.Old.Gone", text)
        self.assertIn("import Mathlib\n", text)

    def test_own_file_reads_the_library_and_guillemets(self):
        self.assertTrue(engine.own_file(self.lib, "P2M.Util"))
        self.assertTrue(engine.own_file(self.lib, next(iter(sorted(m for m in self.own if m.startswith("P2M.Sol."))))))
        self.assertFalse(engine.own_file(self.lib, "Mathlib.Old.Gone"))
        self.assertFalse(engine.own_file(self.lib, ""))
        (self.lib / "P2M" / "Sol" / "1102.4662.lean").write_text("theorem x : True := trivial\n")
        self.assertTrue(engine.own_file(self.lib, "P2M.Sol.«1102.4662»"))


if __name__ == "__main__":
    unittest.main()
