"""Every manifest row names a declaration that is in the text that ships (scripts/bump/bundle.py compose).

The real case (fixtures/aintlib_unkept_passed.json): aintlib part 2 (tengoku #770, 11 Nov 2026) listed 934 verified theorems, and 7 of them were not in their modules: shard 19's keep
step died on "unknown module prefix 'LutzNagell'", the other shards' keep steps happened to keep most of shard 19's theorems, and the 7 nobody kept were cut by the pruning
while compose still wrote a manifest row for every passed theorem (gitar-bot found them; every one of the 2,996 rows of the part checked: these 7 and no other).

The fixture holds the four real modules (shard 19's sources and Lean's ranges), the 14 theorems Gate 2 passed in them, and the constants the real bundle's text kept. compose runs
on exactly that.

Invariants:
  I1  a manifest row's name is declared in the module text that ships;
  I2  a passed theorem the pruning cut is counted as left out, with its reason, and the accounting (shipped + left out = verified) holds;
  I3  nothing else changes: the theorems that ship are the 7 of the real part, with their statements.
Mutant: without the check, the 7 cut theorems are listed again (the test fails).
"""

from __future__ import annotations

import contextlib
import io
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parents[1]
FX = json.loads((HERE / "tests" / "fixtures" / "aintlib_unkept_passed.json").read_text())
sys.path.insert(0, str(HERE))
import bundle  # noqa: E402


# The real bundle's keep gap was 7 of 2,996 passed theorems (0.23%, under MAX_KEEP_GAP); the four modules alone are 7 of 14. compose runs here with the gap allowed for this
# fixture, as the real run's ratio allowed it, so that the code under test is the manifest step and not the gap check.
MAX_GAP_OF_THE_REAL_RUN = 0.5


def run_compose(argv: list[str], max_gap: float) -> tuple[int, str]:
    """bundle.py's command line, run in this process with MAX_KEEP_GAP set (the same `if __name__ == "__main__"` block, executed in the imported module)."""
    src = Path(bundle.__file__).read_text()
    entry = src[src.index('if __name__ == "__main__":'):].replace('if __name__ == "__main__":', "if True:", 1)
    err = io.StringIO()
    with mock.patch.object(sys, "argv", argv), mock.patch.object(bundle, "MAX_KEEP_GAP", max_gap), contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
        try:
            exec(compile(entry, bundle.__file__, "exec"), bundle.__dict__)  # noqa: S102 - the module's own entry point, read from its file
        except SystemExit as e:
            return (e.code if isinstance(e.code, int) else 1), f"{err.getvalue()}{e.code}"
    return 0, err.getvalue()


def declared(name: str, text: str) -> bool:
    """a `theorem`/`lemma` command of the name (its last component, under any written prefix) at the start of a line: a mention in a comment or a proof is not a declaration (cubic, #173)"""
    last = name.split(".")[-1].strip("«»")
    return bool(re.search(r"(?m)^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?(?:theorem|lemma)\s+(?:[\w'.«»]*\.)?«?" + re.escape(last) + r"»?(?![\w'])", text))


class RealCase(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = cls.d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        keep, passed, gate2 = [], {}, []
        for mod, m in FX["modules"].items():
            rel = mod.replace(".", "/")
            (lib / rel).parent.mkdir(parents=True, exist_ok=True)
            (lib / f"{rel}.lean").write_text(m["source"])
            side = lib / ".lake" / "build" / "lib" / "lean" / f"{rel}.olean.ranges.json"
            side.parent.mkdir(parents=True, exist_ok=True)
            side.write_text(json.dumps(m["ranges"]))
            keep += [[mod, n] for n in m["kept_in_shipped_text"]]
            passed[mod] = m["passed"]
            gate2 += [f"GATE2B_PASS old={n} new={n} via=equal" for n in m["passed"]]
        (d / "deps.log").write_text(f"x:1:0: info: BUNDLE_KEEP {json.dumps(keep)} BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps(passed))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/aintlib.git", "commit": "abc123"}))
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text("\n".join(gate2) + "\n")
        (d / "killed.json").write_text("[]")
        argv = [str(HERE / "bundle.py"), "compose", "--gate2-killed", str(d / "killed.json"), "--lib", str(lib), "--log", str(d / "deps.log"),
                "--passed", str(d / "passed.json"), "--meta", str(d / "setup.json"), "--key", "aintlib", "--toolchain", "tc", "--errors", str(d / "build.log"),
                "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src")]
        cls.code, cls.err = run_compose(argv, MAX_GAP_OF_THE_REAL_RUN)
        out = d / "bundle-proposed"
        cls.manifest = [json.loads(x) for x in (out / "manifest.jsonl").read_text().splitlines()] if (out / "manifest.jsonl").exists() else []
        cls.report = json.loads((out / "report.json").read_text()) if (out / "report.json").exists() else {}
        cls.text = {mod: (out / "Tengoku" / "Aintlib" / f"{mod.replace('.', '/')}.lean") for mod in FX["modules"]}

    def test_compose_ran(self):
        self.assertEqual(self.code, 0, self.err[-2000:])

    def test_the_gap_check_still_refuses_this_share_at_the_real_limit(self):
        code, err = run_compose([*self.argv_for_check()], bundle.MAX_KEEP_GAP)
        self.assertNotEqual(code, 0)
        self.assertIn("keeps nothing for 7 of 14 passed theorems", err)

    @classmethod
    def argv_for_check(cls):
        d = Path(tempfile.mkdtemp())
        return [str(HERE / "bundle.py"), "compose", "--gate2-killed", str(cls.d / "killed.json"), "--lib", str(cls.d / "lib"), "--log", str(cls.d / "deps.log"),
                "--passed", str(cls.d / "passed.json"), "--meta", str(cls.d / "setup.json"), "--key", "aintlib", "--toolchain", "tc", "--errors", str(cls.d / "build.log"),
                "--gate2", str(cls.d / "gate2.log"), "--out", str(d / "bundle"), "--src", str(d / "src")]

    def test_every_row_is_declared_in_the_text_that_ships(self):  # I1
        self.assertTrue(self.manifest)
        for r in self.manifest:
            mod = r["module"].removeprefix("Tengoku.Aintlib.")
            self.assertTrue(declared(r["name"], self.text[mod].read_text()), r["name"])

    def test_the_seven_cut_theorems_are_not_listed_and_are_counted_as_left_out(self):  # I2
        missing = {n for m in FX["modules"].values() for n in m["passed_missing_from_shipped"]}
        self.assertEqual(len(missing), 7)
        self.assertFalse(missing & {r["name"] for r in self.manifest})
        self.assertEqual(self.report["left_out"].get(bundle.NOT_KEPT), 7, self.report["left_out"])
        self.assertEqual(self.report["theorems"] + sum(self.report["left_out"].values()), self.report["passed_total"])

    def test_declared_means_a_declaration_not_a_mention(self):
        self.assertTrue(declared("A.foo", "theorem foo : True := trivial"))
        self.assertTrue(declared("A.foo", "@[simp] protected theorem A.foo : True := trivial"))
        self.assertFalse(declared("A.foo", "-- foo is cut\ntheorem bar : True := foo"))
        self.assertFalse(declared("A.foo", "theorem foo_bar : True := trivial"))
        cut = FX["modules"]["ModularCurves.ForMathlib.DivisorChartFibre"]
        shipped = self.text["ModularCurves.ForMathlib.DivisorChartFibre"].read_text()
        for n in cut["passed_missing_from_shipped"]:
            self.assertFalse(declared(n, shipped), n)
        self.assertTrue(declared(n, cut["source"]))  # the source has it: the check is not blind

    def test_the_theorems_that_ship_are_the_seven_of_the_real_part(self):  # I3
        passed = {n for m in FX["modules"].values() for n in m["passed"]}
        missing = {n for m in FX["modules"].values() for n in m["passed_missing_from_shipped"]}
        self.assertEqual({r["name"] for r in self.manifest}, passed - missing)
        self.assertEqual(len(self.manifest), 7)
        for r in self.manifest:
            self.assertTrue(r["statement"].startswith(("theorem", "lemma")), r)


if __name__ == "__main__":
    unittest.main()
