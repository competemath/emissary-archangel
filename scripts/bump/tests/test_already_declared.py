"""A passed name that the module's build refused as 'already declared' is left out with its reason, not counted as a gap of the keep step (scripts/bump/bundle.py compose).

The real case (fixtures/lcs_already_declared_shard.json.gz): lean-characteristic-set's only shard (bump-sharded run 42494414245, 8 Nov 2026; artifact
shard-lean-characteristic-set-0, every file as it was uploaded). CharacteristicSet/Lemmas.lean declares MvPolynomial lemmas that upstream later added to the base
the tree builds on. On the tree's toolchain each one fails with "`MvPolynomial.degreeOf_X_self` has already been declared" (15 such lines). Gate 2 passed 5 of the
names, but it compared them with the base's constants. The keep step had nothing of Lemmas to keep. compose took the 5 for a part of the library the Lean step had lost
(5 of 47 = 10.6%, over MAX_KEEP_GAP) and refused the whole library. Four bumps (two in October, 5 Nov, 8 Nov) failed the same way.

compose runs on exactly that shard: shard_pack.py merge, then bundle.py compose with the workflow's arguments (bump-sharded.yml), except the tree's record names
(the run read them from tengoku main; none of this library's names are records of the tree, and the test must not need the network).

Invariants:
  I1  compose ships the real library: it ran (it refused before), at the real MAX_KEEP_GAP;
  I2  the 5 names are not in the manifest and are counted as left out with ALREADY_DECLARED; shipped + left out = passed;
  I3  only a name the build log reports as already declared, in that module's own file, is excused: every other passed name is shipped or left out for its own reason;
  I4  a real gap is still refused: with the 'already declared' lines gone from the log, compose refuses the same 5 of 47;
  I5  the parser takes exactly the 'already declared' lines (the 15 real ones, and 3,000 generated lines of names and other messages).
Mutant: already_declared returning nothing (the old compose) refuses the library (fails I1).
"""

from __future__ import annotations

import contextlib
import gzip
import io
import json
import random
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parents[1]
FX = json.loads(gzip.open(HERE / "tests" / "fixtures" / "lcs_already_declared_shard.json.gz", "rt", encoding="utf-8").read())
sys.path.insert(0, str(HERE))
import bundle  # noqa: E402

LEMMAS = "CharacteristicSet.Lemmas"
ERRORS = FX["files"]["shard-pack/errors.log"]


def merged(errors: str | None = None) -> Path:
    """The shard as the workflow downloads it, merged by shard_pack.py merge (bump-sharded.yml 'Merge the shards and cut the bundle')."""
    t = Path(tempfile.mkdtemp())
    art = t / "shards" / FX["artifact"]
    for rel, text in FX["files"].items():
        f = art / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(errors if (errors is not None and rel == "shard-pack/errors.log") else text)
    (t / "merged").mkdir()
    (t / "logs").mkdir()
    subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "merge", "--shards", str(t / "shards"), "--out", str(t / "merged"), "--logs", str(t / "logs")],
                   check=True, capture_output=True, text=True)
    (t / "setup.ci.json").write_text(json.dumps({"repo": "https://github.com/WuProver/lean_characteristic_set", "commit": "8631b1326942799529814c4d319aef6813ea6e32"}))
    return t


def compose(t: Path, *, parser=None) -> tuple[int, str, dict, list]:
    """bundle.py compose with the workflow's arguments, run in this process (its own `if __name__ == "__main__"` block) so that a mutant can replace one function."""
    argv = [str(HERE / "bundle.py"), "compose", "--lib", str(t / "merged"), "--log", str(t / "logs" / "bundle-deps.log"), "--passed", str(t / "logs" / "passed.json"),
            "--meta", str(t / "setup.ci.json"), "--key", "lean-characteristic-set", "--toolchain", "leanprover/lean4:v4.34.0-rc2", "--errors", str(t / "logs" / "errors.log"),
            "--gate2", str(t / "logs" / "gate2.log"), "--gate2-killed", str(t / "logs" / "gate2-killed.json"), "--out", str(t / "bundle"), "--src", str(t / "pruned-src"),
            "--drop-modules", "", "--drop-leaks", "--imports", "faithful"]
    src = Path(bundle.__file__).read_text()
    entry = src[src.index('if __name__ == "__main__":'):].replace('if __name__ == "__main__":', "if True:", 1)
    err = io.StringIO()
    patches = [mock.patch.object(sys, "argv", argv), contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO())]
    if parser is not None:
        patches.append(mock.patch.object(bundle, "already_declared", parser))
    code = 0
    with contextlib.ExitStack() as st:
        for p in patches:
            st.enter_context(p)
        try:
            exec(compile(entry, bundle.__file__, "exec"), bundle.__dict__)  # noqa: S102 - the module's own entry point, read from its file
        except SystemExit as e:
            code = e.code if isinstance(e.code, int) else 1
            err.write(str(e.code))
    out = t / "bundle"
    report = json.loads((out / "report.json").read_text()) if (out / "report.json").exists() else {}
    manifest = [json.loads(x) for x in (out / "manifest.jsonl").read_text().splitlines()] if (out / "manifest.jsonl").exists() else []
    return code, err.getvalue(), report, manifest


class RealShard(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.t = merged()
        cls.passed = json.loads((cls.t / "logs" / "passed.json").read_text())
        cls.code, cls.err, cls.report, cls.manifest = compose(cls.t)

    def test_the_fixture_is_the_real_case(self):
        self.assertEqual(sum(len(v) for v in self.passed.values()), 47)
        self.assertEqual(len(self.passed[LEMMAS]), 5)
        self.assertEqual(sum("has already been declared" in ln for ln in ERRORS.splitlines()), 15)

    def test_compose_ships_the_library(self):  # I1
        self.assertEqual(self.code, 0, self.err[-2000:])
        self.assertTrue(self.manifest)

    def test_the_five_are_left_out_with_their_reason(self):  # I2
        five = set(self.passed[LEMMAS])
        self.assertFalse(five & {r["name"] for r in self.manifest})
        self.assertEqual(self.report["left_out"].get(bundle.ALREADY_DECLARED), 5, self.report["left_out"])
        self.assertEqual(self.report["theorems"] + sum(self.report["left_out"].values()), self.report["passed_total"])
        self.assertEqual(self.report["passed_total"], 47)

    def test_only_an_already_declared_name_is_excused(self):  # I3
        already = bundle.already_declared(ERRORS)
        excused = {(m, n) for m, ns in self.passed.items() for n in ns if n in already.get(bundle.rel_of(m), ())}
        self.assertEqual(excused, {(LEMMAS, n) for n in self.passed[LEMMAS]})
        for m, n in excused:
            self.assertIn(f"error: {bundle.rel_of(m)}:", "\n".join(ln for ln in ERRORS.splitlines() if f"`{n}` has already been declared" in ln))
        shipped = {r["name"] for r in self.manifest}
        self.assertLessEqual(shipped, {n for m, ns in self.passed.items() if m != LEMMAS for n in ns})

    def test_a_real_gap_is_still_refused(self):  # I4
        t = merged("\n".join(ln for ln in ERRORS.splitlines() if "has already been declared" not in ln) + "\n")
        code, err, _, _ = compose(t)
        self.assertNotEqual(code, 0)
        self.assertIn("keeps nothing for 5 of 47 passed theorems", err)

    def test_the_old_compose_refuses_the_library(self):  # the mutant
        code, err, _, _ = compose(merged(), parser=lambda _text: {})
        self.assertNotEqual(code, 0)
        self.assertIn("keeps nothing for 5 of 47 passed theorems", err)


class Parser(unittest.TestCase):
    def test_the_real_log(self):  # I5
        already = bundle.already_declared(ERRORS)
        want = {}
        for ln in ERRORS.splitlines():
            m = re.match(r"^error: (\S+?\.lean):\d+:\d+: `(.+)` has already been declared$", ln)
            if m:
                want.setdefault(m.group(1), set()).add(m.group(2))
        self.assertEqual(dict(already), want)
        self.assertEqual(sum(len(v) for v in already.values()), 15)
        self.assertEqual(set(already), {"CharacteristicSet/Lemmas.lean"})

    def test_generated_lines(self):  # I5: 3,000 lines, names with dots, primes, guillemets and backticks around them, mixed with other messages
        rng = random.Random(20261111)
        others = [line.split(": ", 2)[2] for line in ERRORS.splitlines() if line.startswith("error: ") and "has already been declared" not in line]
        others += ["unknown constant `A.b`", "`A.b` has already been declared in another module, see above", "has already been declared", "warning text"]
        lines, want = [], {}
        for i in range(3000):
            f = f"Lib/{rng.choice(['A', 'B', 'C.D', '1102.4662', 'Two Words', 'a b/c d'])}.lean"  # a path with a space too (cubic, #177)
            if rng.random() < 0.4:
                name = ".".join(rng.choice(["Foo", "bar_baz", "x'", "«weird name»", "MvPolynomial", "degreeOf_X_self"]) for _ in range(rng.randint(1, 4)))
                lines.append(f"error: {f}:{i}:{rng.randint(0, 80)}: `{name}` has already been declared")
                want.setdefault(f, set()).add(name)
            else:
                lines.append(f"error: {f}:{i}:0: {rng.choice(others)}" if rng.random() < 0.9 else f"warning: {f}:{i}:0: `x` has already been declared")
        self.assertEqual(dict(bundle.already_declared("\n".join(lines))), want)

    def test_a_path_with_a_space(self):  # cubic, #177: portfolio.ERROR takes no space in the path; the module `A.«B C»` is the file A/B C.lean
        log = "error: A/B C.lean:3:8: `A.foo` has already been declared\nerror: ./A/D.lean:1:0: `A.bar` has already been declared\n"
        self.assertEqual(dict(bundle.already_declared(log)), {"A/B C.lean": {"A.foo"}, "A/D.lean": {"A.bar"}})
        self.assertEqual(bundle.rel_of("A.«B C»"), "A/B C.lean")
        self.assertEqual(bundle.without_already({"A.«B C»": ["A.foo", "A.baz"]}, bundle.already_declared(log)), {"A.«B C»": ["A.baz"]})

    def test_rel_of_names_the_file_the_log_names(self):
        self.assertEqual(bundle.rel_of("CharacteristicSet.Lemmas"), "CharacteristicSet/Lemmas.lean")
        self.assertEqual(bundle.rel_of("Foo.«1102.4662»"), "Foo/1102.4662.lean")


if __name__ == "__main__":
    unittest.main()
