"""An import clash in a shard's keep step: the clashing module is left out with what imports it, the step runs again, and compose leaves out the same.

The real case: archon-firstproof-p6 (2026-11-07, run 42340425280). The library holds one file twice, as FirstProof6_constant and FirstProof6_constant3; BundleKeep loads every module
with a passed theorem into one environment, and Lean stopped it with the line below, so the shard's bundle-deps.log had no BUNDLE_KEEP line and compose died ("bundle-deps.log has
no BUNDLE_KEEP line although theorems passed"). bump-library.yml has left such a module out and run the step again since 2026-10-09; the shard workflow had never been given the loop.

Here the shard's own step (read from bump-shard.yml and run with bash) meets a stand-in `lake` that answers like Lean: the real clash line while both copies are loaded, the
BUNDLE_KEEP line once they are not. Invariants: the step ends with a BUNDLE_KEEP line; the later copy and its importers are left out of the keep input, and only they; the shard
pack carries the list; merge joins the lists of every shard; every compose of bump-sharded.yml hands compose that list with the run's own `drop` input.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]

CLASH = (
    "uncaught exception: import FirstProof.FirstProof6_constant3.Auxiliary.ColoringFramework failed, environment already contains "
    "'Problem6.PartialColoring.recOn' from FirstProof.FirstProof6_constant.Auxiliary.ColoringFramework"
)
A = "FirstProof.FirstProof6_constant.Auxiliary.ColoringFramework"
B = "FirstProof.FirstProof6_constant3.Auxiliary.ColoringFramework"
B_MAIN = "FirstProof.FirstProof6_constant3.Main"  # imports B
OTHER = "FirstProof.Other"

# Lean's answer: a module is loaded with what it imports (read from the library's sources), and the two copies cannot both be in one environment
FAKE_LAKE = r'''#!/usr/bin/env python3
import json, re, sys
from pathlib import Path
k = json.loads(Path(sys.argv[-1]).read_text())
def deps(m, seen):
    if m in seen:
        return
    seen.add(m)
    f = Path(*m.split(".")).with_suffix(".lean")
    if f.exists():
        for i in re.findall(r"^import\s+(\S+)", f.read_text(), re.M):
            deps(i, seen)
loaded = set()
for m in k["imports"]:
    deps(m, loaded)
if "%A%" in loaded and "%B%" in loaded:
    print("%CLASH%")
    sys.exit(1)
print("x:1:0: info: BUNDLE_KEEP " + json.dumps([[n.rsplit(".", 1)[0], n] for n in k["names"]]) + " BUNDLE_END")
'''.replace("%A%", A).replace("%B%", B).replace("%CLASH%", CLASH)


def step_run(wf: str, name: str) -> str:
    import yaml

    doc = yaml.safe_load((ROOT / ".github" / "workflows" / wf).read_text())
    for job in doc["jobs"].values():
        for st in job.get("steps", []):
            if st.get("name") == name:
                return st["run"]
    raise AssertionError(f"{wf} has no step {name!r}")


def compose_drop_lines() -> list[str]:
    """The line before each compose of bump-sharded.yml that makes its --drop-modules."""
    text = (ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text()
    return re.findall(r"^\s*(drop=\$\(.*keep-drops\.txt.*\))\s*$", text, re.M)


class KeepFixture(unittest.TestCase):
    """the library, the stand-in lake and timeout, and how the step is run (no test of its own)"""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        em = self.tmp / "emissary"
        (em / "scripts").mkdir(parents=True)
        os.symlink(HERE, em / "scripts" / "bump")
        lib = em / "lib"
        base = lib / ".lake" / "build" / "lib" / "lean"
        sources = {A: "", B: "", B_MAIN: f"import {B}\n", OTHER: f"import {A}\n"}
        for m, imp in sources.items():
            f = lib / Path(*m.split(".")).with_suffix(".lean")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(imp + "theorem t : True := trivial\n")
            o = base / Path(*m.split(".")).with_suffix(".olean")
            o.parent.mkdir(parents=True, exist_ok=True)
            o.write_bytes(b"")
        self.passed = {m: [f"{m}.t"] for m in sources}
        (em / "passed.json").write_text(json.dumps(self.passed))
        bin_ = self.tmp / "bin"
        bin_.mkdir()
        for name, body in (("lake", FAKE_LAKE), ("timeout", '#!/bin/sh\nshift\nexec "$@"\n')):
            (bin_ / name).write_text(body)
            (bin_ / name).chmod(0o755)
        # `lake env lean --run X file` -> the stand-in reads the last argument
        self.env = {**os.environ, "PATH": f"{bin_}:{os.path.dirname(sys.executable)}:{os.environ['PATH']}", "ROOTS": "FirstProof"}
        self.em = em

    def run_step(self, script: str) -> subprocess.CompletedProcess:
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script], cwd=self.em, env=self.env, capture_output=True, text=True, timeout=120)


class ShardKeepStep(KeepFixture):
    def test_the_clash_is_left_out_and_the_step_ends_with_a_keep_line(self):
        p = self.run_step(step_run("bump-shard.yml", "What the passed theorems are made of"))
        self.assertEqual(p.returncode, 0, p.stderr + p.stdout)
        log = (self.em / "bundle-deps.log").read_text()
        self.assertRegex(log, r"BUNDLE_KEEP (\[.*?\]) BUNDLE_END")  # what compose reads
        self.assertNotIn("environment already contains", log)
        self.assertEqual((self.em / "keep-drops.txt").read_text().split(), [B])  # the later copy, as Lean named it, and nothing else
        k = json.loads((self.em / "lib" / "bundle-keep.json").read_text())
        self.assertEqual(k["imports"], [A, OTHER])  # the copy and what imports it are out; the first copy and its importer stay
        self.assertIn(f"import clash in the keep step: {B}", p.stdout)

    def test_without_a_clash_the_step_runs_once_and_drops_nothing(self):
        (self.em / "passed.json").write_text(json.dumps({A: [f"{A}.t"], OTHER: [f"{OTHER}.t"]}))
        p = self.run_step(step_run("bump-shard.yml", "What the passed theorems are made of"))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual((self.em / "keep-drops.txt").read_text(), "")
        self.assertEqual(json.loads((self.em / "lib" / "bundle-keep.json").read_text())["imports"], [A, OTHER])

    def test_the_list_reaches_compose_through_pack_and_merge(self):
        p = self.run_step(step_run("bump-shard.yml", "What the passed theorems are made of"))
        self.assertEqual(p.returncode, 0, p.stderr)
        shards = self.tmp / "shards"
        for i, drops in ((0, None), (1, "")):
            art = shards / f"shard-k-{i}"
            out = art / "shard-pack"
            for f in ("gate2.log", "build-final.log", "gate2-results.json"):
                (self.em / f).write_text("")
            cmd = [sys.executable, str(HERE / "shard_pack.py"), "pack", "--lib", str(self.em / "lib"), "--roots", "FirstProof", "--out", str(out), "--gate2", str(self.em / "gate2.log"),
                   "--errors", str(self.em / "build-final.log"), "--passed", str(self.em / "passed.json"), "--keep", str(self.em / "bundle-deps.log")]
            if drops is None:
                cmd += ["--keep-drops", str(self.em / "keep-drops.txt")]
            q = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(q.returncode, 0, q.stderr)
            (art / "emissary").mkdir()
            (art / "emissary" / "gate2-killed.json").write_text("[]")
        logs = self.tmp / "logs"
        logs.mkdir()  # the workflow makes it (mkdir -p ../merged ../logs)
        m = subprocess.run([sys.executable, str(HERE / "shard_pack.py"), "merge", "--shards", str(shards), "--out", str(self.tmp / "merged"), "--logs", str(logs)], capture_output=True, text=True)
        self.assertEqual(m.returncode, 0, m.stderr)
        self.assertEqual((logs / "keep-drops.txt").read_text().split(), [B])  # a shard without the file (an older artifact) adds nothing
        self.assertIn("1 left out of the keep step for an import clash", m.stdout)
        lines = compose_drop_lines()
        self.assertEqual(len(lines), 2)  # compose and finish
        (self.tmp / "emissary2").mkdir()
        for line, given in ((lines[0], ""), (lines[1], f"X.Y, {B}")):  # the run's own drop input, with a space and with the same module again
            r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", line + '\nprintf "%s" "$drop"'], cwd=self.tmp / "emissary2", env={**self.env, "DROP": given}, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual(r.stdout.split(","), sorted({B, *(x.strip() for x in given.split(",") if x.strip())}))  # each module once, no spaces
        (logs / "keep-drops.txt").write_text("")
        r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", lines[0] + '\nprintf "[%s]" "$drop"'], cwd=self.tmp / "emissary2", env={**self.env, "DROP": ""}, capture_output=True, text=True)
        self.assertEqual((r.returncode, r.stdout), (0, "[]"))  # nothing to drop: an empty list, and the step does not fail on it


class ReadingTheClash(unittest.TestCase):
    """The step's own line that reads the module out of Lean's refusal (cubic on emissary#154: a quoted part with a space was cut at the space, and the retry dropped nothing)."""

    def bad_of(self, log: str) -> str:
        run = step_run("bump-shard.yml", "What the passed theorems are made of")
        line = next(ln.strip() for ln in run.splitlines() if ln.strip().startswith("bad=$("))
        d = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, d, True)
        (d / "bundle-deps.log").write_text(log)
        r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", line + '\nprintf "%s" "$bad"'], cwd=d, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return r.stdout

    def test_the_module_is_read_whole(self):
        self.assertEqual(self.bad_of("x\n" + CLASH + "\n"), B)  # the real line
        for mod in ("Lib.«bar baz».Aux", "Lib.«1102.4662»", "Lib.«a-b»", "Lib.A"):
            line = f"uncaught exception: import {mod} failed, environment already contains 'X.y' from Lib.Other\n"
            self.assertEqual(self.bad_of("warning: z\n" + line), mod)
        self.assertEqual(self.bad_of("x:1:0: info: BUNDLE_KEEP [] BUNDLE_END\n"), "")  # no clash: nothing
        self.assertEqual(self.bad_of("uncaught exception: import Lib.A failed, object file ./Lib/A.olean does not exist\n"), "")  # not a clash: no drop


class Budget(KeepFixture):
    def test_a_name_with_a_comma_stops_the_step(self):
        lake = self.tmp / "bin" / "lake"
        lake.write_text("#!/bin/sh\necho \"uncaught exception: import FirstProof.«a,b» failed, environment already contains 'x' from FirstProof.Other\"\n")
        p = self.run_step(step_run("bump-shard.yml", "What the passed theorems are made of"))
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("has a comma", p.stdout)

    def test_the_tries_share_one_budget(self):
        # a clock that moves 4,000 s each time it is read: the budget is 7,200 s, so the first try runs and the second finds the budget spent
        clock = self.tmp / "bin" / "date"
        clock.write_text(f"#!/bin/sh\nf={self.tmp}/clock; n=$(cat \"$f\" 2>/dev/null || echo 0); echo $((n + 1)) > \"$f\"; echo $((1000000 + n * 4000))\n")
        clock.chmod(0o755)
        lake = self.tmp / "bin" / "lake"
        lake.write_text("#!/bin/sh\necho \"uncaught exception: import X.Y$$ failed, environment already contains 'x' from X.Z\"\n")  # a new clash every try
        p = self.run_step(step_run("bump-shard.yml", "What the passed theorems are made of"))
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertIn("the keep step's 120 minutes are spent after 1 tries", p.stdout)
        self.assertEqual(len((self.em / "keep-drops.txt").read_text().split()), 1)

    def test_each_try_is_limited_to_what_is_left(self):
        run = step_run("bump-shard.yml", "What the passed theorems are made of")
        self.assertIn('timeout "${left}s" lake env lean --run', run)
        self.assertNotIn("timeout 120m", run)


class Workflows(unittest.TestCase):
    def test_every_compose_of_the_sharded_bump_drops_what_the_keep_step_left_out(self):
        text = (ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text()
        chunks = text.split("bundle.py compose")[1:]
        self.assertEqual(len(chunks), 2)
        for chunk in chunks:
            command = chunk.split("\n      - name:")[0].split("\n\n")[0]
            self.assertIn('--drop-modules "$drop"', command)
        self.assertEqual(len(compose_drop_lines()), 2)

    def test_the_shard_packs_the_list(self):
        self.assertIn("--keep-drops keep-drops.txt", step_run("bump-shard.yml", "Pack this shard"))


if __name__ == "__main__":
    unittest.main()
