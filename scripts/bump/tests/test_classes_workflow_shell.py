"""Class-level tests of the SHELL in the factory's workflow steps: the real `run:` text of a step is executed (bash -e -o pipefail, as Actions does) in a sandbox with a fake `lake` / `elan`.

The Python behind a step is tested elsewhere; what these guard is the control flow around it, the class of bug no unit test of a function can see:

  * ROUNDS: a step that repairs and builds again repeats until a round finds nothing (bounded), repairs a module once, and leaves the log of the LAST round for the verdicts (Navier 2026-10-21:
    one round was not enough, three more modules timed out behind the first).
  * TIME: nothing is planned (nothing in the checkout changes) unless there is time to build again; a log is never emptied for a build that does not run (an empty log refuses every importer).
  * LOG CONTRACT: build.log ends with the marker and the LAST round of the importers' build; the first rounds stay readable as build-dups-N.log; the files the artifact lists exist.
  * RETRY: an infrastructure error (the toolchain does not download) is retried, not read as a result.
  * SINGLE SOURCE: a step that edits a module also records the edit where the cut will find it (dups.json repairs, new.json sha).

A new step of this shape is covered by writing a scenario here, not by waiting for a production run.
"""

from __future__ import annotations

import json
import os
import stat
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
import tree_verify as tv  # noqa: E402

WORKFLOW = yaml.safe_load((REPO / ".github" / "workflows" / "bump-sharded.yml").read_text(encoding="utf-8"))

FAKE_LAKE = r'''#!/usr/bin/env python3
"""a Lake that knows three kinds of module (marker lines in the module text):
  TIMEOUT      times out in its declaration (a typeclass search at 20000) unless the text has the `set_option synthInstance.maxHeartbeats` a repair puts there;
  BROKEN       fails with an error whatever is done;
  TIMEOUT_TWICE  times out even after a repair (needs more than the cap).
A module whose import failed is not built and not mentioned (Lake stops there). Every call is counted in lake-calls."""
import re, sys, os
from pathlib import Path
calls = Path(os.environ["FAKE_STATE"]) / "lake-calls"
n = int(calls.read_text()) + 1 if calls.exists() else 1
calls.write_text(str(n))
adv = float(os.environ.get("FAKE_LAKE_ADVANCE_MIN", "0"))
if adv:  # a long build: the clock the step reads (the `date` shim) moves on
    off = Path(os.environ["FAKE_STATE"]) / "clock-offset"
    off.write_text(str(int(float(off.read_text()) if off.exists() else 0) + int(adv * 60)))
if sys.argv[1:2] != ["build"]:
    sys.exit(0)
targets = sys.argv[2:]
tree = Path.cwd()
def path(m): return tree / (m.replace("Tengoku.", "Tengoku/", 1).replace(".", "/") + ".lean")
text = {m: path(m).read_text() for m in targets}
imports = {m: re.findall(r"^import (Tengoku\.\S+)", text[m], re.M) for m in targets}
failed, lines, built = set(), [], 0
def fails(m):
    t = text[m]
    if "BROKEN" in t: return "error"
    if "TIMEOUT_TWICE" in t: return "timeout"
    if "TIMEOUT" in t and "set_option synthInstance.maxHeartbeats" not in t: return "timeout"
    return None
for m in targets:  # the targets are in import order
    if any(i in failed for i in imports[m]):
        failed.add(m); continue
    how = fails(m)
    rel = str(path(m).relative_to(tree))
    if how == "timeout":
        line = next(i for i, l in enumerate(text[m].split("\n"), 1) if l.startswith("theorem"))
        lines.append(f"error: {rel}:{line}:2: failed to synthesize\n  Inst\n(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached\n\nNote: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.")
        failed.add(m)
    elif how == "error":
        lines.append(f"error: {rel}:3:0: unknown identifier")
        failed.add(m)
    else:
        built += 1
        lines.append(f"✔ [{built}/{len(targets)}] Built {m} (3.1s)")
if failed:
    lines += ["Some required targets logged failures:"] + [f"- {m}" for m in targets if m in failed and not any(i in failed for i in imports[m])] + ["error: build failed"]
    print("\n".join(lines)); sys.exit(1)
lines.append(f"Build completed successfully ({built} jobs).")
print("\n".join(lines))
'''

DATE_SHIM = """#!/usr/bin/env python3
import os, sys, time
from pathlib import Path
if sys.argv[1:] == ["+%s"]:
    off = Path(os.environ["FAKE_STATE"]) / "clock-offset"
    print(int(time.time()) + (int(off.read_text()) if off.exists() else 0))
else:
    os.execv("/bin/date", ["date", *sys.argv[1:]])
"""

TIMEOUT_SHIM = "#!/bin/sh\nwhile [ \"$1\" = -k ] || [ \"${1#-}\" != \"$1\" ]; do shift 2 2>/dev/null || shift; done\nshift\nexec \"$@\"\n"


def step_run(job: str, needle: str) -> str:
    for s in WORKFLOW["jobs"][job]["steps"]:
        if needle in s.get("name", ""):
            return s["run"]
    raise KeyError(needle)


class Sandbox:
    """workspace/{emissary -> repo, tree/, out/} plus a bin/ with the fakes; the library is a chain of modules M0 <- M1 <- … (each imports the one before)."""

    def __init__(self, kinds: list[str]):
        self.d = Path(tempfile.mkdtemp())
        self.mods = [f"M{i}" for i in range(len(kinds))]
        bundle, self.tree, self.out, self.bin, self.state = (self.d / x for x in ("bundle", "tree", "out", "bin", "state"))
        for p in (self.tree, self.bin, self.state):
            p.mkdir()
        (self.d / "emissary").symlink_to(REPO)
        files = {"Tengoku/ToyLib.lean": "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in self.mods), "Tengoku/ToyLib/Deps.lean": "-- ToyLib\n"}
        for i, (m, kind) in enumerate(zip(self.mods, kinds)):
            files[f"Tengoku/ToyLib/Toy/{m}.lean"] = (f"import Tengoku.ToyLib.Toy.{self.mods[i - 1]}\n" if i else "import Tengoku\n") + f"-- {kind}\n\ntheorem t_{m} : 1 = 1 := rfl\n"
        for rel, text in files.items():
            p = bundle / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        tv.main(["apply", "--bundle", str(bundle), "--tree", str(self.tree), "--out", str(self.out)])  # copies the modules into tree/, writes out/new.json and out/targets.txt
        (self.out / "dups.json").write_text(json.dumps({"ns": "ToyLib", "mode": "proposed", "aliases": {}, "not_same": {}, "refused": {}}))
        for name, body in (("lake", FAKE_LAKE), ("timeout", TIMEOUT_SHIM), ("date", DATE_SHIM)):
            f = self.bin / name
            f.write_text(body)
            f.chmod(f.stat().st_mode | stat.S_IEXEC)

    def run(self, script: str, *, remaining_min: int = 300, extra_env: dict | None = None, elan_fails: int = 0) -> subprocess.CompletedProcess:
        env = {**os.environ, "PATH": f"{self.bin}:{os.environ['PATH']}", "FAKE_STATE": str(self.state), "GITHUB_WORKSPACE": str(self.d), **(extra_env or {})}
        # the job has JOB_START and 355 minutes: `remaining_min` minutes are left of them
        env["JOB_START"] = str(int(time.time()) - (355 - remaining_min) * 60)
        f = self.d / "step.sh"
        f.write_text(script)
        return subprocess.run(["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", str(f)], cwd=self.d, env=env, capture_output=True, text=True)

    def lake_calls(self) -> int:
        f = self.state / "lake-calls"
        return int(f.read_text()) if f.exists() else 0

    def text(self, rel: str) -> str:
        return (self.out / rel).read_text()


DUPS_STEP = "Copies of tree modules, the importers built on the tree's module"


class ImportersBuild(unittest.TestCase):
    def go(self, kinds: list[str], **kw):
        sb = Sandbox(kinds)
        p = sb.run(step_run("verify", DUPS_STEP), **kw)
        self.assertEqual(p.returncode, 0, p.stdout[-600:] + p.stderr[-600:])
        return sb

    def test_a_module_that_times_out_is_given_room_and_the_build_runs_again(self):
        sb = self.go(["PLAIN", "TIMEOUT", "PLAIN"])
        self.assertEqual(sb.lake_calls(), 2)
        self.assertIn("set_option synthInstance.maxHeartbeats", (sb.tree / "Tengoku/ToyLib/Toy/M1.lean").read_text())
        self.assertIn("timeout at `typeclass`", sb.text("build-dups-1.log"))  # the first round stays for the reader
        final = sb.text("build-dups.log")
        self.assertIn("Build completed successfully", final)  # LOG CONTRACT: the verdicts read the last round
        self.assertNotIn("error:", final)
        self.assertEqual(list(json.loads(sb.text("dups.json"))["repairs"]), ["Toy.M1"])  # SINGLE SOURCE: the cut finds the edit
        spec = json.loads(sb.text("new.json"))["modules"]["Tengoku.ToyLib.Toy.M1"]
        self.assertTrue(spec["repaired"])
        self.assertEqual(spec["sha256"], tv.sha256((sb.tree / "Tengoku/ToyLib/Toy/M1.lean").read_bytes()))  # and the bytes the build accepted are the ones recorded
        build = sb.text("build.log")
        self.assertIn(tv.DUPS_MARKER, build)
        self.assertEqual(build.split(tv.DUPS_MARKER)[1].strip(), final.strip())  # build.log ends with the marker and the LAST round only

    def test_modules_that_time_out_one_behind_the_other_are_repaired_in_rounds_each_once(self):
        """ROUNDS: the second module is only reached once the first builds."""
        sb = self.go(["TIMEOUT", "TIMEOUT", "TIMEOUT", "PLAIN"])
        self.assertEqual(sb.lake_calls(), 4)  # one build, three rounds
        self.assertEqual(sorted(json.loads(sb.text("dups.json"))["repairs"]), ["Toy.M0", "Toy.M1", "Toy.M2"])
        for i in (1, 2, 3):
            self.assertTrue((sb.out / f"build-dups-{i}.log").is_file(), f"round {i}")
        for m in ("M0", "M1", "M2"):
            self.assertEqual((sb.tree / f"Tengoku/ToyLib/Toy/{m}.lean").read_text().count("set_option synthInstance.maxHeartbeats"), 1, f"{m} is repaired once")
        self.assertNotIn("error:", sb.text("build-dups.log"))

    def test_the_rounds_are_bounded(self):
        sb = self.go(["TIMEOUT"] * 9)
        self.assertEqual(sb.lake_calls(), 7)  # one build and six rounds, not nine
        self.assertEqual(len(json.loads(sb.text("dups.json"))["repairs"]), 6)
        self.assertIn("error:", sb.text("build-dups.log"))  # what is still failing is in the log the verdicts read

    def test_a_module_that_still_times_out_after_its_repair_is_not_repaired_again(self):
        sb = self.go(["PLAIN", "TIMEOUT_TWICE"])
        self.assertEqual(sb.lake_calls(), 2)  # the repair, one build again, and no second repair of the same module
        self.assertEqual((sb.tree / "Tengoku/ToyLib/Toy/M1.lean").read_text().count("set_option synthInstance.maxHeartbeats"), 1)
        self.assertIn("error:", sb.text("build-dups.log"))

    def test_a_failure_that_is_not_a_timeout_costs_no_second_build(self):
        sb = self.go(["PLAIN", "BROKEN", "PLAIN"])
        self.assertEqual(sb.lake_calls(), 1)
        self.assertEqual(json.loads(sb.text("dups.json")).get("repairs", {}), {})
        self.assertIn("error:", sb.text("build-dups.log"))
        self.assertIn("error:", sb.text("build.log"))  # the verdicts see it

    def test_a_clean_build_is_left_alone(self):
        sb = self.go(["PLAIN", "PLAIN"])
        self.assertEqual(sb.lake_calls(), 1)
        self.assertIn("Build completed successfully", sb.text("build-dups.log"))
        self.assertFalse((sb.out / "build-dups-1.log").exists())

    def test_with_no_time_left_for_a_second_build_nothing_is_planned_and_no_log_is_emptied(self):
        """TIME. The first build takes the time that was left for a second (the fake lake moves the clock on 30 minutes): the checkout and new.json stay as the first build saw them and the first round's
        log stands. An emptied log would refuse every importer, the ones that built too."""
        sb = Sandbox(["PLAIN", "TIMEOUT"])
        before = (sb.tree / "Tengoku/ToyLib/Toy/M1.lean").read_text()
        spec_before = json.loads(sb.text("new.json"))
        p = sb.run(step_run("verify", DUPS_STEP), remaining_min=125, extra_env={"FAKE_LAKE_ADVANCE_MIN": "30"})  # cap 15 for the first build; 95 left after it: cap -15
        self.assertEqual(p.returncode, 0, p.stdout[-400:] + p.stderr[-400:])
        self.assertEqual(sb.lake_calls(), 1)
        self.assertEqual((sb.tree / "Tengoku/ToyLib/Toy/M1.lean").read_text(), before)  # the checkout is not repaired
        self.assertEqual(json.loads(sb.text("new.json")), spec_before)  # new.json is not touched
        self.assertEqual(json.loads(sb.text("dups.json")).get("repairs", {}), {})
        self.assertIn("timeout at `typeclass`", sb.text("build-dups.log"))  # the first round's verdict stands, it is not emptied
        self.assertIn("::warning::", p.stdout)
        self.assertFalse((sb.out / "build-dups-1.log").exists())

    def test_with_no_time_even_for_the_first_build_the_log_is_empty_and_says_so(self):
        """(the step's own contract: an empty log is 'nothing was built', never a clean one)"""
        sb = Sandbox(["PLAIN", "TIMEOUT"])
        p = sb.run(step_run("verify", DUPS_STEP), remaining_min=115)  # cap 5
        self.assertEqual(p.returncode, 0, p.stdout[-400:] + p.stderr[-400:])
        self.assertEqual(sb.lake_calls(), 0)
        self.assertEqual(sb.text("build-dups.log"), "")
        self.assertIn("::warning::", p.stdout)

    def test_the_artifact_lists_exactly_files_that_the_step_writes(self):
        """LOG CONTRACT: every file of the verdict artifact is one directory deep under out/ and the dups step's own files are in the list."""
        paths = [x.strip() for x in next(s for s in WORKFLOW["jobs"]["verify"]["steps"] if s.get("uses", "").startswith("actions/upload-artifact") and "out/dups.json" in s["with"]["path"])["with"]["path"].split("\n") if x.strip()]
        for want in ("out/build-dups.log", "out/build-dups-[1-6].log", "out/dups-repairs.json", "out/dups-repairs.txt", "out/dups.json"):
            self.assertIn(want, paths)
        self.assertTrue(all(p.count("/") == 1 for p in paths))


class ToolchainRetry(unittest.TestCase):
    def line(self) -> str:
        run = step_run("verify", "Lean toolchain")
        return next(x for x in run.split("\n") if x.strip().startswith("for i in 1 2 3 4 5; do"))

    def elan(self, fails: int):
        d = Path(tempfile.mkdtemp())
        (d / ".elan" / "bin").mkdir(parents=True)
        f = d / ".elan" / "bin" / "elan"
        f.write_text(f'#!/bin/sh\nc=$(cat "{d}/calls" 2>/dev/null || echo 0); c=$((c+1)); echo $c > "{d}/calls"\n[ "$c" -le {fails} ] && {{ echo "error: SSL connect error" >&2; exit 1; }}\nexit 0\n')
        f.chmod(f.stat().st_mode | stat.S_IEXEC)
        return d

    def run_line(self, fails: int):
        d = self.elan(fails)
        shim = d / "sleep"
        shim.write_text("#!/bin/sh\nexit 0\n")
        shim.chmod(shim.stat().st_mode | stat.S_IEXEC)
        p = subprocess.run(["bash", "-e", "-c", self.line()], env={**os.environ, "HOME": str(d), "TOOLCHAIN": "leanprover/lean4:v9", "PATH": f"{d}:{os.environ['PATH']}"}, capture_output=True, text=True)
        return p, int((d / "calls").read_text())

    def test_a_download_error_is_retried_until_it_works(self):
        """RETRY. An infrastructure error is not a result."""
        p, calls = self.run_line(2)
        self.assertEqual((p.returncode, calls), (0, 3), p.stderr)

    def test_it_gives_up_after_five_and_does_not_fail_the_step_itself(self):
        p, calls = self.run_line(99)
        self.assertEqual((p.returncode, calls), (0, 5))  # the build step then fails loudly (collect refuses a build that built nothing)


if __name__ == "__main__":
    unittest.main()
