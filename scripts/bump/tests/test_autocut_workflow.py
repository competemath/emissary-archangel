"""bump-autocut.yml reads the tree's merge-queue log and the bundle the queue built (as data), and, only when the proposal is complete, starts a recut of bump-library.yml.

What is pinned here: the job that reads the library's files holds no write token, the job that holds one reads nothing of the library and dispatches from the default branch only; nothing
of an input reaches a shell line but through the environment; every action is pinned to a commit; the log can only come from the tree's repository; the recut is started exactly when the
proposal says `go`; and the real `run:` text of the steps is executed (bash -e -o pipefail, as Actions does) in a sandbox with a fake `gh`, over a real bundle and a real log.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE))
import test_propose_cut as tpc  # noqa: E402

PATH = REPO / ".github" / "workflows" / "bump-autocut.yml"
TEXT = PATH.read_text(encoding="utf-8")
DOC = yaml.safe_load(TEXT)
PROPOSE = DOC["jobs"]["propose"]
RECUT = DOC["jobs"]["recut"]
INPUTS = DOC[True]["workflow_dispatch"]["inputs"]  # `on:` is read as True by YAML 1.1


def step(job: dict, name_start: str) -> dict:
    return next(s for s in job["steps"] if s.get("name", "").startswith(name_start) or s.get("id") == name_start)


def bash(block: str, env: dict, cwd: Path, path_prefix: Path | None = None) -> subprocess.CompletedProcess:
    e = {"PATH": f"{path_prefix}:{os.environ['PATH']}" if path_prefix else os.environ["PATH"], "HOME": str(cwd), **env}
    return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", block], cwd=cwd, env=e, capture_output=True, text=True)


class Structure(unittest.TestCase):
    def test_no_default_permissions_the_reader_cannot_write_and_the_writer_reads_nothing(self):
        self.assertEqual(DOC["permissions"], {})
        self.assertEqual(PROPOSE["permissions"], {"contents": "read", "actions": "read"})
        self.assertEqual(RECUT["permissions"], {"actions": "write"})
        self.assertTrue(all("uses" not in s for s in RECUT["steps"]))  # no action, no checkout: nothing of the repository or the bundle is in that job
        self.assertNotIn("persist-credentials: true", TEXT)

    def test_every_action_is_pinned_to_a_commit_with_its_version_in_a_comment(self):
        uses = [ln for ln in TEXT.splitlines() if "uses:" in ln]
        self.assertGreaterEqual(len(uses), 4)
        for ln in uses:
            self.assertRegex(ln, r"uses: [\w./-]+@[0-9a-f]{40} # v\d", ln)

    def test_the_pins_are_the_ones_the_other_workflows_use(self):
        known = set()
        for f in (PATH.parent).glob("*.yml"):
            if f != PATH:
                known |= set(re.findall(r"uses: ([\w./-]+@[0-9a-f]{40})", f.read_text(encoding="utf-8")))
        for ln in TEXT.splitlines():
            m = re.search(r"uses: ([\w./-]+@[0-9a-f]{40})", ln)
            if m:
                self.assertIn(m.group(1), known, "a pin no other workflow of the repository uses")

    def test_an_input_reaches_a_shell_line_only_through_the_environment(self):
        for job in (PROPOSE, RECUT):
            for s in job["steps"]:
                if "run" in s:
                    self.assertNotIn("${{", s["run"], s.get("name"))

    def test_the_library_files_are_read_as_data_by_python_in_isolated_mode(self):
        block = step(PROPOSE, "propose")["run"]
        self.assertIn("python3 -I scripts/bump/propose_cut.py", block)
        for job in (PROPOSE, RECUT):
            for s in job["steps"]:
                self.assertNotRegex(s.get("run", ""), r"\blake\b|\belan\b|\blean\b", "this workflow runs none of the library's Lean")
        self.assertTrue((REPO / "scripts" / "bump" / "propose_cut.py").exists())

    def test_the_log_can_only_come_from_the_trees_repository(self):
        block = step(PROPOSE, "The inputs")["run"]
        self.assertIn(r"^https://api\.github\.com/repos/competemath/tengoku/actions/jobs/[0-9]+/logs$", block)
        fetch = step(PROPOSE, "The queue's log")["run"]
        self.assertEqual(sorted(set(re.findall(r"repos/([\w/-]+)/actions", fetch))), ["competemath/tengoku"])
        self.assertEqual(step(PROPOSE, "The queue's log")["env"], {"GH_TOKEN": "${{ github.token }}"})  # the factory's own token: it reads a public repository's logs

    def test_exactly_one_of_the_two_ways_to_name_the_log(self):
        block = step(PROPOSE, "The inputs")["run"]
        self.assertIn("not both", block)
        self.assertIn("give tengoku_run or queue_log_url", block)

    def test_the_recut_starts_only_on_go_and_only_when_asked_and_only_from_the_default_branch(self):
        cond = RECUT["if"]
        self.assertIn("needs.propose.outputs.go == 'true'", cond)
        self.assertIn("inputs.recut == 'true'", cond)
        self.assertIn("github.ref == format('refs/heads/{0}', github.event.repository.default_branch)", cond)
        self.assertEqual(RECUT["needs"], "propose")
        self.assertEqual(PROPOSE["outputs"]["go"], "${{ steps.propose.outputs.go }}")

    def test_it_dispatches_bump_library_with_inputs_that_workflow_has(self):
        lib = yaml.safe_load((PATH.parent / "bump-library.yml").read_text(encoding="utf-8"))[True]["workflow_dispatch"]["inputs"]
        block = step(RECUT, "Recut")["run"]
        self.assertIn("gh workflow run bump-library.yml", block)
        sent = set(re.findall(r'-f "(\w+)=', block))
        self.assertEqual(sent, {"key", "recut_from", "drop", "scope", "parts"})
        self.assertLessEqual(sent, set(lib))
        self.assertIn("RECUT", lib["recut_from"]["description"])

    def test_defaults_are_the_safe_ones(self):
        self.assertEqual(INPUTS["drop_unexplained"]["default"], "false")
        self.assertEqual(INPUTS["mode"]["default"], "proposed")
        self.assertEqual(DOC["concurrency"]["cancel-in-progress"], False)
        self.assertEqual(DOC["concurrency"]["group"], "bump-autocut-${{ inputs.key }}")

    def test_the_proposal_is_uploaded_even_when_a_step_failed(self):
        up = [s for s in PROPOSE["steps"] if s.get("uses", "").startswith("actions/upload-artifact")][0]
        self.assertEqual(up["if"], "always()")
        self.assertIn("proposal.json", up["with"]["path"])

    def test_the_flags_it_passes_exist_in_the_script(self):
        script = (REPO / "scripts" / "bump" / "propose_cut.py").read_text(encoding="utf-8")
        block = step(PROPOSE, "propose")["run"]
        for flag in re.findall(r"(--[a-z-]+)", block):
            self.assertIn(f'"{flag}"', script, flag)


class Steps(unittest.TestCase):
    """The `run:` text of the steps, executed."""

    def validate(self, **env) -> subprocess.CompletedProcess:
        base = {"KEY": "lib", "BUMP_RUN": "123", "TENGOKU_RUN": "456", "QUEUE_LOG_URL": "", "MODE": "proposed", "PRIOR_DROP": "", "DROP_UNEXPLAINED": "false"}
        return bash(step(PROPOSE, "The inputs")["run"], {**base, **env}, Path(tempfile.mkdtemp()))

    def test_good_inputs_pass(self):
        self.assertEqual(self.validate().returncode, 0)
        self.assertEqual(self.validate(TENGOKU_RUN="", QUEUE_LOG_URL="https://api.github.com/repos/competemath/tengoku/actions/jobs/99/logs", KEY="stafford38-formal").returncode, 0)

    def test_bad_inputs_fail(self):
        bad = [
            {"KEY": "Lib; rm -rf"},
            {"KEY": ""},
            {"BUMP_RUN": "12a"},
            {"TENGOKU_RUN": "4 5"},
            {"TENGOKU_RUN": "", "QUEUE_LOG_URL": ""},
            {"TENGOKU_RUN": "1", "QUEUE_LOG_URL": "https://api.github.com/repos/competemath/tengoku/actions/jobs/99/logs"},
            {"TENGOKU_RUN": "", "QUEUE_LOG_URL": "https://api.github.com/repos/evil/tengoku/actions/jobs/99/logs"},
            {"TENGOKU_RUN": "", "QUEUE_LOG_URL": "https://evil.example/repos/competemath/tengoku/actions/jobs/99/logs"},
            {"TENGOKU_RUN": "", "QUEUE_LOG_URL": "https://api.github.com/repos/competemath/tengoku/actions/jobs/99/logs?x=1"},
            {"MODE": "../strict"},
            {"DROP_UNEXPLAINED": "yes"},
        ]
        for env in bad:
            self.assertNotEqual(self.validate(**env).returncode, 0, env)

    def recut(self, **env):
        d = Path(tempfile.mkdtemp())
        fake = d / "bin"
        fake.mkdir()
        (fake / "gh").write_text('#!/bin/bash\nprintf "%s\\n" "$@" > "$GH_CALLS"\n')
        (fake / "gh").chmod(0o755)
        base = {"GH_TOKEN": "t", "KEY": "lib", "BUMP_RUN": "123", "DROP": "Lib.A,Lib.«1000.0»", "SCOPE": "", "PARTS": "300", "DEFAULT_BRANCH": "main", "GITHUB_REPOSITORY": "competemath/emissary-archangel", "GITHUB_STEP_SUMMARY": str(d / "s"), "GH_CALLS": str(d / "calls")}
        r = bash(step(RECUT, "Recut")["run"], {**base, **env}, d, fake)
        calls = (d / "calls").read_text().splitlines() if (d / "calls").exists() else None
        return r, calls

    def test_the_recut_is_dispatched_with_the_drop_the_bundle_and_nothing_else(self):
        r, calls = self.recut()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(calls, ["workflow", "run", "bump-library.yml", "-R", "competemath/emissary-archangel", "--ref", "main", "-f", "key=lib", "-f", "recut_from=123", "-f", "drop=Lib.A,Lib.«1000.0»", "-f", "scope=", "-f", "parts=300"])

    def test_scope_is_passed_through_as_one_argument(self):
        r, calls = self.recut(SCOPE="leak: a b; leak: c $(touch x)")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("scope=leak: a b; leak: c $(touch x)", calls)

    def test_an_empty_drop_or_one_with_a_space_or_a_bad_run_is_never_dispatched(self):
        for env in ({"DROP": ""}, {"DROP": "Lib.A Lib.B"}, {"DROP": "Lib.A\nLib.B"}, {"BUMP_RUN": "1; x"}, {"KEY": "A B"}, {"PARTS": "x"}):
            r, calls = self.recut(**env)
            self.assertNotEqual(r.returncode, 0, env)
            self.assertIsNone(calls, env)

    def sandbox(self, log: str, *, bundle: bool = True, **env):
        d = Path(tempfile.mkdtemp())
        (d / "scripts").symlink_to(REPO / "scripts")
        shards, shipped = tpc.shapes()
        (d / "bump").mkdir()
        with tarfile.open(d / "bump" / "bundle-lib-proposed.tar", "w") as t:
            for f in sorted(shipped.rglob("*.lean")):
                t.add(f, arcname=str(f.relative_to(shipped)))
        (d / "queue.log").write_text(log)
        (d / "shards").mkdir()
        (d / "shards" / "shard-lib-0").symlink_to(shards / "shard-lib-0")
        base = {"KEY": "lib", "MODE": "proposed", "PRIOR_DROP": "", "DROP_UNEXPLAINED": "false", "GITHUB_OUTPUT": str(d / "out"), "GITHUB_STEP_SUMMARY": str(d / "sum")}
        r = bash(step(PROPOSE, "propose")["run"], {**base, **env}, d)
        out = (d / "out").read_text() if (d / "out").exists() else ""
        return r, out, d

    def test_a_complete_proposal_says_go(self):
        r, out, d = self.sandbox(tpc.err("Lib/B.lean", 4, "Unknown identifier `helper_thing`"))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(out, "go=true\ndrop=Lib.B\n")
        self.assertTrue((d / "proposal.json").exists() and (d / "proposal.txt").exists())
        self.assertIn("### bump-autocut", (d / "sum").read_text())

    def test_it_uses_the_shards_when_there_are_some_and_does_without(self):
        log = tpc.err("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`")
        self.assertEqual(self.sandbox(log)[1], "go=true\ndrop=Lib.A\n")  # class A needs the shards' errors and sources
        r, out, d = self.sandbox(log)
        (d / "shards" / "shard-lib-0").unlink()
        (d / "out").unlink()
        r = bash(step(PROPOSE, "propose")["run"], {"KEY": "lib", "MODE": "proposed", "PRIOR_DROP": "", "DROP_UNEXPLAINED": "false", "GITHUB_OUTPUT": str(d / "out"), "GITHUB_STEP_SUMMARY": str(d / "sum")}, d)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "out").read_text(), "go=true\ndrop=Lib.A\n")  # the name is declared nowhere in the shipped files: dropped as E, with less certainty
        self.assertIn("no shard artifacts", (d / "proposal.json").read_text())

    def test_a_residual_means_no_recut_and_a_green_step(self):
        r, out, d = self.sandbox(tpc.err("Lib/B.lean", 4, "Unknown identifier `helper_thing`") + tpc.err("Lib/G.lean", 3, "failed to synthesize instance"))
        self.assertEqual((r.returncode, out), (0, "go=false\ndrop=\n"))
        self.assertIn("RESIDUAL", (d / "proposal.txt").read_text())
        r, out, d = self.sandbox(tpc.err("Lib/B.lean", 4, "Unknown identifier `helper_thing`") + tpc.err("Lib/G.lean", 3, "failed to synthesize instance"), DROP_UNEXPLAINED="true")
        self.assertEqual((r.returncode, out), (0, "go=true\ndrop=Lib.B,Lib.G\n"))

    def test_a_refusal_by_the_guard_is_a_green_step_with_no_go_and_the_proposal_kept(self):
        log = "".join(tpc.err(f"Lib/{m}.lean", 3, f"Unknown constant `Nat.zzz_{m}`") for m in "ABCDG")
        r, out, d = self.sandbox(log)
        self.assertEqual((r.returncode, out), (0, "go=false\ndrop=\n"))
        self.assertIn("REFUSED", (d / "proposal.txt").read_text())
        self.assertIn('"refused"', (d / "proposal.json").read_text())

    def test_a_script_that_dies_fails_the_step(self):
        r, out, d = self.sandbox("", PRIOR_DROP="not a module")
        self.assertNotEqual(r.returncode, 0)
        self.assertNotIn("go=true", out)
        r, out, d = self.sandbox("", MODE="nonesuch")  # no such bundle
        self.assertNotEqual(r.returncode, 0)


if __name__ == "__main__":
    unittest.main()
