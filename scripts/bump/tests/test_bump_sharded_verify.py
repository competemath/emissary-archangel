"""bump-sharded.yml builds the bundle in the tree before it signs it: compose -> verify -> finish.

The factory used to hand the merge queue a bundle that had never been compiled in the tree (2026-10-10 to 12: seven rejected parts, every one a module the tree behaves
differently on). The guarantee is structural, so it is pinned structurally: what runs the library's Lean holds no signing identity, what signs runs no Lean, the draft and the
final bundle are cut by the same command, and nothing is packed before the byte-for-byte check.
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

import yaml

PATH = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "bump-sharded.yml"
DOC = yaml.safe_load(PATH.read_text(encoding="utf-8"))
JOBS = DOC["jobs"]
INPUTS = DOC[True]["workflow_dispatch"]["inputs"]


def runs(job: str) -> str:
    return "\n".join(s["run"] for s in JOBS[job]["steps"] if isinstance(s.get("run"), str))


def step(job: str, needle: str) -> dict:
    found = [s for s in JOBS[job]["steps"] if needle in s.get("name", "")]
    assert len(found) == 1, (job, needle, len(found))
    return found[0]


def needs(job: str) -> set[str]:
    n = JOBS[job].get("needs", [])
    return {n} if isinstance(n, str) else set(n)


def compose_command(job: str) -> str:
    text = step(job, "Merge the shards and cut the bundle")["run"]
    return re.search(r"python3 scripts/bump/bundle\.py compose.*", text, re.S).group(0)


class Order(unittest.TestCase):
    def test_compose_then_verify_then_finish(self):
        self.assertEqual(needs("compose"), {"plan", "shard"})
        self.assertEqual(needs("verify"), {"compose"})
        self.assertEqual(needs("finish"), {"compose", "verify"})

    def test_a_verify_that_failed_or_was_killed_ships_nothing(self):
        cond = JOBS["finish"]["if"]
        self.assertIn("needs.compose.result == 'success'", cond)
        self.assertIn("needs.verify.result == 'success' || needs.verify.result == 'skipped'", cond)
        self.assertNotIn("always()", cond)

    def test_verify_is_skipped_only_when_no_mode_is_to_be_verified(self):
        self.assertIn("needs.compose.outputs.modes != '[]'", JOBS["verify"]["if"])

    def test_the_inputs(self):
        self.assertEqual(INPUTS["verify"]["default"], "true")
        self.assertEqual(INPUTS["verify_partial"]["default"], "false")  # a build that does not finish fails the run unless someone asks otherwise
        self.assertEqual(INPUTS["verify_modes"]["default"], "proposed")  # what intake_open ships (--mode proposed)

    def test_the_artifact_the_opener_reads_keeps_its_name(self):
        names = [s["with"]["name"] for s in JOBS["finish"]["steps"] if "upload-artifact" in str(s.get("uses", ""))]
        self.assertEqual(names, ["bump-${{ inputs.key }}"])


class Privileges(unittest.TestCase):
    def test_what_compiles_the_library_holds_no_signing_identity_and_no_write(self):
        self.assertEqual(JOBS["verify"]["permissions"], {"contents": "read"})

    def test_compose_signs_nothing(self):
        self.assertNotIn("id-token", JOBS["compose"]["permissions"])
        self.assertNotIn("attestations", JOBS["compose"]["permissions"])

    def test_only_finish_signs_and_it_runs_no_lean(self):
        self.assertIn("id-token", JOBS["finish"]["permissions"])
        self.assertIn("attestations", JOBS["finish"]["permissions"])
        text = runs("finish")
        self.assertIsNone(re.search(r"(?<![\w./-])(lake|lean|elan|elan-init)\s", text), "a command that runs Lean")  # `.lean ` in a path is no command
        self.assertNotIn("tree_verify.py apply", text)
        self.assertNotIn("tree_verify.py collect", text)

    def test_the_build_step_sees_no_token(self):
        build = step("verify", "Build them")
        self.assertNotIn("GH_TOKEN", build.get("env", {}))
        self.assertNotIn("GH_TOKEN", JOBS["verify"].get("env", {}))
        self.assertNotIn("GITHUB_TOKEN", build.get("env", {}))
        seed = step("verify", "seeded from the newest published cache")
        self.assertEqual(seed["env"]["TENGOKU_VERIFY"], "require")  # an unattested cache is refused, as in the queue
        self.assertEqual(seed["env"]["TENGOKU_TOPUPS"], "1")  # the queue's starting point: the nightly cache plus the newest promoted top-up

    def test_the_build_is_capped_inside_the_job(self):
        cap = int(re.search(r"timeout -k \d+ (\d+)m lake build", step("verify", "Build them")["run"]).group(1))
        self.assertLess(cap, JOBS["verify"]["timeout-minutes"])
        self.assertLessEqual(JOBS["verify"]["timeout-minutes"], 360)  # what a hosted runner allows


class PartialBuilds(unittest.TestCase):
    def test_the_flag_reaches_every_collect_step_only_when_asked_for(self):
        self.assertEqual(JOBS["verify"]["env"]["VERIFY_PARTIAL"], "${{ inputs.verify_partial }}")
        for name in ("What the build accepted", "The modules that share a name with the tree", "What the tree accepted"):
            run = step("verify", name)["run"]
            self.assertIn('if [ "$VERIFY_PARTIAL" = true ]; then flag=(--allow-unfinished); fi', run, name)
            self.assertIn('"${flag[@]}"', run, name)

    def test_the_budgets_fit_inside_the_job(self):
        build = int(re.search(r"timeout -k \d+ (\d+)m lake build", step("verify", "Build them")["run"]).group(1))
        axioms = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", step("verify", "The axiom check")["run"]).group(1))
        self.assertLessEqual(build + axioms + 20 + 50 + 25, JOBS["verify"]["timeout-minutes"])  # + the clash scan's 20, the union import's 50, and 25 minutes for the seed, the copy, the verdict and the upload


class TheUnionCheck(unittest.TestCase):
    """`import Tengoku.All` loads every library at once; no module imports two of them, so only this finds a name two libraries both declare (lean-pool part 10, 2026-10-12)."""

    def names(self) -> list[str]:
        return [s.get("name", "") for s in JOBS["verify"]["steps"]]

    def test_it_runs_after_the_build_is_read_and_before_the_axiom_check(self):
        n = self.names()
        first = next(i for i, x in enumerate(n) if x.startswith("What the build accepted"))
        clash = next(i for i, x in enumerate(n) if x.startswith("The names that two modules"))
        axioms = next(i for i, x in enumerate(n) if x.startswith("The axiom check"))
        last = next(i for i, x in enumerate(n) if x.startswith("What the tree accepted"))
        self.assertTrue(first < clash < axioms < last)

    def test_a_module_that_shares_a_name_never_reaches_the_axiom_check(self):
        """lana-oka, 2026-10-19: the axiom check imports everything that built in ONE environment, and the library's own copy of Mathlib's Sheaf/Submodule (SheafOfModules.Submodule.noConfusion,
        also in the seed) stopped it with `environment already contains`, before the scan that names such a pair had run: the whole verify failed and nothing shipped."""
        n = self.names()
        clash = next(i for i, x in enumerate(n) if x.startswith("The names that two modules"))
        refresh = next(i for i, x in enumerate(n) if x.startswith("The modules that share a name with the tree"))
        axioms = next(i for i, x in enumerate(n) if x.startswith("The axiom check"))
        self.assertTrue(clash < refresh < axioms)
        run = step("verify", "The modules that share a name with the tree")["run"]
        self.assertIn("tree_verify.py collect", run)
        self.assertIn("--out out", run)  # it rewrites out/built.txt, the list the axiom check imports
        self.assertIn("--clashes out/clashes.txt", run)
        self.assertNotIn("--axioms", run)  # there is no axiom check yet
        self.assertNotIn("env", step("verify", "The modules that share a name with the tree"))  # no token
        self.assertIn("../out/built.txt", step("verify", "The axiom check")["run"])

    def test_it_reads_the_modules_that_built_and_the_verdict_reads_its_output(self):
        run = step("verify", "The names that two modules")["run"]
        self.assertIn("lake env lean --run ../emissary/scripts/bump/ModuleClashes.lean .lake/build/lib/lean ../out/built.txt Tengoku", run)
        self.assertIn("tee ../out/clashes.txt", run)
        self.assertIn("timeout -k 60 20m", run)
        self.assertNotIn("env", step("verify", "The names that two modules"))  # no token
        self.assertIn("--clashes out/clashes.txt", step("verify", "What the tree accepted")["run"])
        self.assertNotIn("--clashes", step("verify", "What the build accepted")["run"])

    def test_its_output_travels_to_the_artifact(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        self.assertIn("out/clashes.txt", up)

    def test_the_program_prints_what_the_python_side_reads(self):
        lean = (PATH.parents[2] / "scripts" / "bump" / "ModuleClashes.lean").read_text()
        self.assertIn('IO.println s!"CLASH\\t{files[i]!.1}\\t{files[j]!.1}\\t{c}\\t{f}"', lean)
        self.assertIn('clashes: {pairs.size} module pair(s), {names} name(s)', lean)

    def test_the_program_applies_leans_own_duplicate_rule(self):
        """The first run (lean-pool, 2026-10-13) flagged 155 modules, most of them over `foo.eq_1` / `foo.congr_simp`, which Lean's import allows (Lean.Environment `subsumesInfo`)."""
        lean = (PATH.parents[2] / "scripts" / "bump" / "ModuleClashes.lean").read_text()
        self.assertIn("def subsumes (a b : ConstantInfo) : Bool", lean)
        self.assertIn("a.name == b.name && a.type == b.type && a.levelParams == b.levelParams", lean)
        self.assertIn(".thmInfo x, .thmInfo y => x.all == y.all", lean)
        self.assertNotIn(".axiomInfo x, .axiomInfo y", lean)  # two axioms are a clash (the real rule needs a propositional type that this program cannot look up)
        self.assertIn("!(subsumes ci prev || subsumes prev ci)", lean)  # either direction, as `importModules` tries both
        self.assertIn("for n in data.constNames, ci in data.constants do", lean)

    def test_the_budgets_still_fit_the_job(self):
        build = int(re.search(r"timeout -k \d+ (\d+)m lake build", step("verify", "Build them")["run"]).group(1))
        axioms = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", step("verify", "The axiom check")["run"]).group(1))
        clash = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", step("verify", "The names that two modules")["run"]).group(1))
        union = int(re.search(r"deadline=\$\(\(SECONDS \+ (\d+)\)\)", step("verify", "The import of the whole tree")["run"]).group(1)) // 60
        self.assertLessEqual(build + axioms + clash + union + 25, JOBS["verify"]["timeout-minutes"])


class TheUnionImport(unittest.TestCase):
    """Lean itself is the authority on what `import Tengoku.All` accepts: a static scan of the oleans missed a real clash twice (lean-pool part 10, 2026-10-13)."""

    def names(self) -> list[str]:
        return [s.get("name", "") for s in JOBS["verify"]["steps"]]

    def test_it_runs_after_the_static_scan_and_before_the_final_verdict(self):
        n = self.names()
        clash = next(i for i, x in enumerate(n) if x.startswith("The names that two modules"))
        union = next(i for i, x in enumerate(n) if x.startswith("The import of the whole tree"))
        last = next(i for i, x in enumerate(n) if x.startswith("What the tree accepted"))
        self.assertTrue(clash < union < last)

    def test_it_elaborates_the_generated_file_with_lake_env_lean_and_loops_on_the_refusal(self):
        run = step("verify", "The import of the whole tree")["run"]
        self.assertIn("tree_verify.py union-input", run)
        self.assertIn("lake env lean ../out/UnionImport.lean", run)
        self.assertIn("tree_verify.py union-next", run)
        self.assertIn("timeout -k 30 20m", run)  # one elaboration is capped
        self.assertRegex(run, r"deadline=\$\(\(SECONDS \+ 3000\)\)")  # the loop is capped too
        self.assertIn('[ "$settled" = 1 ] ||', run)  # a loop that did not settle fails the job: nothing ships on a guess

    def test_only_those_the_build_made_ok_are_new(self):
        self.assertIn("--keep out/built.txt", step("verify", "The import of the whole tree")["run"])

    def test_the_tree_is_the_root_the_queue_builds_and_is_not_enumerated(self):
        """Two attempts that listed the tree's modules were refused by pairs no `import Tengoku.All` contains: stale oleans of modules that no longer exist (the seed's move), and the sources of
        alternatives that are never imported together (Aesop's DiscrKeyConfig and DiscrTreeConfig both declare `Aesop.indexConfig`). The queue's last step builds `Tengoku.All`, so that is the root."""
        run = step("verify", "The import of the whole tree")["run"]
        self.assertIn("tree_verify.py union-input --root Tengoku.All", run)
        self.assertNotIn("find Tengoku", run)
        self.assertNotIn("tree-modules", run)
        self.assertNotIn("--tree-modules", run)


    def test_the_refreshed_collect_runs_before_it_and_the_final_one_reads_its_verdict(self):
        run = step("verify", "The import of the whole tree")["run"]
        self.assertLess(run.index("tree_verify.py collect"), run.index("tree_verify.py union-input"))
        self.assertIn("--union-excluded out/union-excluded.txt", step("verify", "What the tree accepted")["run"])
        self.assertNotIn("--union-excluded", run)

    def test_it_holds_no_token(self):
        self.assertNotIn("env", step("verify", "The import of the whole tree"))

    def test_what_it_leaves_travels_to_the_artifact(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        for f in ("out/union-excluded.txt", "out/union-excluded.reasons", "out/union-*.txt"):
            self.assertIn(f, up)


class ArtifactLayout(unittest.TestCase):
    """The first live run (2026-10-12): the artifact held `out/summary.txt` next to `tree-sha.txt`, so its root was the workspace and every path had `out/` in front; the glob in `finish`
    matched nothing and the list of refused modules was empty. Only the byte-for-byte check kept the bundle from shipping."""

    def test_every_file_of_the_verdict_artifact_is_under_out_so_that_out_is_its_root(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        paths = [p.strip() for p in up.splitlines() if p.strip()]
        self.assertTrue(paths)
        self.assertTrue(all(p.startswith("out/") for p in paths), paths)
        self.assertTrue(all(p.rsplit("/", 1)[0] == "out" for p in paths), "one directory deep: the artifact's root is out/")

    def run_step(self, modes: str, layout: dict[str, str]):
        import subprocess
        import tempfile

        d = Path(tempfile.mkdtemp())
        (d / "draft").mkdir()
        (d / "draft" / "tree-names.txt").write_text("")
        (d / "draft" / "tree-decls.txt").write_text("")
        (d / "emissary").symlink_to(PATH.parents[2])  # the step merges the repairs with the repository's own script
        for rel, text in layout.items():
            (d / rel).parent.mkdir(parents=True, exist_ok=True)
            (d / rel).write_text(text)
        r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step("finish", "What the tree refused")["run"]], cwd=d, env={"PATH": __import__("os").environ["PATH"], "KEY": "lib", "MODES": modes}, capture_output=True, text=True)
        return r, d

    NO_REPAIRS = '{"rule": "R2", "modules": {}}'
    GOOD = {f"treeverify/treeverify-lib-proposed/{f}": "" for f in ("ok.json", "new.json", "summary.txt")} | {"treeverify/treeverify-lib-proposed/repairs.json": NO_REPAIRS}

    def test_a_complete_verdict_is_read(self):
        r, d = self.run_step('["proposed"]', {**self.GOOD, "treeverify/treeverify-lib-proposed/failing.txt": "B.C\nA.X\n"})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "tree-failures.txt").read_text(), "A.X\nB.C\n")

    def test_the_refusals_of_two_modes_are_joined_without_repeats(self):
        layout = {f"treeverify/treeverify-lib-{m}/{f}": "" for m in ("proposed", "wide") for f in ("ok.json", "new.json", "summary.txt")}
        layout |= {f"treeverify/treeverify-lib-{m}/repairs.json": self.NO_REPAIRS for m in ("proposed", "wide")}
        layout["treeverify/treeverify-lib-proposed/failing.txt"] = "A.X\n"
        layout["treeverify/treeverify-lib-wide/failing.txt"] = "A.X\nW.Y\n"
        r, d = self.run_step('["proposed", "wide"]', layout)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "tree-failures.txt").read_text(), "A.X\nW.Y\n")

    def test_the_repairs_of_every_verified_mode_are_merged_for_compose(self):
        import json

        entry = {"module": "Tengoku.Lib.X", "path": "Tengoku/Lib/X.lean", "before": "1", "after": "2", "repairs": []}
        layout = {f"treeverify/treeverify-lib-{m}/{f}": "" for m in ("proposed", "wide") for f in ("ok.json", "new.json", "summary.txt", "failing.txt")}
        layout["treeverify/treeverify-lib-proposed/repairs.json"] = json.dumps({"rule": "R2", "modules": {"X": entry}})
        layout["treeverify/treeverify-lib-wide/repairs.json"] = json.dumps({"rule": "R2", "modules": {"X": entry, "Y": entry}})
        r, d = self.run_step('["proposed", "wide"]', layout)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(sorted(json.loads((d / "tree-repairs.json").read_text())["modules"]), ["X", "Y"])

    def test_a_verdict_without_its_repairs_stops_the_run(self):
        layout = dict(self.GOOD)
        del layout["treeverify/treeverify-lib-proposed/repairs.json"]
        layout["treeverify/treeverify-lib-proposed/failing.txt"] = ""
        r, _ = self.run_step('["proposed"]', layout)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("repairs.json is missing", r.stdout + r.stderr)

    def test_a_verdict_with_the_old_out_prefix_is_not_an_empty_list(self):
        r, _ = self.run_step('["proposed"]', {f"treeverify/treeverify-lib-proposed/out/{f}": "" for f in ("failing.txt", "ok.json", "new.json", "summary.txt")})
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("incomplete", r.stdout + r.stderr)

    def test_a_mode_whose_artifact_is_missing_stops_the_run(self):
        r, _ = self.run_step('["proposed"]', {})
        self.assertNotEqual(r.returncode, 0)

    def test_a_verdict_missing_one_file_stops_the_run(self):
        layout = {**self.GOOD, "treeverify/treeverify-lib-proposed/failing.txt": ""}
        del layout["treeverify/treeverify-lib-proposed/ok.json"]
        r, _ = self.run_step('["proposed"]', layout)
        self.assertNotEqual(r.returncode, 0)

    def test_no_mode_to_verify_is_an_empty_list_and_no_error(self):
        r, d = self.run_step("[]", {})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "tree-failures.txt").read_text(), "")
        self.assertEqual(__import__("json").loads((d / "tree-repairs.json").read_text()), {"rule": "R2", "modules": {}})  # an empty file, not a missing one: compose is given the path either way


class TheQueuesAxiomCheckToo(unittest.TestCase):
    def names(self) -> list[str]:
        return [s.get("name", "") for s in JOBS["verify"]["steps"]]

    def test_the_axiom_check_runs_between_the_build_and_the_final_verdict(self):
        n = self.names()
        build = next(i for i, x in enumerate(n) if x.startswith("Build them"))
        first = next(i for i, x in enumerate(n) if x.startswith("What the build accepted"))
        axioms = next(i for i, x in enumerate(n) if x.startswith("The axiom check"))
        last = next(i for i, x in enumerate(n) if x.startswith("What the tree accepted"))
        self.assertTrue(build < first < axioms < last)

    def test_it_checks_exactly_what_built_and_the_verdict_reads_its_output(self):
        run = step("verify", "The axiom check")["run"]
        self.assertIn("lake env lean --run ../emissary/scripts/bump/ModuleAxioms.lean ../out/built.txt", run)
        self.assertIn("tee ../out/axioms.txt", run)
        self.assertIn("timeout -k 60 15m", run)
        self.assertIn("--axioms out/axioms.txt", step("verify", "What the tree accepted")["run"])
        self.assertNotIn("--axioms", step("verify", "What the build accepted")["run"])

    def test_the_axiom_check_has_no_token_either(self):
        self.assertNotIn("env", step("verify", "The axiom check"))

    def test_its_output_travels_to_the_artifact(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        self.assertIn("out/axioms.txt", up)

    def test_the_program_prints_what_the_python_side_reads(self):
        lean = (PATH.parents[2] / "scripts" / "bump" / "ModuleAxioms.lean").read_text()
        self.assertIn('IO.println s!"AXIOM\\t{m}\\t{n}\\t', lean)
        self.assertIn('axioms: {checked} declarations checked, {bad} with non-standard axioms', lean)
        self.assertIn("[``propext, ``Classical.choice, ``Quot.sound]", lean)  # the same allowed list as the tree's TengokuAxioms.lean


class CopiesOfTreeModules(unittest.TestCase):
    """`dups` (tree_dups.py): a library's copy of a module the tree has is kept for the tree's build to decide; if it is the same as the tree's, what imports it imports the tree's module.
    The workflow's part of the guarantee: nothing changes unless the input is on; whatever does not run, has no time, or does not finish leaves 'nothing aliased'; the swap's refusals reach
    every verdict that is read afterwards; and the cut that ships makes the same edit as the checkout."""

    def names(self) -> list[str]:
        return [s.get("name", "") for s in JOBS["verify"]["steps"]]

    def dups_steps(self) -> list[str]:
        return [n for n in self.names() if n.startswith("Copies of tree modules")]

    def test_the_input_is_off_by_default(self):
        self.assertEqual(INPUTS["dups"]["default"], "false")
        self.assertEqual(JOBS["verify"]["env"]["DUPS"], "${{ inputs.dups }}")

    def test_the_draft_keeps_the_copies_only_when_asked_for_and_only_with_a_tree_build_to_decide_them(self):
        run = step("compose", "Merge the shards and cut the bundle")["run"]
        self.assertIn('if [ "$DUPS" = true ] && [ "$VERIFY" != false ]; then keep=(--keep-dups); fi', run)
        self.assertTrue(run.rstrip().endswith('"${keep[@]}"'))
        self.assertNotIn("--tree-dups", run)  # nothing is decided yet

    def test_the_final_cut_applies_the_verdict_only_when_the_tree_built_the_draft(self):
        run = step("finish", "Merge the shards and cut the bundle")["run"]
        self.assertIn('if [ "$DUPS" = true ] && [ "$VERIFIED" = success ]; then keep=(--keep-dups --tree-dups ../tree-dups.json); fi', run)
        self.assertTrue(run.rstrip().endswith('"${keep[@]}"'))
        self.assertEqual(JOBS["finish"]["env"]["VERIFIED"], "${{ needs.verify.result }}")

    def test_the_verdict_of_every_verified_mode_is_required_and_merged(self):
        run = step("finish", "What the tree refused")["run"]
        self.assertIn('dups_files+=("$dir/dups.json")', run)
        self.assertIn("has no dups.json", run)  # an artifact that lacks its verdict must never read as 'nothing aliased'
        self.assertIn('tree_dups.py merge --out tree-dups.json "${dups_files[@]}"', run)

    def test_the_steps_run_after_the_build_is_read_and_before_the_clash_scan(self):
        n = self.names()
        first = next(i for i, x in enumerate(n) if x.startswith("What the build accepted"))
        clash = next(i for i, x in enumerate(n) if x.startswith("The names that two modules"))
        idx = [i for i, x in enumerate(n) if x.startswith("Copies of tree modules")]
        self.assertEqual(len(idx), 5)
        self.assertTrue(first < idx[0] and idx[-1] < clash, (first, idx, clash))

    def test_what_is_found_decides_which_later_step_runs(self):
        for name in self.dups_steps()[1:3]:
            self.assertEqual(step("verify", name)["if"], "${{ steps.dups_find.outputs.found == 'true' }}")
        for name in self.dups_steps()[3:]:
            self.assertEqual(step("verify", name)["if"], "${{ steps.dups_plan.outputs.swapped == 'true' }}")

    def test_no_step_holds_a_token_and_every_lean_run_is_capped(self):
        for name in self.dups_steps():
            st = step("verify", name)
            self.assertNotIn("env", st, name)
            run = st["run"]
            if "lake env lean" in run:
                self.assertIn("timeout -k", run, name)
            if "lake build" in run:
                self.assertIn("timeout -k 60", run, name)

    def test_a_clash_scan_that_does_not_finish_leaves_nothing_aliased_and_does_not_fail_the_job(self):
        """CodeRabbit on emissary#69: the scan can stop at its cap (3 minutes at the least). Its output then has no `clashes:` line, `candidates` would refuse it, and the step (and so verify, and with it
        the whole bundle) would fail for an optional step."""
        run = step("verify", "Copies of tree modules in the draft")["run"]
        scan = run.index("ModuleClashes.lean")
        line = run[scan: run.index("\n", scan)]
        self.assertIn("> ../out/clashes-dups.txt 2>&1 || true", line)  # no pipe (pipefail) and no failing exit
        self.assertNotIn("| tee", line)
        guard = run.index("grep -q '^clashes: ' out/clashes-dups.txt")
        self.assertLess(guard, run.index("tree_dups.py candidates"))  # candidates runs only on a scan that has its ending
        self.assertIn("did not finish: nothing is aliased", run)

    def test_the_default_verdict_exists_whatever_runs(self):
        """A step that does not run, has no time, or whose Lean program does not finish leaves a verdict in which nothing is aliased: `finish` finds the file and the copy goes the way it went before."""
        self.assertIn("dups-failures.txt", step("verify", "Copy the new modules into the tree")["run"])
        self.assertIn('json.dump({"ns": n["ns"], "mode": sys.argv[1], "aliases": {}', step("verify", "Copies of tree modules in the draft")["run"])

    def test_the_time_they_may_spend_leaves_the_steps_that_must_still_run(self):
        """The clock starts the job; each step spends what is left of the job less the caps of the steps after it (the axiom check, the clash scan, the whole-tree import, the verdict)."""
        self.assertEqual(self.names()[0], "The clock")
        self.assertIn("JOB_START=$(date +%s)", step("verify", "The clock")["run"])
        axioms = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", step("verify", "The axiom check")["run"]).group(1))
        clash = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", step("verify", "The names that two modules")["run"]).group(1))
        union = int(re.search(r"deadline=\$\(\(SECONDS \+ (\d+)\)\)", step("verify", "The import of the whole tree")["run"]).group(1)) // 60
        reserve = axioms + clash + union + 25
        for name in self.dups_steps():
            run = step("verify", name)["run"]
            if "JOB_START" in run:
                self.assertIn(f"JOB_START + {JOBS['verify']['timeout-minutes']} * 60", run, name)
                self.assertIn(f"/ 60 - {reserve} ))", run, name)

    def test_the_refusals_of_the_swap_reach_every_verdict_read_afterwards(self):
        flag = "--extra-failing out/dups-failures.txt"
        self.assertNotIn(flag, step("verify", "What the build accepted")["run"])  # before the swap
        self.assertIn(flag, step("verify", "The modules that share a name with the tree")["run"])  # the list the axiom check imports
        self.assertIn(flag, step("verify", "The import of the whole tree")["run"])  # the refreshed collect before the union loop
        self.assertIn(flag, step("verify", "What the tree accepted")["run"])  # the final verdict

    def test_the_swap_is_built_by_the_queues_command_and_its_log_joins_the_build_log(self):
        run = step("verify", "Copies of tree modules, the importers built")["run"]
        self.assertIn("lake build $targets", run)
        self.assertIn("tee ../out/build-dups.log", run)
        self.assertIn("cat ../out/build-dups.log >> ../out/build.log", run)  # the verdicts that read build.log see a failure of the second build too
        self.assertLess(run.index(": > out/build-dups.log"), run.index("lake build"))  # no time: an empty log is 'nothing was built', never a clean one

    def test_the_program_prints_what_the_python_side_reads(self):
        lean = (PATH.parents[2] / "scripts" / "bump" / "ModuleFingerprint.lean").read_text()
        self.assertIn('IO.println s!"FP\\t{m}\\t{canon n}\\t{kindName ci}\\t{hex16 h.1}{hex16 h.2}"', lean)
        self.assertIn('IO.println s!"fingerprints: {count} declarations"', lean)
        self.assertNotIn("sorry", lean)  # it is a program that decides nothing about truth, and says so

    def test_the_artifact_carries_the_verdict_and_what_it_rests_on(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        for f in ("out/dups.json", "out/dups-failures.txt", "out/dups-candidates.json", "out/fp-before.txt", "out/fp-partners.txt", "out/fp-after.txt", "out/build-dups.log"):
            self.assertIn(f, up)


class NothingMutableRunsBeforeTheVerdict(unittest.TestCase):
    """CodeRabbit (emissary#39): the verify job's verdict is what `finish` signs, so the installer it runs must be pinned and checked, not `releases/latest`."""

    def test_the_elan_installer_is_pinned_to_a_commit_and_checked_against_its_digest(self):
        run = step("verify", "Lean toolchain")["run"]
        self.assertRegex(run, r"raw\.githubusercontent\.com/leanprover/elan/[0-9a-f]{40}/elan-init\.sh")
        self.assertRegex(run, r'echo "[0-9a-f]{64}  elan-init\.sh" \| sha256sum -c -')
        self.assertLess(run.index("sha256sum -c -"), run.index("sh elan-init.sh"))  # checked BEFORE it runs
        self.assertNotIn("releases/latest", run)

    def test_it_is_the_installer_the_other_lean_workflow_already_uses(self):
        other = (PATH.parent / "bundle-keep-tests.yml").read_text()
        run = step("verify", "Lean toolchain")["run"]
        commit = re.search(r"/elan/([0-9a-f]{40})/", run).group(1)
        digest = re.search(r'echo "([0-9a-f]{64})  elan-init', run).group(1)
        self.assertIn(commit, other)
        self.assertIn(digest, other)

    def test_no_job_that_compiles_library_code_downloads_a_mutable_binary(self):
        for job in ("compose", "verify", "finish"):
            self.assertNotIn("releases/latest", runs(job), job)


class TheDiskIsMeasuredAndFreed(unittest.TestCase):
    """2026-10-13: the tauceti verify job, the queue's last step for lean-pool part 10 and both nightly cache builds were LOST (no log, no error) within 12 hours: the runner has 145 GB, 34 GB
    used before anything runs, and the tree's build directory takes most of the rest."""

    def test_the_runner_is_cleaned_of_what_the_build_does_not_use(self):
        run = step("verify", "Free disk")["run"]
        for path in ("/opt/hostedtoolcache", "/usr/lib/jvm", "/usr/share/miniconda", "/usr/local/lib/android", "/usr/share/dotnet", "/opt/ghc"):
            self.assertIn(path, run)
        self.assertIn("docker image prune --all --force", run)
        self.assertIn("swapoff -a", run)

    def test_what_the_build_needs_is_not_removed(self):
        run = step("verify", "Free disk")["run"]
        for needed in ("/usr/bin", "/usr/lib/x86_64", "/home/runner", "$HOME", "/usr/local/bin", "/usr/local/sbin"):
            self.assertNotIn(f"rm -rf {needed}", run)
            self.assertNotRegex(run, rf"rm -rf [^|]*\s{re.escape(needed)}(\s|$)")

    def test_the_disk_is_logged_after_freeing_after_seeding_every_minute_and_after_the_build(self):
        self.assertIn("out/disk.log", step("verify", "Free disk")["run"])
        self.assertIn("du -sh .lake/build", step("verify", "The tree, seeded")["run"])
        build = step("verify", "Build them")["run"]
        self.assertIn("sleep 60", build)
        self.assertIn("MemAvailable", build)
        self.assertIn('kill "$sampler"', build)  # the sampler never outlives the build

    def test_the_log_travels_to_the_artifact(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["path"]
        self.assertIn("out/disk.log", up)

    def test_the_apply_step_does_not_wipe_the_log(self):
        # out/ is created by the Free disk step now; apply must go on writing into it
        self.assertIn("mkdir -p out", step("verify", "Free disk")["run"])


class SameBundle(unittest.TestCase):
    def test_the_draft_and_the_final_bundle_are_cut_by_the_same_command(self):
        draft, final = compose_command("compose"), compose_command("finish")
        self.assertNotIn("--tree-failures", draft)
        self.assertNotIn("--tree-repairs", draft)  # the repairs come out of the tree's build of the draft
        self.assertEqual(final.replace(" --tree-failures ../tree-failures.txt", "").replace(" --tree-repairs ../tree-repairs.json", ""), draft)

    def test_both_use_the_names_the_draft_froze(self):
        self.assertIn("cp draft/tree-names.txt draft/tree-decls.txt .", runs("finish"))
        self.assertNotIn("tree_names.py", runs("finish"))  # not recomputed: a part that merged in between would change what is pruned
        self.assertIn("cp tree-names.txt tree-decls.txt draft/", runs("compose"))

    def test_the_scope_rewrite_comes_before_the_draft_is_taken_and_before_the_check(self):
        c = [s.get("name", "") for s in JOBS["compose"]["steps"]]
        self.assertLess(next(i for i, n in enumerate(c) if "registrations" in n), next(i for i, n in enumerate(c) if "draft, for" in n))
        f = [s.get("name", "") for s in JOBS["finish"]["steps"]]
        self.assertLess(next(i for i, n in enumerate(f) if "registrations" in n), next(i for i, n in enumerate(f) if "byte for byte" in n))

    def test_the_artifact_names_match_between_verify_and_finish(self):
        up = next(s for s in JOBS["verify"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["name"]
        down = next(s for s in JOBS["finish"]["steps"] if "download-artifact" in str(s.get("uses", "")) and "treeverify" in str(s["with"].get("pattern", "")))["with"]["pattern"]
        self.assertEqual(up, "treeverify-${{ inputs.key }}-${{ matrix.mode }}")
        self.assertEqual(down, "treeverify-${{ inputs.key }}-*")
        self.assertEqual(next(s for s in JOBS["compose"]["steps"] if "upload-artifact" in str(s.get("uses", "")))["with"]["name"], "draft-${{ inputs.key }}")


class NothingIsPackedBeforeTheCheck(unittest.TestCase):
    def test_the_check_runs_before_packing_and_signing(self):
        names = [s.get("name", s.get("uses", "")) for s in JOBS["finish"]["steps"]]
        check = next(i for i, n in enumerate(names) if "byte for byte" in n)
        pack = next(i for i, n in enumerate(names) if n == "Pack and attest")
        attest = next(i for i, n in enumerate(names) if "attest-build-provenance" in n)
        self.assertLess(check, pack)
        self.assertLess(pack, attest)

    def test_the_final_compose_drops_what_the_tree_refused_and_the_check_covers_every_verified_mode(self):
        self.assertIn("--tree-failures ../tree-failures.txt", compose_command("finish"))
        text = step("finish", "byte for byte")["run"]
        self.assertIn("tree_verify.py check", text)
        self.assertIn('for mode in $(python3 -c', text)  # every mode that was to be verified (compose's list), not whatever directories happen to be there
        self.assertEqual(step("finish", "byte for byte")["env"]["MODES"], "${{ needs.compose.outputs.modes }}")
        self.assertIn("sort -u -o tree-failures.txt", step("finish", "What the tree refused")["run"])

    def test_the_draft_of_a_mode_is_the_bundle_of_that_mode(self):
        text = step("compose", "The draft")["run"]
        self.assertIn('dir=bundle; [ "$mode" != strict ] && dir="bundle-$mode"', text)
        self.assertIn('tar -C "$dir" -cf "draft-$mode.tar" .', text)
        self.assertIn('x not in ("strict", "proposed", "wide")', text)  # an unknown mode name is an error, not a silent skip


if __name__ == "__main__":
    unittest.main()
