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
    def test_the_flag_reaches_both_collect_steps_only_when_asked_for(self):
        self.assertEqual(JOBS["verify"]["env"]["VERIFY_PARTIAL"], "${{ inputs.verify_partial }}")
        for name in ("What the build accepted", "What the tree accepted"):
            run = step("verify", name)["run"]
            self.assertIn('if [ "$VERIFY_PARTIAL" = true ]; then flag=(--allow-unfinished); fi', run, name)
            self.assertIn('"${flag[@]}"', run, name)

    def test_the_budgets_fit_inside_the_job(self):
        build = int(re.search(r"timeout -k \d+ (\d+)m lake build", step("verify", "Build them")["run"]).group(1))
        axioms = int(re.search(r"timeout -k \d+ (\d+)m lake env lean", step("verify", "The axiom check")["run"]).group(1))
        self.assertLessEqual(build + axioms + 25, JOBS["verify"]["timeout-minutes"])  # 25 minutes for the seed, the copy, the verdict and the upload


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
        for rel, text in layout.items():
            (d / rel).parent.mkdir(parents=True, exist_ok=True)
            (d / rel).write_text(text)
        r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step("finish", "What the tree refused")["run"]], cwd=d, env={"PATH": __import__("os").environ["PATH"], "KEY": "lib", "MODES": modes}, capture_output=True, text=True)
        return r, d

    GOOD = {f"treeverify/treeverify-lib-proposed/{f}": "" for f in ("ok.json", "new.json", "summary.txt")}

    def test_a_complete_verdict_is_read(self):
        r, d = self.run_step('["proposed"]', {**self.GOOD, "treeverify/treeverify-lib-proposed/failing.txt": "B.C\nA.X\n"})
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "tree-failures.txt").read_text(), "A.X\nB.C\n")

    def test_the_refusals_of_two_modes_are_joined_without_repeats(self):
        layout = {f"treeverify/treeverify-lib-{m}/{f}": "" for m in ("proposed", "wide") for f in ("ok.json", "new.json", "summary.txt")}
        layout["treeverify/treeverify-lib-proposed/failing.txt"] = "A.X\n"
        layout["treeverify/treeverify-lib-wide/failing.txt"] = "A.X\nW.Y\n"
        r, d = self.run_step('["proposed", "wide"]', layout)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "tree-failures.txt").read_text(), "A.X\nW.Y\n")

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
        self.assertIn("timeout -k 60 60m", run)
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


class SameBundle(unittest.TestCase):
    def test_the_draft_and_the_final_bundle_are_cut_by_the_same_command(self):
        draft, final = compose_command("compose"), compose_command("finish")
        self.assertNotIn("--tree-failures", draft)
        self.assertEqual(final.replace(" --tree-failures ../tree-failures.txt", ""), draft)

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
