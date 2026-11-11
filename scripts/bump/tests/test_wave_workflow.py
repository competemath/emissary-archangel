"""The build-once as the workflows run it: bump-waves.yml's chain of waves, plan_waves.py's outputs on flt-anthropic's real import graph, and bump-shard.yml's order of steps.

Invariants: the chain is the same job 32 times, each after the one before; no wave runs when the plan has none for it; a failed job does not cancel the waves after it, and the bundle only starts when none
failed; the token is in one step and that step comes before any code of the library; the build-once steps are off for a plain bump."""

import gzip
import json
import sys
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import build_waves as bw  # noqa: E402
import in_tree  # noqa: E402
import plan_waves as pw  # noqa: E402

WF = HERE.parents[2] / ".github" / "workflows"
G = json.loads(gzip.open(HERE / "fixtures" / "real-flt-imports.json.gz").read())
waves = yaml.safe_load((WF / "bump-waves.yml").read_text())
shard = yaml.safe_load((WF / "bump-shard.yml").read_text())
STEPS = shard["jobs"]["shard"]["steps"]
ON = waves[True]


def index(words):
    hits = [i for i, s in enumerate(STEPS) if words in s.get("name", "")]
    assert len(hits) == 1, (words, hits)
    return hits[0]


class Outputs(unittest.TestCase):
    def test_the_real_plan_fits_and_every_shard_runs_once(self):
        p = bw.to_shards(bw.plan(G["imports"], G["lines"], 132000, 17), G["imports"], set())
        out = pw.outputs(p)
        self.assertEqual(len(out), pw.MAX_WAVES)
        ran = [s for k in out for s in json.loads(out[k])]
        self.assertEqual(sorted(ran), list(range(len(p["shards"]))))
        self.assertEqual(sum(v != "[]" for v in out.values()), p["waves"])
        for s in p["shards"]:
            self.assertIn(s["shard"], json.loads(out[f"w{s['wave']}"]))

    def test_a_plan_with_too_many_waves_stops(self):
        with self.assertRaisesRegex(ValueError, "33 waves"):
            pw.outputs({"waves": 33, "shards": []})

    def test_exactly_the_limit_is_allowed(self):
        self.assertEqual(pw.outputs({"waves": 32, "shards": []})["w31"], "[]")


class Chain(unittest.TestCase):
    def test_as_many_waves_as_the_plan_allows(self):
        self.assertEqual(sorted(k for k in waves["jobs"] if k[0] == "w"), sorted(f"w{i}" for i in range(pw.MAX_WAVES)))
        self.assertEqual(set(waves["jobs"]["plan"]["outputs"]), {f"w{i}" for i in range(pw.MAX_WAVES)} | {"packs", "fill"})  # packs: a resumed run's reused packs; fill: the runs of its chain (lane_reuse.py)

    def test_every_wave_is_the_same_job_after_the_one_before(self):
        base = None
        for i in range(pw.MAX_WAVES):
            j = dict(waves["jobs"][f"w{i}"])
            self.assertEqual(j.pop("needs"), "plan" if i == 0 else ["plan", f"w{i - 1}"], i)
            text = json.dumps(j).replace(f"outputs.w{i})", "outputs.WAVE)").replace(f"outputs.w{i} ", "outputs.WAVE ")
            base = base or text
            self.assertEqual(text, base, i)
            self.assertNotIn("outputs.w", text.replace("outputs.WAVE", ""), i)

    def test_a_failed_wave_does_not_cancel_the_next_and_an_empty_wave_is_skipped(self):
        cond = waves["jobs"]["w7"]["if"]
        self.assertIn("!cancelled()", cond)
        self.assertIn("needs.plan.result == 'success'", cond)
        self.assertIn("needs.plan.outputs.w7 != '[]'", cond)
        self.assertFalse(waves["jobs"]["w7"]["strategy"]["fail-fast"])

    def test_every_wave_is_a_build_once_with_read_only_rights(self):
        for i in range(pw.MAX_WAVES):
            j = waves["jobs"][f"w{i}"]
            self.assertEqual(j["uses"], "./.github/workflows/bump-shard.yml")
            self.assertEqual(j["with"]["build_once"], "true")
            self.assertEqual(j["with"]["imports"], "${{ inputs.imports }}")
            self.assertEqual(j["permissions"], {"contents": "read", "actions": "read"})

    def test_the_wave_passes_only_inputs_the_shard_workflow_has(self):
        allowed = set(shard[True]["workflow_call"]["inputs"])
        self.assertEqual(set(waves["jobs"]["w0"]["with"]) - allowed, set())

    def test_the_bundle_waits_for_every_wave_and_none_may_have_failed(self):
        b = waves["jobs"]["bundle"]
        self.assertEqual(set(b["needs"]), {"plan"} | {f"w{i}" for i in range(pw.MAX_WAVES)})
        self.assertIn("!contains(needs.*.result, 'failure')", b["if"])
        self.assertIn("refs/heads/main", b["if"])
        self.assertEqual(b["permissions"], {"actions": "write"})
        run = b["steps"][0]["run"]
        self.assertIn('recut_from="$GITHUB_RUN_ID"', run)
        self.assertNotIn("${{", run)

    def test_a_library_already_in_the_tree_can_be_cut_from_it(self):
        """flt-anthropic, 9 Nov 2026: part 1 merged on 6 Nov (116 theorems), so a lane that always said from_tree=false stopped in its first ten seconds"""
        self.assertEqual(ON["workflow_dispatch"]["inputs"]["from_tree"]["default"], "false")
        steps = waves["jobs"]["plan"]["steps"]
        guard = next(s for s in steps if "in_tree.py" in s.get("run", ""))
        self.assertIn('--from-tree "$FROM_TREE"', guard["run"])
        self.assertEqual(waves["jobs"]["plan"]["env"]["FROM_TREE"], "${{ inputs.from_tree }}")
        self.assertIn('[[ "$FROM_TREE" =~ ^(true|false)$ ]]', steps[0]["run"])
        bundle = waves["jobs"]["bundle"]
        self.assertEqual(bundle["env"]["FROM_TREE"], "${{ inputs.from_tree }}")
        self.assertIn('-f from_tree="$FROM_TREE"', bundle["steps"][0]["run"])

    def test_the_real_library_in_the_tree_passes_only_with_from_tree(self):
        real = ["data/intake/flt-anthropic/manifest.jsonl", "data/intake/flt-anthropic/report.json"]
        self.assertFalse(in_tree.verdict(real, "flt-anthropic", "false", "300")[0])
        ok, why = in_tree.verdict(real, "flt-anthropic", "true", "300")
        self.assertTrue(ok)
        self.assertIn("from part 002", why)

    def test_a_build_once_keeps_the_authors_imports(self):
        self.assertEqual(ON["workflow_dispatch"]["inputs"]["imports"]["default"], "faithful")

    def test_no_step_of_the_plan_interpolates_an_input(self):
        for s in waves["jobs"]["plan"]["steps"]:
            self.assertNotIn("${{", s.get("run", ""), s.get("name"))
        self.assertEqual(waves["permissions"], {})
        self.assertIn("key", ON["workflow_dispatch"]["inputs"])


class ShardSteps(unittest.TestCase):
    fetch = "The work of the earlier jobs"
    place = "The earlier jobs' work, into the library"
    library = "The library at its pinned commit"
    build = "Build this shard's modules"
    pack = "This job's work, for the jobs after it"
    gate2 = "Batched Gate 2"

    def test_the_token_is_fetched_with_before_any_code_of_the_library_runs(self):
        self.assertLess(index(self.fetch), index(self.library))
        with_token = [s.get("name", s.get("uses")) for s in STEPS if "GH_TOKEN" in (s.get("env") or {})]
        self.assertEqual(len(with_token), 1)
        self.assertIn(self.fetch, with_token[0])

    def test_the_order_of_the_build_once_steps(self):
        self.assertLess(index(self.library), index(self.place))
        self.assertLess(index(self.place), index(self.build))
        self.assertLess(index(self.build), index(self.pack))
        self.assertLess(index(self.pack), index(self.gate2))
        self.assertIn("--report tb-final.json", STEPS[index(self.pack)]["run"])

    def test_the_build_once_steps_are_off_for_a_plain_bump(self):
        for words in (self.fetch, self.place, self.pack):
            self.assertEqual(STEPS[index(words)]["if"], "inputs.build_once == 'true'", words)
        uploads = [s for s in STEPS if "with" in s and str(s["with"].get("name", "")).startswith("wave-")]
        self.assertEqual(len(uploads), 3)  # the upload and its two later tries (test_lane_chain.py I8)
        self.assertEqual(uploads[0]["if"], "inputs.build_once == 'true'")
        for u in uploads[1:]:
            self.assertTrue(u["if"].startswith("inputs.build_once == 'true' && "), u["if"])
        for s in STEPS:  # the waits between the tries too
            if s.get("run", "").startswith("sleep") and "wave_up" in s.get("if", ""):
                self.assertTrue(s["if"].startswith("inputs.build_once == 'true' && "), s["if"])
        self.assertEqual(shard[True]["workflow_call"]["inputs"]["build_once"]["default"], "false")

    def test_the_build_passes_own_only_for_a_build_once(self):
        run = STEPS[index(self.build)]["run"]
        self.assertIn('$([ "$BUILD_ONCE" != true ] || echo --own own.txt)', run)  # build_rounds.py passes it to every build

    def test_a_shard_pack_of_a_build_once_is_its_own_modules(self):
        run = STEPS[index("Pack this shard")]["run"]
        self.assertIn('"$([ "$BUILD_ONCE" = true ] && echo own.txt || echo build.txt)"', run)

    def test_the_caller_of_a_plain_bump_grants_what_the_shard_workflow_asks_for(self):
        plain = yaml.safe_load((WF / "bump-sharded.yml").read_text())
        self.assertEqual(plain["jobs"]["shard"]["permissions"], {"contents": "read", "actions": "read"})
        self.assertEqual(shard["jobs"]["shard"]["permissions"], {"contents": "read", "actions": "read"})


if __name__ == "__main__":
    unittest.main()
