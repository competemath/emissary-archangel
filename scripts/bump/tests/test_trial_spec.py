"""scripts/trial-library-build.py for a repository that is NOT registered yet (a candidate): the spec file replaces data/exports/KEY/setup.ci.json, and the report says how many of the
library's headline declarations sit in a module that built unchanged."""

import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[2] / "trial-library-build.py"
spec_ = importlib.util.spec_from_file_location("trial_library_build", SCRIPT)
tlb = importlib.util.module_from_spec(spec_)
spec_.loader.exec_module(tlb)

SPEC = {
    "repo": "https://github.com/someone/lean-thing",
    "commit": "0123456789abcdef0123456789abcdef01234567",
    "toolchain": "leanprover/lean4:v4.33.0",
    "roots": ["Thing"],
    "headlines": [
        {"name": "Thing.main_theorem", "module": "Thing.Main"},
        {"name": "Thing.Aux.bound", "module": "Thing.Aux"},
        {"name": "Thing.Lost.deep", "module": "Thing.Lost"},
        {"name": "Thing.Gone.x", "module": "Thing.Gone"},
    ],
}


class Spec(unittest.TestCase):
    def setUp(self):
        self.old_cwd, self.old_env = os.getcwd(), os.environ.get("TRIAL_SPEC")
        self.tmp = tempfile.TemporaryDirectory()
        os.chdir(self.tmp.name)

    def tearDown(self):
        os.chdir(self.old_cwd)
        self.tmp.cleanup()
        if self.old_env is None:
            os.environ.pop("TRIAL_SPEC", None)
        else:
            os.environ["TRIAL_SPEC"] = self.old_env

    def test_meta_reads_the_spec_when_there_is_no_registered_record(self):
        Path("spec.json").write_text(json.dumps(SPEC))
        os.environ["TRIAL_SPEC"] = "spec.json"
        self.assertEqual(tlb.load_setup("anything"), SPEC)

    def test_a_registered_library_still_reads_its_own_record(self):
        os.environ.pop("TRIAL_SPEC", None)
        Path("data/exports/k").mkdir(parents=True)
        Path("data/exports/k/setup.ci.json").write_text(json.dumps({"repo": "r", "commit": "c", "toolchain": "t", "roots": ["R"]}))
        self.assertEqual(tlb.load_setup("k")["roots"], ["R"])

    def test_headline_survival_counts_by_module_status(self):
        got = tlb.headline_survival(SPEC["headlines"], built=["Thing.Main", "Thing.Aux"], failed=["Thing.Lost"], blocked=[])
        self.assertEqual((got["total"], got["built"], got["failed"], got["blocked"], got["no_module"]), (4, 2, 1, 0, 1))
        self.assertEqual(got["lost"], ["Thing.Lost.deep", "Thing.Gone.x"])

    def test_no_headlines_is_an_empty_report_not_a_crash(self):
        got = tlb.headline_survival([], built=[], failed=[], blocked=[])
        self.assertEqual((got["total"], got["built"], got["lost"]), (0, 0, []))

    def test_analyze_end_to_end_on_a_fake_library(self):
        # a library with three modules: Main builds (an .olean exists), Aux fails with its own error, Lost is blocked behind it
        lib = Path("lib")
        for mod in ("Main", "Aux", "Lost"):
            (lib / "Thing").mkdir(parents=True, exist_ok=True)
            (lib / "Thing" / f"{mod}.lean").write_text("theorem t : True := trivial\n")
        olean = lib / ".lake/build/lib/lean/Thing/Main.olean"
        olean.parent.mkdir(parents=True)
        olean.write_bytes(b"")
        Path("build.log").write_text("error: ./Thing/Aux.lean:3:4: unknown identifier 'foo'\n")
        spec = dict(SPEC, headlines=[{"name": "Thing.main", "module": "Thing.Main"}, {"name": "Thing.aux", "module": "Thing.Aux"}, {"name": "Thing.lost", "module": "Thing.Lost"}])
        Path("spec.json").write_text(json.dumps(spec))
        os.environ["TRIAL_SPEC"] = "spec.json"
        tlb.analyze("lib", "someone--lean-thing", "pass1", "build.log")
        res = json.loads(Path("pass1.json").read_text())
        self.assertEqual(res["modules"], {"total": 3, "built": 1, "failed_own_error": 1, "blocked_behind_failure": 1})
        self.assertEqual((res["headlines"]["total"], res["headlines"]["built"]), (3, 1))
        self.assertEqual(sorted(res["headlines"]["lost"]), ["Thing.aux", "Thing.lost"])


if __name__ == "__main__":
    unittest.main()
