"""The factory's side of the born-tagged intake lane (scripts/bump/canonicalise_bundle.py, the copy of tengoku's isnad_tag.py it uses, and the two workflows that run it
before they pack the attested archive)."""

import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import canonicalise_bundle as cb  # noqa: E402
import isnad_tag as tg  # noqa: E402

REPO = HERE.parents[2]
SCRIPT = HERE.parent / "canonicalise_bundle.py"

# The same pin and the same cases are in tengoku's scripts/ci/tests/test_isnad_copy.py: a change to either file fails a test in its own repository until the other is changed.
PIN = "585bd7ea7eff7a0067cf1c1c4a4ef260f5f8267d6e571a537569eb4de619185c"  # sha256 of scripts/isnad_tag.py in competemath/tengoku, which scripts/bump/isnad_tag.py here is a verbatim copy of
GOLDEN = {
    "one-line docstring": ("/-- Words. -/\ntheorem a : True := trivial\n", "/-- Words.-/\ntheorem a : True := trivial\n"),
    "two-line docstring": ("/-- Two\nlines. -/\ntheorem g : True := trivial\n", "/-- Two\nlines.-/\ntheorem g : True := trivial\n"),
    "a tag in the docstring": ("/-- Words.\n  @isnad1 from=novel sha=abc123\n-/\ntheorem t : True := trivial\n", "/-- Words.-/\ntheorem t : True := trivial\n"),
    "a tag, translated": ("/-- Words.\n@isnad1 from=translated sha=ff\n-/\ntheorem u : True := trivial\n", "/-- Words.-/\ntheorem u : True := trivial\n"),
    "closing marker in a string": ('def s : String := "x -/ y"\n', 'def s : String := "x -/ y"\n'),
    "no docstring": ("theorem v : True := trivial\n", "theorem v : True := trivial\n"),
    "module header": (
        "module\n\npublic import Tengoku\n\n/-- Mod. -/\ntheorem w : True := trivial\n",
        "module\n\npublic import Tengoku\n\n/-- Mod.-/\ntheorem w : True := trivial\n",
    ),
}
ONE_LINE, CANON = GOLDEN["one-line docstring"]


class Copy(unittest.TestCase):
    def test_the_copy_is_tengokus_file_byte_for_byte(self):
        self.assertEqual(hashlib.sha256((HERE.parent / "isnad_tag.py").read_bytes()).hexdigest(), PIN, "scripts/bump/isnad_tag.py is a verbatim copy of tengoku's scripts/isnad_tag.py")

    def test_the_golden_cases(self):
        for name, (text, want) in GOLDEN.items():
            self.assertEqual(tg.canonical_text(text), want, name)
            self.assertEqual(tg.canonical_text(want), want, f"{name}: idempotent")


class Rewrite(unittest.TestCase):
    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        self.b = self.d / "bundle"
        (self.b / "Tengoku/Lib").mkdir(parents=True)

    def test_a_module_is_rewritten_in_place_and_the_rest_is_not_touched(self):
        (self.b / "Tengoku/Lib/A.lean").write_text(ONE_LINE)
        (self.b / "manifest.jsonl").write_text('{"doc": "/-- Words. -/"}\n')
        (self.b / "report.json").write_text("{}\n")
        self.assertEqual(cb.canonicalise_dir(str(self.b)), (1, 1, 0))
        self.assertEqual((self.b / "Tengoku/Lib/A.lean").read_text(), CANON)
        self.assertEqual((self.b / "manifest.jsonl").read_text(), '{"doc": "/-- Words. -/"}\n')

    def test_a_second_run_changes_nothing(self):
        (self.b / "Tengoku/Lib/A.lean").write_text(ONE_LINE)
        cb.canonicalise_dir(str(self.b))
        self.assertEqual(cb.canonicalise_dir(str(self.b)), (1, 0, 0))

    def test_a_module_that_is_not_utf8_is_left_alone(self):
        (self.b / "Tengoku/Lib/B.lean").write_bytes(b"theorem x : True := trivial -- \xff\n")
        self.assertEqual(cb.canonicalise_dir(str(self.b)), (1, 0, 1))
        self.assertEqual((self.b / "Tengoku/Lib/B.lean").read_bytes(), b"theorem x : True := trivial -- \xff\n")

    def test_a_symlink_is_never_followed(self):
        outside = self.d / "outside.lean"
        outside.write_text(ONE_LINE)
        (self.b / "Tengoku/Lib/L.lean").symlink_to(outside)
        self.assertEqual(cb.canonicalise_dir(str(self.b)), (0, 0, 0))
        self.assertEqual(outside.read_text(), ONE_LINE)

    def test_the_command_skips_a_mode_the_run_did_not_have(self):
        (self.b / "Tengoku/Lib/A.lean").write_text(ONE_LINE)
        r = subprocess.run([sys.executable, str(SCRIPT), "--bundle", str(self.b), "--bundle", str(self.d / "bundle-wide")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("1 rewritten", r.stdout)
        self.assertIn("no such bundle in this run, skipped", r.stdout)


class Workflows(unittest.TestCase):
    """The step is in both attest jobs, only when the variable is 1, before the archive is packed, and the job fetches and executes nothing from tengoku (CodeRabbit on
    emissary#99: the attest job holds the OIDC token and the attestation permission)."""

    def doc(self, name):
        return yaml.safe_load((REPO / ".github" / "workflows" / name).read_text(encoding="utf-8"))

    def steps(self, name, job):
        return self.doc(name)["jobs"][job]["steps"]

    def check(self, name, job):
        steps = self.steps(name, job)
        idx = [i for i, s in enumerate(steps) if "python3 emissary/scripts/bump/canonicalise_bundle.py" in s.get("run", "")]
        self.assertEqual(len(idx), 1, name)
        step = steps[idx[0]]
        self.assertEqual(step["if"], "${{ vars.TENGOKU_ISNAD_REQUIRED == '1' }}")
        self.assertNotIn("curl", step["run"])
        self.assertNotIn("--isnad", step["run"])
        pack = next(i for i, s in enumerate(steps) if "python3 emissary/scripts/bump/bundle_tar.py" in s.get("run", ""))
        self.assertLess(idx[0], pack, "the modules are canonical before the archive is packed")
        attest = next(i for i, s in enumerate(steps) if "attest-build-provenance" in s.get("uses", ""))
        self.assertLess(idx[0], attest)

    def test_bump_library(self):
        self.check("bump-library.yml", "attest")

    def test_bump_sharded(self):
        self.check("bump-sharded.yml", "finish")

    def test_nothing_of_tengoku_is_downloaded_into_a_job_that_attests(self):
        for name, job in (("bump-library.yml", "attest"), ("bump-sharded.yml", "finish")):
            for s in self.steps(name, job):
                self.assertNotIn("raw.githubusercontent.com/competemath/tengoku/main/scripts", s.get("run", ""), f"{name}: {s.get('name')}")

    def test_bump_library_fetches_both_files_with_the_other_factory_scripts(self):
        clone = next(s["run"] for s in self.steps("bump-library.yml", "attest") if "sparse-checkout set" in s.get("run", ""))
        self.assertIn("/scripts/bump/canonicalise_bundle.py", clone)
        self.assertIn("/scripts/bump/isnad_tag.py", clone)


if __name__ == "__main__":
    unittest.main()
