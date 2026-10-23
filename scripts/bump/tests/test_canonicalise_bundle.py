"""The factory's side of the born-tagged intake lane (scripts/bump/canonicalise_bundle.py, and the two workflows that run it before they pack the attested archive)."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import canonicalise_bundle as cb  # noqa: E402

REPO = HERE.parents[2]
SCRIPT = HERE.parent / "canonicalise_bundle.py"

# a stand-in with the one property that matters here: not the identity on a one-line docstring, idempotent, and it does not see the tag line
STUB = '''
import re

def canonical_text(text):
    text = re.sub(r"^[ \\t]*@isnad1.*\\n", "", text, flags=re.M)
    return re.sub(r"[ \\t]+-/", "-/", text)
'''
ONE_LINE = "/-- Words. -/\ntheorem a : True := trivial\n"
CANON = "/-- Words.-/\ntheorem a : True := trivial\n"


class Rewrite(unittest.TestCase):
    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        self.stub = self.d / "isnad_tag.py"
        self.stub.write_text(STUB)
        self.b = self.d / "bundle"
        (self.b / "Tengoku/Lib").mkdir(parents=True)
        self.canonical = cb.load_canonical(str(self.stub))

    def test_a_module_is_rewritten_in_place_and_the_rest_is_not_touched(self):
        (self.b / "Tengoku/Lib/A.lean").write_text(ONE_LINE)
        (self.b / "manifest.jsonl").write_text('{"doc": "/-- Words. -/"}\n')
        (self.b / "report.json").write_text("{}\n")
        self.assertEqual(cb.canonicalise_dir(str(self.b), self.canonical), (1, 1, 0))
        self.assertEqual((self.b / "Tengoku/Lib/A.lean").read_text(), CANON)
        self.assertEqual((self.b / "manifest.jsonl").read_text(), '{"doc": "/-- Words. -/"}\n')

    def test_a_second_run_changes_nothing(self):
        (self.b / "Tengoku/Lib/A.lean").write_text(ONE_LINE)
        cb.canonicalise_dir(str(self.b), self.canonical)
        self.assertEqual(cb.canonicalise_dir(str(self.b), self.canonical), (1, 0, 0))

    def test_a_module_that_is_not_utf8_is_left_alone(self):
        (self.b / "Tengoku/Lib/B.lean").write_bytes(b"theorem x : True := trivial -- \xff\n")
        self.assertEqual(cb.canonicalise_dir(str(self.b), self.canonical), (1, 0, 1))
        self.assertEqual((self.b / "Tengoku/Lib/B.lean").read_bytes(), b"theorem x : True := trivial -- \xff\n")

    def test_a_symlink_is_never_followed(self):
        outside = self.d / "outside.lean"
        outside.write_text(ONE_LINE)
        (self.b / "Tengoku/Lib/L.lean").symlink_to(outside)
        self.assertEqual(cb.canonicalise_dir(str(self.b), self.canonical), (0, 0, 0))
        self.assertEqual(outside.read_text(), ONE_LINE)

    def test_the_command_skips_a_mode_the_run_did_not_have(self):
        (self.b / "Tengoku/Lib/A.lean").write_text(ONE_LINE)
        r = subprocess.run(
            [sys.executable, str(SCRIPT), "--isnad", str(self.stub), "--bundle", str(self.b), "--bundle", str(self.d / "bundle-wide")], capture_output=True, text=True
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("1 rewritten", r.stdout)
        self.assertIn("no such bundle in this run, skipped", r.stdout)

    def test_a_file_without_canonical_text_is_refused(self):
        bad = self.d / "bad.py"
        bad.write_text("x = 1\n")
        with self.assertRaises(SystemExit):
            cb.load_canonical(str(bad))


class Workflows(unittest.TestCase):
    """The step is in both attest jobs, only when the variable is 1, and before the archive is packed."""

    def steps(self, name, job):
        doc = yaml.safe_load((REPO / ".github" / "workflows" / name).read_text(encoding="utf-8"))
        return doc["jobs"][job]["steps"]

    def check(self, name, job, pack_marker):
        steps = self.steps(name, job)
        idx = [i for i, s in enumerate(steps) if "python3 emissary/scripts/bump/canonicalise_bundle.py" in s.get("run", "")]
        self.assertEqual(len(idx), 1, name)
        step = steps[idx[0]]
        self.assertEqual(step["if"], "${{ vars.TENGOKU_ISNAD_REQUIRED == '1' }}")
        self.assertIn("https://raw.githubusercontent.com/competemath/tengoku/main/scripts/isnad_tag.py", step["run"])
        pack = next(i for i, s in enumerate(steps) if pack_marker in s.get("run", ""))
        self.assertLess(idx[0], pack, "the modules are canonical before the archive is packed")
        attest = next(i for i, s in enumerate(steps) if "attest-build-provenance" in s.get("uses", ""))
        self.assertLess(idx[0], attest)

    def test_bump_library(self):
        self.check("bump-library.yml", "attest", "python3 emissary/scripts/bump/bundle_tar.py")

    def test_bump_sharded(self):
        self.check("bump-sharded.yml", "finish", "python3 emissary/scripts/bump/bundle_tar.py")

    def test_bump_library_fetches_the_script_with_the_other_factory_scripts(self):
        clone = next(s["run"] for s in self.steps("bump-library.yml", "attest") if "sparse-checkout set" in s.get("run", ""))
        self.assertIn("/scripts/bump/canonicalise_bundle.py", clone)


if __name__ == "__main__":
    unittest.main()
