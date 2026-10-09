"""A library with a `subdir` (fagin, immerman-vardi, formal-math, openai-math) has `lib` as a symlink to its Lake project, inside the clone. In bash, `cd lib` keeps the
logical path but the kernel resolves a relative `../x` in a redirection or an argument by the physical directory: it lands next to the symlink's TARGET, not in `emissary/`.

2026-10-09: the batched Gate 2 step of bump-library.yml wrote `../gate2-pass.log` from `(cd lib; ...)` and read `gate2-pass.log` from `emissary/`: `cat: gate2-pass.log: No such
file or directory`, exit 1, on every one of those libraries (the other 40 have a real `lib`). The steps resolve `W="$PWD"` before the `cd` and use `$W/...`."""

from __future__ import annotations

import re
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

WORKFLOWS = Path(__file__).resolve().parents[3] / ".github" / "workflows"
CD_LIB = re.compile(r"\bcd\s+lib2?\b")


def code_of(line: str) -> str:
    return re.split(r"\s#\s", line, maxsplit=1)[0]


class WorkflowsDoNotStepOutOfASymlinkedLib(unittest.TestCase):
    def test_no_relative_parent_path_on_a_line_that_runs_in_lib(self):
        problems = []
        for name in ("bump-library.yml", "bump-shard.yml"):
            doc = yaml.safe_load((WORKFLOWS / name).read_text(encoding="utf-8"))
            for job, spec in doc["jobs"].items():
                for step in spec.get("steps", []):
                    script = step.get("run", "")
                    if not isinstance(script, str):
                        continue
                    for ln in script.replace("\\\n", " ").splitlines():
                        code = code_of(ln)
                        if CD_LIB.search(code) and re.search(r"(?<![\w.])\.\./", code):
                            problems.append(f"{name} {job} / {step.get('name', '?')[:50]}: {code.strip()[:120]}")
        self.assertEqual(problems, [])

    def test_the_cause_in_bash(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "emissary").mkdir()
            (root / "real" / "proj").mkdir(parents=True)
            (root / "emissary" / "lib").symlink_to("../real/proj")

            def run(script: str) -> subprocess.CompletedProcess:
                return subprocess.run(["bash", "-e", "-c", script], cwd=root / "emissary", capture_output=True, text=True)

            old = run("(cd lib; echo verdicts > ../gate2-pass.log); cat gate2-pass.log")
            self.assertNotEqual(old.returncode, 0)
            self.assertIn("No such file", old.stderr)
            self.assertTrue((root / "real" / "gate2-pass.log").exists())  # it landed next to the target
            new = run('W="$PWD"; (cd lib; echo verdicts > "$W/gate2-pass2.log"); cat gate2-pass2.log')
            self.assertEqual(new.returncode, 0, new.stderr)
            self.assertEqual(new.stdout.strip(), "verdicts")


class PrunedBuildNextToItsPathDependencies(unittest.TestCase):
    def test_lib2_of_a_subdir_library_is_next_to_the_siblings_lib_has(self):
        """2026-10-09 (fagin, immerman-vardi): after the first fix the build of the pruned sources died on `Lax979537: package directory not found`: lib2 was a plain directory
        in emissary/, and the lakefile's path dependency `../Lax979537` resolved next to lib2, not next to lib's target in the clone."""
        doc = yaml.safe_load((WORKFLOWS / "bump-library.yml").read_text(encoding="utf-8"))
        script = next(s["run"] for s in doc["jobs"]["bump"]["steps"] if "mkdir -p lib2/.lake" in s.get("run", ""))
        snippet = "\n".join(ln for ln in script.splitlines() if ln.strip().startswith("if [ -L lib ]"))
        self.assertTrue(snippet, "the step has no symlink branch for lib2")
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "emissary" / "lib-repo" / "proofs").mkdir(parents=True)
            (root / "emissary" / "lib-repo" / "Lax979537").mkdir()
            (root / "emissary" / "lib").symlink_to("lib-repo/proofs")
            run = lambda s: subprocess.run(["bash", "-e", "-c", s], cwd=root / "emissary", capture_output=True, text=True)
            done = run(snippet + "\nmkdir -p lib2/.lake\n(cd lib2 && ls ../Lax979537 >/dev/null && echo resolved)")
            self.assertEqual(done.stdout.strip(), "resolved", done.stderr)
            (root / "emissary" / "lib2").unlink()  # the symlink the snippet made
            plain = run("mkdir -p lib2/.lake\n(cd lib2 && ls ../Lax979537)")  # what it was
            self.assertNotEqual(plain.returncode, 0)
            # a library without a subdir (lib is a real directory) is unchanged
            (root / "emissary" / "lib").unlink()
            (root / "emissary" / "lib").mkdir()
            (root / "emissary" / "lib2").unlink() if (root / "emissary" / "lib2").is_symlink() else None
            self.assertEqual(run(snippet + "\nmkdir -p lib2/.lake\ntest -d lib2/.lake && ! test -L lib2 && echo plain").stdout.strip(), "plain")


if __name__ == "__main__":
    unittest.main()
