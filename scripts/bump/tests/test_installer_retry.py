"""Every workflow step that installs Lean's installer (elan) tries again, up to 20 times, 30 s apart.

The real case: on 8 Nov 2026 from 09:34 the download `github.com/leanprover/elan/releases/latest/download/...` answered 504 on the Actions runners ("curl: (22) The requested URL
returned error: 504", "elan: command failed: curl -sSfL ..."), while a Tengoku job got through at 09:47 and the same URL answered 200 from elsewhere. One try per step: #158's
`lean` job and its campaign failed seven times in 35 minutes, each in 5 seconds, with no second try.

Invariants, on the real text of every install step of every workflow (the step's own line, run by bash -e -o pipefail, as Actions does, with a fake `curl`/`sleep`):
  * every install of elan in every workflow is inside the retry; there are at least the 12 known sites;
  * an installer that fails 1, 5 or 19 times with the real error text and then succeeds: the step succeeds, the installer ran exactly that many times + 1, the sleeps are all 30 s;
  * an installer that always fails: the step fails, after exactly 20 tries and 19 sleeps (never loops for ever, never reports success);
  * a success on the first try: one run, no sleep, no notice.
"""

from __future__ import annotations

import glob
import os
import re
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
WF = sorted(glob.glob(str(REPO / ".github" / "workflows" / "*.yml")))
INSTALL = re.compile(r"elan-init\.sh( \| sh -s --)? -y --default-toolchain ")  # the two forms: run the checked file, or the pinned script piped to sh; any toolchain
ERROR = "curl: (22) The requested URL returned error: 504\nelan: command failed: curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz"


def sites() -> list[tuple[str, int, str]]:
    out = []
    for f in WF:
        for i, line in enumerate(Path(f).read_text(encoding="utf-8").split("\n"), 1):
            if INSTALL.search(line):
                out.append((Path(f).name, i, line.strip()))
    return out


class InstallerRetry(unittest.TestCase):
    def run_line(self, line: str, fails: int) -> tuple[int, str, int, list[str]]:
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            (t / "bin").mkdir()
            count, sleeps = t / "count", t / "sleeps"
            count.write_text("0")
            # the installer: fails `fails` times with the real text, then succeeds. The piped form runs what the fake curl prints; the file form runs elan-init.sh
            body = f'n=$(cat "{count}"); n=$((n+1)); echo $n > "{count}"; if [ "$n" -le {fails} ]; then echo "{ERROR}" >&2; exit 1; fi; exit 0\n'
            (t / "elan-init.sh").write_text(body)
            fake_curl = t / "bin" / "curl"
            fake_curl.write_text(f'#!/bin/sh\ncat "{t / "elan-init.sh"}"\n')
            fake_curl.chmod(fake_curl.stat().st_mode | stat.S_IEXEC)
            fake_sleep = t / "bin" / "sleep"
            fake_sleep.write_text(f'#!/bin/sh\necho "$1" >> "{sleeps}"\n')
            fake_sleep.chmod(fake_sleep.stat().st_mode | stat.S_IEXEC)
            (t / "step.sh").write_text(line + "\n")
            env = {"PATH": f"{t / 'bin'}:{os.environ['PATH']}", "HOME": str(t), "GITHUB_PATH": str(t / "gp"), "TOOLCHAIN": "leanprover/lean4:v4.31.0"}
            r = subprocess.run(["bash", "--noprofile", "--norc", "-e", "-o", "pipefail", str(t / "step.sh")], cwd=t, env=env, capture_output=True, text=True, check=False)
            return r.returncode, r.stdout + r.stderr, int(count.read_text()), sleeps.read_text().split() if sleeps.exists() else []

    def test_every_install_is_inside_the_retry(self):
        found = sites()
        self.assertGreaterEqual(len(found), 12, found)
        bad = [(f, n) for f, n, line in found if not line.startswith("for try in $(seq 1 20); do ")]
        self.assertEqual(bad, [])

    def test_it_recovers_after_failures_and_gives_up_after_twenty_on_every_site(self):
        for f, n, line in sites():
            for fails in (0, 1, 5, 19):
                code, out, ran, sleeps = self.run_line(line, fails)
                self.assertEqual(code, 0, f"{f}:{n} fails={fails}: {out}")
                self.assertEqual(ran, fails + 1, f"{f}:{n} fails={fails}")
                self.assertEqual(sleeps, ["30"] * fails, f"{f}:{n}")
                self.assertEqual(out.count("::notice::the Lean installer failed"), fails, f"{f}:{n}")
            code, out, ran, sleeps = self.run_line(line, 10_000)
            self.assertNotEqual(code, 0, f"{f}:{n}: a dead download must fail the step")
            self.assertEqual((ran, len(sleeps)), (20, 19), f"{f}:{n}")


if __name__ == "__main__":
    unittest.main()
