"""Every workflow step that installs Lean's installer (elan) tries again, up to 20 times, 30 s apart, and never runs what fails its digest.

The real case: on 8 Nov 2026 from 09:34, on and off for over 90 minutes, the download `github.com/leanprover/elan/releases/latest/download/...` answered 504 on the Actions runners
("curl: (22) The requested URL returned error: 504", "elan: command failed: curl -sSfL ..."), while a Tengoku job got through at 09:47. One try per step: emissary #158's job and campaigns
failed in seconds, again and again.

One form at every site (the same text but for the toolchain): each try fetches the pinned script to a file with a time limit, checks its digest, runs it with a time limit. The earlier
`curl | sh` reports sh's status: a step without pipefail read a failed fetch as success (cubic, #159), which is why the steps here are run with AND without pipefail.

Invariants, on the real line of every install step of every workflow (.yml and .yaml), under bash -e and under bash -e -o pipefail, with fake curl, sha256sum, timeout and sleep:
  * every install is in the one form; there are at least the 12 known sites; no site pipes the installer into a shell, and no fetch or digest is left outside the loop;
  * the fetch failing, or the installer failing with the real error text, or a try hanging (timeout's 124), 1, 5 or 19 times and then succeeding: the step passes, after exactly that many
    + 1 tries, with 30 s sleeps;
  * a dead download (the fetch or the installer always failing): the step fails after exactly 20 tries and 19 sleeps; it never reports success;
  * a digest that does not match: the installer NEVER runs, and the step fails after 20 tries;
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
WF = sorted(glob.glob(str(REPO / ".github" / "workflows" / "*.yml")) + glob.glob(str(REPO / ".github" / "workflows" / "*.yaml")))
ERROR = "curl: (22) The requested URL returned error: 504\\nelan: command failed: curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz"
MODES = (["-e"], ["-e", "-o", "pipefail"])  # a step's `run:` is bash -e by default, bash -e -o pipefail under `shell: bash`


def sites() -> list[tuple[str, int, str]]:
    return [(Path(f).name, i, line.strip()) for f in WF for i, line in enumerate(Path(f).read_text(encoding="utf-8").split("\n"), 1) if "elan-init" in line]


def forms() -> list[tuple[str, int, str]]:
    """One site per distinct text (the sites are one text but for the toolchain: test_every_install_is_in_the_one_form), so the behaviour is run on each form once."""
    seen: dict[str, tuple[str, int, str]] = {}
    for s in sites():
        seen.setdefault(s[2], s)
    return list(seen.values())


def fake(path: Path, body: str) -> None:
    path.write_text("#!/bin/bash\n" + body)
    path.chmod(path.stat().st_mode | stat.S_IEXEC)


class InstallerRetry(unittest.TestCase):
    def run_line(self, line: str, mode: list[str], curl_fails: int = 0, install_fails: int = 0, hangs: int = 0, digest_ok: bool = True) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            (t / "bin").mkdir()
            for c in ("fetches", "installs", "timeouts"):
                (t / c).write_text("0")
            bump = lambda name: f'n=$(cat "{t / name}"); n=$((n+1)); echo $n > "{t / name}"'
            fake(t / "bin" / "curl", f'{bump("fetches")}\nif [ "$n" -le {curl_fails} ]; then echo "curl: (22) The requested URL returned error: 504" >&2; exit 22; fi\n'
                 f'while [ $# -gt 0 ]; do [ "$1" = -o ] && out="$2"; shift; done\ncp "{t / "script"}" "$out"\n')
            (t / "script").write_text(f'{bump("installs")}\nif [ "$n" -le {install_fails} ]; then printf "{ERROR}\\n" >&2; exit 1; fi\nexit 0\n')
            fake(t / "bin" / "sha256sum", f'cat >/dev/null\nexit {0 if digest_ok else 1}\n')
            fake(t / "bin" / "timeout", f'{bump("timeouts")}\nif [ "$n" -le {hangs} ]; then exit 124; fi\nshift\nexec "$@"\n')
            fake(t / "bin" / "sleep", f'echo "$1" >> "{t / "sleeps"}"\n')
            (t / "step.sh").write_text(line + "\n")
            env = {"PATH": f"{t / 'bin'}:{os.environ['PATH']}", "HOME": str(t), "TOOLCHAIN": "leanprover/lean4:v4.31.0"}
            r = subprocess.run(["bash", "--noprofile", "--norc", *mode, str(t / "step.sh")], cwd=t, env=env, capture_output=True, text=True, check=False)
            sleeps = (t / "sleeps").read_text().split() if (t / "sleeps").exists() else []
            return {"code": r.returncode, "out": r.stdout + r.stderr, "fetches": int((t / "fetches").read_text()), "installs": int((t / "installs").read_text()), "sleeps": sleeps}

    def test_every_install_is_in_the_one_form(self):
        found = sites()
        self.assertGreaterEqual(len(found), 12, found)
        form = re.compile(r"""^for try in \$\(seq 1 20\); do curl --proto '=https' --tlsv1\.2 -sSfL --max-time 120 -o elan-init\.sh https://raw\.githubusercontent\.com/leanprover/elan/[0-9a-f]{40}/elan-init\.sh && echo "[0-9a-f]{64}  elan-init\.sh" \| sha256sum -c - && timeout 300 sh elan-init\.sh -y --default-toolchain (none|"\$TOOLCHAIN") && break; \[ "\$try" -lt 20 \] \|\| exit 1; echo "::notice::the Lean installer failed \(try \$try of 20\): again in 30 s"; sleep 30; done$""")
        self.assertEqual([(f, n) for f, n, line in found if not form.match(line)], [])
        self.assertEqual(len({re.sub(r"--default-toolchain \S+", "", line) for _, _, line in found}), 1)  # one text: a fix cannot reach some sites and miss others

    def test_it_recovers_and_gives_up_after_twenty_in_both_shell_modes(self):
        self.assertEqual(len(forms()), 2)  # the toolchain `none` and "$TOOLCHAIN"
        for f, n, line in forms():
            for mode in MODES:
                where = f"{f}:{n} {mode}"
                r = self.run_line(line, mode)
                self.assertEqual((r["code"], r["fetches"], r["installs"], r["sleeps"]), (0, 1, 1, []), where)
                self.assertNotIn("::notice::", r["out"], where)
                for fails in (1, 5, 19):
                    r = self.run_line(line, mode, curl_fails=fails)
                    self.assertEqual((r["code"], r["fetches"], r["installs"], r["sleeps"]), (0, fails + 1, 1, ["30"] * fails), f"{where} fetch fails {fails}")
                    r = self.run_line(line, mode, install_fails=fails)
                    self.assertEqual((r["code"], r["fetches"], r["installs"], r["sleeps"]), (0, fails + 1, fails + 1, ["30"] * fails), f"{where} install fails {fails}")
                    r = self.run_line(line, mode, hangs=fails)
                    self.assertEqual((r["code"], r["installs"], r["sleeps"]), (0, 1, ["30"] * fails), f"{where} hangs {fails}")
                for kw in ({"curl_fails": 10_000}, {"install_fails": 10_000}, {"hangs": 10_000}):
                    r = self.run_line(line, mode, **kw)
                    self.assertNotEqual(r["code"], 0, f"{where} {kw}: a dead download must fail the step")
                    self.assertEqual(len(r["sleeps"]), 19, f"{where} {kw}")
                    self.assertEqual(r["fetches"], 20, f"{where} {kw}")

    def test_a_wrong_digest_never_runs_the_installer(self):
        for f, n, line in forms():
            for mode in MODES:
                r = self.run_line(line, mode, digest_ok=False)
                self.assertNotEqual(r["code"], 0, f"{f}:{n} {mode}")
                self.assertEqual((r["installs"], r["fetches"]), (0, 20), f"{f}:{n} {mode}")


if __name__ == "__main__":
    unittest.main()
