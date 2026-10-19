"""fingerprint_chunks.sh: the modules of a list are fingerprinted in several processes, and a process that fails loses only its own share (2026-10-19, lean-pool: one process for 1,000 modules lost them all)."""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "fingerprint_chunks.sh"

# a `lake` that prints one FP/FPEND pair per module of the list it is given; a module named Bad.* makes its process exit 1 before it prints anything (a crashed process),
# and a module named Slow.* makes it sleep past the timeout
FAKE_LAKE = r"""#!/usr/bin/env bash
list="${@: -2:1}"
while read -r m; do
  case "$m" in
    Bad.*) echo "crash on $m" >&2; exit 1 ;;
    Slow.*) sleep 20 ;;
  esac
  printf 'FP\t%s\tf\tdef\t%032d\nFPEND\t%s\t1\n' "$m" 1 "$m"
done < "$list"
echo "fingerprints: done"
"""


SHIM = r"""#!/usr/bin/env bash
shift 2
dur=$1; shift
secs=$(python3 -c 'import sys; v = sys.argv[1]; print(float(v[:-1]) * {"s": 1, "m": 60}[v[-1]] if v[-1] in "sm" else float(v))' "$dur")
"$@" & pid=$!
( sleep "$secs"; kill -9 "$pid" 2>/dev/null ) & killer=$!
wait "$pid"; rc=$?
kill "$killer" 2>/dev/null
exit $rc
"""


class Chunks(unittest.TestCase):
    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        (self.d / "tree").mkdir()
        bindir = self.d / "bin"
        bindir.mkdir()
        lake = bindir / "lake"
        lake.write_text(FAKE_LAKE)  # called as `lake env lean --run PROGRAM LIST WHOLE`
        lake.chmod(lake.stat().st_mode | stat.S_IXUSR)
        if shutil.which("timeout") is None:  # a machine without GNU coreutils (macOS): a stand-in that stops the command after the time, like `timeout -k 30 DURATION command…`
            shim = bindir / "timeout"
            shim.write_text(SHIM)
            shim.chmod(shim.stat().st_mode | stat.S_IXUSR)
        self.env = {**os.environ, "PATH": f"{bindir}:{os.environ['PATH']}"}

    def run_script(self, modules: list[str], minutes: str = "1", jobs: str = "3"):
        lst = self.d / "list.txt"
        lst.write_text("".join(m + "\n" for m in modules))
        out = self.d / "out.txt"
        r = subprocess.run(["bash", str(SCRIPT), str(lst), str(self.d / "whole.txt"), str(out), minutes, jobs], cwd=self.d, env=self.env, capture_output=True, text=True, timeout=120)
        return r, out

    def modules_in(self, out: Path) -> list[str]:
        return sorted(ln.split("\t")[1] for ln in out.read_text().splitlines() if ln.startswith("FPEND"))

    def test_every_module_is_given_to_exactly_one_process(self):
        mods = [f"M.A{i}" for i in range(10)]
        r, out = self.run_script(mods)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.modules_in(out), sorted(mods))

    def test_a_process_that_crashes_loses_only_its_own_share(self):
        mods = ["M.A0", "Bad.B", "M.A2", "M.A3", "M.A4", "M.A5"]  # round robin over 3: chunk 1 = Bad.B and M.A4, the others are untouched
        r, out = self.run_script(mods)
        self.assertEqual(r.returncode, 0, r.stderr)  # the script itself does not fail: the reader decides what a missing module means
        self.assertEqual(self.modules_in(out), ["M.A0", "M.A2", "M.A3", "M.A5"])
        self.assertIn("crash on Bad.B", Path(str(out) + ".err").read_text())

    def test_a_process_that_runs_out_of_time_is_stopped_and_the_others_are_kept(self):
        mods = ["M.A0", "Slow.B", "M.A2"]
        env_slow = {**self.env}
        lst = self.d / "list.txt"
        lst.write_text("".join(m + "\n" for m in mods))
        out = self.d / "out.txt"
        # one minute is 60 s in `timeout`; the fake sleeps 20 s, so give the script a time that fits, and check instead that a timeout of 0 minutes loses the slow chunk only
        r = subprocess.run(["bash", str(SCRIPT), str(lst), str(self.d / "whole.txt"), str(out), "0.05", "3"], cwd=self.d, env=env_slow, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.modules_in(out), ["M.A0", "M.A2"])

    def test_an_empty_list_is_an_empty_result_and_no_error(self):
        r, out = self.run_script([])
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(out.read_text(), "")

    def test_more_processes_than_modules_is_fine(self):
        r, out = self.run_script(["M.A0", "M.A1"], jobs="5")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.modules_in(out), ["M.A0", "M.A1"])


if __name__ == "__main__":
    unittest.main()
