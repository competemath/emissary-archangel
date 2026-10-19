"""bump-shard.yml: the Lean toolchain is installed with retries before the library's first `lake`.

2026-10-19, the fresh lean-pool run: 3 of its 32 shards failed in the step that clones the library, minutes apart, each with `error during download` / `SSL connect error` from elan, which downloads the
toolchain on the first `lake update`. A shard that has done no work is lost to a flake of the network.
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

import yaml

PATH = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "bump-shard.yml"
DOC = yaml.safe_load(PATH.read_text(encoding="utf-8"))
STEP = next(s for s in DOC["jobs"]["shard"]["steps"] if "The library at its pinned commit" in s.get("name", ""))["run"]


class ToolchainRetry(unittest.TestCase):
    def test_the_toolchain_is_installed_before_the_first_lake(self):
        self.assertIn('elan toolchain install "$TOOLCHAIN"', STEP)
        self.assertLess(STEP.index('elan toolchain install "$TOOLCHAIN"'), STEP.index("lake update"))
        self.assertLess(STEP.index("trial-library-build.py retarget"), STEP.index('elan toolchain install "$TOOLCHAIN"'))  # the toolchain the library will ask for is the one that is written

    def test_it_is_tried_several_times_with_a_longer_wait_each_time(self):
        self.assertRegex(STEP, r"for attempt in 1 2 3 4 5; do")
        self.assertIn("sleep $((attempt * 20))", STEP)

    def test_it_ends_the_shard_with_a_message_when_every_attempt_failed(self):
        self.assertRegex(STEP, r'if \[ "\$attempt" = 5 \]; then echo "::error::the toolchain \$TOOLCHAIN did not download in 5 attempts"; exit 1; fi')

    def test_a_success_stops_the_loop(self):
        self.assertRegex(STEP, r'if elan toolchain install "\$TOOLCHAIN" > /dev/null 2>&1; then break; fi')

    def test_the_toolchain_is_the_one_the_shard_is_given(self):
        self.assertEqual(DOC["jobs"]["shard"]["env"]["TOOLCHAIN"], "${{ inputs.toolchain }}")


if __name__ == "__main__":
    unittest.main()
