import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import orchestrate  # noqa: E402


def done(code, out="", err=""):
    return subprocess.CompletedProcess([], code, out, err)


class Gh(unittest.TestCase):
    def test_a_read_that_hits_a_5xx_is_tried_again(self):
        with (
            mock.patch.object(
                orchestrate.subprocess,
                "run",
                side_effect=[
                    done(1, err="HTTP 503"),
                    done(1, err="HTTP 503"),
                    done(0, "[]"),
                ],
            ) as run,
            mock.patch.object(orchestrate.time, "sleep"),
        ):
            self.assertEqual(orchestrate.gh("run", "list", "-R", "x/y"), "[]")
        self.assertEqual(run.call_count, 3)

    def test_a_read_that_keeps_failing_raises(self):
        with (
            mock.patch.object(
                orchestrate.subprocess, "run", return_value=done(1, err="HTTP 503")
            ) as run,
            mock.patch.object(orchestrate.time, "sleep"),
        ):
            with self.assertRaises(RuntimeError):
                orchestrate.gh("run", "view", "1")
        self.assertEqual(run.call_count, 6)

    def test_a_dispatch_is_never_repeated(self):
        with (
            mock.patch.object(
                orchestrate.subprocess, "run", return_value=done(1, err="HTTP 503")
            ) as run,
            mock.patch.object(orchestrate.time, "sleep"),
        ):
            with self.assertRaises(RuntimeError):
                orchestrate.gh("workflow", "run", "bump-library.yml")
        self.assertEqual(run.call_count, 1)


if __name__ == "__main__":
    unittest.main()
