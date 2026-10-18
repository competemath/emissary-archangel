"""upstream_pins.py: the pins of sources.json against the upstream heads (report only). Offline: the two network calls are injected."""

from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import upstream_pins as up  # noqa: E402

A, B, C = "a" * 40, "b" * 40, "c" * 40


class Registered(unittest.TestCase):
    def test_only_a_github_repository_with_a_full_commit_counts(self):
        src = {
            "sources": {
                "ok": {"repo": "https://github.com/o/ok", "commit": A},
                "dotgit": {"repo": "https://github.com/o/dot.git", "commit": A},
                "short": {"repo": "https://github.com/o/short", "commit": "abc123"},
                "nowhere": {"repo": "https://gitlab.com/o/x", "commit": A},
                "none": {"label": "a source without a repo"},
                "weird": "not a dict",
            }
        }
        self.assertEqual(up.registered(src), [("dotgit", "o/dot", A), ("ok", "o/ok", A)])

    def test_a_flat_file_without_the_sources_wrapper_is_read_too(self):
        self.assertEqual(up.registered({"k": {"repo": "https://github.com/o/k", "commit": A}}), [("k", "o/k", A)])


class Head(unittest.TestCase):
    def fake(self, rc, out):
        return lambda *a, **k: subprocess.CompletedProcess(a, rc, stdout=out, stderr="")

    def test_the_head_is_the_first_sha_of_ls_remote(self):
        self.assertEqual(up.head_of("o/r", run=self.fake(0, f"{B}\tHEAD\n")), B)

    def test_an_unreadable_repository_is_none_not_an_error(self):
        self.assertIsNone(up.head_of("o/r", run=self.fake(128, "")))
        self.assertIsNone(up.head_of("o/r", run=self.fake(0, "not a sha\tHEAD\n")))

    def test_compare_reads_the_counts_and_a_rewritten_history_is_diverged(self):
        self.assertEqual(up.compare("o/r", A, B, run=self.fake(0, '{"ahead_by": 4, "files": 12, "last": "2026-10-12T21:55:24Z"}')), {"ahead_by": 4, "files": 12, "last": "2026-10-12"})
        self.assertEqual(up.compare("o/r", A, B, run=self.fake(1, "")), {"diverged": True})


class Failures(unittest.TestCase):
    """CodeRabbit on emissary#59: one slow or missing repository must not cost the whole weekly report"""

    @staticmethod
    def raising(exc):
        def run(*a, **k):
            raise exc

        return run

    def test_a_timeout_or_a_missing_git_is_an_unreadable_repository(self):
        for exc in (subprocess.TimeoutExpired(["git"], 120), FileNotFoundError("git")):
            self.assertIsNone(up.head_of("o/r", run=self.raising(exc)))

    def test_a_timeout_in_the_comparison_or_garbage_from_gh_is_unknown_not_a_crash(self):
        self.assertEqual(up.compare("o/r", A, B, run=self.raising(subprocess.TimeoutExpired(["gh"], 120))), {"unknown": True})
        self.assertEqual(up.compare("o/r", A, B, run=lambda *a, **k: subprocess.CompletedProcess(a, 0, stdout="not json", stderr="")), {"unknown": True})

    def test_the_table_still_lists_a_comparison_that_failed(self):
        rows = [{"key": "k", "slug": "o/k", "pinned": A, "head": B, "state": "behind", "unknown": True}]
        self.assertIn("unknown (the comparison failed)", up.markdown(rows, 3))

    def test_one_failing_library_does_not_stop_the_others(self):
        items = [("a", "o/a", A), ("b", "o/b", A)]
        heads = {"o/a": None, "o/b": B}
        rows = up.report(items, heads=lambda slug: heads[slug], comparer=lambda slug, p, h: {"ahead_by": 2, "files": 1, "last": "2026-10-01"})
        self.assertEqual([r["key"] for r in rows], ["b", "a"])


class Report(unittest.TestCase):
    def test_only_what_moved_is_listed_most_behind_first_and_the_unreadable_too(self):
        items = [("same", "o/same", A), ("small", "o/small", A), ("big", "o/big", A), ("gone", "o/gone", A)]
        heads = {"o/same": A, "o/small": B, "o/big": C, "o/gone": None}
        counts = {"o/small": {"ahead_by": 1, "files": 1, "last": "2026-10-01"}, "o/big": {"ahead_by": 40, "files": 300, "last": "2026-10-12"}}
        rows = up.report(items, heads=lambda slug: heads[slug], comparer=lambda slug, p, h: counts[slug])
        self.assertEqual([r["key"] for r in rows], ["big", "small", "gone"])
        self.assertEqual(rows[2]["state"], "unreadable")

    def test_the_table_says_how_many_moved_and_that_nothing_was_changed(self):
        rows = [{"key": "big", "slug": "o/big", "pinned": A, "head": C, "state": "behind", "ahead_by": 40, "files": 300, "last": "2026-10-12"}, {"key": "gone", "slug": "o/gone", "pinned": A, "head": None, "state": "unreadable"}, {"key": "rew", "slug": "o/rew", "pinned": A, "head": B, "state": "behind", "diverged": True}]
        text = up.markdown(rows, 115)
        self.assertIn("3 of 115", text)
        self.assertIn("nothing was changed", text)
        self.assertIn("| big | o/big | `aaaaaaaaaa` | `cccccccccc` | 40 | 300 | 2026-10-12 |", text)
        self.assertIn("unreadable", text)
        self.assertIn("diverged", text)

    def test_the_real_sources_file_parses(self):
        p = Path(__file__).resolve().parents[3] / "sources.json"
        if p.exists():
            import json

            self.assertGreater(len(up.registered(json.loads(p.read_text(encoding="utf-8")))), 50)


class WorkflowFile(unittest.TestCase):
    """the weekly workflow only reports: it may write ONE issue, and nothing else"""

    PATH = Path(__file__).resolve().parents[3] / ".github" / "workflows" / "upstream-pins.yml"

    def test_it_reads_the_repository_writes_issues_and_nothing_else(self):
        import yaml

        wf = yaml.safe_load(self.PATH.read_text(encoding="utf-8"))
        self.assertEqual(wf["permissions"], {})
        self.assertEqual(wf["jobs"]["report"]["permissions"], {"contents": "read", "issues": "write"})
        text = self.PATH.read_text(encoding="utf-8")
        for forbidden in ("gh pr ", "git push", "gh workflow run", "sources.json >", "contents: write", "pull-requests: write"):
            self.assertNotIn(forbidden, text, forbidden)

    def test_it_runs_weekly_and_on_demand(self):
        import yaml

        wf = yaml.safe_load(self.PATH.read_text(encoding="utf-8"))
        on = wf[True]
        self.assertIn("schedule", on)
        self.assertIn("workflow_dispatch", on)


if __name__ == "__main__":
    unittest.main()
