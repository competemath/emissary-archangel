import io
import json
import os
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.memory_intake import compose as C
from scripts.memory_intake import run as R
from scripts.memory_intake.tests.helpers import candidate, fake_review


def comp():
    return C.compose(candidate([1, 2]), fake_review())


class Archive(unittest.TestCase):
    def test_the_archive_is_the_modules_the_manifest_lines_and_the_report_in_the_form_the_gate_rebuilds(self):
        c = comp()
        d = tempfile.mkdtemp()
        sha = R.bundle_tar(c, "leanprover/lean4:v4.34.0-rc2", lambda t: t.upper(), str(Path(d) / "b.tar"))
        with tarfile.open(Path(d) / "b.tar") as tf:
            names = tf.getnames()
            self.assertEqual(names, sorted([*c.modules, "manifest.jsonl", "report.json"]))
            member = tf.extractfile("manifest.jsonl").read().decode()  # type: ignore[union-attr]
            module = tf.extractfile(sorted(c.modules)[0]).read().decode()  # type: ignore[union-attr]
        self.assertEqual(len(member.splitlines()), 2)
        self.assertIn("leanprover/lean4:v4.34.0-rc2", member)
        self.assertEqual(module, c.modules[sorted(c.modules)[0]].upper(), "each module goes through the canonical function")
        self.assertEqual(len(sha), 64)
        # the same composition gives the same bytes (the gate rebuilds them from the PR and compares)
        self.assertEqual(sha, R.bundle_tar(comp(), "leanprover/lean4:v4.34.0-rc2", lambda t: t.upper(), str(Path(d) / "c.tar")))

    def test_the_report_member_is_the_reports_file_bytes(self):
        c = comp()
        d = tempfile.mkdtemp()
        R.bundle_tar(c, "t", lambda t: t, str(Path(d) / "b.tar"))
        with tarfile.open(Path(d) / "b.tar") as tf:
            self.assertEqual(tf.extractfile("report.json").read(), (json.dumps(c.report, ensure_ascii=False) + "\n").encode())  # type: ignore[union-attr]


class Dump(unittest.TestCase):
    def test_a_composition_survives_the_artifact(self):
        c = comp()
        back = R.load(json.loads(json.dumps(R.dump(c), ensure_ascii=False)))
        self.assertEqual((back.target, back.author, back.bundle, back.modules, back.manifest_lines, back.report), (c.target, c.author, c.bundle, c.modules, c.manifest_lines, c.report))
        self.assertEqual([(v.verdict, v.codes, v.entry["id"]) for v in back.verdicts], [(v.verdict, v.codes, v.entry["id"]) for v in c.verdicts])


class Post(unittest.TestCase):
    def test_events_prs_and_marks_are_what_the_site_takes(self):
        d = Path(tempfile.mkdtemp())
        (d / "events.json").write_text(json.dumps([{"username": "ada", "target": "t", "kind": "returned", "code": "bar.merit", "ids": ["a" * 8], "names": ["x"]}]))
        (d / "opened.json").write_text(json.dumps([
            {"username": "ada", "target": "t", "number": 5, "url": "https://github.com/competemath/tengoku/pull/5", "bundle": "b" * 64, "ids": ["a" * 8], "names": ["x"]},
            {"username": "ada", "target": "t", "number": 0, "url": "", "bundle": "c" * 64, "ids": ["b" * 8], "names": ["y"]},  # a dry run opened nothing
        ]))
        sent = []

        def fake_http(method, url, token, body=None):
            sent.append((method, url.rsplit("/", 2)[-2:], token, body))
            return {"ok": True}

        with mock.patch.object(R, "http", fake_http), mock.patch.dict(os.environ, {"LEAK_OIDC_TOKEN": "tok"}), mock.patch("builtins.print"):
            R.main(["post", "--out", str(d)])
        self.assertEqual([s[1] for s in sent], [["memory", "intake-events"], ["memory", "candidates"]])
        events = sent[0][3]
        self.assertEqual(len(events["events"]), 1)
        self.assertEqual([(p["number"], p["events"][0]["code"]) for p in events["prs"]], [(5, "pr.opened")])
        self.assertEqual(sent[1][3], {"marks": [{"username": "ada", "target": "t", "ids": ["a" * 8], "bundle": "b" * 64}]})
        self.assertTrue(all(s[2] == "tok" for s in sent))

    def test_nothing_to_say_posts_nothing(self):
        d = Path(tempfile.mkdtemp())
        with mock.patch.object(R, "http") as h, mock.patch.dict(os.environ, {"LEAK_OIDC_TOKEN": "tok"}):
            R.main(["post", "--out", str(d)])
        h.assert_not_called()


class OpenKeepsGoing(unittest.TestCase):
    """A bundle that fails to open does not stop the others, and what was opened is written down at once (the post step marks it, so it is not offered again)."""

    def setUp(self):
        self.out = Path(tempfile.mkdtemp())
        for n in range(3):
            d = self.out / str(n)
            d.mkdir()
            (d / "composition.json").write_text(json.dumps(R.dump(C.compose(candidate([1, 2, n + 3]), fake_review()))))
        self.args = mock.Mock(out=str(self.out), repo="competemath/tengoku", base="a" * 40, bot="b[bot]", email="e@x", dry_run=False)

    def test_the_failing_bundle_is_skipped_the_others_are_recorded_and_the_exit_code_is_one(self):
        calls = []

        def open_pr(api, repo, base, comp, bot, email, dry_run=False):
            calls.append(comp.bundle)
            if len(calls) == 2:
                raise R.G.ApiError("gh api POST git/refs: HTTP 500")
            return {"number": 10 + len(calls), "url": f"https://github.com/{repo}/pull/{10 + len(calls)}", "branch": "b"}

        with mock.patch.object(R.G, "open_pr", open_pr), mock.patch("builtins.print"):
            code = R.cmd_open(self.args)
        self.assertEqual(code, 1)
        self.assertEqual(len(calls), 3, "the third bundle was still tried")
        recorded = json.loads((self.out / "opened.json").read_text())
        self.assertEqual([o["number"] for o in recorded], [11, 13])

    def test_opened_json_is_written_after_each_pull_request(self):
        seen = []

        def open_pr(api, repo, base, comp, bot, email, dry_run=False):
            seen.append(json.loads((self.out / "opened.json").read_text()) if (self.out / "opened.json").exists() else [])
            return {"number": len(seen), "url": "u", "branch": "b"}

        with mock.patch.object(R.G, "open_pr", open_pr), mock.patch("builtins.print"):
            self.assertEqual(R.cmd_open(self.args), 0)
        self.assertEqual([len(x) for x in seen], [0, 1, 2], "each call sees the ones opened before it already on disk")


if __name__ == "__main__":
    unittest.main()
