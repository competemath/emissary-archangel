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


if __name__ == "__main__":
    unittest.main()
