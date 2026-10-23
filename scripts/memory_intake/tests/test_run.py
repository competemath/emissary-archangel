import json
import os
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.memory_intake import compose as C
from scripts.memory_intake import run as R
from scripts.memory_intake.tests import test_settle as TS
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
        self.assertEqual([(e["kind"], e["code"], e.get("prNumber")) for e in events["events"]], [("returned", "bar.merit", None), ("submitted", "pr.opened", 5)],
                         "the bar's return, and the opened pull request as a loose `submitted` event (it answers the earlier verdicts on its theorems)")
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


class GhWithChecks(TS.Gh):
    """test_settle.Gh with the two calls the reporter makes for the state of a pull request."""

    def __call__(self, method, path, body=None, raw=False):
        if method == "GET" and "/check-runs" in path:
            return {"check_runs": []}
        if method == "GET" and path.endswith("/reviews?per_page=100"):
            return []
        return super().__call__(method, path, body, raw)


class Decisions(unittest.TestCase):
    """A code owner's decisions travel: settle (close, free) -> settled.json -> post; report (every 30 minutes) says the same thing for the pull requests that are closed."""

    def sent_by(self, fn):
        sent = []

        def fake_http(method, url, token, body=None):
            sent.append((method, url.rsplit("/", 2)[-2:], body))
            return {"ok": True}

        with mock.patch.object(R, "http", fake_http), mock.patch.dict(os.environ, {"LEAK_OIDC_TOKEN": "tok"}), mock.patch("builtins.print"):
            fn()
        return sent

    def test_settle_writes_what_post_sends(self):
        gh = GhWithChecks()
        gh.add(7, comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        out = Path(tempfile.mkdtemp())
        with mock.patch.object(R.G, "gh_api", gh), mock.patch("builtins.print"):
            self.assertEqual(R.main(["settle", "--out", str(out), "--repo", TS.REPO, "--bot", TS.BOT]), 0)
        settled = json.loads((out / "settled.json").read_text())
        self.assertEqual([r["accepted"] for r in settled["reviews"]], [[TS.IDS[1], TS.IDS[2]]])
        sent = self.sent_by(lambda: R.main(["post", "--out", str(out)]))
        self.assertEqual([s[1] for s in sent], [["memory", "intake-events"]], "no PR was opened and nothing is marked: only the decisions go")
        body = sent[0][2]
        self.assertEqual(body["events"], [])
        self.assertEqual([p["number"] for p in body["prs"]], [7])
        self.assertEqual(body["reviews"][0]["returned"], [{"id": TS.IDS[0], "code": "merit"}])

    def test_a_dry_run_of_settle_writes_no_file(self):
        gh = GhWithChecks()
        gh.add(7, comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        out = Path(tempfile.mkdtemp())
        with mock.patch.object(R.G, "gh_api", gh), mock.patch("builtins.print"):
            R.main(["settle", "--out", str(out), "--repo", TS.REPO, "--bot", TS.BOT, "--dry-run"])
        self.assertFalse((out / "settled.json").exists())
        self.assertEqual(gh.writes, [])

    def test_report_posts_the_decisions_of_an_open_pr_without_freeing_anything(self):
        gh = GhWithChecks()
        gh.add(7, comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        with mock.patch.object(R.G, "gh_api", gh):
            sent = self.sent_by(lambda: R.main(["report", "--repo", TS.REPO]))
        body = sent[0][2]
        self.assertEqual([e["code"] for e in body["prs"][0]["events"]], ["pr.opened", "review.return.merit"])
        self.assertEqual(body["reviews"][0]["accepted"], [], "the other theorems are freed when the pull request is closed, not before")

    def test_report_frees_the_others_of_a_closed_pr_and_ignores_decisions_on_a_merged_one(self):
        gh = GhWithChecks()
        gh.add(7, state="closed", comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        gh.add(8, state="closed", merged_at="2026-10-23T00:00:00Z", comments=[TS.cm(1, "studied: reject a1b2c3d4 hygiene")])
        with mock.patch.object(R.G, "gh_api", gh):
            sent = self.sent_by(lambda: R.main(["report", "--repo", TS.REPO]))
        body = sent[0][2]
        self.assertEqual([(r["accepted"]) for r in body["reviews"]], [[TS.IDS[1], TS.IDS[2]]])
        by_number = {p["number"]: [e["code"] for e in p["events"]] for p in body["prs"]}
        self.assertEqual(by_number, {7: ["review.superseded", "review.return.merit"], 8: ["pr.merged"]})

    def test_report_counts_decisions_only_on_the_apps_own_pull_requests(self):
        gh = GhWithChecks()
        gh.add(7, author="stranger", comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        with mock.patch.object(R.G, "gh_api", gh):
            sent = self.sent_by(lambda: R.main(["report", "--repo", TS.REPO]))
        self.assertEqual(sent[0][2]["reviews"], [])

    def test_report_skips_a_pull_request_whose_calls_fail_posts_the_others_and_fails_the_run(self):
        gh = GhWithChecks()
        gh.add(7, comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        gh.add(8)
        real = gh.__call__

        def flaky(method, path, body=None, raw=False):
            if path.endswith("/pulls/8"):
                raise R.G.ApiError("GET pulls/8: HTTP 502")
            return real(method, path, body, raw)

        code = []
        with mock.patch.object(R.G, "gh_api", flaky):
            sent = self.sent_by(lambda: code.append(R.main(["report", "--repo", TS.REPO])))
        self.assertEqual(code, [1])
        self.assertEqual([p["number"] for p in sent[0][2]["prs"]], [7])

    def test_an_unreadable_code_owners_file_reports_nothing_instead_of_reporting_without_the_decisions(self):
        gh = GhWithChecks()
        gh.add(7, state="closed", comments=[TS.cm(1, "studied: return a1b2c3d4 merit")])
        real = gh.__call__

        def down(method, path, body=None, raw=False):
            if "CODEOWNERS" in path:
                raise R.G.ApiError("GET CODEOWNERS: HTTP 503")
            return real(method, path, body, raw)

        code, sent = [], []
        with mock.patch.object(R.G, "gh_api", down):
            sent = self.sent_by(lambda: code.append(R.main(["report", "--repo", TS.REPO])))
        self.assertEqual((code, sent), ([1], []), "a snapshot without the decisions would make the site answer their notices for good")

    def test_report_without_decisions_is_what_it_was(self):
        gh = GhWithChecks()
        gh.add(7)
        with mock.patch.object(R.G, "gh_api", gh):
            sent = self.sent_by(lambda: R.main(["report", "--repo", TS.REPO]))
        self.assertEqual(sent[0][2]["reviews"], [])
        self.assertEqual([e["code"] for e in sent[0][2]["prs"][0]["events"]], ["pr.opened"])


if __name__ == "__main__":
    unittest.main()
