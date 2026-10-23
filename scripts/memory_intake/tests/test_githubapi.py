import base64
import json
import unittest

from scripts.memory_intake import compose as C
from scripts.memory_intake import githubapi as G
from scripts.memory_intake.tests.helpers import candidate, fake_review

REPO = "competemath/tengoku"
BASE = "a" * 40
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"


class Fake:
    def __init__(self, files: dict[str, str] | None = None):
        self.files = {"lean-toolchain": TOOLCHAIN + "\n", "Tengoku/All.lean": "import Tengoku.Foo\n", **(files or {})}
        self.writes: list = []
        self.blobs: dict[str, str] = {}
        self.refs: set[str] = set()  # branches that exist
        self.prs: dict[str, dict] = {}  # head branch -> pull request
        self.comments: dict[int, list] = {}  # pull request number -> its comments

    def __call__(self, method, path, body=None, raw=False):
        if method == "GET" and "/contents/" in path:
            p = path.split("/contents/")[1].split("?")[0]
            return self.files.get(p, "").encode()
        if method == "GET" and path.endswith(f"/git/commits/{BASE}"):
            return {"tree": {"sha": "t" * 40}}
        if method == "GET" and "/git/ref/heads/" in path:
            if path.split("/git/ref/heads/")[1] not in self.refs:
                raise G.ApiError(f"gh api GET {path}: gh: Not Found (HTTP 404)")
            return {"object": {"sha": "c" * 40}}
        if method == "GET" and "/issues/" in path and "/comments" in path:
            return self.comments.get(int(path.split("/issues/")[1].split("/")[0]), []) if "page=1" in path else []
        if method == "GET" and "/pulls?head=" in path:
            pr = self.prs.get(path.split("?head=")[1].split("&")[0].split(":", 1)[1])
            return [pr] if pr else []
        self.writes.append((method, path, body))
        if path.endswith("/git/refs"):
            self.refs.add(body["ref"].removeprefix("refs/heads/"))
        if path.endswith("/git/blobs"):
            sha = f"{len(self.blobs):040x}"
            self.blobs[sha] = base64.b64decode(body["content"]).decode()
            return {"sha": sha}
        if path.endswith("/git/trees"):
            return {"sha": "e" * 40}
        if path.endswith("/git/commits"):
            return {"sha": "c" * 40}
        if path.endswith("/pulls"):
            return {"number": 77, "html_url": f"https://github.com/{REPO}/pull/77"}
        return {}


def comp(ns=(1, 2)):
    return C.compose(candidate(list(ns)), fake_review())


class Files(unittest.TestCase):
    def test_the_first_bundle_of_the_first_target_creates_the_top_files(self):
        c = comp()
        files = G.pr_files(Fake(), REPO, BASE, c)
        mods = sorted(c.modules)
        self.assertEqual(sorted(p for p in files if p.startswith("Tengoku/Studied/Erdos396/")), mods)
        m = files["data/studied/erdos-396/manifest.jsonl"]
        self.assertEqual(len(m.splitlines()), 2)
        self.assertIn(f'"toolchain": "{TOOLCHAIN}"', m)
        self.assertNotIn("{toolchain}", m)
        self.assertEqual(json.loads(files[f"data/studied/erdos-396/bundles/{c.bundle[:16]}.json"])["bundle"], c.bundle)
        self.assertEqual(files["Tengoku/Studied/Erdos396.lean"], "".join(f"import {p[:-5].replace('/', '.')}\n" for p in mods))
        self.assertEqual(files["Tengoku/Studied.lean"], "import Tengoku.Studied.Erdos396\n")
        self.assertEqual(files["Tengoku/All.lean"], "import Tengoku.Foo\nimport Tengoku.Studied\n")

    def test_a_later_bundle_only_appends(self):
        old_manifest = '{"name": "earlier"}\n'
        gh = Fake({"data/studied/erdos-396/manifest.jsonl": old_manifest, "Tengoku/Studied/Erdos396.lean": "import Tengoku.Studied.Erdos396.Sold\n", "Tengoku/Studied.lean": "import Tengoku.Studied.Erdos396\n"})
        files = G.pr_files(gh, REPO, BASE, comp((3,)))
        self.assertTrue(files["data/studied/erdos-396/manifest.jsonl"].startswith(old_manifest))
        self.assertTrue(files["Tengoku/Studied/Erdos396.lean"].startswith("import Tengoku.Studied.Erdos396.Sold\n"))
        self.assertNotIn("Tengoku/Studied.lean", files)
        self.assertNotIn("Tengoku/All.lean", files)

    def test_a_second_target_adds_its_line_to_the_top_file_only(self):
        gh = Fake({"data/studied/other/manifest.jsonl": "{}\n", "Tengoku/Studied.lean": "import Tengoku.Studied.Other\n"})
        files = G.pr_files(gh, REPO, BASE, comp())
        self.assertEqual(files["Tengoku/Studied.lean"], "import Tengoku.Studied.Other\nimport Tengoku.Studied.Erdos396\n")
        self.assertNotIn("Tengoku/All.lean", files)

    def test_a_manifest_without_its_final_newline_is_refused(self):
        with self.assertRaises(G.ApiError):
            G.pr_files(Fake({"data/studied/erdos-396/manifest.jsonl": "{}"}), REPO, BASE, comp())


class Open(unittest.TestCase):
    def test_one_commit_one_branch_one_pr_one_label(self):
        gh, c = Fake(), comp()
        r = G.open_pr(gh, REPO, BASE, c, "tengoku-supervisor[bot]", "1+tengoku-supervisor[bot]@users.noreply.github.com")
        self.assertEqual((r["number"], r["branch"]), (77, f"studied/erdos-396/{c.bundle[:16]}"))
        kinds = [(m, p.split("/", 3)[-1]) for m, p, _ in gh.writes]
        self.assertEqual(kinds[-4:], [("POST", "git/commits"), ("POST", "git/refs"), ("POST", "pulls"), ("POST", "issues/77/labels")])
        commit = next(b for m, p, b in gh.writes if p.endswith("/git/commits"))
        self.assertEqual(commit["parents"], [BASE])
        self.assertIn("Signed-off-by: tengoku-supervisor[bot] <1+tengoku-supervisor[bot]@users.noreply.github.com>", commit["message"])
        pr = next(b for m, p, b in gh.writes if p.endswith("/pulls"))
        self.assertEqual((pr["base"], pr["head"]), ("main", r["branch"]))
        self.assertIn("<!-- studied:v1", pr["body"])
        self.assertEqual(next(b for m, p, b in gh.writes if p.endswith("/labels")), {"labels": ["studied"]})

    def run_open(self, gh, c):
        return G.open_pr(gh, REPO, BASE, c, "tengoku-supervisor[bot]", "1+tengoku-supervisor[bot]@users.noreply.github.com")

    def test_a_rerun_after_the_branch_was_made_but_not_the_pr_makes_the_pr_only(self):
        gh, c = Fake(), comp()
        gh.refs.add(f"studied/erdos-396/{c.bundle[:16]}")  # the earlier run stopped after the ref POST
        r = self.run_open(gh, c)
        self.assertEqual(r["number"], 77)
        self.assertEqual([p.split("/", 3)[-1] for m, p, _ in gh.writes], ["pulls", "issues/77/labels"])  # no second commit, no second ref

    def test_a_rerun_after_the_pr_was_made_but_not_labelled_labels_it(self):
        gh, c = Fake(), comp()
        gh.refs.add(f"studied/erdos-396/{c.bundle[:16]}")
        gh.prs[f"studied/erdos-396/{c.bundle[:16]}"] = {"number": 41, "html_url": f"https://github.com/{REPO}/pull/41"}
        r = self.run_open(gh, c)
        self.assertEqual((r["number"], r["url"]), (41, f"https://github.com/{REPO}/pull/41"))
        self.assertEqual([(m, p.split("/", 3)[-1]) for m, p, _ in gh.writes], [("POST", "issues/41/labels")])

    def test_two_runs_in_a_row_make_one_pr(self):
        gh, c = Fake(), comp()
        first = self.run_open(gh, c)
        gh.prs[first["branch"]] = {"number": first["number"], "html_url": first["url"]}
        before = len(gh.writes)
        second = self.run_open(gh, c)
        self.assertEqual(second, first)
        self.assertEqual([p.split("/", 3)[-1] for m, p, _ in gh.writes[before:]], [f"issues/{first['number']}/labels"])

    def test_an_error_that_is_not_a_missing_branch_is_not_hidden(self):
        def api(method, path, body=None, raw=False):
            if "/git/ref/heads/" in path:
                raise G.ApiError("gh api GET: HTTP 502 Bad Gateway")
            return Fake()(method, path, body, raw)

        with self.assertRaises(G.ApiError):
            G.open_pr(api, REPO, BASE, comp(), "bot", "e@x")

    BOT = "tengoku-supervisor[bot]"

    def settled_pr(self, number, state="closed", merged_at=None, by=BOT, comment=None):
        pr = {"number": number, "html_url": f"https://github.com/{REPO}/pull/{number}", "state": state, "merged_at": merged_at}
        return pr, [{"body": f"Closed by the intake.\n\n{comment or G.SETTLED}", "user": {"login": by}}]

    def test_a_bundle_closed_on_a_code_owners_decisions_goes_on_in_the_next_round(self):
        gh, c = Fake(), comp()
        first = f"studied/erdos-396/{c.bundle[:16]}"
        gh.refs.add(first)
        gh.prs[first], gh.comments[41] = self.settled_pr(41)
        r = self.run_open(gh, c)
        self.assertEqual(r["branch"], first + "-r2")
        self.assertNotEqual(r["number"], 41)
        self.assertIn(first + "-r2", gh.refs)
        pr = next(b for m, p, b in gh.writes if p.endswith("/pulls"))
        self.assertEqual(pr["head"], first + "-r2")
        self.assertEqual(sum(p.endswith("/git/commits") for m, p, b in gh.writes), 1)

    def test_a_second_and_a_third_round(self):
        gh, c = Fake(), comp()
        first = f"studied/erdos-396/{c.bundle[:16]}"
        gh.refs.update({first, first + "-r2"})
        gh.prs[first], gh.comments[41] = self.settled_pr(41)
        gh.prs[first + "-r2"], gh.comments[42] = self.settled_pr(42)
        self.assertEqual(self.run_open(gh, c)["branch"], first + "-r3")
        gh2 = Fake()
        gh2.refs.update({first, first + "-r2"})
        gh2.prs[first], gh2.comments[41] = self.settled_pr(41)
        gh2.prs[first + "-r2"] = {"number": 42, "html_url": f"https://github.com/{REPO}/pull/42", "state": "open", "merged_at": None}
        r = self.run_open(gh2, c)
        self.assertEqual((r["number"], r["branch"]), (42, first + "-r2"), "an open round is reused, not opened again")
        self.assertEqual([p.split("/", 3)[-1] for m, p, _ in gh2.writes], ["issues/42/labels"])

    def test_a_pr_a_person_closed_or_one_that_merged_is_not_a_round(self):
        for pr, comments in (
            self.settled_pr(41, comment="no marker here"),  # closed by a person: a decision already made
            self.settled_pr(41, by="stranger"),  # the marker in someone else's comment is not the intake's
            self.settled_pr(41, state="closed", merged_at="2026-10-23T00:00:00Z"),  # merged
        ):
            gh, c = Fake(), comp()
            first = f"studied/erdos-396/{c.bundle[:16]}"
            gh.refs.add(first)
            gh.prs[first], gh.comments[41] = pr, comments
            r = self.run_open(gh, c)
            self.assertEqual((r["number"], r["branch"]), (41, first), comments)
            self.assertEqual([p.split("/", 3)[-1] for m, p, _ in gh.writes], ["issues/41/labels"])

    def test_the_rounds_are_bounded(self):
        gh, c = Fake(), comp()
        first = f"studied/erdos-396/{c.bundle[:16]}"
        for n in range(1, 21):
            b = first if n == 1 else f"{first}-r{n}"
            gh.refs.add(b)
            gh.prs[b], gh.comments[100 + n] = self.settled_pr(100 + n)
        with self.assertRaises(G.ApiError):
            self.run_open(gh, c)

    def test_a_dry_run_writes_nothing(self):
        gh = Fake()
        r = G.open_pr(gh, REPO, BASE, comp(), "bot", "e@x", dry_run=True)
        self.assertEqual(gh.writes, [])
        self.assertIn("Tengoku/Studied.lean", r["files"])


class Comments(unittest.TestCase):
    def test_the_comments_of_a_pr_are_read_page_by_page_and_only_objects_count(self):
        pages = {1: [{"id": i} for i in range(100)], 2: [{"id": 100}, "junk"], 3: [{"id": 999}]}
        asked = []

        def api(method, path, body=None, raw=False):
            asked.append(path.split("&page=")[1])
            return pages.get(int(path.split("&page=")[1]), [])

        got = G.pr_comments(api, REPO, 5)
        self.assertEqual([c["id"] for c in got][-2:], [99, 100])
        self.assertEqual(len(got), 101)
        self.assertEqual(asked, ["1", "2"], "a page of fewer than a hundred is the last")
        self.assertEqual(len(G.pr_comments(api, REPO, 5, pages=1)), 100, "the page limit holds")

    def test_a_comment_is_left_once_by_the_bot_only(self):
        posted = []
        existing = [{"body": "x <!-- m --> y", "user": {"login": "stranger"}}]

        def api(method, path, body=None, raw=False):
            if method == "GET":
                return existing if "page=1" in path else []
            posted.append(body)
            return {}

        self.assertTrue(G.comment_once(api, REPO, 5, "<!-- m -->", "hello <!-- m -->", "bot"), "a stranger's comment with the marker does not stop the bot")
        existing.append({"body": "hello <!-- m -->", "user": {"login": "bot"}})
        self.assertFalse(G.comment_once(api, REPO, 5, "<!-- m -->", "hello <!-- m -->", "bot"))
        self.assertEqual(len(posted), 1)

    def test_code_owners_are_the_star_line_of_the_file_on_main_and_nobody_when_there_is_no_file(self):
        def api(method, path, body=None, raw=False):
            assert path.endswith("/contents/.github/CODEOWNERS?ref=main"), path
            return b"* @Ada @bob\n/x @eve\n"

        self.assertEqual(G.code_owners(api, REPO), {"ada", "bob"})
        self.assertEqual(G.code_owners(lambda *a, **k: b"", REPO), set())


class State(unittest.TestCase):
    def test_only_pull_requests_are_listed(self):
        def api(method, path, body=None, raw=False):
            return [{"number": 1, "pull_request": {}}, {"number": 2}]

        self.assertEqual([r["number"] for r in G.open_studied_prs(api, REPO)], [1])


if __name__ == "__main__":
    unittest.main()
