import unittest

from scripts.memory_intake import events as E
from scripts.memory_intake import githubapi as G
from scripts.memory_intake import settle as S

REPO = "competemath/tengoku"
BOT = "tengoku-supervisor[bot]"
IDS = ["a1b2c3d4" + "0" * 32, "e5f6a7b8" + "1" * 32, "c9d0e1f2" + "2" * 32]
NAMES = ["first", "second", "third"]
BUNDLE = "b" * 64
CODEOWNERS = "* @mikael-bashir @mikaelbashir14096545\n/scripts/ @mikael-bashir\n"


def body(ids=IDS, names=NAMES):
    rows = [{"id": i, "name": n, "stars": 4} for i, n in zip(ids, names)]
    return E.pr_body("ada", "erdos-396", BUNDLE, rows, 1)


def cm(cid, text, login="mikael-bashir", assoc="OWNER", utype="User", created="2026-10-23T10:00:00Z"):
    return {"id": cid, "body": text, "user": {"login": login, "type": utype}, "author_association": assoc, "created_at": created}


class Gh:
    """The pull requests of a repository as the REST API shows them: enough of it for settle()."""

    def __init__(self, codeowners=CODEOWNERS):
        self.codeowners = codeowners
        self.prs: dict[int, dict] = {}
        self.comments: dict[int, list] = {}
        self.writes: list = []
        self.next_comment = 1000

    def add(self, number, text=None, state="open", merged_at=None, author=BOT, comments=()):
        self.prs[number] = {"number": number, "html_url": f"https://github.com/{REPO}/pull/{number}", "state": state, "merged_at": merged_at, "user": {"login": author}, "head": {"sha": "a" * 40}, "body": body() if text is None else text}
        self.comments[number] = list(comments)

    def __call__(self, method, path, body=None, raw=False):
        if method == "GET" and path.endswith("/contents/.github/CODEOWNERS?ref=main"):
            return self.codeowners.encode()
        if method == "GET" and "/issues?labels=studied" in path:
            return [{"number": n, "pull_request": {}} for n in sorted(self.prs, reverse=True)]
        if method == "GET" and "/comments" in path:
            return list(self.comments[int(path.split("/issues/")[1].split("/")[0])]) if "page=1" in path else []
        if method == "GET" and "/pulls/" in path:
            return dict(self.prs[int(path.rsplit("/", 1)[1])])
        self.writes.append((method, path, body))
        if method == "POST" and path.endswith("/comments"):
            n = int(path.split("/issues/")[1].split("/")[0])
            self.next_comment += 1
            self.comments[n].append(cm(self.next_comment, body["body"], login=BOT, assoc="NONE", utype="Bot"))
        if method == "PATCH":
            self.prs[int(path.rsplit("/", 1)[1])]["state"] = body["state"]
        return {}


class Settle(unittest.TestCase):
    def test_a_decision_closes_the_pull_request_with_a_comment_and_tells_the_site(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "Looks fine, but:\nstudied: return a1b2c3d4 merit nothing uses it\nstudied: reject e5f6a7b8 hygiene")])
        prs, reviews, log, failed = S.settle(gh, REPO, BOT)
        self.assertEqual(gh.prs[7]["state"], "closed")
        comment = next(b for m, p, b in gh.writes if p.endswith("/comments"))["body"]
        self.assertIn("returned: the author may come back with a better one: `first` (merit)", comment)
        self.assertIn("rejected: not shipped: `second` (hygiene)", comment)
        self.assertIn("the others go into the next bundle, as a new pull request: `third`", comment)
        self.assertTrue(comment.rstrip().endswith(G.SETTLED))
        self.assertEqual([(m, p.rsplit("/", 2)[-2:]) for m, p, _ in gh.writes], [("POST", ["7", "comments"]), ("PATCH", ["pulls", "7"])], "the comment first, then the close")
        self.assertEqual([(p["number"], [e["code"] for e in p["events"]]) for p in prs], [(7, ["review.superseded", "review.reject.hygiene", "review.return.merit"])])
        self.assertEqual(reviews[0]["accepted"], [IDS[2]])
        self.assertEqual((reviews[0]["bundle"], reviews[0]["username"]), (BUNDLE, "ada"))
        self.assertTrue(any("PR #7: closed" in x for x in log))

    def test_it_does_nothing_twice(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 merit")])
        S.settle(gh, REPO, BOT)
        n = len(gh.writes)
        prs, reviews, log, failed = S.settle(gh, REPO, BOT)
        self.assertEqual((len(gh.writes), prs, reviews), (n, [], []), "a closed pull request is left alone")

    def test_a_close_that_failed_half_way_is_finished_without_a_second_comment(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 merit")])
        gh.prs[7]["state"] = "open"
        real = gh.__call__

        def failing(method, path, body=None, raw=False):
            if method == "PATCH":
                raise G.ApiError("PATCH: HTTP 502")
            return real(method, path, body, raw)

        prs, reviews, log, failed = S.settle(failing, REPO, BOT)
        self.assertEqual((failed, prs, reviews), (1, [], []))
        self.assertTrue(any("PR #7 was not settled" in x for x in log))
        self.assertEqual(gh.prs[7]["state"], "open")
        S.settle(gh, REPO, BOT)
        self.assertEqual(gh.prs[7]["state"], "closed")
        self.assertEqual(sum(p.endswith("/comments") for m, p, b in gh.writes), 1, "one close comment in all")

    def test_a_pull_request_whose_calls_fail_does_not_stop_the_others(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 merit")])
        gh.add(8, comments=[cm(1, "studied: reject e5f6a7b8 scope")])
        real = gh.__call__

        def flaky(method, path, body=None, raw=False):
            if path.endswith("/pulls/8"):  # the newer one is read first
                raise G.ApiError("GET pulls/8: HTTP 502")
            return real(method, path, body, raw)

        prs, reviews, log, failed = S.settle(flaky, REPO, BOT)
        self.assertEqual(failed, 1)
        self.assertEqual([p["number"] for p in prs], [7], "the other pull request was settled")
        self.assertEqual((gh.prs[7]["state"], gh.prs[8]["state"]), ("closed", "open"))

    def test_only_a_code_owner_decides(self):
        gh = Gh()
        gh.add(7, comments=[
            cm(1, "studied: reject a1b2c3d4 hygiene", login="stranger", assoc="NONE"),
            cm(2, "studied: reject a1b2c3d4 hygiene", login="ada", assoc="CONTRIBUTOR"),
            cm(3, "studied: reject a1b2c3d4 hygiene", login="gitar-bot", utype="Bot", assoc="NONE"),
            cm(4, "> studied: reject a1b2c3d4 hygiene\nI would not.", login="mikael-bashir"),
            cm(5, "```\nstudied: reject a1b2c3d4 hygiene\n```", login="mikael-bashir"),
        ])
        prs, reviews, log, failed = S.settle(gh, REPO, BOT)
        self.assertEqual((gh.prs[7]["state"], gh.writes, prs, reviews), ("open", [], [], []))

    def test_a_pull_request_the_app_did_not_open_is_never_closed(self):
        gh = Gh()
        gh.add(7, author="stranger", comments=[cm(1, "studied: reject a1b2c3d4 hygiene")])  # a forged marker in someone else's pull request
        gh.add(8, text="no marker at all", comments=[cm(1, "studied: reject a1b2c3d4 hygiene")])
        gh.add(9, state="closed", merged_at="2026-10-23T00:00:00Z", comments=[cm(1, "studied: reject a1b2c3d4 hygiene")])
        S.settle(gh, REPO, BOT)
        self.assertEqual(gh.writes, [])

    def test_an_unreadable_code_owners_file_settles_nothing_and_fails_the_run(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: reject a1b2c3d4 hygiene")])
        real = gh.__call__

        def down(method, path, body=None, raw=False):
            if "CODEOWNERS" in path:
                raise G.ApiError("GET CODEOWNERS: HTTP 503")
            return real(method, path, body, raw)

        prs, reviews, log, failed = S.settle(down, REPO, BOT)
        self.assertEqual((gh.writes, prs, reviews, failed), ([], [], [], 1))

    def test_no_code_owners_file_means_no_decision_counts(self):
        gh = Gh(codeowners="")
        gh.add(7, comments=[cm(1, "studied: reject a1b2c3d4 hygiene")])
        prs, reviews, log, failed = S.settle(gh, REPO, BOT)
        self.assertEqual((gh.writes, prs, reviews), ([], [], []))
        self.assertIn("no code owner", log[0])

    def test_a_decision_naming_every_theorem_frees_nobody(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 docs\nstudied: return e5f6a7b8 docs\nstudied: reject c9d0e1f2 scope")])
        prs, reviews, _, _f = S.settle(gh, REPO, BOT)
        self.assertEqual(reviews[0]["accepted"], [])
        self.assertIn("none left", next(b for m, p, b in gh.writes if p.endswith("/comments"))["body"])
        self.assertEqual(prs[0]["events"][0]["code"], "pr.closed")

    def test_a_dry_run_changes_nothing_and_reports_nothing_to_the_site(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 merit\nstudied: oops")])
        prs, reviews, log, failed = S.settle(gh, REPO, BOT, dry_run=True)
        self.assertEqual((gh.writes, prs, reviews, gh.prs[7]["state"]), ([], [], [], "open"))
        self.assertTrue(any("would close" in x for x in log))

    def test_an_owners_malformed_line_is_answered_once_on_the_pull_request(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 nonsense\nstudied: return deadbeef merit")])
        S.settle(gh, REPO, BOT)
        S.settle(gh, REPO, BOT)
        notes = [b["body"] for m, p, b in gh.writes if p.endswith("/comments")]
        self.assertEqual(len(notes), 1)
        self.assertIn("line 1: `nonsense` is not a return code", notes[0])
        self.assertIn("line 2: `deadbeef` is not the id of exactly one theorem", notes[0])
        self.assertEqual(gh.prs[7]["state"], "open", "nothing was decided")

    def test_a_non_owners_noise_is_not_answered(self):
        gh = Gh()
        gh.add(7, comments=[cm(1, "studied: return a1b2c3d4 merit", login="stranger", assoc="NONE"), cm(2, "studied: nonsense", login="stranger", assoc="NONE")])
        S.settle(gh, REPO, BOT)
        self.assertEqual(gh.writes, [])

    def test_the_names_in_the_comment_cannot_break_the_markdown(self):
        gh = Gh()
        gh.add(7, text=body(names=["a`b", "second", "third"]), comments=[cm(1, "studied: return a1b2c3d4 docs")])
        S.settle(gh, REPO, BOT)
        comment = next(b for m, p, b in gh.writes if p.endswith("/comments"))["body"]
        self.assertIn("`a_b` (docs)", comment)


if __name__ == "__main__":
    unittest.main()
