import unittest

from scripts.memory_intake import events as E

MARK = {"account": "ada", "target": "erdos-396", "bundle": "b" * 64, "ids": ["a1" * 8], "names": ["lemma_1"]}


def pr(**over):
    return {"number": 12, "html_url": "https://github.com/competemath/tengoku/pull/12", "state": "open", "merged": False, "merged_at": None, "head": {"sha": "a" * 40},
            "body": E.pr_body("ada", "erdos-396", "b" * 64, [{"id": "a1" * 8, "name": "lemma_1", "stars": 4}], 1), **over}


def check(name, conclusion, title=""):
    return {"name": name, "conclusion": conclusion, "output": {"title": title}}


class Body(unittest.TestCase):
    def test_the_marker_round_trips(self):
        m = E.parse_marker(pr()["body"])
        self.assertEqual(m, {"account": "ada", "target": "erdos-396", "bundle": "b" * 64, "ids": ["a1" * 8], "names": ["lemma_1"]})

    def test_a_body_without_a_marker_or_with_a_bad_one(self):
        for body in (None, "", "no marker", "<!-- studied:v1 {not json} -->", '<!-- studied:v1 {"account": 3} -->', '<!-- studied:v1 [1] -->'):
            self.assertIsNone(E.parse_marker(body), body)

    def test_the_body_names_the_theorems_and_the_bar(self):
        b = pr()["body"]
        self.assertIn("`lemma_1` (4 stars)", b)
        self.assertIn("bar/0", b)
        self.assertIn("two independent contributors", b)


class Derive(unittest.TestCase):
    def kinds(self, p, checks=(), reviews=()):
        return [(e["kind"], e["code"]) for e in E.derive(p, list(checks), list(reviews), E.parse_marker(p["body"]))]

    def test_open_is_submitted(self):
        self.assertEqual(self.kinds(pr()), [("submitted", "pr.opened")])

    def test_merged_and_closed_say_only_that(self):
        self.assertEqual(self.kinds(pr(merged=True, merged_at="2026-10-23T00:00:00Z", state="closed")), [("merged", "pr.merged")])
        self.assertEqual(self.kinds(pr(state="closed")), [("closed", "pr.closed")])

    def test_failed_checks_become_gate_failures_with_the_codes_the_catalogue_knows(self):
        got = self.kinds(pr(), [check("born tagged (the isnad tags are in the PR)", "failure"), check("studied checks", "failure"), check("queue build", "timed_out"),
                                check("lint", "failure"), check("something else", "failure"), check("fine", "success"), check("pending", None)])
        self.assertEqual(got, [("submitted", "pr.opened"), ("gate_failed", "gate.isnad"), ("gate_failed", "gate.studied"), ("gate_failed", "gate.build"),
                               ("gate_failed", "gate.lint"), ("gate_failed", "gate.other")])

    def test_one_event_per_code_even_if_many_checks_fail(self):
        got = self.kinds(pr(), [check("build a", "failure"), check("build b", "failure")])
        self.assertEqual(got.count(("gate_failed", "gate.build")), 1)

    def test_a_change_request_stands_until_the_reviewer_approves_or_it_is_dismissed(self):
        asked = {"user": {"login": "rev"}, "state": "CHANGES_REQUESTED", "body": "please generalise lemma_1"}
        self.assertEqual(self.kinds(pr(), reviews=[asked]), [("submitted", "pr.opened"), ("changes_requested", "review.changes")])
        self.assertEqual(self.kinds(pr(), reviews=[asked, {"user": {"login": "rev"}, "state": "APPROVED", "body": ""}]), [("submitted", "pr.opened")])
        self.assertEqual(self.kinds(pr(), reviews=[asked, {"user": {"login": "rev"}, "state": "DISMISSED", "body": ""}]), [("submitted", "pr.opened")])
        self.assertEqual(len(self.kinds(pr(), reviews=[asked, {"user": {"login": "other"}, "state": "APPROVED", "body": ""}])), 2, "another reviewer's approval answers nothing")

    def test_the_reviewers_words_are_carried_as_detail_only(self):
        ev = E.derive(pr(), [], [{"user": {"login": "r"}, "state": "CHANGES_REQUESTED", "body": "x" * 900}], E.parse_marker(pr()["body"]))
        self.assertEqual(len(ev[-1]["detail"]), 500)
        self.assertEqual(ev[-1]["code"], "review.changes")

    def test_report_for(self):
        r = E.report_for(pr(), [], [])
        self.assertEqual((r["username"], r["target"], r["number"], r["url"]), ("ada", "erdos-396", 12, "https://github.com/competemath/tengoku/pull/12"))
        self.assertEqual(r["events"][0]["names"], ["lemma_1"])
        self.assertIsNone(E.report_for(pr(body="a human's PR"), [], []))
        self.assertIsNone(E.report_for(pr(html_url="http://evil"), [], []))


if __name__ == "__main__":
    unittest.main()
