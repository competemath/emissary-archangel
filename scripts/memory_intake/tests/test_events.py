import unittest

from scripts.memory_intake import decisions as D
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

    def test_the_body_shows_the_first_eight_characters_of_each_id_for_the_decision_lines(self):
        b = pr()["body"]
        self.assertIn("`lemma_1` (4 stars) · id `a1a1a1a1`", b)
        self.assertIn("`studied: return <id> <code>`", b)
        self.assertIn("`studied: reject <id> <code>`", b)

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

    def decided(self, *lines, ids=("a1" * 20, "b2" * 20, "c3" * 20)):
        mark = {"account": "ada", "target": "erdos-396", "bundle": "b" * 64, "ids": list(ids), "names": ["one", "two", "three"]}
        owners = {"boss"}
        comment = {"id": 1, "body": "\n".join(lines), "user": {"login": "boss", "type": "User"}, "author_association": "OWNER", "created_at": "2026-10-23T00:00:00Z"}
        return mark, D.parse([comment], list(ids), owners)[0]

    def test_an_open_pr_with_decisions_lists_them_beside_its_own_state(self):
        mark, ds = self.decided("studied: return a1a1a1a1 merit", "studied: reject b2b2b2b2 hygiene")
        got = [(e["kind"], e["code"]) for e in E.derive(pr(), [], [], mark, ds)]
        self.assertEqual(got, [("submitted", "pr.opened"), ("rejected", "review.reject.hygiene"), ("returned", "review.return.merit")])

    def test_a_closed_pr_with_decisions_and_others_left_is_superseded_and_the_decisions_stay(self):
        mark, ds = self.decided("studied: return a1a1a1a1 merit")
        ev = E.derive(pr(state="closed"), [], [], mark, ds)
        self.assertEqual([(e["kind"], e["code"]) for e in ev], [("closed", "review.superseded"), ("returned", "review.return.merit")])
        self.assertEqual((ev[0]["names"], ev[0]["ids"]), (["two", "three"], ["b2" * 20, "c3" * 20]), "the superseded notice names the theorems that go on")

    def test_a_closed_pr_with_every_theorem_decided_is_plainly_closed(self):
        mark, ds = self.decided("studied: return a1a1a1a1 merit", "studied: reject b2b2b2b2 scope", "studied: reject c3c3c3c3 report")
        self.assertEqual([e["code"] for e in E.derive(pr(state="closed"), [], [], mark, ds)], ["pr.closed", "review.reject.report", "review.reject.scope", "review.return.merit"])

    def test_a_closed_pr_without_decisions_and_a_merged_one_are_as_before(self):
        mark, ds = self.decided("studied: return a1a1a1a1 merit")
        self.assertEqual([e["code"] for e in E.derive(pr(state="closed"), [], [], mark, [])], ["pr.closed"])
        self.assertEqual([e["code"] for e in E.derive(pr(merged=True, merged_at="2026-10-23T00:00:00Z", state="closed"), [], [], mark, ds)], ["pr.merged"], "a merged pull request is settled: decisions do not matter")

    def test_report_for(self):
        r = E.report_for(pr(), [], [])
        self.assertEqual((r["username"], r["target"], r["number"], r["url"]), ("ada", "erdos-396", 12, "https://github.com/competemath/tengoku/pull/12"))
        self.assertEqual(r["events"][0]["names"], ["lemma_1"])
        self.assertIsNone(E.report_for(pr(body="a human's PR"), [], []))
        self.assertIsNone(E.report_for(pr(html_url="http://evil"), [], []))


if __name__ == "__main__":
    unittest.main()
