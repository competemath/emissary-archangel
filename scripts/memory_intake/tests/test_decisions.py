import unittest

from scripts.memory_intake import decisions as D

IDS = ["a1b2c3d4" + "0" * 32, "e5f6a7b8" + "1" * 32, "e5f6a7b9" + "2" * 32]  # the last two share their first seven characters
NAMES = ["first", "second", "third"]
MARK = {"account": "ada", "target": "erdos-396", "bundle": "b" * 64, "ids": IDS, "names": NAMES}
OWNERS = {"mikael-bashir", "mikaelbashir14096545"}
CODEOWNERS = """\
# Tier 4: maintainer plus a second approver.
*                        @mikael-bashir @mikaelbashir14096545
/Tengoku.lean            @mikael-bashir
/Tengoku/*/
/data/trusted/           @someone-else @org/team
"""


def cm(cid, body, login="mikael-bashir", assoc="OWNER", utype="User", created="2026-10-23T10:00:00Z"):
    return {"id": cid, "body": body, "user": {"login": login, "type": utype}, "author_association": assoc, "created_at": created}


def parse(*comments, ids=IDS):
    return D.parse(list(comments), ids, OWNERS)


class Owners(unittest.TestCase):
    def test_the_star_line_only_and_accounts_only(self):
        self.assertEqual(D.owners_from_codeowners(CODEOWNERS), {"mikael-bashir", "mikaelbashir14096545"})
        self.assertEqual(D.owners_from_codeowners("/data/ @a\n"), set(), "no star line: nobody decides")
        self.assertEqual(D.owners_from_codeowners("* @org/team @Ada  # comment @evil\n"), {"ada"}, "a team is not an account; the case is folded; a trailing comment is not read")
        self.assertEqual(D.owners_from_codeowners(""), set())

    def test_an_owner_is_a_user_of_that_login_with_write_access(self):
        ok = cm(1, "x")
        self.assertTrue(D.is_owner(ok, OWNERS))
        self.assertTrue(D.is_owner(cm(1, "x", login="Mikael-Bashir", assoc="MEMBER"), OWNERS), "logins are compared without case")
        self.assertFalse(D.is_owner(cm(1, "x", login="stranger"), OWNERS))
        self.assertFalse(D.is_owner(cm(1, "x", utype="Bot"), OWNERS), "a bot with an owner's name is not the owner")
        for assoc in ("NONE", "CONTRIBUTOR", "FIRST_TIME_CONTRIBUTOR", None):
            self.assertFalse(D.is_owner(cm(1, "x", assoc=assoc), OWNERS), assoc)


class Grammar(unittest.TestCase):
    def test_a_return_and_a_reject(self):
        got, ignored = parse(cm(1, "Thanks.\n\nstudied: return a1b2c3d4 merit not used anywhere\nstudied: reject e5f6a7b8 hygiene\n"))
        self.assertEqual(ignored, [])
        self.assertEqual([(d.id, d.verdict, d.code, d.detail) for d in got], [(IDS[1], "reject", "hygiene", ""), (IDS[0], "return", "merit", "not used anywhere")])

    def test_every_documented_code(self):
        for code in D.RETURN_CODES:
            self.assertEqual(len(parse(cm(1, f"studied: return a1b2c3d4 {code}"))[0]), 1, code)
        for code in D.REJECT_CODES:
            self.assertEqual(len(parse(cm(1, f"studied: reject a1b2c3d4 {code}"))[0]), 1, code)

    def test_the_latest_decision_of_an_id_wins_across_comments_and_within_one(self):
        got, _ = parse(
            cm(2, "studied: reject a1b2c3d4 scope", created="2026-10-23T12:00:00Z"),
            cm(1, "studied: return a1b2c3d4 merit", created="2026-10-23T11:00:00Z"),
        )
        self.assertEqual([(d.verdict, d.code) for d in got], [("reject", "scope")], "listed out of order: the later comment still wins")
        got, _ = parse(cm(1, "studied: return a1b2c3d4 merit\nstudied: return a1b2c3d4 docs"))
        self.assertEqual([d.code for d in got], ["docs"])

    def test_malformed_lines_are_ignored_and_reported_never_guessed(self):
        cases = {
            "studied: return a1b2c3d4": "no code",
            "studied: return a1b2c3 merit": "id too short",
            "studied: return A1B2C3D4 merit": "id in capitals",
            "studied: send a1b2c3d4 merit": "no such verdict",
            "Studied: return a1b2c3d4 merit": "capital S",
            "studied:return a1b2c3d4 merit": "no space after the colon",
            "studied: return a1b2c3d4 MERIT": "code in capitals",
            "studied: return a1b2c3d4 merit2": "code with a digit",
        }
        for line, why in cases.items():
            got, ignored = parse(cm(1, line))
            self.assertEqual(got, [], why)
            self.assertEqual([(i.owner, i.line) for i in ignored], [(True, 1)], why)

    def test_a_code_of_the_other_verdict_is_refused(self):
        for line in ("studied: reject a1b2c3d4 merit", "studied: return a1b2c3d4 hygiene", "studied: return a1b2c3d4 nonsense"):
            got, ignored = parse(cm(1, line))
            self.assertEqual(got, [], line)
            self.assertIn("is not a", ignored[0].why)

    def test_an_id_that_is_not_in_the_pull_request_or_is_ambiguous_is_refused(self):
        got, ignored = parse(cm(1, "studied: return deadbeef merit"))
        self.assertEqual((got, ignored[0].why.startswith("`deadbeef`")), ([], True))
        got, ignored = parse(cm(1, "studied: return e5f6a7b8 merit\nstudied: return e5f6a7b9 merit"), ids=IDS)
        self.assertEqual([d.id for d in got], [IDS[1], IDS[2]], "the 8 characters name exactly one theorem each")
        got, ignored = parse(cm(1, "studied: return e5f6a7b8 merit"), ids=[IDS[1], "e5f6a7b8" + "9" * 32])
        self.assertEqual((got, len(ignored)), ([], 1), "two theorems share the 8 characters: neither is guessed")

    def test_the_owners_free_text_is_cleaned_and_cut(self):
        got, _ = parse(cm(1, "studied: return a1b2c3d4 merit  a‮b \u0007 c  " + "x" * 400))
        self.assertTrue(got[0].detail.startswith("a b c x"))
        self.assertLessEqual(len(got[0].detail), D.MAX_DETAIL)


class WhoAndWhere(unittest.TestCase):
    """The decision line is only a decision when a code owner wrote it as a line of their own text."""

    LINE = "studied: reject a1b2c3d4 hygiene"

    def taken(self, comment):
        got, ignored = parse(comment)
        return len(got), ignored

    def test_another_account_decides_nothing(self):
        for c in (cm(1, self.LINE, login="stranger", assoc="NONE"), cm(1, self.LINE, login="stranger", assoc="CONTRIBUTOR"), cm(1, self.LINE, login="ada"), cm(1, self.LINE, login="gitar-bot", utype="Bot", assoc="NONE"),
                  cm(1, self.LINE, login="mikael-bashir", utype="Bot"), cm(1, self.LINE, login="mikael-bashir", assoc="CONTRIBUTOR")):
            n, ignored = self.taken(c)
            self.assertEqual(n, 0, c["user"])
            self.assertEqual([i.owner for i in ignored], [False], "reported, but as noise: the pull request is not answered")

    def test_a_quoted_decision_is_not_a_decision(self):
        for body in (f"> {self.LINE}", f">{self.LINE}", f"> > {self.LINE}", f"@stranger wrote:\n> {self.LINE}\nI disagree."):
            n, ignored = self.taken(cm(1, body))
            self.assertEqual((n, ignored), (0, []), body)

    def test_a_line_that_markdown_still_renders_inside_a_quote_is_not_a_decision(self):
        for body in (f"> wrote:\n{self.LINE}", f"> wrote:\n> more\n{self.LINE}", f"> wrote:\nand also\n{self.LINE}"):
            n, ignored = self.taken(cm(1, body))
            self.assertEqual(n, 0, body)
            self.assertEqual([(i.owner, i.line) for i in ignored], [(True, body.count("\n") + 1)], "an owner is told why, once")
        n, ignored = self.taken(cm(1, f"> wrote:\n\n{self.LINE}"))
        self.assertEqual((n, ignored), (1, []), "a blank line ends the quote")
        n, _ = self.taken(cm(1, f"> wrote:\n```\nin a block\n```\n{self.LINE}"))
        self.assertEqual(n, 1, "a code block ends it too")
        n, ignored = self.taken(cm(1, f"> wrote:\n{self.LINE}", login="stranger", assoc="NONE"))
        self.assertEqual((n, [i.owner for i in ignored]), (0, [False]))

    def test_a_decision_in_a_code_block_is_not_a_decision(self):
        for body in (f"```\n{self.LINE}\n```", f"```text\n{self.LINE}\n```\n", f"~~~\n{self.LINE}\n~~~", f"````\n```\n{self.LINE}\n```\n````", f"```\n{self.LINE}\n"):
            n, ignored = self.taken(cm(1, body))
            self.assertEqual((n, ignored), (0, []), body)

    def test_a_decision_after_the_block_closes_is_one(self):
        n, _ = self.taken(cm(1, f"```\nstudied: return a1b2c3d4 merit\n```\n{self.LINE}"))
        self.assertEqual(n, 1)
        n, _ = self.taken(cm(1, f"````\n```\nnot closed by three\n{self.LINE}\n````\n{self.LINE}"))
        self.assertEqual(n, 1)

    def test_a_hidden_or_inline_or_indented_or_listed_line_is_not_a_decision(self):
        for body in (f"<!-- {self.LINE} -->", f"<!--\n{self.LINE}\n-->", f"as in `{self.LINE}`", f"I will write {self.LINE}", f"    {self.LINE}", f"\t{self.LINE}", f"- {self.LINE}"):
            n, ignored = self.taken(cm(1, body))
            self.assertEqual(n, 0, body)
            self.assertEqual([i for i in ignored if i.owner], [], body)

    def test_a_decision_next_to_a_hidden_comment_is_still_one(self):
        n, _ = self.taken(cm(1, f"<!-- note -->\n{self.LINE}"))
        self.assertEqual(n, 1)

    def test_crlf_and_a_few_leading_spaces(self):
        n, _ = self.taken(cm(1, "hello\r\n   studied: reject a1b2c3d4 hygiene\r\n"))
        self.assertEqual(n, 1)


class Payloads(unittest.TestCase):
    def decided(self):
        return parse(cm(1, "studied: return a1b2c3d4 merit make it general\nstudied: return e5f6a7b8 merit\nstudied: reject e5f6a7b9 hygiene sorry in the proof"))[0]

    def test_one_event_per_verdict_and_code_with_the_owners_words_as_detail(self):
        ev = D.events_for(MARK, self.decided())
        self.assertEqual([(e["kind"], e["code"], e["names"]) for e in ev], [("rejected", "review.reject.hygiene", ["third"]), ("returned", "review.return.merit", ["first", "second"])])
        self.assertEqual(ev[1]["detail"], "first: make it general")
        self.assertEqual(ev[0]["detail"], "third: sorry in the proof")
        self.assertEqual(ev[1]["ids"], [IDS[0], IDS[1]])

    def test_the_review_holds_the_decided_and_frees_the_rest_only_once_closed(self):
        ds = self.decided()
        self.assertEqual(
            D.review_payload(MARK, ds, closed=False),
            {"username": "ada", "target": "erdos-396", "bundle": "b" * 64, "returned": [{"id": IDS[0], "code": "merit"}, {"id": IDS[1], "code": "merit"}], "rejected": [{"id": IDS[2], "code": "hygiene"}], "accepted": []},
        )
        only = parse(cm(1, "studied: return a1b2c3d4 docs"))[0]
        self.assertEqual(D.review_payload(MARK, only, closed=True)["accepted"], [IDS[1], IDS[2]])
        self.assertEqual(D.review_payload(MARK, ds, closed=True)["accepted"], [], "everything decided: nothing to free")
        self.assertIsNone(D.review_payload(MARK, [], closed=True))


if __name__ == "__main__":
    unittest.main()
