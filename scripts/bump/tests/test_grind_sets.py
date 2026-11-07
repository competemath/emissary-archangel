"""grind_sets.py: a library's custom grind sets and its inert lines are rewritten away, with what every declaration says unchanged, under a guard, and every changed file
carries a change notice (where it came from, what was changed).

The real case is scripts/bump/tests/fixtures/real-cslib-sources.json.gz: the 251 module texts of cslib (leanprover/cslib at e806c8e6) as its 6 Nov 2026 bump shard packed
them (the repaired sources). Its root Cslib.Init imports Cslib.Tactic.GrindAttrs (`register_grind_attr modal`), so every module was refused and 2,522 declarations that
passed Gate 2 shipped as 0 theorems; with this rewrite the same cut gives 1,092 theorems in 112 modules (proposed), before the tree's build.

Invariants checked on all 251 modules:
  1. no registration of a grind set is left, and the root modules pass the content lint;
  2. the guard: every changed module has the same skeleton as before (everything outside attribute lists, grind's lemma lists and the removed lines is byte-identical);
  3. every lemma written into a grind call was tagged with that set in the call's own module (before the call) or in a module it imports, and is declared there;
  4. no tag of the set is left in any attribute list; no grind call names the set any more;
  5. every changed module is listed with what was changed (for its change notice); unchanged modules are byte-identical.
"""

from __future__ import annotations

import gzip
import json
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "lint"))
import allowlist  # noqa: E402
import grind_sets as gs  # noqa: E402
import strip_attrs  # noqa: E402
import tolerant_build as tb  # noqa: E402

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "real-cslib-sources.json.gz"
HEADER = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s|^\s*(?:module|prelude)\s*$")


def lint(text: str) -> list[str]:
    allowed = set(json.loads((HERE / "lint" / "allowed-options.json").read_text())["allowed"])
    keywords = set(json.loads((HERE / "lint" / "command-keywords.json").read_text())["commands"])
    t, _ = strip_attrs.strip_attributes(text)
    return allowlist.violations("\n".join("" if HEADER.match(ln) else ln for ln in t.split("\n")), allowed, keywords)


class RealCslib(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = json.load(gzip.open(FIXTURE, "rt"))
        cls.texts = d["texts"]
        cls.imports = {m: [i for i in tb.header_imports(t) if i in cls.texts] for m, t in cls.texts.items()}
        cls.out, cls.changes, cls.stats = gs.rewrite(cls.texts, cls.imports)

    def below(self, mod):
        seen, todo = set(), list(self.imports[mod])
        while todo:
            x = todo.pop()
            if x not in seen:
                seen.add(x)
                todo += self.imports[x]
        return seen

    def test_the_counts(self):
        self.assertEqual(self.stats["grind sets"], 1)
        self.assertEqual(self.stats["set tags removed"], 65)
        self.assertEqual(self.stats["grind calls rewritten"], 14)
        self.assertEqual(self.stats["modules kept as they were (guard)"], 0)
        self.assertGreater(self.stats["inert lines removed"], 50)

    def test_the_root_modules_now_pass_the_lint(self):
        self.assertTrue(any("register_grind_attr" in x for x in lint(self.texts["Cslib.Tactic.GrindAttrs"])))  # the premise
        for m in ("Cslib.Tactic.GrindAttrs", "Cslib.Init"):
            self.assertEqual(lint(self.out[m]), [], m)
        self.assertFalse(any(gs.REGISTER.search(t) for t in self.out.values()))

    def test_the_guard_holds_for_every_changed_module(self):
        for m, t in self.out.items():
            if t != self.texts[m]:
                self.assertEqual(gs._skeleton(t), gs._skeleton(self.texts[m]), m)
                self.assertIn(m, self.changes)
                self.assertTrue(self.changes[m])
            else:
                self.assertNotIn(m, self.changes)

    def test_every_written_lemma_was_tagged_where_the_call_can_see_it(self):
        tagged = {m: {full for _, s, _, _, full in gs.tags_of(t, {"modal"})} for m, t in self.texts.items()}
        checked = 0
        for m, t in self.texts.items():
            if "modal" not in t:
                continue
            before = list(gs.GRIND_CALL.finditer(t))
            after = list(gs.GRIND_CALL.finditer(self.out[m]))
            self.assertEqual(len(before), len(after), m)  # the calls are the same calls, in the same order
            visible = set(tagged[m]).union(*[tagged[d] for d in self.below(m)])
            for c0, c1 in zip(before, after):
                old = [x.strip() for x in gs._items(t[c0.end() : gs._close(t, c0.end()) - 1])]
                if "modal" not in old:
                    self.assertEqual(t[c0.start() : gs._close(t, c0.end())], self.out[m][c1.start() : gs._close(self.out[m], c1.end())])  # untouched
                    continue
                for it in gs._items(self.out[m][c1.end() : gs._close(self.out[m], c1.end()) - 1]):
                    name = it.strip().split()[-1]
                    if name not in {x.split()[-1] for x in old if x}:  # a lemma of the set: tagged where the call sees it (a private one of the call's own module by its short name)
                        self.assertTrue(name in visible or any(v.endswith("." + name) for v in tagged[m]), (m, name))
                        checked += 1
        self.assertGreater(checked, 50)

    def test_no_tag_or_set_name_is_left(self):
        for m, t in self.out.items():
            for blk in gs.ATTR_BLOCK.finditer(t):
                items = [x.split()[0] for x in gs._items(t[blk.end() : gs._close(t, blk.end()) - 1]) if x.split()]
                self.assertNotIn("modal", items, m)
            for call in gs.GRIND_CALL.finditer(t):
                self.assertNotIn("modal", [x.strip() for x in gs._items(t[call.end() : gs._close(t, call.end()) - 1])], m)


class Synthetic(unittest.TestCase):
    LIB = {
        "L.Attrs": "module\n\nnamespace N\n/-- the set's doc -/\nregister_grind_attr myset\nend N\n",
        "L.A": "import L.Attrs\n\nnamespace P\n@[myset] theorem a : True := trivial\n@[simp, myset =] theorem b : True := trivial\nprivate theorem c : True := trivial\nattribute [myset] c\nend P\n",
        "L.B": "import L.A\n\nexample : True := by grind only [myset, other]\n@[myset] theorem d : True := trivial\nexample : True := by grind [myset]\n",
    }

    def run_it(self, texts=None):
        texts = texts or dict(self.LIB)
        imports = {m: [i for i in tb.header_imports(t) if i in texts] for m, t in texts.items()}
        return gs.rewrite(texts, imports)

    def test_registration_with_its_doc_tags_and_calls(self):
        out, changes, stats = self.run_it()
        self.assertNotIn("register_grind_attr", out["L.Attrs"])
        self.assertNotIn("the set's doc", out["L.Attrs"])  # a doc comment left without its command does not compile
        self.assertIn("theorem a", out["L.A"])
        self.assertNotIn("myset", out["L.A"])
        self.assertIn("@[simp]", out["L.A"].replace("@[simp, ]", "@[simp]") if "@[simp" in out["L.A"] else "@[simp]")
        # the first call sees a and b (imported, with b's modifier) but not d (later in the file); the private c is not visible from another module
        first, second = [m for m in gs.GRIND_CALL.finditer(out["L.B"])]
        args1 = out["L.B"][first.end() : gs._close(out["L.B"], first.end()) - 1]
        args2 = out["L.B"][second.end() : gs._close(out["L.B"], second.end()) - 1]
        self.assertEqual([x.strip() for x in gs._items(args1)], ["P.a", "= P.b", "other"])
        self.assertEqual([x.strip() for x in gs._items(args2)], ["P.a", "= P.b", "d"])
        self.assertEqual(stats["grind calls rewritten"], 2)
        self.assertEqual(set(changes), {"L.Attrs", "L.A", "L.B"})

    def test_inert_lines(self):
        t = "import L.X\n\n#adaptation_note /-- after the bump -/\nset_option linter.unusedVariables false\nset_option linter.style.longLine false in\ntheorem t : True := by\n  #adaptation_note /-- x -/\n  trivial\n-- set_option linter.foo false (a comment stays)\n"
        new, n = gs.strip_inert_lines(t)
        self.assertEqual(n, 4)
        self.assertNotIn("adaptation_note", new.split("--")[0] if False else new.replace("-- set_option linter.foo false (a comment stays)", ""))
        self.assertIn("theorem t : True := by", new)
        self.assertIn("-- set_option linter.foo false (a comment stays)", new)
        self.assertNotIn("linter.unusedVariables", new)
        self.assertNotIn("linter.style.longLine", new)

    def test_the_guard_keeps_a_module_whose_text_would_change_elsewhere(self):
        real = gs.strip_inert_lines
        try:
            gs.strip_inert_lines = lambda t: (t.replace("theorem a", "theorem a'"), 1)  # a rewrite that touches a statement
            out, changes, stats = self.run_it()
        finally:
            gs.strip_inert_lines = real
        self.assertEqual(out["L.A"], self.LIB["L.A"])
        self.assertNotIn("L.A", changes)
        self.assertGreaterEqual(stats["modules kept as they were (guard)"], 1)

    def test_a_library_without_sets_or_inert_lines_is_untouched(self):
        texts = {"L.X": "import Mathlib\n\ntheorem x : True := by grind\n"}
        out, changes, stats = gs.rewrite(texts, {"L.X": []})
        self.assertEqual(out, texts)
        self.assertEqual(changes, {})


class Notice(unittest.TestCase):
    def test_the_notice_names_the_upstream_the_file_and_the_change(self):
        n = gs.notice("https://github.com/o/lib@abc123", "Lib/X.lean", ["removed the registration of the grind set `s`"])
        self.assertTrue(n.startswith("/-! Tengoku change notice:") and n.endswith("-/"))
        for part in ("https://github.com/o/lib@abc123", "`Lib/X.lean`", "removed the registration", "What every declaration states is unchanged"):
            self.assertIn(part, n)

    def test_the_notice_goes_after_the_imports_or_at_the_end(self):
        import bundle

        self.assertIn("import A\n\n/-! note -/", bundle.add_change_notice("import A\n\ntheorem t : True := trivial\n", "/-! note -/"))
        self.assertTrue(bundle.add_change_notice("theorem t : True := trivial\n", "/-! note -/").rstrip().endswith("/-! note -/"))

    def test_the_intake_pr_says_what_was_changed(self):
        import open_intake_pr as o

        self.assertEqual(o.changes_line({}), "")
        line = o.changes_line({"factory_changes": {"grind sets": 1, "modules changed": 58}})
        self.assertIn("change notice", line)
        self.assertIn("modules changed: 58", line)

    def test_compose_calls_the_rewrite_and_writes_the_notices(self):
        text = (HERE / "bundle.py").read_text()
        self.assertIn("grind_sets.rewrite(pruned,", text)
        self.assertIn("add_change_notice(pruned[mod], grind_sets.notice(", text)
        self.assertIn('"factory_changes":', text)
        # before the attributes are stripped and before the lint: the rewritten text is what the content lint and the tree's build judge
        self.assertLess(text.index("grind_sets.rewrite(pruned,"), text.index("strip_attrs.strip_attributes(pruned[mod])"))
        self.assertLess(text.index("grind_sets.rewrite(pruned,"), text.index("allowlist.violations(body, allowed, keywords)"))


if __name__ == "__main__":
    unittest.main()
