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
        self.assertIn("@[simp] theorem b", out["L.A"])  # the other attribute of the list stays
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


class MoreCases(unittest.TestCase):
    def rw(self, texts):
        imports = {m: [i for i in tb.header_imports(t) if i in texts] for m, t in texts.items()}
        return gs.rewrite(texts, imports)

    def args(self, text, k=0):
        c = list(gs.GRIND_CALL.finditer(text))[k]
        return [x.strip() for x in gs._items(text[c.end() : gs._close(text, c.end()) - 1])]

    REG = "module\n\nregister_grind_attr s\n"

    def test_a_private_lemma_in_the_calls_own_module_keeps_its_short_name(self):
        out, _, _ = self.rw({"L.R": self.REG, "L.A": "import L.R\n\nnamespace N\n@[s] private theorem p : True := trivial\nexample : True := by grind [s]\nend N\n"})
        self.assertEqual(self.args(out["L.A"]), ["p"])

    def test_scoped_and_local_tags_count(self):
        out, _, _ = self.rw({"L.R": self.REG, "L.A": "import L.R\n\n@[local s] theorem a : True := trivial\nattribute [scoped s =] a\nexample : True := by grind [s]\n"})
        self.assertEqual(self.args(out["L.A"]), ["a", "= a"])
        self.assertNotIn("s]", out["L.A"].split("example")[0].replace("[s]", ""))

    def test_a_removed_lemma_is_not_listed(self):
        out, _, _ = self.rw({"L.R": self.REG, "L.A": "import L.R\n\n@[s] theorem a : True := trivial\n@[s] theorem b : True := trivial\nattribute [-s] a\nexample : True := by grind [s]\n"})
        self.assertEqual(self.args(out["L.A"]), ["b"])

    def test_an_emptied_attribute_list_or_command_goes_whole(self):
        out, _, _ = self.rw({"L.R": self.REG, "L.A": "import L.R\n\n@[s] theorem a : True := trivial\ntheorem b : True := trivial\nattribute [s] b\nexample : True := by grind [s]\n"})
        self.assertNotIn("@[]", out["L.A"])
        self.assertNotIn("attribute []", out["L.A"])
        self.assertNotIn("attribute [", out["L.A"])
        self.assertIn("theorem a : True := trivial", out["L.A"])

    def test_a_bracket_in_a_comment_inside_a_grind_list_is_not_one(self):
        out, _, _ = self.rw({"L.R": self.REG, "L.A": "import L.R\n\n@[s] theorem a : True := trivial\nexample : True := by grind [s, /- an unbalanced ] in a note -/ other]\n"})
        call = list(gs.GRIND_CALL.finditer(out["L.A"]))[0]
        self.assertEqual(out["L.A"][call.start() : gs._close(out["L.A"], call.end())], "grind [a, /- an unbalanced ] in a note -/ other]")

    def test_a_module_the_guard_keeps_adds_nothing_to_the_counts(self):
        real = gs.strip_inert_lines
        try:
            gs.strip_inert_lines = lambda t: ((t.replace("theorem a", "theorem a'"), 1) if "theorem a" in t else (t, 0))
            out, changes, stats = self.rw({"L.R": self.REG, "L.A": "import L.R\n\n@[s] theorem a : True := trivial\nexample : True := by grind [s]\n"})
        finally:
            gs.strip_inert_lines = real
        self.assertNotIn("L.A", changes)
        self.assertEqual(stats["grind calls rewritten"], 0)  # L.A's call was not shipped rewritten
        self.assertEqual(stats["set tags removed"], 0)
        self.assertEqual(stats["set registrations removed"], 1)  # L.R's change ships
        self.assertEqual(stats["modules kept as they were (guard)"], 1)


class Compose(unittest.TestCase):
    """bundle.py compose on the toy library of test_bundle, with an inert line in the module that ships: the shipped file carries its change notice and the report counts it."""

    def test_the_shipped_file_has_its_notice_and_the_report_its_counts(self):
        import subprocess
        import tempfile

        sys.path.insert(0, str(HERE / "tests"))
        import test_records as T

        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy").mkdir(parents=True)
        B = T.B.replace("namespace Toy\n", "set_option linter.unusedVariables false\n\nnamespace Toy\n", 1)
        (lib / "Toy" / "A.lean").write_text(T.A)
        (lib / "Toy" / "B.lean").write_text(B)
        la, lb = T.A.split("\n"), B.split("\n")
        ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
        sidecars = {"Toy/A": [["Toy.one", ln(la, "/-- the number one"), ln(la, "def one")], ["Toy.one_pos", ln(la, "theorem one_pos"), ln(la, "theorem one_pos")]],
                    "Toy/B": [["Toy.uses_one_pos", ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos")]]}
        for m, rows in sidecars.items():
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(rows))
        keep = [["Toy.B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one"]]
        (d / "deps.log").write_text(f"x:1:0: info: BUNDLE_KEEP {json.dumps(keep)} BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps({"Toy.B": ["Toy.uses_one_pos"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy", "commit": "abc123def456789"}))
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text("GATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n")
        (d / "killed.json").write_text("[]")
        subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--gate2-killed", str(d / "killed.json"), "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"),
                        "--meta", str(d / "setup.json"), "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"),
                        "--src", str(d / "src")], check=True, capture_output=True)
        b = (d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "B.lean").read_text()
        self.assertIn("Tengoku change notice", b)
        self.assertIn("https://github.com/o/toy@abc123def456", b)
        self.assertIn("`Toy/B.lean`", b)
        self.assertFalse(any(ln.strip().startswith("set_option linter") for ln in b.splitlines()))  # the line is gone (the notice names it)
        report = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertEqual(report["factory_changes"].get("inert lines removed"), 1)
        self.assertEqual(report["factory_changes"].get("modules changed"), 1)
        self.assertEqual(report["theorems"], 1)


class SpaceInAModuleName(unittest.TestCase):
    """uniform-sheafy-tate-domains, 2026-11-07: 4 of the 6 modules of its draft live under `Adic spaces/`; the verify build split `«Adic spaces».X` at the space
    (`unknown target ...«Adic`) and died before building anything, and the tree's merge queue builds the same space-separated list."""

    def test_compose_leaves_such_a_module_out_and_says_why(self):
        import subprocess
        import tempfile

        sys.path.insert(0, str(HERE / "tests"))
        import test_records as T

        d = Path(tempfile.mkdtemp())
        lib = d / "lib"
        (lib / "Toy" / "Sub dir").mkdir(parents=True)
        (lib / "Toy" / "A.lean").write_text(T.A)
        (lib / "Toy" / "Sub dir" / "B.lean").write_text(T.B)
        la, lb = T.A.split("\n"), T.B.split("\n")
        ln = lambda lines, needle: next(i + 1 for i, x in enumerate(lines) if needle in x)
        sidecars = {"Toy/A": [["Toy.one", ln(la, "/-- the number one"), ln(la, "def one")], ["Toy.one_pos", ln(la, "theorem one_pos"), ln(la, "theorem one_pos")]],
                    "Toy/Sub dir/B": [["Toy.uses_one_pos", ln(lb, "open Nat in"), ln(lb, "theorem uses_one_pos")]]}
        for m, rows in sidecars.items():
            f = lib / ".lake" / "build" / "lib" / "lean" / (m + ".olean.ranges.json")
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(rows))
        keep = [["Toy.«Sub dir».B", "Toy.uses_one_pos"], ["Toy.A", "Toy.one_pos"], ["Toy.A", "Toy.one"]]
        (d / "deps.log").write_text(f"x:1:0: info: BUNDLE_KEEP {json.dumps(keep)} BUNDLE_END\n")
        (d / "passed.json").write_text(json.dumps({"Toy.«Sub dir».B": ["Toy.uses_one_pos"]}))
        (d / "setup.json").write_text(json.dumps({"repo": "https://github.com/o/toy", "commit": "abc"}))
        (d / "build.log").write_text("")
        (d / "gate2.log").write_text("GATE2B_PASS old=Toy.uses_one_pos new=Toy.uses_one_pos via=equal\n")
        (d / "killed.json").write_text("[]")
        p = subprocess.run([sys.executable, str(HERE / "bundle.py"), "compose", "--gate2-killed", str(d / "killed.json"), "--lib", str(lib), "--log", str(d / "deps.log"), "--passed", str(d / "passed.json"),
                            "--meta", str(d / "setup.json"), "--key", "toy-lib", "--toolchain", "tc", "--errors", str(d / "build.log"), "--gate2", str(d / "gate2.log"), "--out", str(d / "bundle"),
                            "--src", str(d / "src")], capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr[-2000:])
        report = json.loads((d / "bundle-proposed" / "report.json").read_text())
        self.assertTrue(any("a module name with a space" in k for k in report["left_out"]), report["left_out"])
        self.assertFalse((d / "bundle-proposed" / "Tengoku" / "ToyLib" / "Toy" / "Sub dir" / "B.lean").exists())

    def test_the_verify_build_passes_one_argument_per_module(self):
        import yaml

        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "bump-sharded.yml").read_text())
        step = next(s["run"] for s in wf["jobs"]["verify"]["steps"] if s.get("name") == "Build them (the queue's own command)")
        self.assertIn("mapfile -t tg < <(grep -v '^[[:space:]]*$' ../out/targets.txt)", step)
        self.assertIn('lake build "${tg[@]}"', step)
        self.assertNotIn("lake build $targets", step)


ROOT = Path(__file__).resolve().parents[3]


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

    def test_a_part_report_keeps_the_changes(self):
        text = (HERE / "bundle_layers.py").read_text()
        self.assertIn('"factory_changes": report.get("factory_changes", {})', text)

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
