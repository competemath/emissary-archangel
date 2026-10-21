"""Class-level tests of `lean_names.names`: the names a module declares, read from its text, whatever scope constructs it uses.

THE CLASS (Navier recut 10, 2026-10-21). The reader tracks `namespace` / `section` / `end`. A section opener it does not know (`public section`, `@[expose] public section`, `meta section`: 4,049 of
lean-pool's 4,131 files) is a scope that the `end` below it pops all the same, so the names that follow lose a namespace, or gain one they do not have. The tree's name list was wrong for every such file;
a forked copy (`namespace LeanPoolFork`, left open to the end of the file) was read as if it had no fork, the library's own modules that were already in the tree were called clashes with it, and
12,707 theorems went with them. The invariants hold for every file, so an opener nobody has thought of breaks a test here, not a recut:

  ORACLE        for a random file made of nested namespaces and sections (every opener form, named and unnamed `end`s, scopes left open at the end), the names are exactly the ones the structure gives.
  OPENER FORM   changing the form of every section opener changes no name.
  PROSE         a comment, a docstring or a string that looks like a scope or a declaration changes no name.
  FORK          a file wrapped by `apply_fork_text` declares exactly the names it did, under the fork's namespace (and the names written with `_root_` stay where they are).
"""

from __future__ import annotations

import random
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import lean_names  # noqa: E402
import tree_dups as td  # noqa: E402

SEEDS = range(300)
OPENERS = ["section", "section Sec{n}", "noncomputable section", "public section", "@[expose] public section", "@[expose] public noncomputable section", "meta section", "private section",
           "@[expose]   public   section", "noncomputable section Sec{n}"]
KINDS = ["theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "noncomputable def", "protected theorem", "@[simp] theorem"]
PROSE = ["-- namespace Fake", "-- end", "-- theorem faketheorem : True := trivial", "/- namespace Fake2\ntheorem fake2 : True := trivial\nend -/",
         "/-- docstring: section Fake3\nend Fake3 -/", 'example : String := "end namespace theorem fake4"']


class Gen:
    def __init__(self, rnd: random.Random, opener: str | None = None, prose: bool = True):
        self.rnd, self.opener, self.prose = rnd, opener, prose
        self.lines: list[str] = []
        self.out: set[str] = set()
        self.n = 0

    def fresh(self, base: str) -> str:
        self.n += 1
        return f"{base}{self.n}"

    def opener_line(self) -> str:
        form = self.opener or self.rnd.choice(OPENERS)
        return form.replace("{n}", str(self.n))

    def decl(self, prefix: list[str]) -> None:
        r = self.rnd
        name = self.fresh("d")
        kind = r.choice(KINDS)
        k = r.random()
        if k < 0.1:
            self.lines.append(f"{kind} _root_.Abs.{name} : True := trivial" if "theorem" in kind else f"{kind} _root_.Abs.{name} : Nat := 1")
            self.out.add(f"Abs.{name}")
            return
        if k < 0.2 and kind.split()[-1] not in ("instance",):
            self.lines.append(f"private {kind} {name} : True := trivial" if "theorem" in kind else f"private {kind} {name} : Nat := 1")
            return  # a private declaration is not a name of the tree
        if kind.endswith("instance"):
            self.lines.append(f"instance {name} : Inhabited Nat := ⟨0⟩")
        elif "theorem" in kind or kind.endswith("lemma"):
            self.lines.append(f"{kind} {name} : True := trivial")
        else:
            self.lines.append(f"{kind} {name} : Nat := 1" if kind.split()[-1] in ("def", "abbrev") else f"{kind} {name} where")
            if kind in ("structure",):
                self.lines.append("  x : Nat")
            if kind in ("inductive",):
                self.lines[-1] = f"inductive {name} where"
                self.lines.append("  | a")
        self.out.add(".".join([*prefix, name]))

    def block(self, prefix: list[str], depth: int, outermost: bool = False) -> None:
        r = self.rnd
        for _ in range(r.randint(1, 4)):
            c = r.random()
            if self.prose and r.random() < 0.15:
                self.lines.append(r.choice(PROSE))
            if c < 0.4 or depth >= 3:
                self.decl(prefix)
            elif c < 0.7:
                ns = ".".join(self.fresh("N") for _ in range(r.randint(1, 2)))
                self.lines.append(f"namespace {ns}")
                self.block([*prefix, ns], depth + 1)
                self.lines.append(r.choice([f"end {ns}", "end"]))
            else:
                op = self.opener_line()
                self.lines.append(op)
                self.block(prefix, depth + 1)
                named = re.search(r"Sec\d+$", op)
                self.lines.append(f"end {named.group(0)}" if named and r.random() < 0.7 else "end")

    def build(self) -> tuple[str, set[str]]:
        r = self.rnd
        self.lines.append("import Mathlib")
        self.lines.append("")
        # a scope left open at the end of the file, like the fork's `namespace` and 4,049 of lean-pool's `public section`
        prefix: list[str] = []
        if r.random() < 0.5:
            ns = self.fresh("Top")
            self.lines.append(f"namespace {ns}")
            prefix = [ns]
        if r.random() < 0.5:
            self.lines.append(self.opener_line())
        self.block(prefix, 0, outermost=True)
        return "\n".join(self.lines) + "\n", self.out


class Oracle(unittest.TestCase):
    def test_names_are_exactly_the_ones_the_structure_gives(self):
        for seed in SEEDS:
            text, want = Gen(random.Random(seed)).build()
            got = lean_names.names(text)
            self.assertEqual(got, want, f"seed {seed}: only read {sorted(got - want)[:4]}, missed {sorted(want - got)[:4]}\n{text}")

    def test_the_form_of_a_section_opener_changes_no_name(self):
        """the same random file, every opener written one way: `section` and each module-system form give the same names"""
        for seed in range(80):
            base = lean_names.names(Gen(random.Random(seed), opener="section").build()[0])
            for form in OPENERS:
                if "{n}" in form:
                    continue
                text, want = Gen(random.Random(seed), opener=form).build()
                self.assertEqual(lean_names.names(text), base, f"seed {seed}, opener {form!r}")

    def test_prose_that_looks_like_code_changes_no_name(self):
        for seed in range(80):
            with_prose, want = Gen(random.Random(seed), prose=True).build()
            self.assertEqual(lean_names.names(with_prose), want, f"seed {seed}")


class ForkedFile(unittest.TestCase):
    def test_a_wrapped_file_declares_what_it_did_under_the_forks_namespace(self):
        """tree_names reads every file of the tree, forked copies included: `namespace Fork` at the top (left open) must put its prefix on every name, module-system section or not"""
        for seed in SEEDS:
            text, want = Gen(random.Random(seed), prose=False).build()
            wrapped = td.apply_fork_text(text, "ToyFork")
            self.assertIsNotNone(wrapped)
            got = lean_names.names(wrapped)
            expected = {n if n.startswith("Abs.") else f"ToyFork.{n}" for n in want}  # a `_root_` name stays where it is
            self.assertEqual(got, expected, f"seed {seed}\n{wrapped}")

    def test_the_lean_pool_shape(self):
        """the file that cost 12,707 theorems: a fork namespace, then two `@[expose] public section` blocks, each with its own namespace closed by name"""
        text = ("module\n\nimport X\n\nnamespace LeanPoolFork\n\n@[expose] public section\n\nnamespace NavierStokes.RadialAlias\ndef a : Nat := 1\nend NavierStokes.RadialAlias\n\n"
                "@[expose] public section\n\nnamespace NavierStokes.TransportPrimitive\nnoncomputable def compactIntegral : Nat := 1\ntheorem compactIntegral_add : True := trivial\nend NavierStokes.TransportPrimitive\n")
        want = {"LeanPoolFork.NavierStokes.RadialAlias.a", "LeanPoolFork.NavierStokes.TransportPrimitive.compactIntegral", "LeanPoolFork.NavierStokes.TransportPrimitive.compactIntegral_add"}
        self.assertEqual(lean_names.names(text), want)
        # the same with the sections closed by a bare `end` before the next one opens, which is what pops a namespace when the opener is not understood
        closed = text.replace("end NavierStokes.RadialAlias\n", "end NavierStokes.RadialAlias\nend\n")
        self.assertEqual(lean_names.names(closed), want)


if __name__ == "__main__":
    unittest.main()
