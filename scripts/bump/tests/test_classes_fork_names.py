"""Class-level tests of the fork edit's handling of NAMES that live in two worlds: the fork's and the tree's.

THE CLASS (Navier recut 8, 2026-10-21: `Ambiguous term Coefficients`, 24 modules refused). A forked copy declares names the tree's module declares too (that is why it is forked). A wrapped file that
`open`s the namespace of such a name and has both modules in its import closure sees the name twice, as `<fork>.N.x` and as `N.x`, and Lean calls that ambiguous. In the library the tree's module did not exist,
so the fork's name is what the file means. The cure is to hide the tree's names where the file opens N (`open _root_.N hiding x`). Lean REFUSES `hiding` of a name that does not exist, so it may only be
done in a file whose import closure contains the tree's module. Three things must hold for every library, not for the one that was seen:

  VISIBILITY   after the edit, for every `open N` the file had: a name of `hide` under N is visible through the fork's N only; every other name is visible through both (the module's other names, in
               the tree's N and not declared by the fork, must still be found: the earlier fix for `Unknown identifier`).
  FRAME        the edit changes nothing but `open` lines, adds nothing but `open _root_` lines after a line, and leaves comments, docstrings, scoped/only/hiding/renaming forms and every other line alone.
  CLOSURE      a module gets hidden names exactly when a tree module that shares names with a forked copy is in its import closure (a naive search is the oracle), and then every name the copy shares
               with it; never a name that is not in both.
"""

from __future__ import annotations

import random
import re
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import tree_dups as td  # noqa: E402
import test_tree_dups  # noqa: E402  (the module: its test classes are not collected twice)

SEEDS = range(150)
NAMESPACES = ["A", "A.B", "C", "D.E.F", "«x y»", "Zz"]
FORK = "ToyFork"
TOK = r"(?:«[^»]*»|[^\s«])+"  # a name: a component in guillemets may have a space in it
ROOT_CHAIN = re.compile(r" in open (?:_root_\." + TOK + r" ?)+(?:hiding(?: (?!in\b)" + TOK + r")+)?(?= in\b)")


def gen_text(rnd: random.Random) -> tuple[str, list[str]]:
    """(a file, the kinds of its lines)"""
    lines, kinds = ["import Tengoku.Lib.Base", ""], ["import", "blank"]

    def add(ln: str, kind: str) -> None:
        lines.append(ln)
        kinds.append(kind)

    for _ in range(rnd.randint(3, 16)):
        ind = rnd.choice(["", "", "  "])
        names = " ".join(rnd.sample(NAMESPACES, rnd.randint(1, 3)))
        kind = rnd.choice(["open", "open", "open", "open_comment", "open_in", "open_in_eol", "scoped", "only", "hiding", "renaming", "comment", "doc", "namespace", "def"])
        if kind == "open":
            add(f"{ind}open {names}", "open")
        elif kind == "open_comment":
            add(f"{ind}open {names} -- {rnd.choice(['why', 'open A'])}", "open")
        elif kind == "open_in":
            add(f"{ind}open {names} in def f{len(lines)} : Nat := 1", "open")
        elif kind == "open_in_eol":
            add(f"{ind}open {names} in", "open")
            add(f"{ind}def g{len(lines)} : Nat := 2", "def")
        elif kind == "scoped":
            add(f"{ind}open scoped {names}", "scoped")
        elif kind == "only":
            add(f"{ind}open {rnd.choice(NAMESPACES)} (a b)", "other_open")
        elif kind == "hiding":
            add(f"{ind}open {rnd.choice(NAMESPACES)} hiding a", "other_open")
        elif kind == "renaming":
            add(f"{ind}open {rnd.choice(NAMESPACES)} renaming a → b", "other_open")
        elif kind == "comment":
            add(f"{ind}-- open {names}", "comment")
        elif kind == "doc":
            add("/-- the doc", "doc")
            add("open the door", "doc")
            add("-/", "doc")
            add("def d : Nat := 3", "def")
        elif kind == "namespace":
            add(f"namespace {rnd.choice(NAMESPACES)}", "namespace")
        else:
            add(f"def h{len(lines)} : Nat := 4", "def")
    return "\n".join(lines) + "\n", kinds


def gen_hide(rnd: random.Random) -> set[str]:
    out = set()
    for ns in NAMESPACES:
        for _ in range(rnd.choice([0, 0, 1, 2, 4])):
            out.add(f"{ns}.{rnd.choice(['x', 'y', 'Coef', 'Coef.mk', 'Coef.q', 'z1'])}")
    out |= {"A._private.Foo.0.z", "Zz.0"} if rnd.random() < 0.3 else set()  # names no `hiding` clause can write
    return out


def normalise(line: str) -> str:
    """an `open` line as the original wrote it: no `_root_` token and no chained `in open _root_…`"""
    line = ROOT_CHAIN.sub("", line)
    m = re.match(r"^([ \t]*open(?:[ \t]+scoped)?[ \t]+)(.*?)((?:[ \t]+in\b.*)|(?:[ \t]*--.*))?$", line)
    if not m:
        return line
    toks = [t for t in re.findall(TOK, m.group(2)) if not t.startswith("_root_.")]
    return m.group(1) + " ".join(toks) + (m.group(3) or "")


def commands(line: str) -> list[tuple[str, frozenset[str]]]:
    """the opens of an output line: (namespace as written, the names it hides), `open A B in open _root_.A hiding x in …` read left to right"""
    parts = re.split(r"[ \t]+in[ \t]+(?=open\b)", line.strip())
    out = []
    for part in parts:
        m = re.match(r"open(?:[ \t]+scoped)?[ \t]+(.*?)(?:[ \t]+in\b.*|[ \t]*--.*)?$", part)
        if not m:
            continue
        body = m.group(1)
        if " hiding " in f" {body} ":
            ns, hid = body.split(" hiding ", 1)
            out.append((ns.strip(), frozenset(re.findall(TOK, hid))))
        else:
            out.extend((t, frozenset()) for t in re.findall(TOK, body))
    return out


class OpenRewrite(unittest.TestCase):
    def edit(self, seed: int):
        rnd = random.Random(seed)
        text, kinds = gen_text(rnd)
        hide = gen_hide(rnd)
        out = td.apply_fork_text(text, FORK, hide)
        self.assertIsNotNone(out, f"seed {seed}")
        lines = text.split("\n")
        body = out.split("\n")
        at = body.index(f"namespace {FORK}") + 1
        return rnd, text, kinds, hide, lines, body[at:]

    def aligned(self, seed: int):
        """[(original line, kind, the output lines it became)]"""
        rnd, text, kinds, hide, lines, body = self.edit(seed)
        j, out = 0, []
        for i in range(1, len(lines) - 1):  # the import line stays above the namespace; the blank line after it is the first line of the body  # the last element of split is the empty string after the final newline
            ln, kind = lines[i], kinds[i]
            chunk = [body[j]]
            j += 1
            while j < len(body) and re.match(r"^[ \t]*open _root_\.", body[j]) and not re.match(r"^[ \t]*open _root_\.\S+ hiding", ln):
                chunk.append(body[j])
                j += 1
            out.append((ln, kind, chunk))
        self.assertEqual(j, len(body) - 1, f"seed {seed}: lines are left over in the output")  # the final empty element
        return hide, out

    def test_frame_nothing_but_open_lines_changes_and_only_root_opens_are_added(self):
        for seed in SEEDS:
            hide, chunks = self.aligned(seed)
            for ln, kind, chunk in chunks:
                if kind in ("open", "scoped"):
                    self.assertEqual(normalise(chunk[0]), ln, f"seed {seed}: {ln!r} -> {chunk!r}")
                    for extra in chunk[1:]:
                        self.assertRegex(extra, r"^[ \t]*open _root_\.", f"seed {seed}")
                elif kind == "namespace":
                    self.assertEqual(chunk[0], ln)
                    self.assertLessEqual(len(chunk), 2, f"seed {seed}: a namespace line gets one `open _root_…` line, not {chunk!r}")
                else:  # comments, docstrings, defs and the forms with a list (`(a b)`, hiding, renaming) are left as they were
                    self.assertEqual(chunk, [ln], f"seed {seed}: {ln!r} was changed ({kind})")

    def test_visibility_a_hidden_name_is_the_forks_and_everything_else_is_found_both_ways(self):
        for seed in SEEDS:
            hide, chunks = self.aligned(seed)
            valid = {h for h in hide if td.NAME_TOKEN.match(h)}
            for ln, kind, chunk in chunks:
                if kind != "open":
                    continue
                cmds = [c for part in chunk for c in commands(part)]
                for ns in re.findall(TOK, re.split(r"[ \t]+in\b|--", normalise(chunk[0]).split("open", 1)[1])[0]):
                    under = {h[len(ns) + 1:] for h in valid if h.startswith(ns + ".")}
                    fork_side = [c for c in cmds if c[0] == ns]
                    root_side = [c for c in cmds if c[0] == f"_root_.{ns}"]
                    self.assertTrue(fork_side, f"seed {seed}: `open {ns}` of the fork's namespace is gone from {chunk!r}")
                    self.assertFalse(any(h for _, h in fork_side), f"seed {seed}: the fork's own names are never hidden")
                    self.assertTrue(root_side, f"seed {seed}: `open {ns}` no longer opens the tree's namespace ({chunk!r})")
                    for name in under | {"other", "Coef.other"}:
                        visible = any(name not in h for _, h in root_side)
                        self.assertEqual(visible, name not in under, f"seed {seed}: {ns}.{name} through the tree's namespace in {chunk!r}")

    def test_without_hidden_names_the_edit_is_what_it_was(self):
        """the earlier behaviour is kept for every file that has nothing to hide: `open a b` -> `open a _root_.a b _root_.b`, on one line, tail untouched"""
        for seed in SEEDS:
            rnd = random.Random(seed)
            text, kinds = gen_text(rnd)
            out = td.apply_fork_text(text, FORK)
            self.assertEqual(out, td.apply_fork_text(text, FORK, ()))
            self.assertNotIn(" hiding _", out.replace(" hiding a", ""))
            for ln in out.split("\n"):
                self.assertNotRegex(ln, r"open _root_\.\S+ hiding", f"seed {seed}: nothing to hide, and a `hiding` clause was written")
            for ln in text.split("\n"):
                m = re.match(r"^([ \t]*)open[ \t]+([^()]*?)([ \t]+in\b.*)?$", ln)
                if m and "hiding" not in ln and "renaming" not in ln and not ln.lstrip().startswith(("open scoped", "--")) and "the door" not in ln and "-- " not in ln:
                    toks = re.findall(TOK, m.group(2))
                    want = f"{m.group(1)}open {' '.join(t + ' _root_.' + t for t in toks)}{m.group(3) or ''}"
                    self.assertIn(want, out.split("\n"), f"seed {seed}: {ln!r}")

    def test_a_name_no_hiding_clause_can_write_is_not_written(self):
        out = td.apply_fork_text("import X\nopen A\n", FORK, {"A._private.Foo.0.z", "A.0", "A.ok"})
        self.assertIn("open _root_.A hiding ok", out)
        self.assertNotIn("_private", out)
        self.assertNotIn("hiding ok 0", out)
        self.assertNotIn("0\n", out.replace("ok\n", ""))


def make_tree(root: Path, files: dict[str, list[str]]) -> None:
    for m, imps in files.items():
        f = root / (m.replace(".", "/") + ".lean")
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text("".join(f"import {i}\n" for i in imps) + "\ndef x := 1\n")


class ForkHide(unittest.TestCase):
    def test_a_module_gets_the_shared_names_of_exactly_the_partners_in_its_closure(self):
        for seed in range(80):
            rnd = random.Random(seed)
            n = rnd.randint(4, 14)
            mods = [f"Tengoku.T.M{i}" for i in range(n)]
            imports = {m: rnd.sample(mods[:i], rnd.randint(0, min(i, 3))) for i, m in enumerate(mods)}  # acyclic: a module imports earlier ones
            imports.update({"Tengoku.T.Leaf": []})
            for m in list(imports):
                imports[m] = [*imports[m], *(["Lean.Meta"] if rnd.random() < 0.3 else [])]  # a module with no source file in the checkout is a leaf
            partners = rnd.sample(mods, rnd.randint(1, min(3, n)))
            names = {p: {f"N.{rnd.choice('abcd')}{rnd.randint(0, 3)}" for _ in range(rnd.randint(1, 4))} for p in partners}
            copies = {"C1": set().union(*(set(rnd.sample(sorted(names[p]), rnd.randint(0, len(names[p])))) | {"N.only_copy"} for p in partners[:2])),
                      "C2": {f"N.{rnd.choice('abcd')}{rnd.randint(0, 3)}" for _ in range(3)}}
            partner_of = {"C1": partners[:2], "C2": partners[1:]}
            wrap = set(rnd.sample(mods, rnd.randint(1, n)))
            tmp = Path(tempfile.mkdtemp())
            make_tree(tmp, imports)
            got = td.fork_hide(copies, partner_of, names, wrap, tmp)

            def closure(m: str) -> set[str]:
                seen, todo = set(), [m]
                while todo:
                    x = todo.pop()
                    if x not in seen:
                        seen.add(x)
                        todo.extend(imports.get(x, []))
                return seen

            shared: dict[str, set[str]] = {}
            for c, ps in partner_of.items():
                for p in ps:
                    shared.setdefault(p, set()).update(copies[c] & names.get(p, set()))
            for w in sorted(wrap):
                want = {name for p in closure(w) & set(partners) for name in shared.get(p, set())}
                self.assertEqual(set(got.get(w, [])), want, f"seed {seed}: {w}")
                for name in got.get(w, []):
                    self.assertTrue(any(name in copies[c] for c in copies) and any(name in names[p] for p in names), f"seed {seed}: {name} is not in both")
            self.assertEqual(set(got) - wrap, set(), f"seed {seed}: a module that is not wrapped was given names")

    def test_an_import_cycle_does_not_loop(self):
        tmp = Path(tempfile.mkdtemp())
        make_tree(tmp, {"Tengoku.T.A": ["Tengoku.T.B"], "Tengoku.T.B": ["Tengoku.T.A", "Tengoku.T.P"], "Tengoku.T.P": []})
        got = td.fork_hide({"C": {"N.x"}}, {"C": ["Tengoku.T.P"]}, {"Tengoku.T.P": {"N.x"}}, {"Tengoku.T.A"}, tmp)
        self.assertEqual(got, {"Tengoku.T.A": ["N.x"]})

    def test_order_of_the_modules_does_not_change_the_answer(self):
        tmp = Path(tempfile.mkdtemp())
        make_tree(tmp, {"Tengoku.T.A": ["Tengoku.T.B"], "Tengoku.T.B": ["Tengoku.T.P"], "Tengoku.T.C": ["Tengoku.T.B"], "Tengoku.T.P": []})
        wrap = {"Tengoku.T.A", "Tengoku.T.B", "Tengoku.T.C"}
        a = td.fork_hide({"C": {"N.x"}}, {"C": ["Tengoku.T.P"]}, {"Tengoku.T.P": {"N.x"}}, wrap, tmp)
        self.assertEqual(sorted(a), sorted(wrap))
        self.assertEqual(a, td.fork_hide({"C": {"N.x"}}, {"C": ["Tengoku.T.P"]}, {"Tengoku.T.P": {"N.x"}}, set(reversed(sorted(wrap))), tmp))

    def test_nothing_shared_is_nothing_hidden(self):
        tmp = Path(tempfile.mkdtemp())
        make_tree(tmp, {"Tengoku.T.A": ["Tengoku.T.P"], "Tengoku.T.P": []})
        self.assertEqual(td.fork_hide({"C": {"N.x"}}, {"C": ["Tengoku.T.P"]}, {"Tengoku.T.P": {"N.y"}}, {"Tengoku.T.A"}, tmp), {})


class PlanMergeCompose(test_tree_dups.FlowBase):
    """The names travel: plan decides them on the checkout, merge carries them, compose makes the same bytes."""

    FILES = {
        "Tengoku/ToyLib/Toy/M.lean": "import Tengoku\n\nnamespace Toy\ndef f := 1\nend Toy\n",
        "Tengoku/ToyLib/Toy/B.lean": "import Tengoku\nimport Tengoku.ToyLib.Toy.M\nimport Tengoku.Other.Lib.X\n\nopen Toy\ntheorem t : f = 1 := rfl\n",
        "Tengoku/ToyLib/Toy/C.lean": "import Tengoku.ToyLib.Toy.B\n\nopen Toy\ntheorem u : 1 = 1 := rfl\n",
        "Tengoku/ToyLib/Toy/E.lean": "import Tengoku.ToyLib.Toy.M\n\nopen Toy\ntheorem w : f = 1 := rfl\n",
        "Tengoku/ToyLib/Toy/U.lean": "import Tengoku\n\ntheorem v : 2 = 2 := rfl\n",
        "Tengoku/ToyLib.lean": "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in "MBCEU"),
        "Tengoku/ToyLib/Deps.lean": "-- ToyLib\n",
    }
    BUILT = "".join(f"✔ [{i}/5] Built Tengoku.ToyLib.Toy.{m} (1s)\n" for i, m in enumerate("MBCEU", 1)) + "Build completed successfully.\n"

    def setUp(self):
        super().setUp()
        write = test_tree_dups.write
        write(self.tree, {"Tengoku/Other/Lib/X.lean": "namespace Toy\ndef f := 2\nend Toy\n"})
        self.original = {m: (self.tree / f"Tengoku/ToyLib/Toy/{m}.lean").read_text() for m in "BCE"}
        rows = {"Tengoku.ToyLib.Toy.M": {"Toy.f": ("def", 99)}, "Tengoku.ToyLib.Toy.B": {"Toy.t": ("theorem", 10)}, "Tengoku.ToyLib.Toy.C": {"Toy.u": ("theorem", 11)}, "Tengoku.ToyLib.Toy.E": {"Toy.w": ("theorem", 12)}}
        self.plan(before=test_tree_dups.fp(rows), fork=True)

    def test_plan_hides_the_trees_name_where_the_trees_module_is_imported_and_only_there(self):
        dups = json.loads((self.out / "dups.json").read_text())
        self.assertEqual(dups["fork_hide"], {"Toy.B": ["Toy.f"], "Toy.C": ["Toy.f"]})  # C reaches X through B; E imports M only
        text = lambda m: (self.tree / f"Tengoku/ToyLib/Toy/{m}.lean").read_text()  # noqa: E731
        self.assertIn("open Toy\nopen _root_.Toy hiding f\n", text("B"))
        self.assertIn("open Toy\nopen _root_.Toy hiding f\n", text("C"))
        self.assertIn("open Toy _root_.Toy\n", text("E"))
        self.assertNotIn("hiding", text("E"))

    def test_merge_carries_them_and_compose_makes_the_same_bytes(self):
        td.main(["merge", "--out", str(self.d / "merged.json"), str(self.out / "dups.json")])
        got = td.load_fork_hide_for_compose(str(self.d / "merged.json"))
        self.assertEqual(got, {"proposed": {"Toy.B": ["Toy.f"], "Toy.C": ["Toy.f"]}})
        for m in "BCE":
            built = (self.tree / f"Tengoku/ToyLib/Toy/{m}.lean").read_text()
            self.assertEqual(td.apply_fork_text(self.original[m], "ToyLibFork", got["proposed"].get(f"Toy.{m}", ())), built, f"{m}: compose must make the bytes the tree built")

    def test_a_merged_file_from_before_this_existed_hides_nothing(self):
        (self.d / "old.json").write_text(json.dumps({"ns": "ToyLib", "modes": {"proposed": {"aliases": {}, "not_same": {}, "refused": {}}}}))
        self.assertEqual(td.load_fork_hide_for_compose(str(self.d / "old.json")), {"proposed": {}})

    def test_a_malformed_list_is_an_error_not_an_empty_answer(self):
        (self.d / "bad.json").write_text(json.dumps({"modes": {"proposed": {"aliases": {}, "fork_hide": {"Toy.B": "f"}}}}))
        with self.assertRaises(SystemExit):
            td.load_fork_hide_for_compose(str(self.d / "bad.json"))


import json  # noqa: E402

if __name__ == "__main__":
    unittest.main()
