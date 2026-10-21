"""Class-level tests of tree_verify.py collect: what it may conclude from a build log, on random libraries and random logs.

Every test here states an INVARIANT that must hold for every library and every log, not an example; the examples that motivated them are named in the docstrings. The libraries are random import graphs
(seeded: a failure prints its seed and reproduces), the logs are random subsets of what Lake can print. See tests/CLASSES.md for the list of classes and where each is enforced.

  * EVIDENCE: a missing `Built` line is NOT evidence that a module did not build (Lake prints a line for a job that ran, not for every target; Navier 2026-10-20: 67 of 917 modules had none in a
    build that completed, and the 676 that import them were refused with them). What is evidence: an ending that says the build completed, or a module that imports it having built.
  * CLOSURE: whatever ships must import only what ships (a module whose import is refused is refused), whatever the log.
  * MONOTONE: more evidence never removes a verified module; less never adds one.
  * NEVER GOT GOING: a log in which nothing was built is not a partial build (Navier 2026-10-21: the toolchain did not download; 0 of 1,066 built; the run was a success with an empty cut).
  * SEGMENTS: what is appended to the log after the build of the bundle (the second build of tree_dups.py, the repair round) must not change what the first build proves.
"""

from __future__ import annotations

import json
import random
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import tree_repair as tr  # noqa: E402
import tree_verify as tv  # noqa: E402

SEEDS = range(120)


class Lib:
    """A random library `ToyLib` of n modules M0..M{n-1}; Mi imports a random subset of the modules before it. All of them are new (the tree has none)."""

    def __init__(self, seed: int):
        self.rnd = random.Random(seed)
        self.seed = seed
        n = self.rnd.randint(3, 14)
        self.mods = [f"M{i}" for i in range(n)]
        self.imports = {m: sorted(self.rnd.sample(self.mods[:i], self.rnd.randint(0, min(i, 3)))) for i, m in enumerate(self.mods)}
        self.d = Path(tempfile.mkdtemp())
        files = {"Tengoku/ToyLib.lean": "".join(f"import Tengoku.ToyLib.Toy.{m}\n" for m in self.mods), "Tengoku/ToyLib/Deps.lean": "-- ToyLib: a factory bundle\n"}
        for m in self.mods:
            files[f"Tengoku/ToyLib/Toy/{m}.lean"] = "".join(f"import Tengoku.ToyLib.Toy.{j}\n" for j in self.imports[m]) + f"\ntheorem t_{m} : 1 = 1 := rfl\n"
        for rel, text in files.items():
            p = self.d / "bundle" / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        (self.d / "tree").mkdir()
        tv.main(["apply", "--bundle", str(self.d / "bundle"), "--tree", str(self.d / "tree"), "--out", str(self.d / "out")])

    # -- the oracle: closures computed here, independently of tree_verify
    def importers(self, roots: set[str]) -> set[str]:
        out, todo = set(), list(roots)
        while todo:
            x = todo.pop()
            for m in self.mods:
                if x in self.imports[m] and m not in out:
                    out.add(m)
                    todo.append(m)
        return out

    def deps(self, roots: set[str]) -> set[str]:
        out, todo = set(), list(roots)
        while todo:
            for d in self.imports[todo.pop()]:
                if d not in out:
                    out.add(d)
                    todo.append(d)
        return out

    # -- a log
    def log(self, built: set[str], failing: set[str], ending: str | None) -> str:
        lines = [f"✔ [{i}/99] Built Tengoku.ToyLib.Toy.{m} (3.2s)" for i, m in enumerate(sorted(built), 1)]
        lines += [f"error: Tengoku/ToyLib/Toy/{f}.lean:1:0: unknown identifier" for f in sorted(failing)]
        if ending == "success":
            lines.append("Build completed successfully (99 jobs).")
        elif ending == "failures":
            lines += ["Some required targets logged failures:"] + [f"- Tengoku.ToyLib.Toy.{f}" for f in sorted(failing)] + ["error: build failed"]
        return "\n".join(lines) + "\n"

    def collect(self, log: str, partial: bool = False, name: str = "build.log") -> set[str]:
        """the modules `collect` verified (library names M0, M1, …)"""
        (self.d / name).write_text(log)
        out = self.d / f"out-{name}"
        tv.main(["collect", "--new", str(self.d / "out" / "new.json"), "--log", str(self.d / name), "--out", str(out), "--bundle", str(self.d / "bundle"), *(["--allow-unfinished"] if partial else [])])
        return {m.rsplit(".", 1)[1] for m in json.loads((out / "ok.json").read_text())}


def subset(rnd: random.Random, xs: list[str], p: float) -> set[str]:
    return {x for x in xs if rnd.random() < p}


class Evidence(unittest.TestCase):
    def test_a_build_that_completed_built_every_target_whatever_lines_lake_printed(self):
        """EVIDENCE. No failure, an ending that says the build completed: every module is verified, with any subset of `Built` lines (even none)."""
        for seed in SEEDS:
            lib = Lib(seed)
            for p in (0.0, 0.3, 0.7, 1.0):
                built = subset(lib.rnd, lib.mods, p)
                self.assertEqual(lib.collect(lib.log(built, set(), "success")), set(lib.mods), f"seed {seed}, {sorted(built)} printed")

    def test_a_failing_module_and_what_imports_it_are_never_verified_and_everything_else_that_has_evidence_is(self):
        """CLOSURE + EVIDENCE with failures: the build finished and listed its failures. A module outside the failures' cone is verified when it has a line or a module that imports it has one
        (Lake stops at the first failure, so a module with neither was perhaps never reached)."""
        for seed in SEEDS:
            lib = Lib(seed)
            failing = subset(lib.rnd, lib.mods, 0.2) or {lib.rnd.choice(lib.mods)}
            cone = failing | lib.importers(failing)
            built = subset(lib.rnd, lib.mods, 0.6) - cone
            got = lib.collect(lib.log(built, failing, "failures"))
            self.assertFalse(got & cone, f"seed {seed}: a refused module's cone was verified: {sorted(got & cone)}")
            evidence = built | lib.deps(built)
            self.assertEqual(got, set(lib.mods) - cone - (set(lib.mods) - cone - evidence), f"seed {seed}")

    def test_a_partial_build_verifies_only_what_it_has_evidence_for(self):
        """EVIDENCE for a build with no ending (--allow-unfinished): a line, or a module that imports it having built. Nothing else, and nothing that imports a failure."""
        for seed in SEEDS:
            lib = Lib(seed)
            built = subset(lib.rnd, lib.mods, 0.5)
            if not built:
                continue
            failing = subset(lib.rnd, lib.mods, 0.1) - built
            got = lib.collect(lib.log(built, failing, None), partial=True)
            cone = failing | lib.importers(failing)
            self.assertEqual(got, (built | lib.deps(built)) - cone, f"seed {seed}")

    def test_a_partial_build_that_built_nothing_never_got_going_and_is_refused(self):
        """NEVER GOT GOING. Whatever the (non-)ending says, no module built: nothing was tried, so nothing is cut."""
        for seed in SEEDS[:30]:
            lib = Lib(seed)
            for text in ("", "error: could not download file from 'https://releases.lean-lang.org/x'\ninfo: caused by: [35] SSL connect error\n", "lake exit status: 1\n"):
                with self.assertRaises(SystemExit, msg=f"seed {seed}"):
                    lib.collect(text, partial=True)


class Closure(unittest.TestCase):
    def test_what_ships_imports_only_what_ships(self):
        """CLOSURE, for every kind of log at once: no verified module imports a module that is not verified."""
        for seed in SEEDS:
            lib = Lib(seed)
            failing = subset(lib.rnd, lib.mods, 0.15)
            built = subset(lib.rnd, lib.mods, 0.5)
            for ending, partial in (("success" if not failing else "failures", False), (None, True)):
                if partial and not built:
                    continue
                got = lib.collect(lib.log(built, failing, ending), partial=partial)
                for m in got:
                    self.assertTrue(set(lib.imports[m]) <= got, f"seed {seed}, {ending}: {m} is verified and imports {sorted(set(lib.imports[m]) - got)}")
                self.assertFalse(got & failing, f"seed {seed}")

    def test_the_summary_counts_add_up(self):
        for seed in SEEDS[:40]:
            lib = Lib(seed)
            failing = subset(lib.rnd, lib.mods, 0.2)
            lib.collect(lib.log(set(lib.mods) - failing - lib.importers(failing), failing, "failures" if failing else "success"))
            line = (lib.d / "out-build.log" / "summary.txt").read_text().splitlines()[0]
            built, refused = int(line.split("built in the tree")[0].split(":")[1]), int(line.split("built in the tree, ")[1].split(" refused")[0])
            cascade = int(line.rsplit("), ", 1)[1].split(" more")[0])
            self.assertEqual(built + refused + cascade, len(lib.mods), f"seed {seed}: {line}")


class Monotone(unittest.TestCase):
    def test_more_evidence_never_removes_a_verified_module(self):
        """MONOTONE. Adding `Built` lines to a log (same failures, same ending) never shrinks the set; removing lines never grows it."""
        for seed in SEEDS:
            lib = Lib(seed)
            failing = subset(lib.rnd, lib.mods, 0.15)
            small = subset(lib.rnd, lib.mods, 0.3) - failing
            big = small | (subset(lib.rnd, lib.mods, 0.4) - failing)
            for ending, partial in (("failures" if failing else "success", False), (None, True)):
                if partial and not small:
                    continue
                a, b = lib.collect(lib.log(small, failing, ending), partial=partial), lib.collect(lib.log(big, failing, ending), partial=partial)
                self.assertLessEqual(a, b, f"seed {seed}, {ending}")


class Segments(unittest.TestCase):
    def test_the_second_build_appended_to_the_log_does_not_change_what_the_first_one_proves(self):
        """SEGMENTS. The second build (tree_dups.py) is appended after DUPS_MARKER: a success there must not complete a first build that was killed, and a failure there refuses the module it names
        but never un-verifies a module for lack of lines. (Navier 2026-10-20: the ending of the second build was taken for the ending of the first.)"""
        for seed in SEEDS:
            lib = Lib(seed)
            built = subset(lib.rnd, lib.mods, 0.5)
            if not built:
                continue
            first = lib.log(built, set(), None)  # killed: no ending
            second = lib.log(set(), set(), "success")  # only the ending: a `Built` line of the second build is evidence of its own (a module built on the tree's module), the ending is not about the first
            alone = lib.collect(first, partial=True)
            joined = lib.collect(first + tv.DUPS_MARKER + "\n" + second, partial=True, name="joined.log")
            self.assertEqual(alone, joined, f"seed {seed}: a success after the marker changed the verdict of an unfinished first build")
            self.assertIn("did not finish", (lib.d / "out-joined.log" / "summary.txt").read_text())

    def test_a_failure_in_the_second_build_refuses_that_module_and_its_importers_only(self):
        for seed in SEEDS:
            lib = Lib(seed)
            victim = lib.rnd.choice(lib.mods)
            first = lib.log(set(lib.mods), set(), "success")
            second = lib.log(set(), {victim}, "failures")
            got = lib.collect(first + tv.DUPS_MARKER + "\n" + second, name="seg.log")
            self.assertEqual(got, set(lib.mods) - {victim} - lib.importers({victim}), f"seed {seed}")

    def test_a_repaired_module_is_judged_on_the_round_after_the_marker(self):
        """A module repaired in a round is judged on that round (tree_repair MARKER): its failure in the first build is forgiven, one in the second is not."""
        for seed in SEEDS[:40]:
            lib = Lib(seed)
            x = lib.rnd.choice(lib.mods)
            spec = json.loads((lib.d / "out" / "new.json").read_text())
            spec["modules"][f"Tengoku.ToyLib.Toy.{x}"]["repaired"] = True
            (lib.d / "out" / "new.json").write_text(json.dumps(spec))
            first = lib.log(set(lib.mods) - {x} - lib.importers({x}), {x}, "failures")
            ok_round = lib.log({x} | lib.importers({x}), set(), "success")
            got = lib.collect(first + tr.MARKER + "\n" + ok_round, name="rep.log")
            self.assertEqual(got, set(lib.mods), f"seed {seed}: the repaired module and its importers built in the second round")
            bad_round = lib.log(lib.importers({x}), {x}, "failures")
            got = lib.collect(first + tr.MARKER + "\n" + bad_round, name="rep2.log")
            self.assertFalse(got & ({x} | lib.importers({x})), f"seed {seed}")


if __name__ == "__main__":
    unittest.main()
