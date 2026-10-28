"""propose_cut.py: the merge queue's rejection of a bundle -> the `drop=` of its recut, without a person.

Two kinds of test, as everywhere in this directory (see CLASSES.md):

  * SHAPES: the files and log lines of a real rejection (the shapes of test_explain_ejection.py: the factory's shard artifacts, the shipped files, the queue's `error:` lines), one
    example per class A/B/C/E/D, the cascade, a shared cause, and what must NOT reach a workflow (a hostile log line, a module name that cannot be passed on).
  * INVARIANTS on random libraries (seeded: a failure prints its seed): random import DAGs, random modules failing in random ways, random noise, against an oracle written here from the
    specification and not from the code (closures by a plain DFS over the generator's own import lists, the cut by index order).
      CLOSED       no kept module imports a cut one; the cut is exactly what bundle_cut.cut_dir removes when it is given the proposal's drop;
      MINIMAL      a proposed module has an error of its own; a module whose only errors name a declaration of a cut module it imports is NOT proposed (it is in `cascade`);
      MONOTONE     a longer log (more errors, the same build) never un-drops a module;
      NOT ALL      a cut that would remove the whole library is refused, with the errors in the residual and a nonzero status;
      DETERMINISTIC  the same bytes whatever the order of the log's lines, and run twice.
    Each invariant is also checked against MUTANTS (the code broken the way a bug would break it): the same checks must fail on every one.
"""

from __future__ import annotations

import contextlib
import io
import json
import random
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import bundle_cut as bc  # noqa: E402
import explain_ejection as ex  # noqa: E402
import propose_cut as pc  # noqa: E402

SEEDS = range(150)
TS = "2026-10-28T10:00:00.0Z"

# ---------------------------------------------------------------- the shapes of a real rejection (copied from test_explain_ejection.py)
SRC_A = "import Mathlib\n\ntheorem bad_one : True := by\n  apply Finset.prod_le_prod₀\n\ntheorem good_one : True := trivial\n"
SRC_B = "import Mathlib\n\nlemma helper_thing : True := trivial\n\ntheorem user_one : True := by\n  simp only [helper_thing]\n"
SRC_C = "import Mathlib\n\n@[instance_reducible]\ndef bial : Nat := 1\n\ntheorem uses_bial : True := by\n  rw [bial]\n"


def write(root: Path, rel: str, text: str) -> None:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


def err(rel: str, line: int, msg: str, col: int = 2, ns: str = "Ns") -> str:
    return f"{TS} error: Tengoku/{ns}/{rel}:{line}:{col}: {msg}\n"


def shapes() -> tuple[Path, Path]:
    """(shards, shipped): A fails in the factory too and shipped; B lost helper_thing to the pruning; C lost an attribute; D is fine; E imports B; F imports C; G imports nothing."""
    shards, shipped = Path(tempfile.mkdtemp()), Path(tempfile.mkdtemp())
    sp = shards / "shard-lib-0" / "shard-pack"
    for rel, text in (("Lib/A.lean", SRC_A), ("Lib/B.lean", SRC_B), ("Lib/C.lean", SRC_C), ("Lib/D.lean", "import Mathlib\n\ntheorem d_one : 1 = 1 := rfl\n")):
        write(sp / "src", rel, text)
    (sp / "errors.log").write_text("error: Lib/A.lean:4:8: Unknown constant `Finset.prod_le_prod₀`\n")
    write(shipped, "Tengoku/Ns/Lib/A.lean", "import Tengoku\n\ntheorem bad_one : True := by\n  apply Finset.prod_le_prod₀\n")
    write(shipped, "Tengoku/Ns/Lib/B.lean", "import Tengoku\n\ntheorem user_one : True := by\n  simp only [helper_thing]\n")
    write(shipped, "Tengoku/Ns/Lib/C.lean", "import Tengoku\n\ndef bial : Nat := 1\n\ntheorem uses_bial : True := by\n  rw [bial]\n")
    write(shipped, "Tengoku/Ns/Lib/D.lean", "import Tengoku\n\ntheorem d_one : 1 = 1 := rfl\n")
    write(shipped, "Tengoku/Ns/Lib/E.lean", "import Tengoku\nimport Tengoku.Ns.Lib.B\n\ntheorem e_one : True := by\n  exact user_one\n")
    write(shipped, "Tengoku/Ns/Lib/F.lean", "import Tengoku\nimport Tengoku.Ns.Lib.C\n\ntheorem f_one : True := by\n  exact uses_bial\n")
    write(shipped, "Tengoku/Ns/Lib/G.lean", "import Tengoku\n\ntheorem g_one : 2 = 2 := rfl\n")
    write(shipped, "Tengoku/Ns/Deps.lean", "-- Ns: a factory bundle\n")
    write(shipped, "Tengoku/Ns.lean", "".join(f"import Tengoku.Ns.Lib.{m}\n" for m in "ABCDEFG"))
    return shards, shipped


def propose(log: str, shipped: Path, shards: Path | None, **kw) -> dict:
    return pc.propose(log, ex.Shipped(shipped), ex.Factory(shards), **kw)


class Shapes(unittest.TestCase):
    def test_A_B_C_are_dropped_with_their_importers_and_each_says_why(self):
        shards, shipped = shapes()
        log = err("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`") + err("Lib/B.lean", 4, "Unknown identifier `helper_thing`") + err("Lib/C.lean", 6, "Tactic `rewrite` failed: Did not find an occurrence")
        p = propose(log, shipped, shards)
        self.assertEqual(p["drop"], ["Lib.A", "Lib.B", "Lib.C"])
        self.assertEqual(p["cut"], ["Lib.A", "Lib.B", "Lib.C", "Lib.E", "Lib.F"])
        self.assertEqual(p["keep"], ["Lib.D", "Lib.G"])
        self.assertEqual(p["cascade"], {"Lib.A": [], "Lib.B": ["Lib.E"], "Lib.C": ["Lib.F"]})
        self.assertEqual({r: v[0] for r, v in p["reasons"].items()}, {"Lib.A": "A", "Lib.B": "B", "Lib.C": "C"})
        self.assertIn("instance_reducible x1", p["reasons"]["Lib.C"])
        self.assertIn("error: Tengoku/Ns/Lib/B.lean:4:2: Unknown identifier `helper_thing`", p["reasons"]["Lib.B"])  # the evidence is the log line
        self.assertEqual((p["residual"], p["auto"], p["refused"]), ([], True, None))

    def test_E_a_name_the_trees_mathlib_lacks(self):
        shards, shipped = shapes()
        p = propose(err("Lib/D.lean", 3, "Unknown constant `Finset.zzz_missing_name`"), shipped, shards)
        self.assertEqual((p["drop"], p["reasons"]["Lib.D"][0], p["auto"]), (["Lib.D"], "E", True))

    def test_D_is_left_to_a_person_unless_asked(self):
        shards, shipped = shapes()
        log = err("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`") + err("Lib/G.lean", 3, "failed to synthesize instance")
        p = propose(log, shipped, shards)
        self.assertEqual(p["drop"], ["Lib.A"])
        self.assertEqual([(r["module"], r["class"], r["line"]) for r in p["residual"]], [("Lib.G", "D", 3)])
        self.assertFalse(p["auto"])  # a proposal with a residual starts no recut
        q = propose(log, shipped, shards, drop_unexplained=True)
        self.assertEqual((q["drop"], q["residual"], q["auto"]), (["Lib.A", "Lib.G"], [], True))
        self.assertTrue(q["reasons"]["Lib.G"].startswith("D:"))

    def test_a_module_that_fails_only_because_an_import_is_cut_is_not_proposed(self):
        shards, shipped = shapes()
        # E imports B; B lost helper_thing; E's error names user_one, a declaration of B: the cascade of B's cut
        log = err("Lib/B.lean", 4, "Unknown identifier `helper_thing`") + err("Lib/E.lean", 5, "Unknown identifier `user_one`")
        for flag in (False, True):
            p = propose(log, shipped, shards, drop_unexplained=flag)
            self.assertEqual((p["drop"], p["cut"], p["residual"]), (["Lib.B"], ["Lib.B", "Lib.E"], []), flag)
        # the same error where B is not cut: E's own (user_one is there, B fine, E's error is a plain D)
        q = propose(err("Lib/E.lean", 5, "Unknown identifier `user_one`"), shipped, shards)
        self.assertEqual((q["drop"], [r["module"] for r in q["residual"]]), ([], ["Lib.E"]))

    def test_the_cascade_may_also_be_a_namespace_or_a_missing_object_file(self):
        shards, shipped = shapes()
        write(shipped, "Tengoku/Ns/Lib/H.lean", "import Tengoku\nimport Tengoku.Ns.Lib.A\n\ntheorem h : True := trivial\n")
        base = err("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`")
        for msg in ("unknown namespace `bad_one`", "object file '/x/.lake/build/lib/lean/Tengoku/Ns/Lib/A.olean' of module Tengoku.Ns.Lib.A does not exist"):
            p = propose(base + err("Lib/H.lean", 1, msg), shipped, shards, drop_unexplained=True)
            self.assertEqual((p["drop"], p["cut"]), (["Lib.A"], ["Lib.A", "Lib.H"]), msg)

    def test_one_cause_for_several_modules_is_said_once(self):
        shards, shipped = shapes()
        write(shipped, "Tengoku/Ns/Lib/H.lean", "import Tengoku\n\ntheorem h : True := Nat.zzz_gone\n")
        log = err("Lib/D.lean", 3, "Unknown constant `Nat.zzz_gone`") + err("Lib/H.lean", 3, "Unknown constant `Nat.zzz_gone`") + err("Lib/G.lean", 3, "Unknown constant `Nat.other_gone`")
        p = propose(log, shipped, shards)
        self.assertEqual(p["shared_causes"], [{"class": "E", "cause": "`Nat.zzz_gone` is unknown", "modules": ["Lib.D", "Lib.H"]}])

    def test_without_the_shards_a_name_is_still_dropped_and_the_rest_is_not_guessed(self):
        _, shipped = shapes()
        log = err("Lib/D.lean", 3, "Unknown constant `Finset.zzz_missing_name`") + err("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`") + err("Lib/G.lean", 3, "failed to synthesize instance")
        p = propose(log, shipped, None)
        self.assertEqual(p["drop"], ["Lib.A", "Lib.D"])  # both are names declared nowhere in the SHIPPED files; B and E cannot be told
        self.assertIn("no shard artifacts", p["reasons"]["Lib.D"])
        self.assertEqual([r["module"] for r in p["residual"]], ["Lib.G"])
        self.assertFalse(p["stats"]["factory"])

    def test_an_error_outside_the_bundle_and_a_target_without_an_error_line_are_the_residual(self):
        shards, shipped = shapes()
        log = err("Lib/A.lean", 4, "Unknown constant `Finset.prod_le_prod₀`") + err("Seed/Core.lean", 9, "boom", ns="Other") + err("Lib/Nope.lean", 1, "boom")
        log += "Some required targets logged failures:\n- Tengoku.Ns.Lib.G\n- Tengoku.Ns.Lib.A\n- Tengoku.All\n"
        p = propose(log, shipped, shards)
        self.assertEqual(sorted((r["module"] or r["file"]) for r in p["residual"]), ["Lib.G", "Tengoku/Ns/Lib/Nope.lean", "Tengoku/Other/Seed/Core.lean"])
        self.assertFalse(p["auto"])
        q = propose(log, shipped, shards, drop_unexplained=True)
        self.assertEqual(q["drop"], ["Lib.A", "Lib.G"])  # G: listed as failed, no error line: unexplained
        self.assertEqual(len(q["residual"]), 2)  # the two files that are not modules of this bundle remain a person's

    def test_prior_drop_is_listed_again_in_the_recut_list_and_is_not_proposed_twice(self):
        shards, shipped = shapes()
        p = propose(err("Lib/D.lean", 3, "Unknown constant `Finset.zzz_missing_name`"), shipped, shards, prior_drop={"Old.Thing", "Lib.D"})
        self.assertEqual((p["drop"], p["recut_drop"]), (["Lib.D"], ["Lib.D", "Old.Thing"]))

    def test_a_tar_of_the_bundle_and_its_directory_give_one_proposal(self):
        shards, shipped = shapes()
        tar = Path(tempfile.mkdtemp()) / "bundle.tar"
        with tarfile.open(tar, "w") as t:
            for f in sorted(shipped.rglob("*.lean")):
                t.add(f, arcname="./" + str(f.relative_to(shipped)))
        log = err("Lib/B.lean", 4, "Unknown identifier `helper_thing`") + err("Lib/G.lean", 3, "failed to synthesize instance")
        self.assertEqual(propose(log, tar, shards), propose(log, shipped, shards))

    def test_a_hostile_log_line_cannot_reach_a_workflow_command_or_a_drop_list(self):
        shards, shipped = shapes()
        evil = "Unknown constant `Finset.zzz`\x1b[31m ::set-output name=x::y\n::error::fake ```"
        p = propose(err("Lib/D.lean", 3, evil) + f"{TS} error: Tengoku/Ns/Lib/G.lean:3:2: ##[add-mask]abc\n", shipped, shards)
        text = json.dumps(p, ensure_ascii=False) + pc.render(p)
        for bad in ("::", "\x1b", "```", "##["):
            self.assertNotIn(bad, text)
        self.assertEqual(len(p["reasons"]["Lib.D"]) <= pc.MAX_EVIDENCE * 2 + 200, True)

    def test_a_module_whose_name_cannot_be_passed_on_is_never_proposed(self):
        shards, shipped = shapes()
        write(shipped, "Tengoku/Ns/Lib/Z\x01Z.lean", "import Tengoku\n\ntheorem z : True := trivial\n")
        write(shipped, "Tengoku/Ns/Lib/Y.lean", "import Tengoku\nimport Tengoku.Ns.Lib.«Z\x01Z»\n\ntheorem y : True := trivial\n")
        p = propose(err("Lib/Z\x01Z.lean", 3, "Unknown constant `Nat.zzz_gone`"), shipped, shards)
        self.assertEqual(p["drop"], [])
        self.assertEqual([r["module"] for r in p["residual"]], ["Lib.«Z\x01Z»"])
        self.assertFalse(p["auto"])

    def test_the_logs_of_nothing_are_total(self):
        shards, shipped = shapes()
        for log in ("", "garbage\n\x00\xff", "error: Tengoku/Ns/Lib/A.lean:x:y: no\n", "Some required targets logged failures:\n"):
            p = propose(log, shipped, shards)
            self.assertEqual((p["drop"], p["refused"], p["auto"]), ([], None, False), repr(log))
        self.assertTrue(propose("", Path(tempfile.mkdtemp()), shards)["refused"])  # no module in the shipped files
        two = Path(tempfile.mkdtemp())
        write(two, "Tengoku/One/A.lean", "import Tengoku\n")
        write(two, "Tengoku/Two/A.lean", "import Tengoku\n")
        self.assertIn("2 libraries", propose("", two, shards)["refused"])


class Guard(unittest.TestCase):
    GRAPH = {"A": [], "B": ["A"], "C": ["B"], "D": []}

    def proposal(self, cut, keep=None, drop=None):
        return {"cut": sorted(cut), "keep": sorted(keep if keep is not None else set(self.GRAPH) - set(cut)), "drop": sorted(drop if drop is not None else cut)}

    def test_a_closed_cut_passes(self):
        self.assertIsNone(pc.guard(self.proposal({"B", "C"}), self.GRAPH, None))

    def test_a_cut_that_keeps_an_importer_of_a_cut_module_is_refused(self):
        self.assertIn("not closed", pc.guard(self.proposal({"A", "B"}), self.GRAPH, None))

    def test_a_cut_that_leaves_nothing_is_refused(self):
        self.assertEqual(pc.guard(self.proposal(set(self.GRAPH)), self.GRAPH, None), pc.NOTHING_LEFT)

    def test_the_earlier_proposal_stays_cut(self):
        self.assertIn("not monotone", pc.guard(self.proposal({"D"}), self.GRAPH, {"B", "C"}))
        self.assertIsNone(pc.guard(self.proposal({"B", "C", "D"}), self.GRAPH, {"B", "C"}))

    def test_a_cut_and_keep_that_are_not_a_partition_are_refused(self):
        self.assertIn("partition", pc.guard({"cut": ["B", "C"], "keep": ["A"], "drop": ["B"]}, self.GRAPH, None))

    def test_the_whole_library_cut_is_refused_with_the_errors_and_a_nonzero_status(self):
        shards, shipped = shapes()
        log = "".join(err(f"Lib/{m}.lean", 3, f"Unknown constant `Nat.zzz_{m}`") for m in "ABCDG")  # E and F import B and C
        p = propose(log, shipped, shards)
        self.assertEqual((p["refused"], p["drop"], p["cut"], p["auto"]), (pc.NOTHING_LEFT, [], [], False))
        self.assertEqual(len(p["keep"]), 7)
        self.assertGreaterEqual(len([r for r in p["residual"] if r["module"]]), 5)  # what it would have cut is shown to the person
        d = Path(tempfile.mkdtemp())
        (d / "q.log").write_text(log)
        out = subprocess.run([sys.executable, "-I", str(HERE / "propose_cut.py"), "--queue-log", str(d / "q.log"), "--shipped", str(shipped), "--json", str(d / "p.json"), "--github-output", str(d / "o")], capture_output=True, text=True)
        self.assertEqual(out.returncode, 3, out.stderr)
        self.assertIn("REFUSED", out.stdout)
        self.assertEqual((d / "o").read_text(), "go=false\ndrop=\n")
        self.assertEqual(json.loads((d / "p.json").read_text())["refused"], pc.NOTHING_LEFT)


class Cli(unittest.TestCase):
    def run_cli(self, log: str, *extra: str, shipped=None):
        shards, sh = shapes()
        d = Path(tempfile.mkdtemp())
        (d / "q.log").write_text(log)
        cmd = [sys.executable, "-I", str(HERE / "propose_cut.py"), "--queue-log", str(d / "q.log"), "--shipped", str(shipped or sh), "--shards", str(shards), "--json", str(d / "p.json"), "--github-output", str(d / "o"), *extra]
        r = subprocess.run(cmd, capture_output=True, text=True)
        return r, d

    def test_a_complete_proposal_says_go_and_gives_the_one_line_list(self):
        r, d = self.run_cli(err("Lib/B.lean", 4, "Unknown identifier `helper_thing`"), "--prior-drop", "Old.X")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual((d / "o").read_text(), "go=true\ndrop=Lib.B,Old.X\n")
        self.assertIn("drop=Lib.B,Old.X", r.stdout)

    def test_a_residual_says_no_go_and_still_exits_zero(self):
        r, d = self.run_cli(err("Lib/G.lean", 3, "failed to synthesize instance"))
        self.assertEqual((r.returncode, (d / "o").read_text()), (0, "go=false\ndrop=\n"))

    def test_an_empty_log_is_not_a_cut(self):
        r, d = self.run_cli("")
        self.assertEqual((r.returncode, (d / "o").read_text()), (0, "go=false\ndrop=\n"))

    def test_bad_names_in_prior_drop_are_refused(self):
        r, _ = self.run_cli("", "--prior-drop", "A B,../x")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("not module names", r.stderr)

    def test_the_previous_proposal_is_kept(self):
        shards, shipped = shapes()
        first = propose(err("Lib/B.lean", 4, "Unknown identifier `helper_thing`"), shipped, shards)
        d = Path(tempfile.mkdtemp())
        (d / "prev.json").write_text(json.dumps(first))
        r, _ = self.run_cli(err("Lib/G.lean", 3, "Unknown constant `Nat.zzz`"), "--previous", str(d / "prev.json"))
        self.assertEqual(r.returncode, 3)  # the longer log (here: another build's) does not cut B and E any more
        self.assertIn("not monotone", r.stdout)


# ---------------------------------------------------------------- random libraries
class Lib:
    """`Rnd`: n modules, each importing a random subset of the ones before it (so the index order is a topological order), some in a subdirectory, some named like `«1000.3»`. Every module
    declares `t_M<i>`. The generator knows how each module is meant to fail; the oracle below uses only that, never the proposal code."""

    def __init__(self, seed: int):
        self.seed = seed
        r = self.rnd = random.Random(seed)
        self.n = r.randint(2, 12)
        self.rel, self.mod = [], []
        for i in range(self.n):
            style = r.choice(["plain", "plain", "sub", "odd"])
            rel, mod = {"plain": (f"Lib/M{i}", f"Lib.M{i}"), "sub": (f"Lib/Sub/M{i}", f"Lib.Sub.M{i}"), "odd": (f"Lib/{1000 + i}.{i}", f"Lib.«{1000 + i}.{i}»")}[style]
            self.rel.append(rel + ".lean")
            self.mod.append(mod)
        self.imports = [sorted(r.sample(range(i), r.randint(0, min(i, 3)))) for i in range(self.n)]
        self.errs: dict[int, list[tuple]] = {}  # module -> [("E",) | ("D",) | ("X", j)]
        self.target_only: set[int] = set()
        for i in range(self.n):
            if r.random() < 0.4:
                self.errs[i] = [self.kind(i) for _ in range(r.randint(1, 2))]
            elif r.random() < 0.12:
                self.target_only.add(i)
        self.noise = [("Other", "Seed/Core.lean")] * r.randint(0, 1) + [("Rnd", "Lib/Gone.lean")] * r.randint(0, 1)
        self.dir = None

    def kind(self, i: int, rnd: random.Random | None = None) -> tuple:
        r = rnd or self.rnd
        reach = sorted(self.reach(i))
        k = r.choice(["E", "E", "E", "D", "D", "X", "X"] if reach else ["E", "E", "D"])
        return ("X", r.choice(reach)) if k == "X" else (k,)

    # -- oracle helpers (a plain DFS over the generator's own lists)
    def reach(self, i: int) -> set[int]:
        out, todo = set(), list(self.imports[i])
        while todo:
            j = todo.pop()
            if j not in out:
                out.add(j)
                todo.extend(self.imports[j])
        return out

    def closure(self, roots: set[int]) -> set[int]:
        return set(roots) | {i for i in range(self.n) if self.reach(i) & set(roots)}

    # -- files
    def text(self, i: int) -> str:
        return "import Tengoku\n" + "".join(f"import Tengoku.Rnd.{self.mod[j]}\n" for j in self.imports[i]) + f"\ntheorem t_M{i} : 1 = 1 := rfl\n"

    def write_dir(self) -> Path:
        if self.dir is None:
            self.dir = Path(tempfile.mkdtemp())
            for i in range(self.n):
                write(self.dir, f"Tengoku/Rnd/{self.rel[i]}", self.text(i))
            write(self.dir, "Tengoku/Rnd/Deps.lean", "-- Rnd: a factory bundle\n")
            write(self.dir, "Tengoku.lean", "")
            write(self.dir, "Tengoku/Rnd.lean", "".join(f"import Tengoku.Rnd.{m}\n" for m in self.mod))
            (self.dir / "manifest.jsonl").write_text("".join(json.dumps({"name": f"t_M{i}", "module": f"Tengoku.Rnd.{self.mod[i]}"}) + "\n" for i in range(self.n)))
            (self.dir / "report.json").write_text(json.dumps({"theorems": self.n, "modules_in_bundle": self.n}))
        return self.dir

    def shipped(self) -> ex.Shipped:
        return ex.Shipped(self.write_dir())

    # -- logs
    def line(self, i: int, kind: tuple, col: int) -> str:
        msg = {"E": f"Unknown constant `Zzz.missing_{i % 3}`", "D": "failed to synthesize instance"}.get(kind[0]) or f"Unknown identifier `t_M{kind[1] if len(kind) > 1 else 0}`"
        return err(self.rel[i], 3, msg, col, ns="Rnd")

    def log_lines(self, errs=None, target_only=None, noise=None) -> list[str]:
        errs = self.errs if errs is None else errs
        target_only = self.target_only if target_only is None else target_only
        noise = self.noise if noise is None else noise
        lines = ["✔ [1/99] Built Tengoku.Rnd.Lib.M0 (3.2s)\n", f"{TS} warning: Tengoku/Rnd/{self.rel[0]}:1:0: some linter\n"]
        for i, ks in sorted(errs.items()):
            lines += [self.line(i, k, 2 + c) for c, k in enumerate(ks)]
            lines.append(self.line(i, ks[0], 2))  # the same line twice: one error
        lines += [err(rel, 9, "boom", ns=ns) for ns, rel in noise]
        lines.append("Some required targets logged failures:\n")
        lines += [f"- Tengoku.Rnd.{self.mod[i]}\n" for i in sorted(set(errs) | target_only)]
        lines.append("error: build failed\n")
        return lines

    def extra(self, rnd: random.Random) -> dict[int, list[tuple]]:
        """More errors of the same build: on random modules, at the same line and the columns the others use (so they can collide with an existing one)."""
        return {i: [self.kind(i, rnd) for _ in range(rnd.randint(1, 2))] for i in rnd.sample(range(self.n), rnd.randint(1, min(3, self.n)))}


def names(lib: Lib, s: set[int]) -> list[str]:
    return sorted(lib.mod[i] for i in s)


def oracle(lib: Lib, errs: dict[int, list[tuple]], target_only: set[int], flag: bool) -> dict:
    """What the specification says, by index order (imports first). Not the code under test."""
    cut: set[int] = set()
    roots: set[int] = set()
    pending: set[int] = set()
    for i in range(lib.n):
        if any(j in cut for j in lib.imports[i]):
            cut.add(i)
        own = unexplained = False
        for k in errs.get(i, ()):
            if k[0] == "X" and k[1] in cut:
                continue  # it names a declaration of a module that is cut and that this one imports: the cascade
            if k[0] == "E" or flag:
                own = True
            else:
                unexplained = True
        if i in target_only and i not in errs:
            own, unexplained = own or flag, unexplained or not flag
        if own:
            roots.add(i)
            cut.add(i)
        elif unexplained:
            pending.add(i)
    return {"roots": roots, "cut": cut, "residual": {i for i in pending if i not in cut}}


def violations(seed: int, flag: bool) -> list[str]:
    """Every way the proposal for this random library and log disagrees with the invariants. Empty: it agrees."""
    lib = Lib(seed)
    v: list[str] = []
    shipped = lib.shipped()
    lines = lib.log_lines()
    log = "".join(lines)

    def run(text: str, **kw) -> dict:
        return pc.propose(text, shipped, ex.Factory(None), drop_unexplained=flag, **kw)

    p = run(log)
    o = oracle(lib, lib.errs, lib.target_only, flag)
    every = set(range(lib.n))
    if not flag:  # a purely declarative second opinion, with no sequence in it
        explained = {i for i, ks in lib.errs.items() if ("E",) in ks}
        if o["cut"] != lib.closure(explained) or o["roots"] != explained:
            v.append("oracle disagrees with the declarative one (a bug of the test)")
    else:
        if o["cut"] != lib.closure(set(lib.errs) | lib.target_only):
            v.append("oracle disagrees with the declarative one (a bug of the test)")
    if o["cut"] == every:  # NOT ALL
        if not (p["refused"] and p["drop"] == [] and p["cut"] == [] and len(p["keep"]) == lib.n):
            v.append(f"NOT ALL: the whole library is cut and the proposal is not refused: {p['refused']!r} drop={p['drop']}")
    else:
        if p["refused"]:
            v.append(f"refused without cause: {p['refused']}")
        if p["drop"] != names(lib, o["roots"]):
            v.append(f"MINIMAL: drop {p['drop']} != {names(lib, o['roots'])}")
        if p["cut"] != names(lib, o["cut"]):
            v.append(f"CLOSED: cut {p['cut']} != {names(lib, o['cut'])}")
        if p["keep"] != names(lib, every - o["cut"]):
            v.append("keep is not the rest")
        for i in every - o["cut"]:  # CLOSED, stated directly
            if any(lib.mod[j] in p["cut"] for j in lib.imports[i]):
                v.append(f"CLOSED: kept {lib.mod[i]} imports a cut module")
        for r in p["drop"]:
            i = lib.mod.index(r)
            if i not in lib.errs and i not in lib.target_only:
                v.append(f"MINIMAL: {r} is proposed and has no error of its own")
            if p["cascade"].get(r) != names(lib, lib.closure({i}) - {i}):
                v.append(f"cascade of {r} is {p['cascade'].get(r)}")
        if set(p["reasons"]) != set(p["drop"]):
            v.append("a proposed module has no reason (or the reverse)")
        res_mods = {r["module"] for r in p["residual"] if r["module"]}
        if res_mods != {lib.mod[i] for i in o["residual"]}:
            v.append(f"residual modules {sorted(res_mods)} != {names(lib, o['residual'])}")
        if len([r for r in p["residual"] if not r["module"]]) != len(set(lib.noise)):
            v.append("the errors outside the bundle are not all in the residual")
        if p["auto"] != (bool(o["roots"]) and not p["residual"]):
            v.append("auto is wrong")
        causes = {c["cause"] for c in p["shared_causes"]}
        for c in p["shared_causes"]:
            if len(c["modules"]) < 2 or not set(c["modules"]) <= set(p["drop"]):
                v.append(f"shared cause {c} is not several proposed modules")
        if not flag:
            by_name: dict[int, set[int]] = {}
            for i in o["roots"]:
                if ("E",) in lib.errs.get(i, ()):
                    by_name.setdefault(i % 3, set()).add(i)
            want = {f"`Zzz.missing_{k}` is unknown" for k, s in by_name.items() if len(s) > 1}
            if causes != want:
                v.append(f"shared causes {causes} != {want}")

    # DETERMINISTIC: the order of the lines, and a second run
    shuffled = lines[:]
    random.Random(seed + 1).shuffle(shuffled)
    if json.dumps(run("".join(shuffled)), sort_keys=True) != json.dumps(p, sort_keys=True):
        v.append("DETERMINISTIC: the order of the log's lines changes the proposal")
    if json.dumps(run(log), sort_keys=True) != json.dumps(p, sort_keys=True):
        v.append("DETERMINISTIC: two runs differ")

    # MONOTONE: more errors of the same build never un-drop a module
    more = lib.extra(random.Random(seed + 2))
    errs2 = {i: lib.errs.get(i, []) + more.get(i, []) for i in set(lib.errs) | set(more)}
    q = run("".join(lib.log_lines(errs=errs2)), previous_cut=set(p["cut"]) if not p["refused"] else None)
    if not p["refused"]:
        if q["refused"] and q["refused"] != pc.NOTHING_LEFT:
            v.append(f"MONOTONE: the longer log is refused: {q['refused']}")
        elif not q["refused"] and not set(p["cut"]) <= set(q["cut"]):
            v.append(f"MONOTONE: {sorted(set(p['cut']) - set(q['cut']))} un-dropped by a longer log")
    return v


class Invariants(unittest.TestCase):
    def check(self, flag: bool):
        for seed in SEEDS:
            v = violations(seed, flag)
            self.assertEqual(v, [], f"seed {seed} flag={flag}")

    def test_explained_errors_only(self):
        self.check(False)

    def test_with_the_unexplained_proposed_too(self):
        self.check(True)

    def test_the_random_cases_are_not_vacuous(self):
        seen = {"refused": 0, "cascade": 0, "residual": 0, "multi_cause": 0, "importer_cut": 0, "dropped": 0, "kept_error_module": 0, "same_position": 0}
        for seed in SEEDS:
            lib = Lib(seed)
            o = oracle(lib, lib.errs, lib.target_only, False)
            seen["refused"] += o["cut"] == set(range(lib.n))
            seen["residual"] += bool(o["residual"])
            seen["dropped"] += bool(o["roots"])
            seen["importer_cut"] += bool(o["cut"] - o["roots"])
            seen["cascade"] += any(k[0] == "X" and k[1] in o["cut"] for ks in lib.errs.values() for k in ks)
            seen["multi_cause"] += len({i % 3 for i in o["roots"]}) < len(o["roots"])
            seen["kept_error_module"] += any(i not in o["cut"] for i in lib.errs)
            seen["same_position"] += any(len(ks) > 1 for ks in lib.errs.values())
        for k, n in seen.items():
            self.assertGreaterEqual(n, 5, f"{k}: {n} of {len(SEEDS)} seeds")

    def test_the_proposal_is_exactly_the_cut_bundle_cut_makes(self):
        done = 0
        for seed in SEEDS:
            lib = Lib(seed)
            d = Path(tempfile.mkdtemp()) / "bundle"
            for f in lib.write_dir().rglob("*"):
                if f.is_file():
                    write(d, str(f.relative_to(lib.write_dir())), f.read_text())
            p = pc.propose("".join(lib.log_lines()), ex.Shipped(d), ex.Factory(None))
            if p["refused"]:
                continue
            r = bc.cut_dir(d, "rnd", set(p["recut_drop"]))
            assert r is not None
            left = sorted(".".join(__import__("tolerant_build").esc(x) for x in f.relative_to(d / "Tengoku" / "Rnd").with_suffix("").parts) for f in (d / "Tengoku" / "Rnd").rglob("*.lean") if f.name != "Deps.lean")
            self.assertEqual((left, r["dropped_modules"]), (p["keep"], len(p["cut"])), f"seed {seed}")
            done += 1
        self.assertGreater(done, 50)

    def test_a_part_tar_or_a_whole_tar_reads_like_the_directory(self):
        for seed in list(SEEDS)[:20]:
            lib = Lib(seed)
            tar = Path(tempfile.mkdtemp()) / "b.tar"
            with tarfile.open(tar, "w") as t:
                for f in sorted(lib.write_dir().rglob("*.lean")):
                    t.add(f, arcname=str(f.relative_to(lib.write_dir())))
            log = "".join(lib.log_lines())
            self.assertEqual(pc.propose(log, ex.Shipped(tar), ex.Factory(None)), pc.propose(log, lib.shipped(), ex.Factory(None)), seed)


class Mutants(unittest.TestCase):
    """The invariants above must catch the code broken the way a bug would break it."""

    def caught(self, *mutations) -> bool:
        with contextlib.ExitStack() as stack:
            for m in mutations:
                stack.enter_context(m)
            return any(violations(seed, flag) for seed in SEEDS for flag in (False, True))

    def test_the_cascade_is_proposed_too(self):
        # nothing is recognised as the cascade of a cut module: a module that only names a cut module's declaration is a root of its own
        self.assertTrue(self.caught(mock.patch.object(pc.Declarations, "modules_named_by", lambda *a, **k: set())))

    def test_the_importers_are_ignored(self):
        self.assertTrue(self.caught(mock.patch.object(bc, "importer_closure", lambda roots, imports: {m for m in roots if m in imports})))

    def test_everything_is_dropped_and_nothing_stops_it(self):
        self.assertTrue(self.caught(mock.patch.object(pc, "guard", lambda *a, **k: None), mock.patch.object(bc, "importer_closure", lambda roots, imports: set(imports) if roots else set())))

    def test_a_longer_log_can_un_drop_a_module(self):
        # the first error at a line wins, in the order of the log, as explain_ejection reads it
        def first_per_line(log_text: str):
            seen: dict[tuple, pc.Err] = {}
            for ln in log_text.splitlines():
                m = ex.ERR.search(ln)
                if m:
                    seen.setdefault((m.group("ns"), m.group("rel"), int(m.group("line"))), pc.Err(m.group("ns"), m.group("rel"), int(m.group("line")), int(m.group("col")), m.group("msg"), ln))
            return list(seen.values())

        self.assertTrue(self.caught(mock.patch.object(pc, "parse_errors", first_per_line)))

    def test_an_unexplained_error_is_taken_for_an_explained_one(self):
        self.assertTrue(self.caught(mock.patch.object(pc, "EXPLAINED", {"A", "B", "C", "D", "E"})))

    def test_the_unmutated_code_is_not_caught(self):
        self.assertFalse(self.caught())


if __name__ == "__main__":
    unittest.main()
