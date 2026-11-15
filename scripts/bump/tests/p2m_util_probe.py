#!/usr/bin/env python3
"""p2m_util_probe.py — run a real Lean on the shortcuts of `P2M/Util.lean` and on what p2m_util.py writes in their place, and compare what they declare.

  p2m_util_probe.py WORKDIR [--mutant | --mutant-extra]     needs `lean` on the PATH (the CI job p2m-util-tests puts it there; nothing here runs on a developer's machine by default)

`WORKDIR` gets: `P2M/Util.lean` (the library's own file, byte for byte: fixtures/real-p2m-util-aa2d8b34.lean), `Defs.lean` (what the cases open, export and reactivate), `Orig.lean` (one case per shortcut,
written the way the library writes them), `New.lean` (what p2m_util.rewrite_module makes of Orig.lean). All three are compiled, and P2MCompare.lean (run with `lean --run`) checks that every constant Orig.lean
declares is declared by New.lean with the same type and the same value (proof terms included): the statement of each case only compiles with the effect of the shortcut it uses (an opened name, a hidden name,
a scoped notation switched on again, an alias), so a rewrite with a different effect fails to compile or declares something else. Exit status 0 only when New.lean compiles and nothing differs; 1 when the rewrite is REFUSED (New.lean does not compile, or declares something else); 2 when the probe itself broke (Orig.lean or the Util does not compile, an assertion): the mutant step of the workflow accepts only 1.
With --mutant the rewrite is made wrong on purpose (`p2m_open` becomes `open scoped`), with --mutant-extra it declares one more theorem: the probe must then FAIL (exit 1) both times.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import p2m_util as pu  # noqa: E402

DEFS = '''namespace Toy
def foo (n : Nat) : Nat := n + 1
def bar (n : Nat) : Nat := n + 2
theorem foo_pos (n : Nat) : 0 < foo n := Nat.succ_pos n
scoped notation "⟪" x "⟫" => foo x
structure T where
  n : Nat
scoped instance : Inhabited T := ⟨⟨7⟩⟩
end Toy
def foo (n : Nat) : Nat := n
'''

ORIG = '''import Defs
import P2M.Util

-- p2m_open: `open Toy` (names), in a section so that every case starts clean
section C1
p2m_open "Toy"
theorem c1 : bar 1 = 3 := rfl
end C1

-- hiding: `Toy.foo` is hidden, so `foo` is the root `foo`
section C2
p2m_open "Toy~foo"
theorem c2 : foo 1 = 1 := rfl
end C2

-- the word `scoped` names no namespace and does nothing; Toy is opened and its notation is on
section C3
p2m_open "scoped Toy"
theorem c3 : bar 1 = 3 ∧ ⟪1⟫ = 2 := ⟨rfl, rfl⟩
end C3

-- p2m_open_scoped: the notation, and no name opened
section C4
p2m_open_scoped "Toy"
theorem c4 : ⟪1⟫ = 2 := rfl
theorem c4b : Toy.bar 1 = 3 := rfl
end C4

-- p2m_reactivate: a scoped notation switched on again after the namespace it lives in was closed
section C5
namespace Toy3
scoped notation "⟦" x "⟧" => Nat.succ x
theorem inner : ⟦1⟧ = 2 := rfl
end Toy3
p2m_reactivate "Toy3"
theorem c5 : ⟦2⟧ = 3 := rfl
end C5

-- p2m_export: aliases in the current namespace
namespace Cur
p2m_export "Toy" "foo bar"
end Cur
theorem c6 : Cur.bar 1 = 3 ∧ Cur.foo 1 = 2 := ⟨rfl, rfl⟩

-- `in` forms
p2m_open "Toy" in
theorem c7a : bar 1 = 3 := rfl
-- (a scoped NOTATION cannot be parsed in the command after `in`: the activation comes after the parse, in the original and in plain Lean alike; a scoped instance is looked up at elaboration)
p2m_open_scoped "Toy" in
theorem c7b : (default : Toy.T).n = 7 := rfl

-- several commands on one line, as the library writes them
namespace Cur8 p2m_export "Toy" "foo" end Cur8
theorem c8 : Cur8.foo 1 = 2 := rfl

-- a Theorems module: binders of every kind, an anonymous hypothesis, a header whose name is on the next line
namespace P2MW.S_c9
theorem solution {α : Type} [Inhabited α] (n : Nat) (h : 0 < n) (_ : α) : n ≠ 0 := Nat.pos_iff_ne_zero.mp h
end P2MW.S_c9
theorem c9 {α : Type} [Inhabited α] (n : Nat) (h : 0 < n) (_ : α) : n ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_c9.solution
namespace P2MW.S_c10
theorem solution : 1 + 1 = 2 := rfl
end P2MW.S_c10
theorem
c10 : 1 + 1 = 2 := by p2m_exact_reverting @_root_.P2MW.S_c10.solution
namespace P2MW.S_c11
theorem solution.{u} {β : Sort u} (x : β) : x = x := rfl
end P2MW.S_c11
theorem c11.{u} {β : Sort u}
    (x : β) :
    x = x := by p2m_exact_reverting @_root_.P2MW.S_c11.solution

-- (the first recut, 15 Nov 2026) a namespace given as an ABSOLUTE name, inside a namespace of the same name: the shortcut exports the root Toy4.a4, plain `export Toy4` meant the namespace it was in
namespace Toy4
def a4 : Nat := 4
end Toy4
namespace Outer
namespace Toy4
def b4 : Nat := 5
p2m_export "Toy4" "a4"
theorem c12 : Outer.Toy4.a4 = 4 := rfl
end Toy4
end Outer

-- a namespace of the module that it never opened is no error for the shortcut; the rewrite leaves it out
namespace P2MW.S_c13
namespace Sub
def q : Nat := 9
end Sub
p2m_open "P2MW.S_c13.Sub P2MW.S_c13.Never"
theorem c13 : q = 9 := rfl
p2m_reactivate "P2MW.S_c13.Sub P2MW.S_c13.AlsoNever"
end P2MW.S_c13

-- the two checks that only print
#p2m_type_eq_warn Toy.foo Toy.bar
#p2m_type_eq Toy.foo Toy.foo
'''


def lean() -> list[str]:
    """`lean`, or `lean +<toolchain>` when LEAN_TOOLCHAIN is set (the library is on Lean 4.33.0, the tree on 4.34.0-rc2: the probe is run on both)"""
    tc = os.environ.get("LEAN_TOOLCHAIN", "")
    return ["lean", f"+{tc}"] if tc else ["lean"]


def compile_(work: Path, mod: str, lean_path: str) -> None:
    out = work / f"{mod}.olean"
    out.parent.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "LEAN_PATH": lean_path}
    subprocess.run([*lean(), f"--root={work}", "-o", str(out), str(work / f"{mod}.lean")], check=True, env=env)


def main(argv: list[str]) -> int:
    work = Path(argv[0])
    mutant = "--mutant" in argv
    extra = "--mutant-extra" in argv
    (work / "P2M").mkdir(parents=True, exist_ok=True)
    (work / "P2M" / "Util.lean").write_bytes((HERE / "fixtures" / "real-p2m-util-aa2d8b34.lean").read_bytes())
    (work / "Defs.lean").write_text(DEFS, encoding="utf-8")
    (work / "Orig.lean").write_text(ORIG, encoding="utf-8")
    new, done, left = pu.rewrite_module(ORIG)
    if mutant:  # a wrong rewrite on purpose: the names of `p2m_open` are opened by `open scoped` (no name opened)
        new = new.replace("open Toy", "open scoped Toy").replace("open Toy~", "open scoped Toy")
    if left or "P2M.Util" in new:
        print("the rewrite left a shortcut or the import: the probe's own case is wrong", left)
        return 2
    if extra:  # a rewrite that adds a constant must be refused too (P2MCompare: EXTRA)
        new = new.rstrip("\n") + "\ntheorem p2m_probe_extra : True := trivial\n"
    (work / "New.lean").write_text(new, encoding="utf-8")
    print("expanded:", dict(done))
    lp = str(work)
    try:
        compile_(work, "P2M/Util", lp)
        compile_(work, "Defs", lp)
        compile_(work, "Orig", lp)
    except subprocess.CalledProcessError:
        print("the library's own module or the original case does not compile: the probe is broken, not the rewrite")
        return 2
    try:
        compile_(work, "New", lp)
    except subprocess.CalledProcessError:
        print("New.lean does not compile")
        return 1
    r = subprocess.run([*lean(), "--run", str(HERE / "lean" / "P2MCompare.lean"), str(work / "Orig.olean"), str(work / "New.olean")], env={**os.environ, "LEAN_PATH": lp})
    return {0: 0, 1: 1}.get(r.returncode, 2)  # the comparison itself crashing is the probe's, not a refusal


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
