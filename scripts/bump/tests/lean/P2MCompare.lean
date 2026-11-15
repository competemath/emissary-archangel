/-
P2MCompare — do two compiled modules declare the same constants with the same types and values?

  lean --run P2MCompare.lean A.olean B.olean

For every constant of A that is not an internal name: B must declare it, with the same universe parameters, the same type and the same value (a theorem's proof term, a definition's body).
Prints `SAME n`, and `DIFF <name>` / `MISSING <name>` / `EXTRA <name>` (B declares what A does not) per offender; the exit status is 1 when there is one. Used by p2m_util_probe.py: the library module with the shortcuts of `P2M/Util.lean`
against the same module with them written out as plain Lean (p2m_util.py).
-/
import Lean

open Lean

def main (argv : List String) : IO UInt32 := do
  let [a, b] := argv | IO.eprintln "usage: P2MCompare A.olean B.olean"; return 2
  let (da, _) ← readModuleData a
  let (db, _) ← readModuleData b
  let mut mb : Std.HashMap Name ConstantInfo := {}
  for n in db.constNames, c in db.constants do
    mb := mb.insert n c
  let mut bad := 0
  let mut same := 0
  for n in da.constNames, c in da.constants do
    if n.isInternal then continue
    match mb[n]? with
    | none =>
      IO.println s!"MISSING {n}"
      bad := bad + 1
    | some d =>
      if c.levelParams == d.levelParams && c.type == d.type && c.value? == d.value? then
        same := same + 1
      else
        IO.println s!"DIFF {n}"
        bad := bad + 1
  -- a rewrite that adds a constant is not the same module either (cubic on #203)
  let mut ma : Std.HashMap Name Unit := {}
  for n in da.constNames do
    ma := ma.insert n ()
  for n in db.constNames do
    if n.isInternal then continue
    unless ma.contains n do
      IO.println s!"EXTRA {n}"
      bad := bad + 1
  IO.println s!"SAME {same}"
  return if bad == 0 then 0 else 1
