/-
  EvmAsm.Rv64.SAsm.RegFile

  The exposed register file for the SAsm structured-assembly DSL.

  SAsm basic blocks compute over a fixed set of *exposed* registers
  (t0–t6 and a0–a7).  `x0` is hardwired zero, `x1`/`x2` (ra/sp) are owned
  by the call machinery, and the s-registers are left to the ambient frame
  (a leaf SAsm function neither reads nor writes them).

  A `RegFile` is a total valuation of registers; the exposure discipline is
  enforced where it matters: `regFileIs` (M2) owns exactly the exposed set,
  and the block engine (M2) rejects reads/writes outside it.  Keeping the
  carrier total makes `get`/`set` and condition denotations simple.

  See docs/sasm-design.md §3.1.
-/

module

public import EvmAsm.Rv64.Basic


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace EvmAsm.Rv64

-- @@ L26-26 verbatim
namespace SAsm


-- @@ L28-32 verbatim
/-- Registers whose values SAsm basic blocks may read and write:
    t0–t6 (scratch) and a0–a7 (arguments/returns). -/
def exposedRegs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]


-- @@ L34-39 verbatim
/-- Decidable membership in the exposed set. -/
def Reg.isExposed (r : Reg) : Bool :=
  match r with
  | .x5 | .x6 | .x7 | .x28 | .x29 | .x30 | .x31 => true
  | .x10 | .x11 | .x12 | .x13 | .x14 | .x15 | .x16 | .x17 => true
  | _ => false


-- @@ L41-43 verbatim
theorem Reg.isExposed_iff_mem (r : Reg) :
    Reg.isExposed r = true ↔ r ∈ exposedRegs := by
  cases r <;> simp [Reg.isExposed, exposedRegs]


-- @@ L45-52 verbatim
/-- A symbolic valuation of the register file.  The values of non-exposed
    registers are irrelevant to SAsm (never read through `get` on well-formed
    programs, never owned by `regFileIs`). -/
-- implicit_reducible: since v4.33 metavariable-assignment type checks run at
-- implicit transparency, so a `Reg → Word` lambda could not be assigned to a
-- metavariable typed `RegFile` (breaking `regFileIs ?rf` matching and the
-- `RegFile.get` equation lemmas) while this synonym stayed semireducible.
@[implicit_reducible] def RegFile := Reg → Word


-- @@ L54-54 verbatim
namespace RegFile


-- @@ L56-58 verbatim
/-- Read a register.  `x0` always reads as zero, matching the machine. -/
def get (rf : RegFile) (r : Reg) : Word :=
  if r = .x0 then 0 else rf r


-- @@ L60-62 verbatim
/-- Write a register.  Writes to `x0` are dropped, matching the machine. -/
def set (rf : RegFile) (r : Reg) (v : Word) : RegFile :=
  fun r' => if r' = r ∧ r ≠ .x0 then v else rf r'


-- @@ L64-64 verbatim
@[simp] theorem get_x0 (rf : RegFile) : rf.get .x0 = 0 := rfl


-- @@ L66-68 verbatim
@[simp] theorem get_set_self (rf : RegFile) (r : Reg) (v : Word)
    (hr : r ≠ .x0) : (rf.set r v).get r = v := by
  simp [get, set, hr]


-- @@ L70-72 verbatim
@[simp] theorem get_set_ne (rf : RegFile) (r r' : Reg) (v : Word)
    (h : r' ≠ r) : (rf.set r v).get r' = rf.get r' := by
  by_cases h0 : r' = .x0 <;> simp [get, set, h, h0]


-- @@ L74-76 verbatim
@[simp] theorem set_x0 (rf : RegFile) (v : Word) : rf.set .x0 v = rf := by
  funext r'
  simp [set]


-- @@ L78-78 verbatim
end RegFile


-- @@ L80-80 verbatim
end SAsm

-- @@ L81-81 verbatim
end EvmAsm.Rv64
