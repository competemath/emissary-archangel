/-
  EvmAsm.Evm64.Shift.Layout

  Scratchpad-layout pilot for the Shift routine family (GH #334, beads
  evm-asm-vst1).

  Shift proofs currently thread the working-limb pointer as `sp + 32` into
  the SHL/SHR/SAR limb specs. This file names that placement as a layout
  field so follow-up DivMod/Shift parameterization can replace the hardcoded
  offset without changing call sites again.
-/

module

public import EvmAsm.Rv64.Word


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace EvmAsm.Evm64


-- @@ L21-21 verbatim
open EvmAsm.Rv64


-- @@ L23-27 verbatim
/-- Layout of the Shift routine's `sp`-relative internal scratch cells. -/
structure ShiftScratchpadLayout : Type where
  /-- Offset from the caller `sp` to the working-limb scratch block. -/
  limbOff : Word
  deriving Repr


-- @@ L29-34 verbatim
/-- Validity bundle for `ShiftScratchpadLayout`.

    The first additive slice only names the existing field. Later migration
    of the Shift specs can strengthen this with address-validity and
    disjointness obligations once the field is consumed by proofs. -/
structure ShiftScratchpadLayout.Valid (_L : ShiftScratchpadLayout) : Prop where


-- @@ L36-39 verbatim
/-- The canonical Shift scratchpad layout matching today's hardcoded
    `sp + 32` working-limb pointer. -/
def canonicalShiftScratchpadLayout : ShiftScratchpadLayout where
  limbOff := 32


-- @@ L41-42 verbatim
theorem canonicalShiftScratchpadLayout_limbOff :
    canonicalShiftScratchpadLayout.limbOff = 32 := rfl


-- @@ L44-46 verbatim
/-- The canonical Shift scratchpad layout is `Valid`. -/
theorem canonicalShiftScratchpadLayout_valid :
    canonicalShiftScratchpadLayout.Valid := {}


-- @@ L48-48 verbatim
end EvmAsm.Evm64
