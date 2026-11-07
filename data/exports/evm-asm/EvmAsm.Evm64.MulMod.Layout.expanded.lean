/-
  EvmAsm.Evm64.MulMod.Layout

  Scratchpad-layout scaffold for the MULMOD opcode (GH #91).
-/

module


-- @@ L9-9 verbatim
@[expose] public section

-- @@ L10-10 verbatim
namespace EvmAsm.Evm64


-- @@ L12-20 verbatim
/-- Layout of the MULMOD routine's `sp`-relative internal scratch cells.

    The current MULMOD subtree is still at the program/spec scaffold stage,
    so no concrete scratch cells have been assigned yet. The struct is kept
    empty for now to establish the naming and parameter-passing convention
    before `evm_mulmod` starts threading its 512-bit product / reduction
    workspace through specs. -/
structure MulModScratchpadLayout : Type where
  deriving Repr


-- @@ L22-28 verbatim
/-- Validity bundle for `MulModScratchpadLayout`.

    With zero fields there are no access-validity or disjointness obligations
    yet. Future MULMOD slices should add named fields here, then extend
    `Valid` with the corresponding `isValidDwordAccess` and disjointness
    constraints rather than hardcoding offsets in specs. -/
structure MulModScratchpadLayout.Valid (_L : MulModScratchpadLayout) : Prop where


-- @@ L30-34 verbatim
/-- Canonical MULMOD scratchpad layout.

    Trivial while the layout has no fields; later slices should preserve this
    name and fill it with the default offsets used by the assembled program. -/
def canonicalMulModScratchpadLayout : MulModScratchpadLayout := {}


-- @@ L36-38 verbatim
/-- The canonical MULMOD scratchpad layout is valid. -/
theorem canonicalMulModScratchpadLayout_valid :
    canonicalMulModScratchpadLayout.Valid := {}


-- @@ L40-40 verbatim
end EvmAsm.Evm64
