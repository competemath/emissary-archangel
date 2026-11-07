/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

  Named per-lane shape predicates `NkShapeIs (b : EvmWord) : Prop` for k=1..4.
  Pairs with `divisor_full_domain_shape` (PR #6973) and `nonzero_divisor_limb_shape`
  (PR #6972) by giving downstream code consistent names for the four shape
  cases.
-/

module

public import EvmAsm.Evm64.Stack


-- @@ L14-14 verbatim
public section


-- @@ L16-16 verbatim
namespace EvmAsm.Evm64


-- @@ L18-18 verbatim
open EvmAsm.Rv64 EvmWord


-- @@ L20-22 verbatim
/-- N1 shape predicate: `b` is nonzero and only its lowest limb is nonzero. -/
abbrev N1ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 = 0 ∧ b.getLimbN 0 ≠ 0


-- @@ L24-26 verbatim
/-- N2 shape predicate: `b` is nonzero with limbs 2 and 3 zero, limb 1 nonzero. -/
abbrev N2ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 ≠ 0


-- @@ L28-30 verbatim
/-- N3 shape predicate: `b` is nonzero with limb 3 zero, limb 2 nonzero. -/
abbrev N3ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 ≠ 0


-- @@ L32-34 verbatim
/-- N4 shape predicate: `b` is nonzero with the top limb nonzero. -/
abbrev N4ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 ≠ 0


-- @@ L36-36 verbatim
end EvmAsm.Evm64
