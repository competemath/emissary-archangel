/-
  EvmAsm.Evm64.DivMod.Spec.DivDispatchShift

  The uniform normalization-shift value carried in `x2` at the DIV unified-loop
  entry: the CLZ of the divisor's top *nonzero* limb (shifted into the `.2 >>> 63`
  form the lanes consume).  Each per-lane stack spec
  (`evm_div_n{1,2,3}_stack_spec_unconditional`) pins `x2` to the CLZ of a
  *shape-specific* limb (n1 → limb 0, n2 → limb 1, n3 → limb 2, n4 → limb 3); this
  file gives the single shape-uniform expression `divDispatchShiftX2` together with
  the four per-shape rewrite lemmas proving it collapses to the lane's pinned value
  under that lane's shape predicate.  These let the 5-lane DIV scaffold
  (`UnconditionalScaffoldV5Div`) be instantiated with one `v2 := divDispatchShiftX2 b`
  and still discharge every per-shape lane.  Assembly prep for bead `evm-asm-wbc4i.10.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed
public import EvmAsm.Evm64.DivMod.Compose.CLZ


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.Evm64


-- @@ L25-25 verbatim
open EvmAsm.Rv64 EvmWord


-- @@ L27-33 verbatim
/-- The shape-uniform `x2` shift value: CLZ of the divisor's top nonzero limb,
    in the `.2 >>> 63` form the lanes pin. -/
def divDispatchShiftX2 (b : EvmWord) : Word :=
  (clzResult (if b.getLimbN 3 ≠ 0 then b.getLimbN 3
              else if b.getLimbN 2 ≠ 0 then b.getLimbN 2
              else if b.getLimbN 1 ≠ 0 then b.getLimbN 1
              else b.getLimbN 0)).2 >>> (63 : Nat)


-- @@ L35-39 verbatim
/-- Under the n4 shape, the uniform shift is the CLZ of limb 3. -/
theorem divDispatchShiftX2_n4 {b : EvmWord} (h : N4ShapeIs b) :
    divDispatchShiftX2 b = (clzResult (b.getLimbN 3)).2 >>> (63 : Nat) := by
  unfold divDispatchShiftX2
  rw [if_pos h.2]


-- @@ L41-45 verbatim
/-- Under the n3 shape, the uniform shift is the CLZ of limb 2. -/
theorem divDispatchShiftX2_n3 {b : EvmWord} (h : N3ShapeIs b) :
    divDispatchShiftX2 b = (clzResult (b.getLimbN 2)).2 >>> (63 : Nat) := by
  unfold divDispatchShiftX2
  rw [if_neg (by rw [h.2.1]; simp), if_pos h.2.2]


-- @@ L47-51 verbatim
/-- Under the n2 shape, the uniform shift is the CLZ of limb 1. -/
theorem divDispatchShiftX2_n2 {b : EvmWord} (h : N2ShapeIs b) :
    divDispatchShiftX2 b = (clzResult (b.getLimbN 1)).2 >>> (63 : Nat) := by
  unfold divDispatchShiftX2
  rw [if_neg (by rw [h.2.1]; simp), if_neg (by rw [h.2.2.1]; simp), if_pos h.2.2.2]


-- @@ L53-58 verbatim
/-- Under the n1 shape, the uniform shift is the CLZ of limb 0. -/
theorem divDispatchShiftX2_n1 {b : EvmWord} (h : N1ShapeIs b) :
    divDispatchShiftX2 b = (clzResult (b.getLimbN 0)).2 >>> (63 : Nat) := by
  unfold divDispatchShiftX2
  rw [if_neg (by rw [h.2.1]; simp), if_neg (by rw [h.2.2.1]; simp),
      if_neg (by rw [h.2.2.2.1]; simp)]


-- @@ L60-60 verbatim
end EvmAsm.Evm64
