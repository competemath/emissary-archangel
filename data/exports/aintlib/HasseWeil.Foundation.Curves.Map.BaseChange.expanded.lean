/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Basic


-- @@ L8-26 verbatim
/-!
# Base change of a smooth plane curve

For a smooth plane curve `C` over a field `F` and an `F`-algebra `L`, we
define `C.baseChange L : SmoothPlaneCurve L` by changing the base of the
underlying Weierstrass data via mathlib's
`WeierstrassCurve.baseChange`. This produces the same curve viewed over
the extension `L`.

This closes ticket `T-II-INFRA-C-001` of the Stream-A infrastructure
plan, and is the foundation for the `F`/`L̄` distinction needed by
T-II-3-004 (Galois action on divisors) and downstream "defined over F"
statements.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], I.2 (definition of
  "defined over `K`")
-/


-- @@ L28-28 verbatim
open WeierstrassCurve


-- @@ L30-30 verbatim
namespace HasseWeil.Curves


-- @@ L32-32 verbatim
namespace SmoothPlaneCurve


-- @@ L34-34 verbatim
variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)


-- @@ L36-42 verbatim
/-- The base change of a smooth plane curve `C/F` along an `F`-algebra
extension `L`. The underlying Weierstrass data is transported via
`WeierstrassCurve.baseChange`.
Reference: Silverman I.2 (definition of "defined over `K`"). -/
noncomputable def baseChange (L : Type*) [Field L] [Algebra F L] :
    SmoothPlaneCurve L where
  toAffine := C.toAffine.baseChange L


-- @@ L44-45 verbatim
@[simp] theorem baseChange_toAffine (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine = C.toAffine.baseChange L := rfl


-- @@ L47-48 verbatim
@[simp] theorem baseChange_a₁ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₁ = algebraMap F L C.toAffine.a₁ := rfl


-- @@ L50-51 verbatim
@[simp] theorem baseChange_a₂ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₂ = algebraMap F L C.toAffine.a₂ := rfl


-- @@ L53-54 verbatim
@[simp] theorem baseChange_a₃ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₃ = algebraMap F L C.toAffine.a₃ := rfl


-- @@ L56-57 verbatim
@[simp] theorem baseChange_a₄ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₄ = algebraMap F L C.toAffine.a₄ := rfl


-- @@ L59-60 verbatim
@[simp] theorem baseChange_a₆ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₆ = algebraMap F L C.toAffine.a₆ := rfl


-- @@ L62-62 verbatim
/-! ### Points over an extension -/


-- @@ L64-68 verbatim
/-- The `L`-rational smooth points of a curve `C` defined over `F`, for
`L` an `F`-algebra: equivalently, smooth points of the base change
`C.baseChange L`. Reference: Silverman I.2 (notation `V(L)`). -/
abbrev pointsOver (L : Type*) [Field L] [Algebra F L] : Type _ :=
  (C.baseChange L).SmoothPoint


-- @@ L70-78 verbatim
/-- The inclusion `C.SmoothPoint → C.pointsOver L` obtained by applying
`algebraMap F L` to coordinates. -/
noncomputable def includePoint (C : SmoothPlaneCurve F) (L : Type*) [Field L]
    [Algebra F L] (P : C.SmoothPoint) : C.pointsOver L where
  x := algebraMap F L P.x
  y := algebraMap F L P.y
  nonsingular :=
    (Affine.map_nonsingular C.toAffine (f := algebraMap F L)
      (FaithfulSMul.algebraMap_injective F L) P.x P.y).mpr P.nonsingular


-- @@ L80-81 verbatim
@[simp] theorem includePoint_x (L : Type*) [Field L] [Algebra F L]
    (P : C.SmoothPoint) : (C.includePoint L P).x = algebraMap F L P.x := rfl


-- @@ L83-84 verbatim
@[simp] theorem includePoint_y (L : Type*) [Field L] [Algebra F L]
    (P : C.SmoothPoint) : (C.includePoint L P).y = algebraMap F L P.y := rfl


-- @@ L86-86 verbatim
end SmoothPlaneCurve


-- @@ L88-88 verbatim
end HasseWeil.Curves
