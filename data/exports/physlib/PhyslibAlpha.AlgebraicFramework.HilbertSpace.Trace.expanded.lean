/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Traciality


-- @@ L11-24 verbatim
/-!

# Trace as a positive linear map on continuous linear maps

## Main definitions

- `PositiveLinearMap.conjugateₚ`: conjugation as a positive linear map.
- `ContinuousLinearMap.traceₚ`: trace as a positive linear map.
- `ContinuousLinearMap.traceMulOpₚ`: the trace pairing with a positive operator.
- `ContinuousLinearMap.traceₚ_isTracial`: the trace is a tracial functional in the sense of
  `LinearMap.IsTracial` (`StarAlgebra/Traciality.lean`) — the fact connecting this concrete
  Hilbert-space trace to the abstract tracial-weight/state framework.

-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
section Conjugate


-- @@ L30-32 verbatim
variable {A : Type*} [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    (R : Type*) [Semiring R] [StarRing R]
    [Module R A] [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]


-- @@ L34-38 verbatim
/-- Conjugation `x ↦ c * x * star x`, as a positive linear map. -/
@[simps!]
def PositiveLinearMap.conjugateₚ (c : A) : A →ₚ[R] A where
  toLinearMap := LinearMap.mulLeftRight R (c, star c)
  monotone' _ _ h := star_right_conjugate_le_conjugate h c


-- @@ L40-40 verbatim
end Conjugate


-- @@ L42-42 verbatim
open ComplexOrder


-- @@ L44-44 verbatim
section Complex


-- @@ L46-46 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


-- @@ L48-48 verbatim
namespace ContinuousLinearMap


-- @@ L50-57 verbatim
/-- The trace on continuous linear maps, bundled as a positive linear map. -/
@[simps!]
noncomputable def traceₚ : (E →L[ℂ] E) →ₚ[ℂ] ℂ := .mk₀
    { toFun x := x.toLinearMap.trace ℂ E
      map_add' x y := by simp
      map_smul' m x := by simp }
    (fun x h ↦ by
      simpa using (x.isPositive_toLinearMap_iff.mpr (x.nonneg_iff_isPositive.mp h)).trace_nonneg)


-- @@ L59-62 verbatim
/-- The trace is a tracial functional: cyclic under multiplication, connecting the concrete
Hilbert-space trace here to `LinearMap.IsTracial` from `StarAlgebra/Traciality.lean`. -/
lemma traceₚ_isTracial : (traceₚ (E := E)).toLinearMap.IsTracial :=
  fun x y => by simp [traceₚ_apply, toLinearMap_mul, LinearMap.trace_mul_comm]


-- @@ L64-64 verbatim
open PositiveLinearMap


-- @@ L66-68 verbatim
/-- The positive linear functional `x ↦ tr (√ρ * x * √ρ†)`. -/
noncomputable def traceMulOpₚ (ρ : E →L[ℂ] E) : (E →L[ℂ] E) →ₚ[ℂ] ℂ :=
  traceₚ.comp (conjugateₚ ℂ (CFC.sqrt ρ))


-- @@ L70-77 verbatim
@[simp]
lemma traceMulOpₚ_apply_of_nonneg {ρ : E →L[ℂ] E} (h : 0 ≤ ρ) (x : E →L[ℂ] E) :
    ρ.traceMulOpₚ x = (↑x * ↑ρ : E →ₗ[ℂ] E).trace ℂ E := by
  simp_rw [traceMulOpₚ, PositiveLinearMap.comp_apply, coe_toLinearMap, conjugateₚ_apply,
    traceₚ_apply, toLinearMap_mul]
  rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc, (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq]
  have := congrArg toLinearMap (CFC.sqrt_mul_sqrt_self ρ h)
  simp_all


-- @@ L79-82 verbatim
@[simp]
lemma traceMulOpₚ_apply_of_not_nonneg {ρ : E →L[ℂ] E} (h : ¬0 ≤ ρ) (x : E →L[ℂ] E) :
    ρ.traceMulOpₚ x = 0 := by
  simp [traceMulOpₚ, CFC.sqrt_of_not_nonneg h]


-- @@ L84-84 verbatim
end ContinuousLinearMap
