/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.WeightBridge


-- @@ L12-28 verbatim
/-!

# Traciality

Traciality is a property of a weight on the positive cone (`Weight.IsTracial`), and independently
a property of a state (`UnitalPositiveLinearMap.IsTracial`) — the standard notion of a tracial
state, stated directly on `𝓢[ℝ, A]` rather than defined as a weight that happens to also be a
state. `Weight.IsState.isTracial` is the theorem connecting the two: a finite tracial weight's
extension to a state is itself a tracial state.

## Main definitions

- `Weight.IsTracial`
- `UnitalPositiveLinearMap.IsTracial`
- `LinearMap.IsTracial`

-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace Weight


-- @@ L34-35 verbatim
variable {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] [One A] [IsOrderUnit A]


-- @@ L37-39 verbatim
/-- A weight is tracial when it assigns equal values to `x† x` and `x x†`. -/
def IsTracial (w : Weight A) : Prop :=
  ∀ x : A, w ⟨star x * x, star_mul_self_nonneg x⟩ = w ⟨x * star x, mul_star_self_nonneg x⟩


-- @@ L41-41 verbatim
namespace IsTracial


-- @@ L43-43 verbatim
variable {w : Weight A}


-- @@ L45-52 verbatim
/-- A finite tracial weight's real positive-linear extension has equal values on `x† x` and
`x x†`. -/
lemma toPositiveLinearMap_star_mul_self (ht : w.IsTracial) (hw : w.IsFinite) (x : A) :
    hw.toPositiveLinearMap (star x * x) = hw.toPositiveLinearMap (x * star x) := by
  change hw.toFun (star x * x) = hw.toFun (x * star x)
  rw [hw.toFun_of_nonneg ⟨star x * x, star_mul_self_nonneg x⟩,
    hw.toFun_of_nonneg ⟨x * star x, mul_star_self_nonneg x⟩]
  exact congrArg ENNReal.toReal (ht x)


-- @@ L54-54 verbatim
end IsTracial


-- @@ L56-56 verbatim
end Weight


-- @@ L58-58 verbatim
namespace UnitalPositiveLinearMap


-- @@ L60-61 verbatim
variable {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] [One A] [IsOrderUnit A]


-- @@ L63-66 expanded
/-- A state is tracial when it assigns equal values to `x† x` and `x x†`: the standard notion of a
tracial state, independent of `Weight.IsTracial` — a state is already a genuine linear functional,
so this needs no detour through a weight. -/
def IsTracial (s : UnitalPositiveLinearMap ℝ A ℝ) : Prop :=
  ∀ x : A, s (star x * x) = s (x * star x)


-- @@ L68-68 verbatim
end UnitalPositiveLinearMap


-- @@ L70-70 verbatim
namespace Weight.IsState


-- @@ L72-73 verbatim
variable {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] [One A] [IsOrderUnit A] {w : Weight A}


-- @@ L75-79 verbatim
/-- A finite tracial weight's extension to a state is itself a tracial state: the representation
theorem connecting `Weight.IsTracial` to `UnitalPositiveLinearMap.IsTracial`, in the same spirit as
`Weight.stateEquiv` connects `Weight.IsState` to `𝓢[ℝ, A]` itself. -/
lemma isTracial (hw : w.IsState) (ht : w.IsTracial) : hw.toUnitalPositiveLinearMap.IsTracial :=
  fun x => ht.toPositiveLinearMap_star_mul_self hw.finite x


-- @@ L81-81 verbatim
end Weight.IsState


-- @@ L83-83 verbatim
namespace LinearMap


-- @@ L85-86 verbatim
variable {A : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]


-- @@ L88-90 verbatim
/-- A complex-linear functional is tracial when it is invariant under cyclic permutations. -/
def IsTracial (f : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ x y : A, f (x * y) = f (y * x)


-- @@ L92-113 verbatim
/-- Equality on `x†x` and `xx†` characterizes tracial complex-linear functionals. -/
lemma isTracial_iff_star_mul_self_eq_mul_star_self (f : A →ₗ[ℂ] ℂ) :
    f.IsTracial ↔ ∀ x : A, f (star x * x) = f (x * star x) := by
  constructor
  · intro ht x
    exact ht (star x) x
  · intro h x y
    have hplus := h (x + star y)
    have hI := h (x + Complex.I • star y)
    have hx := h x
    have hy := h (star y)
    simp only [star_add, star_star, star_smul, Complex.star_def, Complex.conj_I, map_add,
      map_smul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm] at hplus hI
    simp at hI
    simp only [star_star] at hy
    have hp : f (y * x) + f (star x * star y) = f (star y * star x) + f (x * y) := by
      linear_combination hplus - hx - hy
    have hq : -Complex.I • f (y * x) + Complex.I • f (star x * star y) =
        Complex.I • f (star y * star x) - Complex.I • f (x * y) := by
      linear_combination (norm := (ring_nf; simp [Complex.I_sq, hy])) hI - hx - hy
    linear_combination (norm := (ring_nf; simp [Complex.I_sq]; try ring))
      (-Complex.I / 2) * hq - (1 / 2) * hp


-- @@ L115-115 verbatim
end LinearMap
