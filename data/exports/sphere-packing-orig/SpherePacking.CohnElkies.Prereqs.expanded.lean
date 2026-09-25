/-
Copyright (c) 2024 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

/-
## THIS FILE SHOULD EVENTUALLY BE REMOVED AND THE REFERENCES IN COHN-ELKIES MUST BE REPLACED WITH
## THE RIGHT ONES (NOT THE ONES FROM HERE). THIS FILE IS JUST A TEMPORARY SOLUTION TO MAKE THE
## COHN-ELKIES FILE WORK.
-/
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

public import SpherePacking.Basic.SpherePacking
public import SpherePacking.Basic.PeriodicPacking
public import SpherePacking.ForMathlib.InvPowSummability


-- @@ L28-32 verbatim
/-!
# Prerequisites for the Cohn–Elkies Bound

Auxiliary results on Schwartz functions used in the proof of the Cohn–Elkies bound.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open BigOperators Bornology


-- @@ L38-38 verbatim
variable {d : ℕ} [Fact (0 < d)]

-- @@ L39-68 verbatim
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]


-- noncomputable section Dual_Lattice

-- /-
-- This section defines the Dual Lattice of a Lattice. Taken from
-- `SpherePacking/ForMathlib/Dual.lean`.
-- -/

-- def bilinFormOfRealInner.dualSubmodule : AddSubgroup (EuclideanSpace ℝ (Fin d)) where
-- carrier := { x | ∀ l : Λ, ∃ n : ℤ, ⟪x, l⟫_[ℝ] = ↑n }
-- zero_mem' := by
-- simp only [Subtype.forall, Set.mem_setOf_eq, inner_zero_left]
-- intro a _
-- use 0
-- rw [Int.cast_zero]
-- add_mem' := by
-- intros x y hx hy l
-- obtain ⟨n, hn⟩ := hx l
-- obtain ⟨m, hm⟩ := hy l
-- use n + m
-- simp only [inner_add_left, hn, hm, Int.cast_add]
-- neg_mem' := by
-- intros x hx l
-- obtain ⟨n, hn⟩ := hx l
-- use -n
-- simp only [inner_neg_left, hn, Int.cast_neg]

-- end Dual_Lattice


-- @@ L70-70 verbatim
section Euclidean_Space


-- @@ L72-80 verbatim
instance instNonemptyFin : Nonempty (Fin d) := ⟨0, Fact.out⟩
  -- rw [← Fintype.card_pos_iff, Fintype.card_fin]
  -- exact Fact.out

-- noncomputable instance : DivisionCommMonoid ENNReal where
-- inv_inv := inv_inv
-- mul_inv_rev := sorry
-- inv_eq_of_mul := sorry
-- mul_comm := sorry



-- @@ L83-83 verbatim
end Euclidean_Space


-- @@ L85-85 verbatim
open scoped FourierTransform


-- @@ L87-87 verbatim
open Complex Real

-- @@ L88-88 verbatim
open LinearMap (BilinForm)


-- @@ L90-99 verbatim
noncomputable section PSF_L

-- instance inst₁ : IsScalarTower ℤ ℝ (EuclideanSpace ℝ (Fin d)) := AddCommGroup.intIsScalarTower

/-
This section defines the Poisson Summation Formual, Lattice Version (`PSF_L`). This is a direct
dependency of the Cohn-Elkies proof.
-/

-- Could this maybe become a `structure` with each field being a different condition?

-- @@ L100-110 verbatim
def PSF_Conditions (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  /-
    Mention here all the conditions we decide to impose functions on which to define the PSF-L.
    For example, this could be that they must be Schwartz (cf. blueprint) or admissible (cf. Cohn-
    Elkies). This is a placeholder for now, as is almost everything in this file.

    I think Schwartz is a good choice, because we can use the results in
    `Mathlib.Analysis.Distribution.FourierSchwartz` to conclude various things about the function.
  -/
  Summable f ∧
  sorry


-- @@ L112-119 verbatim
theorem PSF_L {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ,
  (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) :=
  sorry

-- The version below is on the blueprint. I'm pretty sure it can be removed.

-- @@ L120-124 verbatim
theorem PSF_L' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f) :
    ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) *
      ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ, (𝓕 f m)
    := by
  simpa using PSF_L Λ hf 0


-- @@ L126-126 verbatim
namespace SchwartzMap


-- @@ L128-138 verbatim
theorem PoissonSummation_Lattices (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ,
      (𝓕 ⇑f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) := by
  sorry

-- theorem PoissonSummation_Lattices' (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
-- ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) * ∑' m : bilinFormOfRealInner.dualSubmodule Λ, (𝓕 f m)
--   := by
-- sorry


-- @@ L140-140 verbatim
end SchwartzMap


-- @@ L142-142 verbatim
end PSF_L


-- @@ L144-144 verbatim
open scoped FourierTransform


-- @@ L146-149 verbatim
section Positivity_on_Nhd

-- TODO: PR this to Mathlib (very useful!)
-- Or was I just not able to find it...


-- @@ L151-151 verbatim
variable {E : Type*} [TopologicalSpace E]


-- @@ L153-164 verbatim
theorem Continuous.pos_iff_exists_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hx
    suffices ∀ᶠ y in nhds x, 0 < f y by
      rw [Filter.eventually_iff] at this
      refine ⟨_, this, by simp⟩
    exact hf₁.tendsto x (eventually_gt_nhds hx)
  · intro hexistsnhd
    obtain ⟨U, hU₁, hU₂⟩ := hexistsnhd
    specialize hU₂ x (mem_of_mem_nhds hU₁)
    exact hU₂


-- @@ L166-166 verbatim
open MeasureTheory


-- @@ L168-168 verbatim
variable [MeasureSpace E] [BorelSpace E]


-- @@ L170-191 verbatim
theorem Continuous.pos_iff_exists_measurable_nhd_pos {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), MeasurableSet U ∧ ∀ y ∈ U, 0 < f y := by
  constructor
  · intro hposatx
    have h₁ : ContinuousAt f x := continuousAt hf₁
    rw [continuousAt_def] at h₁
    have h₁' : Set.Ioo (f x / 2) (3 * f x / 2) ∈ nhds (f x) := by
      apply Ioo_mem_nhds (div_two_lt_of_pos hposatx) ?_
      linarith
    specialize h₁ (Set.Ioo (f x / 2) (3 * f x / 2)) h₁'
    use (f ⁻¹' Set.Ioo (f x / 2) (3 * f x / 2))
    constructor
    · exact h₁
    · constructor
      · exact hf₁.measurable measurableSet_Ioo
      · intro y hy
        have h₂ : f y ∈ Set.Ioo (f x / 2) (3 * f x / 2) := hy
        rw [Set.mem_Ioo] at h₂
        linarith
  · intro hnhx
    obtain ⟨U, hU₁, _, hU₃⟩ := hnhx
    exact (hf₁.pos_iff_exists_nhd_pos x).mpr ⟨U, hU₁, hU₃⟩


-- @@ L193-193 verbatim
end Positivity_on_Nhd


-- @@ L195-195 verbatim
section Integration


-- @@ L197-197 verbatim
open MeasureTheory Filter


-- @@ L199-199 verbatim
variable {E : Type*} [NormedAddCommGroup E]

-- @@ L200-200 verbatim
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]

-- @@ L201-202 verbatim
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)] -- More Generality Possible?


-- @@ L204-204 verbatim
instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular


-- @@ L206-243 verbatim
theorem Continuous.integral_zero_iff_zero_of_nonneg {f : E → ℝ} (hf₁ : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  /- Informal proof:
  ← is obvious. Now, assume the integral is zero. Suppose, for contradiction, that f ≠ 0.
  Then, there is a point x at which 0 < f x. So, there is a neighbourhood of x at which
  0 < f. The integral over this neighbourhood has to be positive, but less than that over
  the entire space. This is a contradiction.
  -/
  constructor
  · intro hintf
    by_contra hne
    -- Get an x at which f x ≠ 0
    obtain ⟨x, hneatx⟩ := Function.ne_iff.mp fun a ↦ hne (id (Eq.symm a))
    have hposatx : 0 < f x := lt_of_le_of_ne (hnn x) hneatx
    -- Get a neighbourhood of x at which f is positive
    obtain ⟨U, hU₁, hU₃⟩ := (hf₁.pos_iff_exists_nhd_pos x).mp hposatx
    -- Compare the integral over this neighbourhood to the integral over the entire space
    have hintgleintf : ∫ (v : E) in U, f v ≤ ∫ (v : E), f v := by
      refine integral_mono_measure Measure.restrict_le_self ?_ hf₂
      simp only [EventuallyLE, Pi.zero_apply, hnn, eventually_true]
    have hintgpos : 0 < ∫ (v : E) in U, f v := by
      refine (integral_pos_iff_support_of_nonneg hnn (Integrable.restrict hf₂)).mpr ?_
      suffices hUpos : 0 < (volume.restrict U) U by
        dsimp [Function.support]
        suffices hInclusion : U ⊆ {x | f x ≠ 0} by
          have : (volume.restrict U) U ≤ (volume.restrict U) {x | f x ≠ 0} := by
            rw [Measure.restrict_apply_self, Measure.restrict_apply_superset hInclusion]
          exact lt_of_lt_of_le hUpos this
        intro y hy
        rw [Set.mem_setOf_eq]
        specialize hU₃ y hy
        exact Ne.symm (ne_of_lt hU₃)
      rw [Measure.restrict_apply_self]
      exact MeasureTheory.Measure.measure_pos_of_mem_nhds volume hU₁
    linarith
  · intro hf
    simp only [hf, Pi.zero_apply]
    exact integral_zero E ℝ


-- @@ L245-247 verbatim
example {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf₁ : Continuous f) (hf₂ : Integrable f)
  (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 :=
  hf₁.integral_zero_iff_zero_of_nonneg hf₂ hnn


-- @@ L249-249 verbatim
namespace SchwartzMap


-- @@ L251-259 verbatim
theorem toFun_eq_zero_iff_zero {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : 𝓢(E, F)) : (f : E → F) = 0 ↔ f = 0 := by
  constructor
  · exact fun a ↦ SchwartzMap.ext (congrFun a)
  · intro hf
    rw [hf]
    exact FunLike.coe_zero


-- @@ L261-265 verbatim
omit [Fact (0 < d)] in
theorem integral_zero_iff_zero_of_nonneg {f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)}
  (hnn : ∀ x, 0 ≤ f x) : ∫ (v : EuclideanSpace ℝ (Fin d)), f v = 0 ↔ f = 0 := by
  rw [← f.toFun_eq_zero_iff_zero]
  exact f.continuous.integral_zero_iff_zero_of_nonneg f.integrable hnn


-- @@ L267-267 verbatim
end SchwartzMap


-- @@ L269-269 verbatim
end Integration


-- @@ L271-273 verbatim
noncomputable section Misc

-- For some reason the following two instances seem to need restating...

-- @@ L274-274 verbatim
instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)


-- @@ L276-277 verbatim
instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))


-- @@ L279-280 verbatim
omit [Fact (0 < d)]
-- Now a small theorem from Complex analysis:

-- @@ L281-281 verbatim
local notation "conj" => starRingEnd ℂ

-- @@ L282-297 verbatim
theorem Complex.exp_neg_real_I_eq_conj (x m : EuclideanSpace ℝ (Fin d)) :
  cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) = conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ])) :=
  calc cexp (-(2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
  _ = Circle.exp (-2 * π * ⟪x, m⟫_[ℝ])
      := by
          rw [Circle.coe_exp]
          push_cast
          ring_nf
  _ = conj (Circle.exp (2 * π * ⟪x, m⟫_[ℝ]))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
  _= conj (cexp (2 * ↑π * I * ↑⟪x, m⟫_[ℝ]))
      := by
          rw [Circle.coe_exp]
          apply congrArg conj
          push_cast
          ring_nf


-- @@ L299-299 verbatim
end Misc
