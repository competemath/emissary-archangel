/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.a.IntegralEstimates.I1
public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.FG

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold


-- @@ L15-30 verbatim
/-!
# Complex integrands Φ₁'–Φ₆' are holomorphic on the upper half-plane

In this file, we prove that all the complex integrands Φ₁' through Φ₆' that appear in our integrals
`I₁`-`I₆` are holomorphic on the upper half-plane.

## Main Results

* `Φⱼ'_holo`: For j = 1…6, `Φⱼ'` is Complex-differentiable on the upper half-plane.
* `Φⱼ'_contDiffOn_ℂ`: For j = 1…6, `Φⱼ'` is Complex-smooth on the upper half-plane.
* `Φⱼ'_contDiffOn`: For j = 1…6, `Φⱼ'` is Real-smooth on the upper half-plane.
* `φ₀''_holo`: `φ₀''` is Complex-differentiable on the upper half-plane.
* `φ₀''_differentiable`: `φ₀''` is differentiable on `Set.univ ×ℂ Ioi 0`.
* `φ₀''_continuous`: `φ₀''` is continuous on the upper half-plane.
* `φ₀_continuous`: `φ₀ : ℍ → ℂ` is continuous.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-36 verbatim
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.IntegralEstimates.I₁
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands


-- @@ L38-38 verbatim
open Complex Real Set Filter intervalIntegral ContDiff UpperHalfPlane


-- @@ L40-40 verbatim
open scoped Function Manifold


-- @@ L42-42 verbatim
local notation "ℍ₀" => upperHalfPlaneSet


-- @@ L44-44 expanded
local notation "Holo(" f ")" => DifferentiableOn ℂ f upperHalfPlaneSet


-- @@ L46-46 expanded
local notation "MDiff(" f ")" => MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f upperHalfPlaneSet


-- @@ L48-48 verbatim
section Helpers


-- @@ L50-50 verbatim
namespace UpperHalfPlane


-- @@ L52-52 expanded
theorem zero_not_mem_upperHalfPlaneSet : (0 : ℂ) ∉ upperHalfPlaneSet := by simp


-- @@ L54-54 verbatim
end UpperHalfPlane


-- @@ L56-56 verbatim
end Helpers


-- @@ L58-58 verbatim
namespace MagicFunction.a.ComplexIntegrands


-- @@ L60-60 verbatim
variable {r : ℝ} (hr : r ≥ 0)


-- @@ L62-62 verbatim
section Holo_Lemmas


-- @@ L64-64 verbatim
/-! # Complex Differentiability -/


-- @@ L66-75 expanded
theorem φ₀''_holo : DifferentiableOn ℂ φ₀'' upperHalfPlaneSet :=
  by
  have hF := UpperHalfPlane.mdifferentiable_iff.mp F_holo
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp CuspForm.discriminant.holo'
  have h_eq :
    EqOn φ₀''
      (fun z =>
        (F ∘ UpperHalfPlane.ofComplex) z / (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) z)
      upperHalfPlaneSet :=
    fun z hz => by simp [φ₀''_def hz, F, φ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ h_eq
  exact
    hF.div hΔ fun z hz => by
      simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz,
        ModularForm.discriminant_ne_zero]


-- @@ L77-85 expanded
/-- For a real shift `c`, `z ↦ φ₀''(-1/(z+c))` is holomorphic on `ℍ₀`: `φ₀''` is holomorphic on
    `ℍ₀` and `z ↦ -1/(z+c)` maps `ℍ₀` into `ℍ₀` (`neg_inv_add_mapsto`). -/
theorem φ₀''_neg_inv_add_holo {c : ℂ} (hc : c.im = 0) :
    DifferentiableOn ℂ (fun z ↦ φ₀'' (-1 / (z + c))) upperHalfPlaneSet :=
  by
  have hmem : ∀ z ∈ upperHalfPlaneSet, z + c ∈ upperHalfPlaneSet := fun z hz ↦ by
    rw [mem_setOf_eq, add_im, hc, add_zero]; exact hz
  refine
    φ₀''_holo.comp
      ((differentiableOn_const (-1)).div (differentiableOn_id.add_const c)
        (fun z hz ↦ ne_of_mem_of_not_mem (hmem z hz) zero_not_mem_upperHalfPlaneSet))
      ?_
  exact neg_inv_add_mapsto hc


-- @@ L87-91 expanded
theorem Φ₁'_holo : DifferentiableOn ℂ (Φ₁' r) upperHalfPlaneSet :=
  by
  refine
    DifferentiableOn.mul ?_
      ((Complex.differentiable_exp.comp <|
          (differentiable_const _).mul differentiable_fun_id).differentiableOn)
  exact
    (φ₀''_neg_inv_add_holo (c := 1) (by simp)).mul
      ((differentiable_fun_id.differentiableOn.add_const 1).pow 2)


-- @@ L93-93 expanded
theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) upperHalfPlaneSet :=
  Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L95-95 expanded
theorem Φ₂'_holo : DifferentiableOn ℂ (Φ₂' r) upperHalfPlaneSet :=
  Φ₁'_holo


-- @@ L97-97 expanded
theorem Φ₂'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₂' r) upperHalfPlaneSet :=
  Φ₁'_contDiffOn_ℂ


-- @@ L99-104 expanded
theorem Φ₃'_holo : DifferentiableOn ℂ (Φ₃' r) upperHalfPlaneSet :=
  by
  refine
    DifferentiableOn.mul ?_
      ((Complex.differentiable_exp.comp <|
          (differentiable_const _).mul differentiable_fun_id).differentiableOn)
  simpa only [Pi.mul_def, Pi.pow_apply, sub_eq_add_neg] using
    (φ₀''_neg_inv_add_holo (c := -1) (by simp)).mul
      ((differentiable_fun_id.differentiableOn.add_const _).pow 2)


-- @@ L106-106 expanded
theorem Φ₃'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₃' r) upperHalfPlaneSet :=
  Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L108-108 expanded
theorem Φ₄'_holo : DifferentiableOn ℂ (Φ₄' r) upperHalfPlaneSet :=
  Φ₃'_holo


-- @@ L110-110 expanded
theorem Φ₄'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₄' r) upperHalfPlaneSet :=
  Φ₃'_contDiffOn_ℂ


-- @@ L112-116 expanded
theorem Φ₅'_holo : DifferentiableOn ℂ (Φ₅' r) upperHalfPlaneSet :=
  by
  refine
    DifferentiableOn.mul ?_
      ((Complex.differentiable_exp.comp <|
          (differentiable_const _).mul differentiable_fun_id).differentiableOn)
  simpa only [Pi.mul_def, add_zero] using
    (φ₀''_neg_inv_add_holo (c := 0) (by simp)).mul (differentiableOn_pow 2)


-- @@ L118-118 expanded
theorem Φ₅'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₅' r) upperHalfPlaneSet :=
  Φ₅'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L120-122 expanded
theorem Φ₆'_holo : DifferentiableOn ℂ (Φ₆' r) upperHalfPlaneSet :=
  (φ₀''_holo.comp differentiableOn_id (mapsTo_id _)).mul
    (Complex.differentiable_exp.comp <|
        (differentiable_const _).mul differentiable_fun_id).differentiableOn


-- @@ L124-124 expanded
theorem Φ₆'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₆' r) upperHalfPlaneSet :=
  Φ₆'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L126-126 verbatim
end Holo_Lemmas


-- @@ L128-128 verbatim
section ContDiffOn_Real


-- @@ L130-130 verbatim
/-! # Real Differentiability -/


-- @@ L132-136 verbatim
private theorem ContDiffOn.restrict_scalars_complex {s : Set ℂ} {f : ℂ → ℂ} {n : WithTop ℕ∞}
    (h : ContDiffOn ℂ n f s) : ContDiffOn ℝ n f s := by
  intro x hx
  exact @ContDiffWithinAt.restrict_scalars ℝ _ ℂ _ _ ℂ _ _ s f x n ℂ _ _ _
    IsScalarTower.right _ IsScalarTower.right (h x hx)


-- @@ L138-138 expanded
theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) upperHalfPlaneSet :=
  Φ₁'_contDiffOn_ℂ.restrict_scalars_complex


-- @@ L140-140 expanded
theorem Φ₂'_contDiffOn : ContDiffOn ℝ ∞ (Φ₂' r) upperHalfPlaneSet :=
  Φ₂'_contDiffOn_ℂ.restrict_scalars_complex


-- @@ L142-142 expanded
theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) upperHalfPlaneSet :=
  Φ₃'_contDiffOn_ℂ.restrict_scalars_complex


-- @@ L144-144 expanded
theorem Φ₄'_contDiffOn : ContDiffOn ℝ ∞ (Φ₄' r) upperHalfPlaneSet :=
  Φ₄'_contDiffOn_ℂ.restrict_scalars_complex


-- @@ L146-146 expanded
theorem Φ₅'_contDiffOn : ContDiffOn ℝ ∞ (Φ₅' r) upperHalfPlaneSet :=
  Φ₅'_contDiffOn_ℂ.restrict_scalars_complex


-- @@ L148-148 expanded
theorem Φ₆'_contDiffOn : ContDiffOn ℝ ∞ (Φ₆' r) upperHalfPlaneSet :=
  Φ₆'_contDiffOn_ℂ.restrict_scalars_complex


-- @@ L150-150 verbatim
end ContDiffOn_Real


-- @@ L152-152 verbatim
section Corollaries


-- @@ L154-154 verbatim
/-! # Corollaries using alternative set notation -/


-- @@ L156-162 expanded
/-- φ₀'' is holomorphic on the upper half-plane (using `Set.univ ×ℂ Ioi 0` notation).
    This is equivalent to `φ₀''_holo` since `Set.univ ×ℂ Ioi 0 = ℍ₀`. -/
theorem φ₀''_differentiable : DifferentiableOn ℂ φ₀'' (Set.univ ×ℂ Ioi 0) :=
  by
  have hset : (Set.univ ×ℂ Ioi 0 : Set ℂ) = upperHalfPlaneSet :=
    by
    ext z
    simp [upperHalfPlaneSet, reProdIm]
  simpa [hset] using φ₀''_holo


-- @@ L164-166 verbatim
/-- φ₀'' is continuous on the upper half-plane. -/
theorem φ₀''_continuous : ContinuousOn φ₀'' (Set.univ ×ℂ Ioi 0) :=
  φ₀''_differentiable.continuousOn


-- @@ L168-172 verbatim
/-- φ₀ : ℍ → ℂ is continuous. Follows from φ₀''_holo. -/
theorem φ₀_continuous : Continuous φ₀ := by
  have h_eq : φ₀ = φ₀'' ∘ (↑· : ℍ → ℂ) := funext fun z => (φ₀''_coe_upperHalfPlane z).symm
  rw [h_eq]
  exact φ₀''_holo.continuousOn.comp_continuous continuous_induced_dom fun z => z.2


-- @@ L174-174 verbatim
end Corollaries


-- @@ L176-176 verbatim
end MagicFunction.a.ComplexIntegrands
