/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import SpherePacking.Dim8.MagicFunction.a.Basic
public import SpherePacking.ModularForms.FG.Basic

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import SpherePacking.ModularForms.Derivative


-- @@ L14-25 verbatim
/-!
# Holomorphy of the complex integrands

This file proves that the complex integrands used in the definition of the auxiliary integrals
`I₁'`-`I₆'` are holomorphic on the upper half-plane set `upperHalfPlaneSet`.

## Main statements
* `φ₀''_holo`, `φ₂''_holo`
* `Φ₁'_holo`, `Φ₃'_holo`, `Φ₅'_holo`, `Φ₆'_holo`
* `Φ₁'_contDiffOn_ℂ`, `Φ₃'_contDiffOn_ℂ`, `Φ₅'_contDiffOn_ℂ`, `Φ₆'_contDiffOn_ℂ`
* `Φ₁'_contDiffOn`, `Φ₃'_contDiffOn`, `Φ₅'_contDiffOn`, `Φ₆'_contDiffOn`
-/


-- @@ L27-27 verbatim
open scoped Function Manifold


-- @@ L29-30 verbatim
open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands


-- @@ L32-32 verbatim
open Complex Real Set Filter intervalIntegral ContDiff UpperHalfPlane


-- @@ L34-34 verbatim
local notation "ℍ₀" => upperHalfPlaneSet


-- @@ L36-36 expanded
local notation "Holo(" f ")" => DifferentiableOn ℂ f upperHalfPlaneSet


-- @@ L38-38 expanded
local notation "MDiff(" f ")" => MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f upperHalfPlaneSet


-- @@ L40-40 verbatim
section Helpers


-- @@ L42-42 verbatim
namespace UpperHalfPlane


-- @@ L44-44 expanded
theorem range_upperHalfPlane_coe : range UpperHalfPlane.coe = upperHalfPlaneSet :=
  range_coe


-- @@ L46-46 expanded
theorem zero_not_mem_upperHalfPlaneSet : (0 : ℂ) ∉ upperHalfPlaneSet := by simp


-- @@ L48-48 verbatim
end UpperHalfPlane


-- @@ L50-50 verbatim
end Helpers


-- @@ L52-52 verbatim
namespace MagicFunction.a.ComplexIntegrands


-- @@ L54-54 verbatim
variable {r : ℝ} (hr : r ≥ 0)


-- @@ L56-61 expanded
private theorem differentiableOn_Delta_ofComplex :
    DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet :=
  by
  refine (UpperHalfPlane.mdifferentiable_iff (f := (Δ : ℍ → ℂ))).1 ?_
  simpa [Delta_apply] using (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (Delta z : ℂ)))


-- @@ L63-66 expanded
private theorem Delta_ofComplex_ne_zero :
    ∀ z ∈ upperHalfPlaneSet, Δ (UpperHalfPlane.ofComplex z) ≠ 0 :=
  by
  intro z hz
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using Δ_ne_zero (UpperHalfPlane.ofComplex z)


-- @@ L68-68 verbatim
section Holo_Lemmas


-- @@ L70-77 expanded
private lemma differentiableOn_E₂_E₄_E₆_Delta :
    DifferentiableOn ℂ (E₂ ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet ∧
      DifferentiableOn ℂ ((E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet ∧
        DifferentiableOn ℂ ((E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet ∧
          DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet :=
  by
  refine ⟨(mdifferentiable_iff (f := E₂)).1 E₂_holo', ?_⟩
  refine ⟨(mdifferentiable_iff (f := (E₄ : ℍ → ℂ))).1 E₄.holo', ?_⟩
  exact ⟨(mdifferentiable_iff (f := (E₆ : ℍ → ℂ))).1 E₆.holo', differentiableOn_Delta_ofComplex⟩


-- @@ L79-82 expanded
private lemma mapsTo_smulAux' (g : GL (Fin 2) ℝ) :
    MapsTo (UpperHalfPlane.smulAux' g) upperHalfPlaneSet upperHalfPlaneSet :=
  by
  intro z hz
  simpa [upperHalfPlaneSet, UpperHalfPlane.smulAux] using
    (UpperHalfPlane.smulAux g ⟨z, by simpa [upperHalfPlaneSet] using hz⟩).2


-- @@ L84-84 verbatim
/-! # Complex Differentiability -/


-- @@ L86-95 expanded
/-- `φ₀''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₀''_holo : DifferentiableOn ℂ φ₀'' upperHalfPlaneSet :=
  by
  have hF := UpperHalfPlane.mdifferentiable_iff.mp F_holo
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
  have h_eq :
    EqOn φ₀'' (fun z => (F ∘ UpperHalfPlane.ofComplex) z / (Δ ∘ UpperHalfPlane.ofComplex) z)
      upperHalfPlaneSet :=
    fun z hz => by simp [φ₀''_def hz, F, φ₀, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ h_eq
  exact
    hF.div hΔ fun z hz => by
      simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Δ_ne_zero]


-- @@ L97-113 expanded
/-- `φ₂''` is holomorphic on `upperHalfPlaneSet`. -/
public theorem φ₂''_holo : DifferentiableOn ℂ φ₂'' upperHalfPlaneSet := by
  -- As for `φ₀''_holo`, work on `upperHalfPlaneSet` and transfer from the composite with
    -- `UpperHalfPlane.ofComplex`.
  
  rcases differentiableOn_E₂_E₄_E₆_Delta with ⟨hE₂, hE₄, hE₆, hΔ⟩
  have hNum :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (E₄ (UpperHalfPlane.ofComplex z)) *
          ((E₂ (UpperHalfPlane.ofComplex z)) * (E₄ (UpperHalfPlane.ofComplex z)) -
            E₆ (UpperHalfPlane.ofComplex z)))
      upperHalfPlaneSet :=
    hE₄.mul ((hE₂.mul hE₄).sub hE₆)
  have hQuot := hNum.div hΔ Delta_ofComplex_ne_zero
  refine hQuot.congr fun z hz => ?_
  have hz' : 0 < z.im := by simpa [upperHalfPlaneSet] using hz
  simp [φ₂'', φ₂', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']


-- @@ L115-129 expanded
/-- The integrand `Φ₁' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₁'_holo : DifferentiableOn ℂ (Φ₁' r) upperHalfPlaneSet :=
  by
  refine
    DifferentiableOn.mul ?_
      ((Complex.differentiable_exp.comp <|
          (differentiable_const _).mul differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.add_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · exact differentiableOn_id.add_const 1
    · intro z hz h0
      exact (ne_of_gt hz) (by simpa using congrArg Complex.im h0)
  · let g : GL (Fin 2) ℝ :=
      Units.mk (!![0, -1; 1, 1]) (!![1, 1; -1, 0]) (by simp [Matrix.one_fin_two])
        (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ upperHalfPlaneSet, UpperHalfPlane.smulAux' g z = -1 / (z + 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ]
    exact MapsTo.congr (mapsTo_smulAux' g) this


-- @@ L131-134 expanded
/-- The integrand `Φ₁' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₁' r) upperHalfPlaneSet :=
  Φ₁'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L136-136 expanded
theorem Φ₂'_holo : DifferentiableOn ℂ (Φ₂' r) upperHalfPlaneSet :=
  Φ₁'_holo


-- @@ L138-138 expanded
theorem Φ₂'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₂' r) upperHalfPlaneSet :=
  Φ₁'_contDiffOn_ℂ


-- @@ L140-154 expanded
/-- The integrand `Φ₃' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₃'_holo : DifferentiableOn ℂ (Φ₃' r) upperHalfPlaneSet :=
  by
  refine
    DifferentiableOn.mul ?_
      ((Complex.differentiable_exp.comp <|
          (differentiable_const _).mul differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| (differentiable_fun_id.differentiableOn.sub_const 1).pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div
    · exact differentiableOn_id.sub_const 1
    · intro z hz h0
      exact (ne_of_gt hz) (by simpa using congrArg Complex.im h0)
  · let g : GL (Fin 2) ℝ :=
      Units.mk (!![0, -1; 1, -1]) (!![-1, 1; -1, 0]) (by simp [Matrix.one_fin_two])
        (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ upperHalfPlaneSet, UpperHalfPlane.smulAux' g z = -1 / (z - 1) := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    exact MapsTo.congr (mapsTo_smulAux' g) this


-- @@ L156-159 expanded
/-- The integrand `Φ₃' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₃' r) upperHalfPlaneSet :=
  Φ₃'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L161-161 expanded
theorem Φ₄'_holo : DifferentiableOn ℂ (Φ₄' r) upperHalfPlaneSet :=
  Φ₃'_holo


-- @@ L163-163 expanded
theorem Φ₄'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₄' r) upperHalfPlaneSet :=
  Φ₃'_contDiffOn_ℂ


-- @@ L165-178 expanded
/-- The integrand `Φ₅' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₅'_holo : DifferentiableOn ℂ (Φ₅' r) upperHalfPlaneSet :=
  by
  refine
    DifferentiableOn.mul ?_
      ((Complex.differentiable_exp.comp <|
          (differentiable_const _).mul differentiable_fun_id).differentiableOn)
  refine DifferentiableOn.mul ?_ <| differentiableOn_pow 2
  apply φ₀''_holo.comp
  · apply (differentiableOn_const (-1)).div differentiableOn_id
    intro _ hz
    exact ne_of_mem_of_not_mem hz <| zero_not_mem_upperHalfPlaneSet
  · let g : GL (Fin 2) ℝ :=
      Units.mk (!![0, -1; 1, 0]) (!![0, 1; -1, 0]) (by simp [Matrix.one_fin_two])
        (by simp [Matrix.one_fin_two])
    have : ∀ z ∈ upperHalfPlaneSet, UpperHalfPlane.smulAux' g z = -1 / z := fun _ _ ↦ by
      simp [smulAux', g, num, denom, σ, ← sub_eq_add_neg]
    exact MapsTo.congr (mapsTo_smulAux' g) this


-- @@ L180-183 expanded
/-- The integrand `Φ₅' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₅'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₅' r) upperHalfPlaneSet :=
  Φ₅'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L185-188 expanded
/-- The integrand `Φ₆' r` is holomorphic on `upperHalfPlaneSet`. -/
public theorem Φ₆'_holo : DifferentiableOn ℂ (Φ₆' r) upperHalfPlaneSet :=
  by
  have hExp :
    DifferentiableOn ℂ (fun z : ℂ => cexp (π * (Complex.I : ℂ) * r * z)) upperHalfPlaneSet := by
    fun_prop
  simpa [Φ₆'] using φ₀''_holo.mul hExp


-- @@ L190-193 expanded
/-- The integrand `Φ₆' r` is smooth as a complex function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn_ℂ : ContDiffOn ℂ ∞ (Φ₆' r) upperHalfPlaneSet :=
  Φ₆'_holo.contDiffOn isOpen_upperHalfPlaneSet


-- @@ L195-195 verbatim
end Holo_Lemmas


-- @@ L197-197 verbatim
section ContDiffOn_Real


-- @@ L199-199 verbatim
/-! ## Real differentiability -/


-- @@ L201-203 expanded
/-- The integrand `Φ₁' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₁'_contDiffOn : ContDiffOn ℝ ∞ (Φ₁' r) upperHalfPlaneSet :=
  (Φ₁'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ


-- @@ L205-205 expanded
theorem Φ₂'_contDiffOn : ContDiffOn ℝ ∞ (Φ₂' r) upperHalfPlaneSet :=
  Φ₂'_contDiffOn_ℂ.restrict_scalars ℝ


-- @@ L207-209 expanded
/-- The integrand `Φ₃' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₃'_contDiffOn : ContDiffOn ℝ ∞ (Φ₃' r) upperHalfPlaneSet :=
  (Φ₃'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ


-- @@ L211-211 expanded
public theorem Φ₄'_contDiffOn : ContDiffOn ℝ ∞ (Φ₄' r) upperHalfPlaneSet :=
  Φ₄'_contDiffOn_ℂ.restrict_scalars ℝ


-- @@ L213-214 expanded
/-- The integrand `Φ₅' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₅'_contDiffOn : ContDiffOn ℝ ∞ (Φ₅' r) upperHalfPlaneSet :=
  Φ₅'_contDiffOn_ℂ.restrict_scalars ℝ


-- @@ L216-218 expanded
/-- The integrand `Φ₆' r` is smooth as a real function on `upperHalfPlaneSet`. -/
public theorem Φ₆'_contDiffOn : ContDiffOn ℝ ∞ (Φ₆' r) upperHalfPlaneSet :=
  (Φ₆'_contDiffOn_ℂ (r := r)).restrict_scalars ℝ


-- @@ L220-220 verbatim
end MagicFunction.a.ComplexIntegrands.ContDiffOn_Real
