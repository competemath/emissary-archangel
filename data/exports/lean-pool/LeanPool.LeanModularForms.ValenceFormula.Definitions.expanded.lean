/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.PowerSeries.Order


-- @@ L12-19 verbatim
/-!
# Valence Formula Definitions

Definitions for the valence formula for SL₂(ℤ): elliptic points i and ρ,
orbifold coefficients, the order of vanishing, and the canonical fundamental domain.

We use `ModularGroup.fd` (notation `𝒟`) from mathlib for the standard fundamental domain.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Complex MeasureTheory Set Filter Topology CongruenceSubgroup

-- @@ L24-24 verbatim
open scoped Real Interval UpperHalfPlane ModularForm Modular


-- @@ L26-26 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-31 verbatim
/-- The elliptic point i as an element of ℍ. -/
def ellipticPointI' : UpperHalfPlane := ⟨I, by simp [Complex.I_im]⟩


-- @@ L33-34 verbatim
/-- The elliptic point `i` as a complex number. -/
abbrev ellipticPointI : ℂ := (ellipticPointI' : ℂ)


-- @@ L36-39 verbatim
/-- The elliptic point ρ = e^{2πi/3} = -1/2 + (√3/2)i as an element of ℍ. -/
def ellipticPointRho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp_all⟩


-- @@ L41-42 verbatim
/-- The elliptic point `ρ` as a complex number. -/
abbrev ellipticPointRho : ℂ := (ellipticPointRho' : ℂ)


-- @@ L44-47 verbatim
/-- The T-translate ρ+1 = e^{πi/3} = 1/2 + (√3/2)i. -/
def ellipticPointRhoPlusOne' : UpperHalfPlane :=
  ⟨1/2 + (Real.sqrt 3 / 2) * I, by
    simp_all⟩


-- @@ L49-50 verbatim
/-- The T-translate `ρ + 1` as a complex number. -/
abbrev ellipticPointRhoPlusOne : ℂ := (ellipticPointRhoPlusOne' : ℂ)


-- @@ L52-54 verbatim
theorem ellipticPointRho_add_one_eq :
    ellipticPointRho + 1 = ellipticPointRhoPlusOne := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) + 1 = 1/2 + (Real.sqrt 3 / 2) * I; ring


-- @@ L56-63 verbatim
private lemma normSq_half_add_sqrt3_half_I (a : ℝ) (ha : a ^ 2 = 1 / 4) :
    Complex.normSq ((a : ℂ) + (Real.sqrt 3 / 2) * I) = 1 := by
  have h1 : ((a : ℝ) : ℂ) + (Real.sqrt 3 / 2) * I =
      ((a : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I, ha,
    show (Real.sqrt 3 / 2) ^ 2 = 3 / 4 from by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num]
  ring


-- @@ L65-69 verbatim
private lemma rho_normSq_eq_one : Complex.normSq (ellipticPointRho' : ℂ) = 1 := by
  change Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  rw [show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = ((-1/2 : ℝ) : ℂ) + (Real.sqrt 3 / 2) * I from by
    push_cast; ring]
  exact normSq_half_add_sqrt3_half_I (-1/2) (by norm_num)


-- @@ L71-76 verbatim
private lemma rho_plus_one_normSq_eq_one :
    Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1 := by
  change Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  rw [show (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = ((1/2 : ℝ) : ℂ) + (Real.sqrt 3 / 2) * I from by
    push_cast; ring]
  exact normSq_half_add_sqrt3_half_I (1/2) (by norm_num)


-- @@ L78-79 verbatim
theorem ellipticPointRhoPlusOne_norm : ‖ellipticPointRhoPlusOne‖ = 1 := by
  rw [Complex.norm_def, rho_plus_one_normSq_eq_one, Real.sqrt_one]


-- @@ L81-82 verbatim
theorem ellipticPointRho_norm : ‖ellipticPointRho‖ = 1 := by
  rw [Complex.norm_def, rho_normSq_eq_one, Real.sqrt_one]


-- @@ L84-89 verbatim
theorem ellipticPointI_mem_fd : ellipticPointI' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointI', mem_ofPred_eq]
  constructor
  · norm_num [Complex.normSq]
  · change |(I : ℂ).re| ≤ (1 : ℝ) / 2
    norm_num


-- @@ L91-93 verbatim
theorem ellipticPointRho_mem_fd : ellipticPointRho' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointRho', mem_ofPred_eq]
  exact ⟨rho_normSq_eq_one ▸ le_refl _, by simp only [UpperHalfPlane.re]; norm_num⟩


-- @@ L95-98 verbatim
lemma ellipticPointI_ne_rho : ellipticPointI' ≠ ellipticPointRho' := by
  intro h
  have h1 : (ellipticPointI' : ℂ).re = (ellipticPointRho' : ℂ).re := by rw [h]
  simp only [ellipticPointI', ellipticPointRho'] at h1; norm_num at h1


-- @@ L100-102 verbatim
/-- Order of vanishing of f at a point in ℍ. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀


-- @@ L104-106 verbatim
/-- The order of vanishing at the cusp (in the q-expansion). -/
noncomputable def orderAtCusp' {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : ℤ :=
  (UpperHalfPlane.qExpansion 1 f).order.toNat


-- @@ L108-108 verbatim
end
