/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalSources
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic


-- @@ L11-16 verbatim
/-! # Past-time extension of a localized pressure field

Zero extension inside the past half-space preserves the localized source
when its cutoff is supported in the smaller cylinder. No global weak-gradient
characterization is asserted for the extended field.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Set MeasureTheory

-- @@ L21-21 verbatim
open scoped ENNReal

-- @@ L22-22 verbatim
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.Step4


-- @@ L24-24 verbatim
noncomputable section

-- @@ L25-25 verbatim
namespace CKN.Core.Endgame


-- @@ L27-30 verbatim
/-- Restrict a vector field to a cylinder in the past, retaining its future values. -/
def causalPressureExtension (R : ℝ) (Dp : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z => if z.2 ≤ 0 then (parabolicCylinder (0 : Vec3) 0 R).indicator Dp z else Dp z


-- @@ L32-36 verbatim
/-- The extension preserves the field on the smaller cylinder. -/
theorem causalPressureExtension_eq_on_cylinder {R : ℝ} (Dp : ParabolicPoint → Vec3)
    {z : ParabolicPoint} (hz : z ∈ parabolicCylinder (0 : Vec3) 0 R) :
    causalPressureExtension R Dp z = Dp z := by
  simp only [causalPressureExtension, ite_eq_left hz.2.2, indicator_of_mem hz]


-- @@ L38-42 verbatim
/-- The extension preserves all future values. -/
theorem causalPressureExtension_eq_on_future (R : ℝ) (Dp : ParabolicPoint → Vec3)
    {z : ParabolicPoint} (hz : 0 < z.2) :
    causalPressureExtension R Dp z = Dp z := by
  simp only [causalPressureExtension, ite_eq_right (not_le.mpr hz)]


-- @@ L44-60 verbatim
/-- Indicating the extension on any larger cylinder gives exactly the
original field indicated on the smaller cylinder, componentwise. -/
theorem indicator_causalPressureExtension_component
    {R₁ R₀ : ℝ} (hR₁ : 0 ≤ R₁) (hR : R₁ ≤ R₀)
    (Dp : ParabolicPoint → Vec3) (i : Fin 3) :
    (parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun z => causalPressureExtension R₁ Dp z i) =
    (parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i) := by
  funext z
  by_cases hz₁ : z ∈ parabolicCylinder (0 : Vec3) 0 R₁
  · have hz₀ := parabolicCylinder_mono hR₁ hR hz₁
    simp only [indicator_of_mem hz₀, indicator_of_mem hz₁,
      causalPressureExtension_eq_on_cylinder Dp hz₁]
  · by_cases hz₀ : z ∈ parabolicCylinder (0 : Vec3) 0 R₀
    · simp only [indicator_of_mem hz₀, indicator_of_notMem hz₁,
        causalPressureExtension, ite_eq_left hz₀.2.2, Pi.zero_apply]
    · simp only [indicator_of_notMem hz₀, indicator_of_notMem hz₁]


-- @@ L62-77 verbatim
/-- Both almost-everywhere measurability and every component Morrey bound
transfer without changing the numerical bound. -/
theorem causalPressureExtension_component_bounds
    {R₁ R₀ P τ : ℝ} {K : ℝ≥0∞}
    (hR₁ : 0 ≤ R₁) (hR : R₁ ≤ R₀) (Dp : ParabolicPoint → Vec3)
    (hAE : ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
      (fun z => Dp z i)) volume)
    (hbound : ∀ i, morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
      (fun z => Dp z i)) ≤ K) :
    ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun z => causalPressureExtension R₁ Dp z i)) volume ∧
      morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
        (fun z => causalPressureExtension R₁ Dp z i)) ≤ K := by
  intro i
  rw [indicator_causalPressureExtension_component hR₁ hR]
  exact ⟨hAE i, hbound i⟩


-- @@ L79-101 verbatim
/-- A cutoff whose past support lies in the smaller cylinder gives the
same localized gradient-slot source after extension. -/
theorem localizedGradientSourceG_causalPressureExtension
    (R : ℝ) (φ : Vec3 × ℝ → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f Dp : ParabolicPoint → Vec3)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 R) :
    localizedGradientSourceG φ u Du f (causalPressureExtension R Dp) =
      localizedGradientSourceG φ u Du f Dp := by
  funext z i
  change CKN.Core.Step3.localizedEquationG φ u Du f z i -
      φ z * causalPressureExtension R Dp z i =
    CKN.Core.Step3.localizedEquationG φ u Du f z i - φ z * Dp z i
  by_cases ht : z.2 ≤ 0
  · by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 R
    · rw [causalPressureExtension_eq_on_cylinder Dp hz]
    · have hraw : (z.1, z.2) ∉ tsupport φ := fun hm => hz (hsupp _ hm ht)
      have hzero : φ (z.1, z.2) = 0 := image_eq_zero_of_notMem_tsupport hraw
      change φ z = 0 at hzero
      rw [hzero]
      simp only [zero_mul]
  · rw [causalPressureExtension_eq_on_future R Dp (lt_of_not_ge ht)]



-- @@ L104-104 verbatim
end CKN.Core.Endgame
