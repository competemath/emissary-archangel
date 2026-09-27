/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders


-- @@ L10-15 verbatim
/-! # Morrey bounds from carrier-local representatives

Almost-everywhere equality on a measurable carrier transfers global bounds
of a representative to the indicated original function. The representative
need not vanish outside the carrier.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Set MeasureTheory

-- @@ L20-20 verbatim
open scoped ENNReal

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
namespace CKN.Core.Endgame


-- @@ L26-38 verbatim
/-- Almost-everywhere equal scalar functions have the same cylinder Morrey norm. -/
theorem morreyNorm_eq_of_ae_eq {P τ : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) : morreyNorm P τ f = morreyNorm P τ g := by
  unfold morreyNorm
  congr 1
  funext z
  congr 1
  funext r
  unfold morreyCell cylinderPowerIntegral
  congr 2
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with w hw
  simp only [hw]


-- @@ L40-46 verbatim
/-- A carrier-local representative bounds the indicated scalar Morrey norm. -/
theorem morreyNorm_indicator_le_of_ae_eq_restrict {P τ : ℝ} (hP : 0 ≤ P)
    {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → ℝ} (huv : u =ᵐ[volume.restrict Q] v) :
    morreyNorm P τ (Q.indicator u) ≤ morreyNorm P τ v := by
  rw [morreyNorm_eq_of_ae_eq ((ae_eq_restrict_iff_indicator_ae_eq hQ).mp huv)]
  exact morreyNorm_indicator_le hP Q v


-- @@ L48-57 verbatim
/-- Component bounds transfer without imposing global equality to the representative. -/
theorem morreyNorm_component_indicator_le_of_ae_eq_restrict
    {P τ : ℝ} (hP : 0 ≤ P) {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → Vec3} (huv : u =ᵐ[volume.restrict Q] v)
    (i : Fin 3) :
    morreyNorm P τ (Q.indicator (fun z => u z i)) ≤
      morreyNorm P τ (fun z => v z i) := by
  apply morreyNorm_indicator_le_of_ae_eq_restrict hP hQ
  filter_upwards [huv] with z hz
  exact congrFun hz i


-- @@ L59-72 verbatim
/-- A global Euclidean-norm bound controls every indicated component. -/
theorem morreyNorm_component_indicator_le_norm_of_ae_eq_restrict
    {P τ : ℝ} (hP : 0 ≤ P) {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → Vec3} (huv : u =ᵐ[volume.restrict Q] v)
    (i : Fin 3) :
    morreyNorm P τ (Q.indicator (fun z => u z i)) ≤
      morreyNorm P τ (fun z => vec3EuclideanNorm (v z)) := by
  apply (morreyNorm_component_indicator_le_of_ae_eq_restrict hP hQ huv i).trans
  apply morreyNorm_mono hP
  intro z
  rw [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v z j)) (Finset.mem_univ i)


-- @@ L74-83 verbatim
/-- Finite global component norms give carrier-local vector Morrey membership. -/
theorem morreyVecMem_of_ae_eq_restrict {P τ : ℝ} (hP : 1 ≤ P) (hPτ : P ≤ τ)
    {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → Vec3} (huv : u =ᵐ[volume.restrict Q] v)
    (hv : ∀ i, morreyNorm P τ (fun z => v z i) < ∞) :
    morreyVecMem P τ Q u := by
  apply (morreyVecMem_iff_cylinder_lt_top hP hPτ Q u).mpr
  intro i
  exact (morreyNorm_component_indicator_le_of_ae_eq_restrict
    (le_trans zero_le_one hP) hQ huv i).trans_lt (hv i)


-- @@ L85-94 verbatim
/-- A finite global Euclidean-norm Morrey bound gives membership at exponents 3 and 25. -/
theorem morreyVecMem_three_twentyFive_of_ae_eq_restrict
    {Q : Set ParabolicPoint} (hQ : MeasurableSet Q)
    {u v : ParabolicPoint → Vec3} (huv : u =ᵐ[volume.restrict Q] v)
    (hv : morreyNorm 3 25 (fun z => vec3EuclideanNorm (v z)) < ∞) :
    morreyVecMem 3 25 Q u := by
  apply (morreyVecMem_iff_cylinder_lt_top (by norm_num) (by norm_num) Q u).mpr
  intro i
  exact (morreyNorm_component_indicator_le_norm_of_ae_eq_restrict
    (by norm_num) hQ huv i).trans_lt hv


-- @@ L96-96 verbatim
end CKN.Core.Endgame
