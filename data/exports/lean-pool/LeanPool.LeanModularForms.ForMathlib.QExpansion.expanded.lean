/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps
import LeanPool.LeanModularForms.ForMathlib.Identities


-- @@ L12-20 verbatim
/-!
# q-expansions of modular forms (project-local extensions)

The bulk of the original `ForMathlib/QExpansion.lean` file has been upstreamed into
`Mathlib.NumberTheory.ModularForms.QExpansion` and
`Mathlib.Analysis.Complex.CauchyIntegral`.  This file now only keeps the project-local
variants that are parameterised by `Γ.width ∣ h` rather than `h ∈ Γ.strictPeriods`, which
the rest of the project still uses.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open scoped Real NNReal MatrixGroups CongruenceSubgroup


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open ModularForm Complex Filter Function


-- @@ L30-30 verbatim
open UpperHalfPlane hiding I


-- @@ L32-33 verbatim
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {h : ℕ} (f : F)
  (τ : ℍ) {z q : ℂ}


-- @@ L35-35 verbatim
local notation "I∞" => comap Complex.im atTop

-- @@ L36-36 verbatim
local notation "𝕢" => Periodic.qParam


-- @@ L38-38 verbatim
namespace SlashInvariantFormClass


-- @@ L40-40 verbatim
variable [hF : SlashInvariantFormClass F Γ k]

-- @@ L41-41 verbatim
include hF


-- @@ L43-53 verbatim
theorem periodic_comp_ofComplex' (hΓ : Γ.width ∣ h) : Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < im w
  · have : 0 < im (w + h) := by simp only [add_im, natCast_im, add_zero, hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw,
      ← vAdd_width_periodic f k (Nat.cast_dvd_cast hΓ) ⟨w, hw⟩]
    congr 1
    simp [UpperHalfPlane.ext_iff, add_comm]
  · have : im (w + h) ≤ 0 := by simpa only [add_im, natCast_im, add_zero, not_lt] using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos this,
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]


-- @@ L55-58 expanded
theorem eq_cuspFunction' {τ : ℍ} [NeZero h] (hΓ : Γ.width ∣ h) :
    cuspFunction h f (Periodic.qParam h τ) = f τ := by
  simpa [UpperHalfPlane.cuspFunction] using
    (periodic_comp_ofComplex' f hΓ).eq_cuspFunction (NeZero.ne _) τ


-- @@ L60-60 verbatim
end SlashInvariantFormClass


-- @@ L62-62 verbatim
open SlashInvariantFormClass


-- @@ L64-64 verbatim
namespace ModularFormClass


-- @@ L66-66 verbatim
variable [hF : ModularFormClass F Γ k]

-- @@ L67-67 verbatim
include hF


-- @@ L69-74 verbatim
/-- Differentiability of `⇑f ∘ ofComplex` at a point with positive imaginary part, recovering the
former `ModularFormClass.differentiableAt_comp_ofComplex` from the manifold-differentiability of a
modular form. -/
theorem differentiableAt_comp_ofComplex {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (⇑f ∘ ↑ofComplex) z :=
  UpperHalfPlane.mdifferentiableAt_iff.mp (holo f ⟨z, hz⟩)


-- @@ L76-76 verbatim
variable [NeZero h] (hΓ : Γ.width ∣ h)

-- @@ L77-77 verbatim
include hΓ


-- @@ L79-92 verbatim
theorem differentiableAt_cuspFunction'
    (hc : IsCusp OnePoint.infty (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)))
    (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  have npos : 0 < (h : ℝ) := mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _))
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex' f hΓ).differentiableAt_cuspFunction_zero npos
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      ((OnePoint.isBoundedAt_infty_iff.mp (ModularFormClass.bdd_at_cusps f hc)).comp_tendsto
        tendsto_comap_im_ofComplex)
  · exact Periodic.qParam_right_inv npos.ne' hq' ▸
      (periodic_comp_ofComplex' f hΓ).differentiableAt_cuspFunction npos.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one npos hq hq'


-- @@ L94-94 verbatim
end ModularFormClass


-- @@ L96-96 verbatim
open ModularFormClass


-- @@ L98-98 verbatim
namespace UpperHalfPlane.IsZeroAtImInfty


-- @@ L100-100 verbatim
variable {f}


-- @@ L102-104 expanded
lemma zeroAtFilter_comp_ofComplex {α : Type*} [Zero α] [TopologicalSpace α] {f : ℍ → α}
    (hf : IsZeroAtImInfty f) : ZeroAtFilter (comap Complex.im atTop) (f ∘ ofComplex) :=
  hf.comp tendsto_comap_im_ofComplex


-- @@ L106-122 verbatim
/-- A modular form which vanishes at the cusp `∞` actually must decay at least as fast as
`Real.exp (-2 * π * τ.im / n)`, if `n` divides the cusp with.

(Note that `Γ` need not be finite index here). -/
theorem exp_decay_atImInfty_of_width_dvd [ModularFormClass F Γ k]
    (hf : IsZeroAtImInfty f) (hΓ : Γ.width ∣ h) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  rcases eq_or_ne h 0 with rfl | hΓ'
  · simp only [Nat.cast_zero, div_zero, Real.exp_zero]
    exact hf.isBoundedAtImInfty
  · have : NeZero h := ⟨hΓ'⟩
    simpa [comp_def] using
      ((periodic_comp_ofComplex' f hΓ).exp_decay_of_zero_at_inf
        (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _)))
        (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
          fun _ ↦ differentiableAt_comp_ofComplex f)
        (hf.zeroAtFilter_comp_ofComplex)).comp_tendsto tendsto_coe_atImInfty


-- @@ L124-124 verbatim
end UpperHalfPlane.IsZeroAtImInfty


-- @@ L126-126 verbatim
namespace ModularFormClass


-- @@ L128-140 verbatim
/-- Recovers the former `ModularFormClass.hasFPowerSeries_cuspFunction`: the `q`-expansion of a
modular form is an `FPowerSeries` representing its `cuspFunction`, derived from the modular-form
instance (analyticity at `0` plus the `q`-expansion `HasSum`). -/
theorem hasFPowerSeries_cuspFunction {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} (f : F) [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction h f)
      (UpperHalfPlane.qExpansionFormalMultilinearSeries h f) 0 1 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.hasFPowerSeries_cuspFunction f hh
    (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (UpperHalfPlane.hasSum_qExpansion hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f))


-- @@ L142-142 verbatim
end ModularFormClass
