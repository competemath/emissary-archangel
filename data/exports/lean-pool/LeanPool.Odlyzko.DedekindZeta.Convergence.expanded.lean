/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.Coefficients


-- @@ L10-10 verbatim
/-! TODO: Add doc-string. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Filter Ideal Set Topology


-- @@ L18-18 verbatim
namespace NumberField.Odlyzko


-- @@ L20-20 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L22-40 verbatim
theorem tendsto_sum_idealNormCount_div :
    Tendsto
      (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) / n)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  rw [NumberField.dedekindZeta_residue_def]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr 1
  norm_cast
  simp only [idealNormCount]
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]


-- @@ L42-47 verbatim
theorem lSeriesSummable_idealNormCount {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealNormCount K n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_
    (fun n ↦ by positivity) zero_le_one hs
  exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using tendsto_sum_idealNormCount_div K)


-- @@ L49-53 verbatim
theorem hasSum_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (LSeries.term (fun n ↦ (idealNormCount K n : ℂ)) s)
      (NumberField.dedekindZeta K s) := by
  rw [dedekindZeta_eq_LSeries_idealNormCount]
  exact (lSeriesSummable_idealNormCount K hs).LSeriesHasSum


-- @@ L55-55 verbatim
end NumberField.Odlyzko
