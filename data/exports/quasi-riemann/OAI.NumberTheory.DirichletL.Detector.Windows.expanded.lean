import OAI.NumberTheory.DirichletL.Detector.Physical


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-21 verbatim
theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le


-- @@ L23-31 verbatim
theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le


-- @@ L33-39 verbatim
theorem elementWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : O → ℂ) :
    Summable (fun m : O => W (elementNorm m / R) * F m) := by
  apply summable_of_hasFiniteSupport
  apply (elementWindow_finite_support W hW R hR).subset
  intro m hm hzero
  exact hm (by simp only [hzero, zero_mul])


-- @@ L41-47 verbatim
theorem idealWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : Ideal O → ℂ) :
    Summable (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R) * F I) := by
  apply summable_of_hasFiniteSupport
  apply (idealWindow_finite_support W hW R hR).subset
  intro I hI hzero
  exact hI (by simp only [hzero, zero_mul])


-- @@ L49-49 verbatim
end SevenEighths.ProbePhysical

-- @@ L50-50 verbatim
end


-- @@ L52-52 verbatim
end OAI
