import OAI.NumberTheory.DirichletL.Reflection.PhysicalBranchMeasure


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open MeasureTheory FourierBridge

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-16 verbatim
lemma weightedKernelCoordinate_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (i : Fin 4) (slope Q t q : ℝ) :
    ‖a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q‖≤1 := by
  rw [norm_mul,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (reciprocalKernelWindows_norm windows M hw hs i _)


-- @@ L18-24 verbatim
lemma weightedKernelDual_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (Qn Qb t n b : ℝ) :
    ‖a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b‖≤1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (kernelDualWeight_norm_le_one _ (reciprocalKernelWindows_norm windows M hw hs) Qn Qb t n b)


-- @@ L26-30 verbatim
lemma weightedKernelCoordinate_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (i : Fin 4) (slope Q q : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q) :=
  ((kernelCoordinateWeight_continuous _ _ _ _).const_mul a).aestronglyMeasurable


-- @@ L32-37 verbatim
lemma weightedKernelDual_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (Qn Qb n b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b) := by
  exact (((kernelCoordinateWeight_continuous _ _ _ _).mul
    (kernelCoordinateWeight_continuous _ _ _ _)).const_mul a).aestronglyMeasurable


-- @@ L39-39 verbatim
end

-- @@ L40-40 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L42-42 verbatim
end OAI
