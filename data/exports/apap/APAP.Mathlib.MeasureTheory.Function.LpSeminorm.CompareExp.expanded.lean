module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp


-- @@ L5-5 verbatim
public section


-- @@ L7-7 verbatim
open ENNReal


-- @@ L9-9 verbatim
namespace MeasureTheory

-- @@ L10-10 verbatim
variable {𝕜 α : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]


-- @@ L12-16 verbatim
/-- Hölder's inequality. -/
theorem eLpNorm_mul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f g : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) [HolderTriple p q r] :
    eLpNorm (f * g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  simpa using eLpNorm_smul_le_mul_eLpNorm hg hf


-- @@ L18-18 verbatim
end MeasureTheory
