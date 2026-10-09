import OAI.Geometry.PolarProducts.PolarApproximation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section LowerBoundInline

-- @@ L6-6 verbatim
open Set Filter Function

-- @@ L7-7 verbatim
open scoped Topology ContDiff NNReal

-- @@ L8-8 verbatim
open Set Filter Metric

-- @@ L9-9 verbatim
open scoped Topology ContDiff

-- @@ L10-10 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L11-11 verbatim
open scoped Topology ContDiff NNReal

-- @@ L12-12 verbatim
open Set Filter Function

-- @@ L13-13 verbatim
open scoped Topology ContDiff

-- @@ L14-14 verbatim
open Set Filter Function

-- @@ L15-15 verbatim
open scoped Topology ContDiff NNReal

-- @@ L16-16 verbatim
open Set Filter

-- @@ L17-17 verbatim
open scoped Topology ContDiff

-- @@ L18-18 verbatim
open Set Filter Function

-- @@ L19-19 verbatim
open scoped Topology ContDiff

-- @@ L20-20 verbatim
open Set Filter Function

-- @@ L21-21 verbatim
open scoped ContDiff Topology

-- @@ L22-22 verbatim
open Set MeasureTheory

-- @@ L23-23 verbatim
open scoped ContDiff Interval Topology

-- @@ L24-24 verbatim
open Set

-- @@ L25-25 verbatim
open scoped Topology ContDiff

-- @@ L26-26 verbatim
open Set

-- @@ L27-27 verbatim
open Set MeasureTheory

-- @@ L28-28 verbatim
open scoped ContDiff Interval Topology

-- @@ L29-29 verbatim
open Set Filter Complex

-- @@ L30-30 verbatim
open scoped Topology ContDiff

-- @@ L31-31 verbatim
open MeasureTheory intervalIntegral Set

-- @@ L32-32 verbatim
open scoped Real

-- @@ L33-33 verbatim
open Set

-- @@ L34-34 verbatim
open scoped ContDiff ENNReal


-- @@ L36-36 verbatim
namespace SymmetricPolar

-- @@ L37-37 verbatim
open Set

-- @@ L38-38 verbatim
open scoped ENNReal

-- @@ L39-39 verbatim
noncomputable section

-- @@ L40-40 verbatim
variable {n : ℕ}


-- @@ L42-46 verbatim
theorem gromovWidth_mono {U V : Set (Phase n)} (h : U ⊆ V) :
    gromovWidth U ≤ gromovWidth V := by
  apply sSup_le_sSup
  rintro _ ⟨c, ⟨hc, he⟩, rfl⟩
  exact ⟨c, ⟨hc, he.mono_target h⟩, rfl⟩


-- @@ L48-58 verbatim
theorem four_le_gromovWidth_polarProduct {K : Set (Position n)} (hK : IsSymmetricConvexBody K) :
    4 ≤ gromovWidth (polarProduct K) := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hr4
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hr4real : (r : ℝ) < 4 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).mp
    simpa using hr4
  apply le_sSup
  refine ⟨(r : ℝ), ⟨hrreal, symmetric_polar_embedding hK hrreal hr4real⟩, ?_⟩
  simp


-- @@ L60-60 verbatim
end

-- @@ L61-61 verbatim
end SymmetricPolar

-- @@ L62-62 verbatim
end LowerBoundInline


-- @@ L64-64 verbatim
end OAI
