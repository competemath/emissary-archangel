import OAI.Geometry.ProjectionVolume.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set MeasureTheory

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace


-- @@ L10-10 verbatim
namespace Paper092


-- @@ L12-14 verbatim
theorem normalHyperplane_volume_is_canonical {n : ℕ} (u : Euclidean n) :
    (volume : Measure (normalHyperplane u)) =
      (stdOrthonormalBasis ℝ (normalHyperplane u)).toBasis.addHaar := rfl


-- @@ L16-21 verbatim
theorem normalHyperplane_finrank {n : ℕ} (u : Euclidean n) (hu : u ≠ 0) :
    Module.finrank ℝ (normalHyperplane u) = n - 1 := by
  have h := (Submodule.span ℝ ({u} : Set (Euclidean n))).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton hu, finrank_euclideanSpace_fin] at h
  change Module.finrank ℝ ((Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ) = n - 1
  omega


-- @@ L23-23 verbatim
end Paper092


-- @@ L25-25 verbatim
end


-- @@ L27-27 verbatim
end OAI
