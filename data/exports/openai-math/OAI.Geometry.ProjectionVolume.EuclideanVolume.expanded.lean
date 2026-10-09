import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import OAI.Geometry.ProjectionVolume.Extrusion


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
universe uι


-- @@ L8-8 verbatim
open Set MeasureTheory

-- @@ L9-9 verbatim
open scoped Pointwise


-- @@ L11-11 verbatim
namespace Paper092


-- @@ L13-17 verbatim
theorem volume_euclidean_image {ι : Type uι} [Fintype ι] (s : Set (ι → ℝ)) :
    (volume : Measure (EuclideanSpace ℝ ι)) (WithLp.toLp 2 '' s) = volume s := by
  change volume ((MeasurableEquiv.toLp 2 (ι → ℝ)) '' s) = volume s
  rw [MeasurableEquiv.image_eq_preimage_symm]
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).measure_preimage_equiv s


-- @@ L19-26 verbatim
theorem toLp_image_add_segment {ι : Type uι} [Fintype ι] (s : Set (ι → ℝ)) :
    WithLp.toLp 2 '' (s + segment ℝ (0 : ι → ℝ) 1) =
      WithLp.toLp 2 '' s + segment ℝ (0 : EuclideanSpace ℝ ι)
        (WithLp.toLp 2 (1 : ι → ℝ)) := by
  let e := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  have ha := Set.image_add (s := s) (t := segment ℝ (0 : ι → ℝ) 1) e.toAddEquiv
  have hs := image_segment ℝ e.toAffineEquiv.toAffineMap (0 : ι → ℝ) 1
  simpa [e] using ha.trans (congrArg (fun t => e '' s + t) hs)


-- @@ L28-33 verbatim
theorem volume_euclidean_cube_add_diagonal (d : ℕ) (hd : 0 < d) :
    volume ((WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1) +
      segment ℝ (0 : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 (1 : Fin d → ℝ))) =
        d + 1 := by
  rw [← toLp_image_add_segment, volume_euclidean_image]
  exact volume_Icc_add_segment_one d hd


-- @@ L35-35 verbatim
end Paper092


-- @@ L37-37 verbatim
end OAI
