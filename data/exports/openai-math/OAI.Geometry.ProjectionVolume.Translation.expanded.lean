import OAI.Geometry.ProjectionVolume.Basic
import Mathlib.MeasureTheory.Group.Action


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
open Set MeasureTheory

-- @@ L7-7 verbatim
open scoped Pointwise


-- @@ L9-9 verbatim
namespace Paper092


-- @@ L11-18 verbatim
theorem projectionVolume_vadd {n : ℕ} (K : Set (Euclidean n)) (v u : Euclidean n) :
    projectionVolume (v +ᵥ K) u = projectionVolume K u := by
  unfold projectionVolume
  let p := (normalHyperplane u).orthogonalProjectionOnto
  have himage : p '' (v +ᵥ K) = p v +ᵥ (p '' K) := by
    change p '' ((fun x => v + x) '' K) = (fun y => p v + y) '' (p '' K)
    simp only [image_image, map_add]
  rw [himage, measure_vadd]


-- @@ L20-22 verbatim
theorem brightness_vadd {n : ℕ} (K : Set (Euclidean n)) (v u : Euclidean n) :
    brightness (v +ᵥ K) u = brightness K u := by
  simp only [brightness, projectionVolume_vadd]


-- @@ L24-27 verbatim
theorem projectionBody_vadd {n : ℕ} (K : Set (Euclidean n)) (v : Euclidean n) :
    projectionBody (v +ᵥ K) = projectionBody K := by
  ext y
  simp only [projectionBody, mem_ofPred_eq, brightness_vadd]


-- @@ L29-32 verbatim
theorem normalizedProjectionVolume_vadd {n : ℕ} (K : Set (Euclidean n))
    (v : Euclidean n) :
    normalizedProjectionVolume (v +ᵥ K) = normalizedProjectionVolume K := by
  simp only [normalizedProjectionVolume, projectionBody_vadd, measure_vadd]


-- @@ L34-34 verbatim
end Paper092


-- @@ L36-36 verbatim
end OAI
