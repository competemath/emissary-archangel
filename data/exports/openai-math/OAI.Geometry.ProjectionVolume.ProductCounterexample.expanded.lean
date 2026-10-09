import OAI.Geometry.ProjectionVolume.Arithmetic
import OAI.Geometry.ProjectionVolume.ProductBrightness
import OAI.Geometry.ProjectionVolume.ProductZonotope
import OAI.Geometry.ProjectionVolume.ProjectionReconstruction


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
open MeasureTheory


-- @@ L10-10 verbatim
namespace Paper092


-- @@ L12-17 verbatim
theorem productWitness_projectionBody :
    projectionBody productWitness = productZonotope := by
  apply projectionBody_eq_of_brightness_eq_support productZonotope_isCompact
    productZonotope_nonempty productZonotope_convex
  intro u
  rw [productWitness_brightness, productZonotope_support]


-- @@ L19-23 verbatim
theorem productZonotope_normalized_volume :
    (volume productZonotope).toReal / (volume productWitness).toReal ^ 19 =
      simplexConstant 10 * simplexConstant 10 := by
  rw [productZonotope_volume_real, productWitness_volume_real]
  norm_num [simplexConstant, Nat.factorial]


-- @@ L25-29 verbatim
theorem productWitness_normalizedProjectionVolume :
    normalizedProjectionVolume productWitness = simplexConstant 10 * simplexConstant 10 := by
  unfold normalizedProjectionVolume
  rw [productWitness_projectionBody]
  exact productZonotope_normalized_volume


-- @@ L31-58 verbatim
theorem product_counterexample :
    (IsCompact productWitness ∧ Convex ℝ productWitness ∧
      (interior productWitness).Nonempty) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) ∧
    normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 ∧
    1 < normalizedProjectionVolume productWitness / simplexConstant 20 ∧
    (volume (projectionBody productWitness)).toReal >
      simplexConstant 20 * (volume productWitness).toReal ^ 19 := by
  have hratio : normalizedProjectionVolume productWitness / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 := by
    rw [productWitness_normalizedProjectionVolume]
    exact dimension_twenty_ratio
  have hchoose : normalizedProjectionVolume productWitness / simplexConstant 20 =
      (121 * (Nat.choose 20 10 : ℝ)) / (21 * (2 : ℝ) ^ 20) := by
    rw [hratio, Nat.choose_eq_factorial_div_factorial (by norm_num : 10 ≤ 20)]
    norm_num [Nat.factorial]
  have hgt : 1 < normalizedProjectionVolume productWitness / simplexConstant 20 := by
    rw [hratio]
    norm_num
  have hnorm : simplexConstant 20 < normalizedProjectionVolume productWitness := by
    rw [productWitness_normalizedProjectionVolume]
    exact dimension_twenty_strict
  change simplexConstant 20 <
    (volume (projectionBody productWitness)).toReal / (volume productWitness).toReal ^ 19 at hnorm
  have hvol := (lt_div_iff₀ (pow_pos productWitness_volume_pos 19)).mp hnorm
  exact ⟨productWitness_is_convex_body, hchoose, hratio, hgt, hvol⟩


-- @@ L60-60 verbatim
end Paper092


-- @@ L62-62 verbatim
end OAI
