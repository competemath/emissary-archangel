import OAI.Probability.GaussianPropeller.ResidualBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L6-6 verbatim
open scoped ENNReal

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace

-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L10-10 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L11-11 verbatim
open Filter

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open scoped RealInnerProductSpace

-- @@ L16-16 verbatim
open Set Filter

-- @@ L17-17 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L18-18 verbatim
open scoped NNReal

-- @@ L19-19 verbatim
open Set Filter

-- @@ L20-20 verbatim
open scoped Topology RealInnerProductSpace NNReal

-- @@ L21-21 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L23-23 verbatim
open MeasureTheory Set Filter

-- @@ L24-24 verbatim
open scoped Topology BigOperators

-- @@ L25-25 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace Topology

-- @@ L27-27 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L29-29 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology ENNReal


-- @@ L32-32 verbatim
namespace GaussianPropeller.Reduction


-- @@ L34-34 verbatim
open scoped RealInnerProductSpace


-- @@ L36-46 verbatim
lemma sqrt_value_lower {C : ℝ} (hC : 9/(8*Real.pi) < C) :
    3/(2*Real.sqrt (2*Real.pi)) < Real.sqrt C := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hs2 : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hrel : (3/(2*Real.sqrt (2*Real.pi)))^2 = 9/(8*Real.pi) := by
    rw [div_pow, mul_pow, hs2]
    ring
  have ht2 := Real.sq_sqrt hCp.le
  have hn : 0 ≤ 3/(2*Real.sqrt (2*Real.pi)) := by positivity
  nlinarith only [hrel,hC,ht2,Real.sqrt_nonneg C]


-- @@ L48-73 verbatim
lemma normalize_pair_constant {C z L M D : ℝ} (hC : 9/(8*Real.pi) < C)
    (hz : 0 ≤ z) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hD : D ≤ 9*z*L*M/(2*Real.pi*Real.sqrt (2*Real.pi))) :
    (Real.sqrt C)⁻¹*(Real.sqrt C)⁻¹*D ≤ (3/Real.pi)*(z/Real.sqrt C)*L*M := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have ht : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hq : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hp : 0 < Real.pi := Real.pi_pos
  have hh := le_of_lt (sqrt_value_lower hC)
  have hh' : 3 ≤ Real.sqrt C*(2*Real.sqrt (2*Real.pi)) := (div_le_iff₀ (by positivity)).mp hh
  have hb : 9/(2*Real.pi*Real.sqrt (2*Real.pi)) ≤ (3/Real.pi)*Real.sqrt C := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      9 ≤ 3*(Real.sqrt C*(2*Real.sqrt (2*Real.pi))) := by linarith only [hh']
      _ = _ := by field_simp
  have hDb : D ≤ (3/Real.pi)*Real.sqrt C*z*L*M := by
    calc
      D ≤ (9/(2*Real.pi*Real.sqrt (2*Real.pi)))*z*L*M := by
        convert hD using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hz) hL) hM
  have hm := mul_le_mul_of_nonneg_left hDb
    (show 0 ≤ (Real.sqrt C)⁻¹*(Real.sqrt C)⁻¹ by positivity)
  convert hm using 1
  field_simp


-- @@ L75-75 verbatim
variable {d k : ℕ} [NeZero k]


-- @@ L77-94 verbatim
theorem minimal_normalized_pair {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hC : 9/(8*Real.pi) < value A) {i j l : Fin k}
    (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0)
    (hl : gaussian d (A l) ≠ 0) (hij : i ≠ j) (hil : i ≠ l) :
    let z := centroid (A i)
    let r := (Real.sqrt (value A))⁻¹ • residualVector z (centroid (A j))
    let s := (Real.sqrt (value A))⁻¹ • residualVector z (centroid (A l))
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      (3/Real.pi)*(‖z‖/Real.sqrt (value A))*(1+residualCoefficient z (centroid (A j)))*
        (1+residualCoefficient z (centroid (A l))) := by
  dsimp only
  rw [GaussianPropeller.Pair.sqrt_gram_smul (by positivity) (by positivity)]
  apply normalize_pair_constant hC (norm_nonneg _)
    (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) (lt_add_of_pos_right _
      (residualCoefficient_pos (negative_inner_of_minimal hA hij hi hj)))))
    (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) (lt_add_of_pos_right _
      (residualCoefficient_pos (negative_inner_of_minimal hA hil hi hl)))))
  exact minimal_residual_pair hA ((by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC) hi hj hl hij hil


-- @@ L96-105 verbatim
omit [NeZero k] in
theorem sum_cell_probability {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i, (gaussian d).real (A i) = 1 := by
  let : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have hsum := integral_congr_ae (sum_indicator_eq hA (fun _ => (1:ℝ)))
  rw [integral_finsetSum] at hsum
  · simpa only [integral_indicator_const (1:ℝ) (hA.1 _), smul_eq_mul, mul_one,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hsum
  · intro i _
    exact (integrable_const (1:ℝ)).indicator (hA.1 i)


-- @@ L107-117 verbatim
omit [NeZero k] in
theorem sum_active_probability {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i : activeLabels A, (gaussian d).real (A i) = 1 := by
  classical
  rw [Finset.sum_coe_sort (activeLabels A) (fun i => (gaussian d).real (A i))]
  have he : ∑ i ∈ activeLabels A, (gaussian d).real (A i) = ∑ i, (gaussian d).real (A i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : gaussian d (A i) = 0 := by simpa only [mem_activeLabels, not_not] using hi
    simp [measureReal_def,hz]
  rw [he,sum_cell_probability hA]


-- @@ L119-127 verbatim
omit [NeZero k] in
theorem sum_active_norm_sq (A : Fin k → Set (Space d)) :
    ∑ i : activeLabels A, ‖centroid (A i)‖^2 = value A := by
  classical
  rw [Finset.sum_coe_sort (activeLabels A) (fun i => ‖centroid (A i)‖^2)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : gaussian d (A i) = 0 := by simpa only [mem_activeLabels, not_not] using hi
  simp [centroid_eq_zero_of_null hz]


-- @@ L129-133 verbatim
omit [NeZero k] in
theorem sum_active_radius_sq (A : Fin k → Set (Space d)) (hpos : 0 < value A) :
    ∑ i : activeLabels A, (‖centroid (A i)‖/Real.sqrt (value A))^2 = 1 := by
  simp only [div_pow, Real.sq_sqrt hpos.le, ← Finset.sum_div, sum_active_norm_sq]
  exact div_self hpos.ne'


-- @@ L135-135 verbatim
end GaussianPropeller.Reduction


-- @@ L137-137 verbatim
end OAI
