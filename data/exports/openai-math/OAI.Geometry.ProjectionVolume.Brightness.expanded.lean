import OAI.Geometry.ProjectionVolume.Basic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set MeasureTheory

-- @@ L6-6 verbatim
open scoped RealInnerProductSpace Pointwise


-- @@ L8-8 verbatim
namespace Paper092


-- @@ L10-13 verbatim
theorem normalHyperplane_smul {n : ℕ} (u : Euclidean n) {c : ℝ} (hc : c ≠ 0) :
    normalHyperplane (c • u) = normalHyperplane u := by
  unfold normalHyperplane
  rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]


-- @@ L15-18 verbatim
theorem projectionVolume_smul {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n)
    {c : ℝ} (hc : c ≠ 0) : projectionVolume K (c • u) = projectionVolume K u := by
  exact congrArg (fun V : Submodule ℝ (Euclidean n) =>
    (volume : Measure V) (V.orthogonalProjectionOnto '' K)) (normalHyperplane_smul u hc)


-- @@ L20-25 verbatim
theorem brightness_smul {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) (c : ℝ) :
    brightness K (c • u) = |c| * brightness K u := by
  by_cases hc : c = 0
  · simp [hc, brightness]
  · rw [brightness, projectionVolume_smul K u hc, norm_smul, Real.norm_eq_abs, brightness]
    ring


-- @@ L27-29 verbatim
theorem brightness_neg {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) :
    brightness K (-u) = brightness K u := by
  simpa using brightness_smul K u (-1)


-- @@ L31-32 verbatim
theorem brightness_nonneg {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) :
    0 ≤ brightness K u := mul_nonneg (norm_nonneg u) ENNReal.toReal_nonneg


-- @@ L34-37 verbatim
theorem zero_mem_projectionBody {n : ℕ} (K : Set (Euclidean n)) :
    0 ∈ projectionBody K := by
  intro u
  simpa using brightness_nonneg K u


-- @@ L39-45 verbatim
theorem neg_mem_projectionBody_iff {n : ℕ} (K : Set (Euclidean n)) (y : Euclidean n) :
    -y ∈ projectionBody K ↔ y ∈ projectionBody K := by
  constructor
  · intro h u
    simpa [brightness_neg] using h (-u)
  · intro h u
    simpa [brightness_neg] using h (-u)


-- @@ L47-50 verbatim
theorem projectionBody_neg_eq {n : ℕ} (K : Set (Euclidean n)) :
    -projectionBody K = projectionBody K := by
  ext y
  simp [neg_mem_projectionBody_iff]


-- @@ L52-54 verbatim
theorem projectionVolume_lt_top {n : ℕ} {K : Set (Euclidean n)} (hK : IsCompact K)
    (u : Euclidean n) : projectionVolume K u < ⊤ := by
  exact (hK.image (normalHyperplane u).orthogonalProjectionOnto.continuous).measure_lt_top


-- @@ L56-58 verbatim
theorem projectionVolume_mono {n : ℕ} {A B : Set (Euclidean n)} (h : A ⊆ B)
    (u : Euclidean n) : projectionVolume A u ≤ projectionVolume B u :=
  measure_mono (image_mono h)


-- @@ L60-64 verbatim
theorem brightness_mono {n : ℕ} {A B : Set (Euclidean n)} (h : A ⊆ B)
    (hB : IsCompact B) (u : Euclidean n) : brightness A u ≤ brightness B u :=
  mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono (projectionVolume_lt_top hB u).ne (projectionVolume_mono h u))
    (norm_nonneg u)


-- @@ L66-68 verbatim
theorem projectionBody_mono {n : ℕ} {A B : Set (Euclidean n)} (h : A ⊆ B)
    (hB : IsCompact B) : projectionBody A ⊆ projectionBody B :=
  fun _ hy u => (hy u).trans (brightness_mono h hB u)


-- @@ L70-73 verbatim
theorem projectionBody_isClosed {n : ℕ} (K : Set (Euclidean n)) :
    IsClosed (projectionBody K) := by
  rw [projectionBody, ofPred_forall]
  exact isClosed_iInter fun u => isClosed_le (innerSL ℝ u).continuous continuous_const


-- @@ L75-78 verbatim
theorem projectionBody_convex {n : ℕ} (K : Set (Euclidean n)) :
    Convex ℝ (projectionBody K) := by
  rw [projectionBody, ofPred_forall]
  exact convex_iInter fun u => (convex_Iic (brightness K u)).linear_preimage (innerSL ℝ u).toLinearMap


-- @@ L80-95 verbatim
theorem projectionBody_norm_le {n : ℕ} (K : Set (Euclidean n))
    {y : Euclidean n} (hy : y ∈ projectionBody K) :
    ‖y‖ ≤ ∑ i : Fin n, brightness K (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  calc
    ‖y‖ = ‖∑ i : Fin n, inner ℝ (b i) y • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i : Fin n, ‖inner ℝ (b i) y • b i‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |inner ℝ (b i) y| := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin n, brightness K (b i) := by
      apply Finset.sum_le_sum
      intro i _
      apply abs_le.mpr
      constructor
      · have h := hy (-b i)
        simpa [brightness_neg] using neg_le_neg h
      · exact hy (b i)


-- @@ L97-101 verbatim
theorem projectionBody_isCompact {n : ℕ} (K : Set (Euclidean n)) :
    IsCompact (projectionBody K) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨projectionBody_isClosed K, isBounded_iff_forall_norm_le.mpr ?_⟩
  exact ⟨_, fun _ hy => projectionBody_norm_le K hy⟩


-- @@ L103-108 verbatim
theorem projectionVolume_body_smul {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n)
    (hu : u ≠ 0) (c : ℝ) :
    projectionVolume (c • K) u = ENNReal.ofReal (|c| ^ (n - 1)) * projectionVolume K u := by
  unfold projectionVolume
  rw [image_smul_comm _ c K (fun x => map_smul _ c x),
    Measure.addHaar_smul, normalHyperplane_finrank u hu, abs_pow]


-- @@ L110-116 verbatim
theorem brightness_body_smul {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) (c : ℝ) :
    brightness (c • K) u = |c| ^ (n - 1) * brightness K u := by
  by_cases hu : u = 0
  · simp [hu, brightness]
  · rw [brightness, projectionVolume_body_smul K u hu c, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg c) _), brightness]
    ring


-- @@ L118-129 verbatim
theorem projectionBody_body_smul {n : ℕ} (K : Set (Euclidean n)) (c : ℝ) (hc : c ≠ 0) :
    projectionBody (c • K) = |c| ^ (n - 1) • projectionBody K := by
  have hq : 0 < |c| ^ (n - 1) := pow_pos (abs_pos.mpr hc) _
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hq.ne']
  constructor
  · intro h u
    have hh := mul_le_mul_of_nonneg_left (h u) (inv_nonneg.mpr hq.le)
    simpa [brightness_body_smul, inner_smul_right, mul_assoc, hq.ne'] using hh
  · intro h u
    have hh := mul_le_mul_of_nonneg_left (h u) hq.le
    simpa [brightness_body_smul, inner_smul_right, mul_assoc, hq.ne'] using hh


-- @@ L131-131 verbatim
end Paper092


-- @@ L133-133 verbatim
end OAI
