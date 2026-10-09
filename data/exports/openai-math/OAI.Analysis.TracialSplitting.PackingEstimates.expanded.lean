import OAI.Analysis.TracialSplitting.OrthogonalPacking


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uA uD uI uM


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace CurrentMain


-- @@ L11-11 verbatim
section


-- @@ L13-13 verbatim
open scoped ComplexOrder


-- @@ L15-15 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L17-24 verbatim
lemma trace_mass_difference_abs_le (τ : Pureness.TracialState D) {a : D} (ha : IsSelfAdjoint a) :
    |(τ.functional a).re| ≤ traceOneNorm τ a := by
  apply abs_le.mpr
  constructor
  · have h := trace_re_le_oneNorm τ ha.neg
    simp only [map_neg, Complex.neg_re, traceOneNorm_neg] at h
    linarith
  · exact trace_re_le_oneNorm τ ha


-- @@ L26-32 verbatim
lemma trace_projected_mass_perturb (τ : Pureness.TracialState D) {p b h : D}
    (hp : IsStarProjection p) (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) {ε : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε) :
    (τ.functional (p * b)).re ≤ (τ.functional (p * h)).re + ε := by
  have ht := (trace_selfAdjoint_contraction_mul_le τ hp.isSelfAdjoint (hb.sub hh) hp.norm_le).trans hclose
  simp only [mul_sub, map_sub, Complex.sub_re] at ht
  linarith


-- @@ L34-34 verbatim
namespace WeightedBlockFamily


-- @@ L36-36 verbatim
variable {r : D} (F : WeightedBlockFamily r)


-- @@ L38-42 verbatim
omit [StarOrderedRing D] in
lemma trace_weightedSum (τ : Pureness.TracialState D) :
    (τ.functional F.weightedSum).re = ∑ j, F.weight j * (τ.functional (F.range j)).re := by
  simp only [weightedSum, map_sum, τ.functional.map_smul_of_tower, Complex.re_sum,
    Complex.smul_re, smul_eq_mul]


-- @@ L44-49 verbatim
omit [StarOrderedRing D] in
lemma trace_mul_weightedSum (τ : Pureness.TracialState D) (z : D) :
    (τ.functional (z * F.weightedSum)).re =
      ∑ j, F.weight j * (τ.functional (z * F.range j)).re := by
  simp only [weightedSum, Finset.mul_sum, mul_smul_comm, map_sum,
    τ.functional.map_smul_of_tower, Complex.re_sum, Complex.smul_re, smul_eq_mul]


-- @@ L51-51 verbatim
end WeightedBlockFamily


-- @@ L53-53 verbatim
namespace SampledPackingRound


-- @@ L55-55 verbatim
variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}


-- @@ L57-57 verbatim
variable (R : SampledPackingRound F z₀ K η δ)


-- @@ L59-62 verbatim
omit [StarOrderedRing D] in
lemma targetMass_eq (τ : Pureness.TracialState D) :
    R.targetMass τ = η * (τ.functional F.weightedSum).re := by
  rw [targetMass, F.trace_weightedSum]


-- @@ L64-76 verbatim
structure Estimates (E : ℝ) : Prop where
  target_upper : ∀ τ : Pureness.TracialState D, R.targetMass τ ≤ 2 * η
  sampled_upper : ∀ τ : Pureness.TracialState D, R.sampledMass τ ≤ 3 * η
  sampled_lower : ∀ τ : Pureness.TracialState D, η * (τ.functional (1 - z₀)).re - 3 * η ^ 2 ≤ R.sampledMass τ
  overlap_upper : ∀ τ : Pureness.TracialState D, R.overlap τ ≤ 4 * η * E + 5 * η ^ 2
  overlap_incr : ∀ τ : Pureness.TracialState D, R.overlap τ ≤ 1000 * η * (E + η)
  linear_sum : ∀ x : unitary D, x ∈ K → ∀ τ : Pureness.TracialState D, (∑ a : F.Index × Bool, ‖τ.functional (R.sampled a * (x : D)) -
    ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) ≤ 7 * η ^ 2
  inserted_energy : ∀ x : unitary D, x ∈ K → ∀ τ : Pureness.TracialState D,
    (∑ a : F.Index × Bool, traceTwoNorm τ ((x : D) * R.inserted a - R.inserted a * (x : D)) ^ 2) ≤
      1000 * η * (E + η)
  remaining : ∀ τ : Pureness.TracialState D, (τ.functional (1 - R.final)).re ≤
    (1 - η) * (τ.functional (1 - z₀)).re + 3 * η ^ 2 + 3 * R.overlap τ


-- @@ L78-146 verbatim
lemma estimates_of_average (hz₀ : IsStarProjection z₀) (hη : 0 < η) (hη1 : η < 1)
    {E : ℝ} (hE : 0 ≤ E) {b : D} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (herror : R.totalError ≤ η ^ 2)
    (hmass : ∀ τ : Pureness.TracialState D,
      (τ.functional (1 - z₀)).re - η ^ 2 ≤ (τ.functional b).re ∧
      (τ.functional b).re ≤ (τ.functional (1 - z₀)).re)
    (hclose : ∀ τ : Pureness.TracialState D, traceOneNorm τ (F.weightedSum - b) ≤ η ^ 2)
    (henergy : ∀ x : unitary D, x ∈ K → ∀ τ : Pureness.TracialState D,
      ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 ≤ 6 * η)
    (hold : ∀ τ : Pureness.TracialState D, (τ.functional (z₀ * b)).re ≤ 4 * E) : R.Estimates E := by
  have hηsq : η ^ 2 ≤ η := by nlinarith
  have hηcube : η ^ 3 ≤ η ^ 2 := by nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hη1.le)]
  have hc (τ : Pureness.TracialState D) :
      η * (τ.functional (1 - z₀)).re - 2 * η ^ 3 ≤ R.targetMass τ ∧ R.targetMass τ ≤ 2 * η := by
    have herr := (trace_mass_difference_abs_le τ
      (F.weightedSum_nonneg.isSelfAdjoint.sub hb.isSelfAdjoint)).trans (hclose τ)
    simp only [map_sub, Complex.sub_re] at herr
    obtain ⟨hl, hu⟩ := abs_le.mp herr
    have hbnds := hmass τ
    have hr := trace_projection_le_one τ hz₀.one_sub
    rw [R.targetMass_eq τ]
    constructor <;> nlinarith
  have hy (τ : Pureness.TracialState D) :
      η * (τ.functional (1 - z₀)).re - 3 * η ^ 2 ≤ R.sampledMass τ ∧ R.sampledMass τ ≤ 3 * η := by
    have herr := abs_le.mp ((R.sampledMass_error τ).trans herror)
    have ht := hc τ
    constructor <;> nlinarith
  have hl (τ : Pureness.TracialState D) : R.overlap τ ≤ 4 * η * E + 5 * η ^ 2 := by
    have hh := trace_projected_mass_perturb τ R.final_projection F.weightedSum_nonneg.isSelfAdjoint
      hb.isSelfAdjoint (hclose τ)
    rw [F.trace_mul_weightedSum] at hh
    have hdiff : 0 ≤ R.final - z₀ := sub_nonneg.mpr R.initial_le_final
    have hm := trace_mul_mono_right τ hdiff hb1
    simp only [mul_one, sub_mul, map_sub, Complex.sub_re] at hm
    have him := (R.insertedMass_bounds τ).2
    have ha := R.overlap_le_target τ hη.le
    have hY := (hy τ).2
    nlinarith [hold τ]
  have hincr (τ : Pureness.TracialState D) : R.overlap τ ≤ 1000 * η * (E + η) := by
    have hηE : 0 ≤ η * E := mul_nonneg hη.le hE
    nlinarith [hl τ, sq_nonneg η]
  refine {
    target_upper := fun τ => (hc τ).2
    sampled_upper := fun τ => (hy τ).2
    sampled_lower := fun τ => (hy τ).1
    overlap_upper := hl
    overlap_incr := hincr
    linear_sum := ?_
    inserted_energy := ?_
    remaining := ?_ }
  · intro x hx τ
    have hs := R.sampled_linear_sum τ x hx
    have hY := (hy τ).2
    have hC := (hc τ).2
    nlinarith
  · intro x hx τ
    have hs := R.sampled_energy_sum τ x hx
    have ht := R.inserted_energy_sum τ x
    have hY := (hy τ).2
    have hC := (hc τ).2
    have hB := henergy x hx τ
    have hL := hl τ
    have hηE : 0 ≤ η * E := mul_nonneg hη.le hE
    nlinarith
  · intro τ
    have hm := (R.insertedMass_bounds τ).1
    have hY := (hy τ).1
    simp only [map_sub, τ.normalized, Complex.sub_re, Complex.one_re] at hY ⊢
    nlinarith


-- @@ L148-148 verbatim
end SampledPackingRound


-- @@ L150-169 verbatim
omit [StarOrderedRing D] [PartialOrder D] in
lemma projection_finset_sum {I : Type uI} (s : Finset I) (t : I → D)
    (ht : ∀ i ∈ s, IsStarProjection (t i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0) :
    IsStarProjection (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsStarProjection.zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, IsStarProjection (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hso : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0 :=
      fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hao : t a * ∑ i ∈ s, t i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact ho a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.sum_insert ha]
    exact (ht a (Finset.mem_insert_self a s)).add (ih hs hso) hao


-- @@ L171-173 verbatim
lemma signed_sum {I : Type uI} {M : Type uM} [Fintype I] [AddCommMonoid M] (f : I × Bool → M) :
    ∑ a, f a = (∑ j, f (j, false)) + ∑ j, f (j, true) := by
  simp [Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]


-- @@ L175-183 verbatim
lemma paired_sum_norm_sub_le {I : Type uI} [Fintype I] (f : I × Bool → ℂ) (t : I → ℂ) :
    ‖(∑ j, f (j, false)) - ∑ j, f (j, true)‖ ≤ ∑ a, ‖f a - t a.1‖ := by
  calc
    _ = ‖(∑ j, (f (j, false) - t j)) - ∑ j, (f (j, true) - t j)‖ := by
      simp only [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ ‖∑ j, (f (j, false) - t j)‖ + ‖∑ j, (f (j, true) - t j)‖ := norm_sub_le _ _
    _ ≤ (∑ j, ‖f (j, false) - t j‖) + ∑ j, ‖f (j, true) - t j‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = _ := (signed_sum (fun a => ‖f a - t a.1‖)).symm


-- @@ L185-185 verbatim
namespace SampledPackingRound


-- @@ L187-187 verbatim
section


-- @@ L189-189 verbatim
variable {r z₀ : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}


-- @@ L191-191 verbatim
variable (R : SampledPackingRound F z₀ K η δ)


-- @@ L193-193 verbatim
def signSum (σ : Bool) : D := ∑ j, R.inserted (j, σ)


-- @@ L195-198 verbatim
omit [StarOrderedRing D] in
lemma signSum_projection (σ : Bool) : IsStarProjection (R.signSum σ) :=
  projection_finset_sum _ _ (fun _ _ => R.inserted_projection _)
    (fun _ _ _ _ h => R.inserted_orthogonal (fun he => h (Prod.mk.inj he).1))


-- @@ L200-207 verbatim
omit [StarOrderedRing D] in
lemma signSum_orthogonal : R.signSum false * R.signSum true = 0 := by
  simp only [signSum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  exact R.inserted_orthogonal (by simp)


-- @@ L209-212 verbatim
omit [StarOrderedRing D] in
lemma initial_signSum_orthogonal (σ : Bool) : z₀ * R.signSum σ = 0 := by
  simp only [signSum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun _ _ => R.initial_orthogonal _


-- @@ L214-218 verbatim
lemma subinitial_signSum_orthogonal {p : D} (hp : IsStarProjection p)
    (hz₀ : IsStarProjection z₀) (hpz : p ≤ z₀) (σ : Bool) : p * R.signSum σ = 0 := by
  calc
    _ = (p * z₀) * R.signSum σ := by rw [(hp.le_iff_mul_eq_left hz₀).mp hpz]
    _ = 0 := by rw [mul_assoc, R.initial_signSum_orthogonal, mul_zero]


-- @@ L220-223 verbatim
omit [StarOrderedRing D] in
lemma final_eq_signSum : R.final = z₀ + (R.signSum false + R.signSum true) := by
  rw [R.final_eq, signed_sum]
  rfl


-- @@ L225-233 verbatim
lemma signSum_energy (τ : Pureness.TracialState D) (x : D) :
    traceTwoNorm τ (x * R.signSum false - R.signSum false * x) ^ 2 +
      traceTwoNorm τ (x * R.signSum true - R.signSum true * x) ^ 2 ≤
      ∑ a, traceTwoNorm τ (x * R.inserted a - R.inserted a * x) ^ 2 := by
  rw [signed_sum]
  apply add_le_add
  all_goals
    exact (orthogonal_sum_energy_le Finset.univ _ (fun _ _ => R.inserted_projection _)
      (fun _ _ _ _ h => R.inserted_orthogonal (fun he => h (Prod.mk.inj he).1)) τ x).2


-- @@ L235-257 verbatim
lemma displacement_sum_le (τ : Pureness.TracialState D) (x : D) (hx : ‖x‖ ≤ 1) :
    (∑ a, ‖τ.functional ((R.inserted a - R.sampled a) * x)‖) ≤
      2 * Real.sqrt (R.sampledMass τ) * Real.sqrt (5 * R.overlap τ) := by
  have hs (a : F.Index × Bool) : 0 ≤ (τ.functional (R.sampled a)).re :=
    (τ.functional.map_nonneg (R.sampled_projection a).nonneg).1
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (F.Index × Bool))
    (fun a => Real.sqrt (τ.functional (R.sampled a)).re)
    (fun a => traceTwoNorm τ (R.inserted a - R.sampled a))
  simp only [Real.sq_sqrt (hs _)] at hcs
  calc
    _ ≤ ∑ a, 2 * Real.sqrt (τ.functional (R.sampled a)).re *
        traceTwoNorm τ (R.inserted a - R.sampled a) :=
      Finset.sum_le_sum fun a _ => (R.bounds a).inserted_linear τ x hx
    _ = 2 * ∑ a, Real.sqrt (τ.functional (R.sampled a)).re *
        traceTwoNorm τ (R.inserted a - R.sampled a) := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ 2 * (Real.sqrt (R.sampledMass τ) *
        Real.sqrt (∑ a, traceTwoNorm τ (R.inserted a - R.sampled a) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      simpa only [← Finset.mul_sum, overlap] using hd


-- @@ L259-287 verbatim
lemma signSum_balance (τ : Pureness.TracialState D) (x : unitary D) (hx : x ∈ K) :
    ‖τ.functional (R.signSum false * (x : D)) - τ.functional (R.signSum true * (x : D))‖ ≤
      η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError +
        2 * Real.sqrt (R.sampledMass τ) * Real.sqrt (5 * R.overlap τ) := by
  have hxu : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have h := paired_sum_norm_sub_le
    (fun a : F.Index × Bool => τ.functional (R.inserted a * (x : D)))
    (fun j => ((η * F.weight j / 2 : ℝ) : ℂ) * τ.functional (F.range j * (x : D)))
  simp only [signSum, Finset.sum_mul, map_sum]
  apply h.trans
  calc
    _ ≤ (∑ a, ‖τ.functional (R.sampled a * (x : D)) -
        ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) +
        ∑ a, ‖τ.functional ((R.inserted a - R.sampled a) * (x : D))‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      have he : τ.functional (R.inserted a * (x : D)) -
          ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D)) =
          (τ.functional (R.sampled a * (x : D)) -
          ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))) +
          τ.functional ((R.inserted a - R.sampled a) * (x : D)) := by
        simp only [sub_mul, map_sub]; abel
      rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (R.sampled_linear_sum τ x hx) (R.displacement_sum_le τ _ hxu)


-- @@ L289-289 verbatim
end


-- @@ L291-291 verbatim
variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}


-- @@ L293-293 verbatim
variable (R : SampledPackingRound F z₀ K η δ)


-- @@ L295-314 verbatim
lemma Estimates.balance {E : ℝ} (H : R.Estimates E) (hη : 0 < η)
    (herror : R.totalError ≤ η ^ 2) (τ : Pureness.TracialState D)
    (x : unitary D) (hx : x ∈ K) :
    ‖τ.functional (R.signSum false * (x : D)) - τ.functional (R.signSum true * (x : D))‖ ≤
      7 * η ^ 2 + 2 * η * Real.sqrt (60 * E + 75 * η) := by
  have hid : Real.sqrt (3 * η) * Real.sqrt (5 * (4 * η * E + 5 * η ^ 2)) =
      η * Real.sqrt (60 * E + 75 * η) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 * η)]
    rw [show 3 * η * (5 * (4 * η * E + 5 * η ^ 2)) = η ^ 2 * (60 * E + 75 * η) by ring]
    rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]
  apply (R.signSum_balance τ x hx).trans
  have hlin : η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError ≤ 7 * η ^ 2 := by
    nlinarith [H.sampled_upper τ, H.target_upper τ]
  calc
    _ ≤ 7 * η ^ 2 + 2 * Real.sqrt (3 * η) * Real.sqrt (5 * (4 * η * E + 5 * η ^ 2)) := by
      apply add_le_add hlin
      gcongr
      · exact H.sampled_upper τ
      · exact H.overlap_upper τ
    _ = _ := by rw [mul_assoc, hid, ← mul_assoc]


-- @@ L316-316 verbatim
end SampledPackingRound


-- @@ L318-323 verbatim
structure OrthogonalProjectionPair (D : Type uD) [CStarAlgebra D] where
  left : D
  right : D
  left_projection : IsStarProjection left
  right_projection : IsStarProjection right
  orthogonal : left * right = 0


-- @@ L325-325 verbatim
namespace OrthogonalProjectionPair


-- @@ L327-327 verbatim
variable (Q : OrthogonalProjectionPair D)


-- @@ L329-329 verbatim
def total : D := Q.left + Q.right


-- @@ L331-332 verbatim
def energy (τ : Pureness.TracialState D) (x : D) : ℝ :=
  traceTwoNorm τ (x * Q.left - Q.left * x) ^ 2 + traceTwoNorm τ (x * Q.right - Q.right * x) ^ 2


-- @@ L334-335 verbatim
def balance (τ : Pureness.TracialState D) (x : D) : ℝ :=
  ‖τ.functional (Q.left * x) - τ.functional (Q.right * x)‖


-- @@ L337-337 verbatim
def remaining (τ : Pureness.TracialState D) : ℝ := (τ.functional (1 - Q.total)).re


-- @@ L339-341 verbatim
omit [PartialOrder D] [StarOrderedRing D] in
lemma total_projection : IsStarProjection Q.total :=
  Q.left_projection.add Q.right_projection Q.orthogonal


-- @@ L343-343 verbatim
lemma left_le_total : Q.left ≤ Q.total := le_add_of_nonneg_right Q.right_projection.nonneg


-- @@ L345-345 verbatim
lemma right_le_total : Q.right ≤ Q.total := le_add_of_nonneg_left Q.left_projection.nonneg


-- @@ L347-349 verbatim
lemma total_energy_le (τ : Pureness.TracialState D) (x : D) :
    traceTwoNorm τ (x * Q.total - Q.total * x) ^ 2 ≤ Q.energy τ x :=
  orthogonal_pair_energy_le τ Q.left_projection Q.right_projection Q.orthogonal x


-- @@ L351-353 verbatim
omit [StarOrderedRing D] in
lemma energy_nonneg (τ : Pureness.TracialState D) (x : D) : 0 ≤ Q.energy τ x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)


-- @@ L355-355 verbatim
variable {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}


-- @@ L357-357 verbatim
variable (R : SampledPackingRound F Q.total K η δ)


-- @@ L359-360 verbatim
lemma right_signSum_orthogonal (σ : Bool) : Q.right * R.signSum σ = 0 :=
  R.subinitial_signSum_orthogonal Q.right_projection Q.total_projection Q.right_le_total σ


-- @@ L362-363 verbatim
lemma left_signSum_orthogonal (σ : Bool) : Q.left * R.signSum σ = 0 :=
  R.subinitial_signSum_orthogonal Q.left_projection Q.total_projection Q.left_le_total σ


-- @@ L365-368 verbatim
lemma signSum_right_orthogonal (σ : Bool) : R.signSum σ * Q.right = 0 := by
  have h := congrArg star (Q.right_signSum_orthogonal R σ)
  simpa only [star_mul, (R.signSum_projection σ).isSelfAdjoint.star_eq,
    Q.right_projection.isSelfAdjoint.star_eq, star_zero] using h


-- @@ L370-377 verbatim
def appendRound : OrthogonalProjectionPair D where
  left := Q.left + R.signSum false
  right := Q.right + R.signSum true
  left_projection := Q.left_projection.add (R.signSum_projection false) (Q.left_signSum_orthogonal R false)
  right_projection := Q.right_projection.add (R.signSum_projection true) (Q.right_signSum_orthogonal R true)
  orthogonal := by
    simp only [add_mul, mul_add, Q.orthogonal, Q.left_signSum_orthogonal R true,
      Q.signSum_right_orthogonal R false, R.signSum_orthogonal, add_zero]


-- @@ L379-382 verbatim
lemma appendRound_total : (Q.appendRound R).total = R.final := by
  rw [R.final_eq_signSum]
  dsimp [appendRound, total]
  abel


-- @@ L384-393 verbatim
lemma appendRound_energy (τ : Pureness.TracialState D) (x : D) :
    (Q.appendRound R).energy τ x ≤ Q.energy τ x +
      ∑ a, traceTwoNorm τ (x * R.inserted a - R.inserted a * x) ^ 2 := by
  have hp := orthogonal_pair_energy_le τ Q.left_projection (R.signSum_projection false)
    (Q.left_signSum_orthogonal R false) x
  have hs := orthogonal_pair_energy_le τ Q.right_projection (R.signSum_projection true)
    (Q.right_signSum_orthogonal R true) x
  have hr := R.signSum_energy τ x
  dsimp [energy, appendRound]
  linarith


-- @@ L395-404 verbatim
lemma appendRound_balance (τ : Pureness.TracialState D) (x : D) :
    (Q.appendRound R).balance τ x ≤ Q.balance τ x +
      ‖τ.functional (R.signSum false * x) - τ.functional (R.signSum true * x)‖ := by
  dsimp [balance, appendRound]
  simp only [add_mul, map_add]
  calc
    _ = ‖(τ.functional (Q.left * x) - τ.functional (Q.right * x)) +
          (τ.functional (R.signSum false * x) - τ.functional (R.signSum true * x))‖ := by
      congr 1; abel
    _ ≤ _ := norm_add_le _ _


-- @@ L406-406 verbatim
end OrthogonalProjectionPair


-- @@ L408-408 verbatim
end


-- @@ L410-410 verbatim
def packingEnergy (η : ℝ) (n : ℕ) : ℝ := η * ((1 + 1000 * η) ^ n - 1)


-- @@ L412-413 verbatim
def packingRemainder (η : ℝ) (n : ℕ) : ℝ :=
  (1 - η) ^ n + 3 * n * η ^ 2 + 3 * packingEnergy η n


-- @@ L415-416 verbatim
def packingBalance (η : ℝ) (n : ℕ) : ℝ :=
  n * (7 * η ^ 2 + 2 * η * Real.sqrt (60 * packingEnergy η n + 75 * η))


-- @@ L418-418 verbatim
@[simp] lemma packingEnergy_zero (η : ℝ) : packingEnergy η 0 = 0 := by simp [packingEnergy]


-- @@ L420-420 verbatim
@[simp] lemma packingRemainder_zero (η : ℝ) : packingRemainder η 0 = 1 := by simp [packingRemainder]


-- @@ L422-422 verbatim
@[simp] lemma packingBalance_zero (η : ℝ) : packingBalance η 0 = 0 := by simp [packingBalance]


-- @@ L424-427 verbatim
lemma packingEnergy_nonneg {η : ℝ} (hη : 0 ≤ η) (n : ℕ) : 0 ≤ packingEnergy η n := by
  apply mul_nonneg hη
  exact sub_nonneg.mpr
    (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg (by norm_num) hη)))


-- @@ L429-432 verbatim
lemma packingEnergy_succ (η : ℝ) (n : ℕ) :
    packingEnergy η (n + 1) = packingEnergy η n + 1000 * η * (packingEnergy η n + η) := by
  simp only [packingEnergy, pow_succ]
  ring


-- @@ L434-438 verbatim
lemma packingEnergy_mono {η : ℝ} (hη : 0 ≤ η) : Monotone (packingEnergy η) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [packingEnergy_succ]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (add_nonneg (packingEnergy_nonneg hη n) hη))


-- @@ L440-444 verbatim
lemma packingRemainder_nonneg {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (n : ℕ) :
    0 ≤ packingRemainder η n := by
  have hE := packingEnergy_nonneg hη n
  dsimp [packingRemainder]
  positivity


-- @@ L446-453 verbatim
lemma packingRemainder_step {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    (1 - η) * packingRemainder η n + 3 * η ^ 2 +
      3 * (1000 * η * (packingEnergy η n + η)) ≤ packingRemainder η (n + 1) := by
  have hE := packingEnergy_nonneg hη n
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 ≤ η * (3 * n * η ^ 2 + 3 * packingEnergy η n) := by positivity
  simp only [packingRemainder, packingEnergy_succ, Nat.cast_add, Nat.cast_one, pow_succ]
  nlinarith


-- @@ L455-462 verbatim
lemma packingBalance_step {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    packingBalance η n + (7 * η ^ 2 + 2 * η * Real.sqrt (60 * packingEnergy η n + 75 * η)) ≤
      packingBalance η (n + 1) := by
  have hE := packingEnergy_mono hη (Nat.le_succ n)
  simp only [packingBalance, Nat.cast_add, Nat.cast_one]
  calc
    _ = (n + 1 : ℝ) * (7 * η ^ 2 + 2 * η * Real.sqrt (60 * packingEnergy η n + 75 * η)) := by ring
    _ ≤ _ := by gcongr


-- @@ L464-474 verbatim
lemma packingEnergy_exp_bound {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    packingEnergy η n ≤ η * Real.exp (1000 * (n * η)) := by
  have hp : (1 + 1000 * η) ^ n ≤ Real.exp (1000 * η) ^ n := by
    gcongr
    simpa only [add_comm (1000 * η) 1] using Real.add_one_le_exp (1000 * η)
  rw [← Real.exp_nat_mul] at hp
  dsimp [packingEnergy]
  apply mul_le_mul_of_nonneg_left _ hη
  have he : (n : ℝ) * (1000 * η) = 1000 * (n * η) := by ring
  rw [he] at hp
  linarith


-- @@ L476-483 verbatim
lemma packing_decay_exp_bound {η : ℝ} (hη1 : η ≤ 1) (n : ℕ) :
    (1 - η) ^ n ≤ Real.exp (-((n : ℝ) * η)) := by
  have hp : (1 - η) ^ n ≤ (Real.exp (-η)) ^ n := by
    apply pow_le_pow_left₀ (sub_nonneg.mpr hη1)
    have h := Real.add_one_le_exp (-η)
    linarith
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_neg] using hp


-- @@ L485-485 verbatim
variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]


-- @@ L487-488 verbatim
def mapUnitary (ι : A →⋆ₐ[ℂ] D) (x : unitary A) : unitary D :=
  ⟨ι (x : A), Unitary.map_mem ι x.property⟩


-- @@ L490-491 verbatim
@[simp] lemma mapUnitary_coe (ι : A →⋆ₐ[ℂ] D) (x : unitary A) :
    (mapUnitary ι x : D) = ι (x : A) := rfl


-- @@ L493-501 verbatim
lemma map_weightedAverage {I : Type uI} [Fintype I] (ι : A →⋆ₐ[ℂ] D)
    (w : I → ℝ) (v : I → A) (a : A) :
    ι (weightedAverage w v a) = weightedAverage w (fun i => ι (v i)) (ι a) := by
  simp only [weightedAverage, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = w i • ι (v i * a * star (v i)) := ι.toLinearMap.map_smul_of_tower (w i) _
    _ = _ := by rw [map_mul, map_mul, map_star]


-- @@ L503-507 verbatim
lemma map_average_defect {I : Type uI} [Fintype I] (ι : A →⋆ₐ[ℂ] D)
    (w : I → ℝ) (v : I → A) :
    ‖1 - weightedAverage w (fun i => ι (v i)) 1‖ ≤ ‖1 - weightedAverage w v 1‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le ι (1 - weightedAverage w v 1)
  simpa only [map_sub, map_one, map_weightedAverage] using h


-- @@ L509-509 verbatim
variable [PartialOrder D] [StarOrderedRing D]


-- @@ L511-542 verbatim
lemma relative_coefficient_tests {I : Type uI} [Fintype I] (ι : A →⋆ₐ[ℂ] D)
    (v : I → A) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ L : Finset (unitary A), ∀ z : D, ∀ τ : Pureness.TracialState D, ∀ E : ℝ, 0 ≤ E →
      (∀ x ∈ L, traceTwoNorm τ (z * ι (x : A) - ι (x : A) * z) ^ 2 ≤ E) →
      ∀ i, traceTwoNorm τ (z * ι (v i) - ι (v i) * z) ^ 2 ≤ 4 * E := by
  classical
  choose u c he hc using fun i => CStarAlgebra.exists_sum_four_unitary (v i)
  let L := Finset.univ.biUnion fun i : I => Finset.univ.image (u i)
  refine ⟨L, ?_⟩
  intro z τ E hE ht i
  have hub (j : Fin 4) : traceTwoNorm τ (z * ι (u i j : A) - ι (u i j : A) * z) ≤ Real.sqrt E :=
    (Real.le_sqrt (traceTwoNorm_nonneg τ _) hE).mpr
      (ht _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩))
  have hdecomp : z * ι (v i) - ι (v i) * z =
      ∑ j, c i j • (z * ι (u i j : A) - ι (u i j : A) * z) := by
    rw [he i, map_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_sub]
  have hn : traceTwoNorm τ (z * ι (v i) - ι (v i) * z) ≤ 2 * Real.sqrt E := by
    rw [hdecomp]
    apply (traceTwoNorm_sum_le _ τ _).trans
    simp_rw [traceTwoNorm_smul]
    calc
      _ ≤ ∑ j : Fin 4, (1 / 2 : ℝ) * Real.sqrt E := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul ((hc i j).trans (by linarith [hv i])) (hub j)
          (traceTwoNorm_nonneg τ _) (by norm_num)
      _ = _ := by simp; ring
  have hsq := (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (by positivity : 0 ≤ 2 * Real.sqrt E)).mpr hn
  rw [mul_pow, Real.sq_sqrt hE] at hsq
  norm_num at hsq ⊢
  exact hsq


-- @@ L544-544 verbatim
end CurrentMain


-- @@ L546-546 verbatim
end


-- @@ L548-548 verbatim
end OAI
