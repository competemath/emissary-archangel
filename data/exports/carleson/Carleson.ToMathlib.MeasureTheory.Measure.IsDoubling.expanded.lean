module

public import Carleson.ToMathlib.CoveredByBalls
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
open MeasureTheory Measure NNReal Metric Filter Topology TopologicalSpace

-- @@ L9-9 verbatim
open ENNReal hiding one_lt_two

-- @@ L10-13 verbatim
noncomputable section

-- Upstreaming status: we want this in mathlib in principle, but a fair amount of polish is
-- possible and needed. Move one lemma, streamline proofs (and perhaps add further documentation).


-- @@ L15-15 verbatim
section Doubling


-- @@ L17-18 verbatim
/-- The blow-up factor of repeatedly increasing the size of balls. -/
def As (A : ℝ≥0) (s : ℝ) : ℝ≥0 := A ^ ⌈Real.logb 2 s⌉₊


-- @@ L20-20 verbatim
end Doubling


-- @@ L22-24 verbatim
namespace MeasureTheory

-- `MeasureTheory.Measure.IsDoubling` is defined in `Defs.lean`


-- @@ L26-26 verbatim
section PseudoMetric


-- @@ L28-28 verbatim
variable {X : Type*} [PseudoMetricSpace X]


-- @@ L30-33 verbatim
lemma ball_subset_ball_of_le {x x' : X} {r r' : ℝ}
    (hr : dist x x' + r' ≤ r) : ball x' r' ⊆ ball x r := by
  rw [dist_comm, add_comm] at hr
  exact ball_subset_ball' hr


-- @@ L35-41 verbatim
lemma dist_lt_of_not_disjoint_ball {x x' : X} {r r' : ℝ} (hd : ¬Disjoint (ball x r) (ball x' r')) :
    dist x x' < r + r' := by
  obtain ⟨y, dy₁, dy₂⟩ := Set.not_disjoint_iff.mp hd
  rw [mem_ball] at dy₁ dy₂
  calc
    _ ≤ dist y x + dist y x' := dist_triangle_left ..
    _ < _ := by gcongr


-- @@ L43-53 verbatim
lemma eq_zero_of_isDoubling_zero [MeasurableSpace X] (μ : Measure X) [hμ : μ.IsDoubling 0] :
    μ = 0 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · exact eq_zero_of_isEmpty μ
  have M (r : ℝ) : μ (ball x r) = 0 := by
    have := hμ.measure_ball_two_le_same x (r / 2)
    simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at this
    convert this
    ring
  rw [← measure_univ_eq_zero, ← iUnion_ball_nat x]
  exact measure_iUnion_null_iff.mpr fun i ↦ M ↑i


-- @@ L55-55 verbatim
variable {A : ℝ≥0} [MeasurableSpace X] {μ : Measure X} [μ.IsDoubling A]


-- @@ L57-75 verbatim
variable (μ) in
lemma eq_zero_of_isDoubling_lt_one [ProperSpace X] [IsFiniteMeasureOnCompacts μ] (hA : A < 1) :
    μ = 0 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · simp [eq_zero_of_isEmpty μ]
  have M (r : ℝ) (hr : 0 ≤ r) : μ (ball x r) = 0 := by
    have I : μ (ball x r) ≤ A * μ (ball x r) := calc
      _ = μ (ball x (2 * (r / 2))) := by
        have : 2 * (r / 2) = r := by ring
        simp [this]
      _ ≤ A * μ (ball x (r / 2)) := by
        apply measure_ball_two_le_same (μ := μ)
      _ ≤ A * μ (ball x r) := by gcongr; linarith
    by_contra H
    have : μ (ball x r) < 1 * μ (ball x r) := by
      apply I.trans_lt (ENNReal.mul_lt_mul_left H measure_ball_lt_top.ne (mod_cast hA))
    simp at this
  rw [← measure_univ_eq_zero, ← iUnion_ball_nat x]
  exact measure_iUnion_null_iff.mpr fun i ↦ M i (by positivity)


-- @@ L77-82 verbatim
lemma IsDoubling.mono {A'} (h : A ≤ A') : IsDoubling μ A' where
  measure_ball_two_le_same := by
    intro x r
    calc μ (Metric.ball x (2 * r))
      _ ≤ A * μ (Metric.ball x r) := measure_ball_two_le_same _ _
      _ ≤ A' * μ (Metric.ball x r) := by gcongr


-- @@ L84-90 verbatim
lemma measure_ball_two_le_same_iterate (x : X) (r : ℝ) (n : ℕ) :
    μ (ball x ((2 ^ n) * r)) ≤ A ^ n * μ (ball x r) := by
  induction n with
  | zero => simp
  | succ m ih =>
      simp_rw [add_comm m 1, pow_add, pow_one, mul_assoc]
      exact le_trans (measure_ball_two_le_same x _) (mul_le_mul_right ih A)


-- @@ L92-96 verbatim
lemma measure_ball_four_le_same (x : X) (r : ℝ) :
    μ (ball x (4 * r)) ≤ A ^ 2 * μ (ball x r) := by
  convert measure_ball_two_le_same_iterate x r 2
  · norm_num
  · infer_instance


-- @@ L98-114 verbatim
lemma measure_ball_le_same (x : X) {r s r' : ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
    μ (ball x r') ≤ As A s * μ (ball x r) := by
  /- If the large ball is empty, all balls are -/
  by_cases! hr : r < 0
  · have hr' : r' < 0 := by
      calc r' ≤ s * r := hs
      _ < 0 := mul_neg_of_pos_of_neg hsp hr
    simp [ball_eq_empty.mpr hr.le, ball_eq_empty.mpr hr'.le]
  /- Show inclusion in larger ball -/
  have haux : s * r ≤ 2 ^ ⌈Real.logb 2 s⌉₊ * r := by
    gcongr
    apply Real.le_pow_natCeil_logb (by norm_num) hsp
  have h1 : ball x r' ⊆ ball x (2 ^ ⌈Real.logb 2 s⌉₊ * r) := ball_subset_ball <| hs.trans haux
  /- Apply result for power of two to slightly larger ball -/
  calc μ (ball x r')
      ≤ μ (ball x (2 ^ ⌈Real.logb 2 s⌉₊ * r)) := by gcongr
    _ ≤ As A s * μ (ball x r) := measure_ball_two_le_same_iterate x r _


-- @@ L116-122 verbatim
lemma measure_ball_le_of_dist_le' {x x' : X} {r r' s : ℝ} (hs : 0 < s)
    (h : dist x x' + r' ≤ s * r) :
    μ (ball x' r') ≤ As A s * μ (ball x r) := by
  calc
    μ (ball x' r')
      ≤ μ (ball x (dist x x' + r')) := by gcongr; exact ball_subset_ball_of_le le_rfl
    _ ≤ As A s * μ (ball x r) := measure_ball_le_same x hs h


-- @@ L124-142 verbatim
include A in
variable (μ) in
lemma isOpenPosMeasure_of_isDoubling [NeZero μ] : IsOpenPosMeasure μ := by
  refine ⟨fun U hU ⟨x, hx⟩ h3U ↦ ?_⟩
  obtain ⟨r, hr, hx⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨r', h⟩ : ∃ r', μ (ball x r') ≠ 0 := by
    have hμ := NeZero.ne μ
    rw [← measure_univ_ne_zero, ← Metric.iUnion_ball_nat x, ne_eq,
      measure_iUnion_null_iff, not_forall] at hμ
    obtain ⟨n, hn⟩ := hμ
    exact ⟨n, hn⟩
  have hr' : 0 < r' := by
    by_contra! hr'
    simp [hr', Metric.ball_eq_empty.mpr] at h
  refine h (nonpos_iff_eq_zero.mp ?_)
  calc
    μ (ball x r') ≤ As A (r' / r) * μ (ball x r) := by -- error if not in tactic mode
        exact measure_ball_le_same x (by positivity) (div_mul_cancel₀ _ hr.ne').ge
      _ = 0 := by rw [measure_mono_null hx h3U, mul_zero]


-- @@ L144-173 verbatim
instance : IsUnifLocDoublingMeasure (μ : Measure X) where
  exists_measure_closedBall_le_mul'' := by
    use max 1 A^2, Set.univ, by simp, Set.univ
    simp only [mem_principal, Set.subset_univ, Set.inter_self, true_and]
    ext r
    simp only [ENNReal.coe_pow, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro x
    let : Nonempty X := ⟨x⟩
    by_cases hr : r ≤ 0
    · have cball_eq : closedBall x (2 * r) = closedBall x r:= by
        by_cases! hr' : r < 0
        · have : 2 * r < 0 := by linarith
          simp [*]
        · simp [le_antisymm hr hr']
      rw [cball_eq]
      nth_rw 1 [← one_mul (μ (closedBall x r))]
      gcongr
      have : (1 : ℝ≥0∞) ≤ (max 1 A : ℝ≥0) := by simp
      rw [← one_mul 1, pow_two]
      gcongr
    · calc
        μ (closedBall x (2 * r))
          ≤ μ (ball x (2 * (2 * r))) := μ.mono (closedBall_subset_ball (by linarith))
        _ ≤ A * μ (ball x (2 * r)) := measure_ball_two_le_same x (2 * r)
        _ ≤ A * (A * μ (ball x r)) := by gcongr; exact measure_ball_two_le_same x r
        _ = ↑(A ^ 2) * μ (ball x r) := by simp only [pow_two, coe_mul, mul_assoc]
        _ ≤ ↑(A ^ 2) * μ (closedBall x r) := by gcongr; exact ball_subset_closedBall
        _ ≤ ↑(max 1 A ^ 2) * μ (closedBall x r) := by gcongr; exact le_max_right 1 A

-- todo: move

-- @@ L174-181 verbatim
lemma Nat.exists_max_image {α : Type*} {s : Set α} (hs : s.Nonempty)
    {f : α → ℕ} (h : BddAbove (f '' s)) : ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
  let n := sSup (f '' s)
  obtain ⟨x, hx, h2x⟩ : n ∈ f '' s := Nat.sSup_mem (hs.image f) h
  use x, hx
  simp_rw [h2x, n]
  intro y hy
  exact le_csSup h <| Set.mem_image_of_mem f hy


-- @@ L183-195 verbatim
include A in
lemma IsDoubling.measure_ball_lt_top [IsLocallyFiniteMeasure μ] {x : X} {r : ℝ} :
    μ (ball x r) < ∞ := by
  obtain hr | hr := le_or_gt r 0
  · simp [Metric.ball_eq_empty.mpr hr]
  obtain ⟨U, hxU, hU, h2U⟩ := exists_isOpen_measure_lt_top μ x
  obtain ⟨ε, hε, hx⟩ := Metric.isOpen_iff.mp hU x hxU
  have : μ (ball x ε) < ∞ := measure_mono hx |>.trans_lt h2U
  calc
    μ (ball x r) ≤ As A (r / ε) * μ (ball x ε) := by
        apply measure_ball_le_same x (by positivity)
        rw [div_mul_cancel₀ _ hε.ne']
    _ < ∞ := by finiteness


-- @@ L197-289 verbatim
include μ in
variable (μ) in
lemma IsDoubling.allBallsCoverBalls [OpensMeasurableSpace X] [NeZero μ]
    [IsLocallyFiniteMeasure μ] : AllBallsCoverBalls X 2 ⌈As A 9⌉₊ := by
  classical
  have := isOpenPosMeasure_of_isDoubling μ
  have hA : A ≠ 0 := by
    rintro rfl
    exact NeZero.ne μ <| eq_zero_of_isDoubling_zero μ
  refine .mk (by norm_num) fun r hr x ↦ ?_
  set R := 2 * r
  set R' := R + r / 2
  set N : ℕ := ⌈As A 9⌉₊
  let S := { s : Finset X | ↑s ⊆ ball x R ∧ ∀ x y, x ∈ s → y ∈ s → x ≠ y → r ≤ dist x y }
  have h1 : ∀ s ∈ S, s.card ≤ N := by
    by_contra!
    obtain ⟨s, ⟨h1s, h2s⟩, h3s⟩ := this
    let B := ⋃ y ∈ s, ball y (r / 2)
    have : ∀ y ∈ s, (As A 9 : ℝ≥0∞)⁻¹ * μ (ball x R') ≤ μ (ball y (r / 2)) := by
      intro y hy
      rw [ENNReal.inv_mul_le_iff]
      · apply measure_ball_le_of_dist_le' (by norm_num)
        calc
          dist y x + R' ≤ R + R' := by
            gcongr
            apply le_of_lt
            simpa using h1s hy
          _ ≤ 9 * (r / 2) := by simp_rw [R', R]; linarith
      · simp [As, hA]
      · simp
    have lem : (s : Set X).PairwiseDisjoint fun y ↦ ball y (r / 2) := by
      intro i hi j hj hij
      refine Set.disjoint_left.mpr fun z hzi hzj ↦ ?_
      exact lt_irrefl _ <| by calc
        r ≤ dist i j := h2s i j hi hj hij
        _ ≤ dist i z + dist z j := dist_triangle ..
        _ < r / 2 + r / 2 := by gcongr; exacts [mem_ball'.mp hzi, mem_ball.mp hzj]
        _ = r := by linarith
    exact lt_irrefl _ <| calc
      μ (ball x R') ≤ N * (As A 9 : ℝ≥0∞)⁻¹ * μ (ball x R') := by
          conv_lhs => rw [← one_mul (μ _)]
          gcongr
          rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le, one_mul]
          · simp [N, Nat.le_ceil]
          · simp [As, hA]
          · simp
      _ < s.card * (As A 9 : ℝ≥0∞)⁻¹ * μ (ball x R') := by
          gcongr
          · refine isOpen_ball.measure_ne_zero μ ?_
            have : 0 < R' := by positivity
            simp [this]
          · exact IsDoubling.measure_ball_lt_top.ne
          · simp [As]
          · simp [As, hA]
      _ = ∑ y ∈ s, (As A 9 : ℝ≥0∞)⁻¹ * μ (ball x R') := by
          simp_rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ y ∈ s, μ (ball y (r / 2)) := by gcongr with i hi; exact this i hi
      _ = μ (⋃ y ∈ s, ball y (r / 2)) := by
          rw [measure_biUnion_finset lem]
          intros; apply measurableSet_ball
      _ ≤ μ (ball x R') := by
          apply measure_mono
          simp_rw [Set.iUnion_subset_iff]
          intro i hi z hz
          rw [mem_ball]
          calc
            dist z x ≤ dist z i + dist i x := dist_triangle ..
            _ < r / 2 + R := by simp at hz; gcongr; simpa using h1s hi
            _ = R' := by ring
  have h1' : BddAbove ((·.card) '' S) := by
    simp only [bddAbove_def, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    use N, h1
  have h2 : S.Nonempty := ⟨∅, by simp, by simp⟩
  obtain ⟨s, hs, s_max⟩ := Nat.exists_max_image h2 h1'
  have := hs; obtain ⟨h1s, h2s⟩ := this
  use s, h1 s hs
  intro y hy
  push _ ∈ _
  simp only [mem_ball]
  by_contra! h2y
  have hys : y ∉ s := by intro h3y; simpa [hr.not_ge] using h2y y h3y
  have h2 : insert y s ∈ S := by
    suffices ∀ (x y_1 : X), x = y ∨ x ∈ s → y_1 = y ∨ y_1 ∈ s → ¬x = y_1 → r ≤ dist x y_1 by
      simp [Set.subset_def, -Metric.mem_ball] at h1s
      simp [S] at hs hy
      simp [S, Set.insert_subset_iff, hs, hy, eq_true_intro this]
    rintro u v (rfl|hu) (rfl|hv) huv
    · simp at huv
    · exact h2y v hv
    · rw [dist_comm]; exact h2y u hu
    · exact h2s u v hu hv huv
  specialize s_max (insert y s) h2
  simp [hys] at s_max


-- @@ L291-291 verbatim
variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]


-- @@ L293-298 verbatim
lemma measureReal_ball_two_le_same (x : X) (r : ℝ) :
    μ.real (ball x (2 * r)) ≤ A * μ.real (ball x r) := by
  simp_rw [Measure.real, ← ENNReal.coe_toReal, ← toReal_mul]
  gcongr
  · finiteness
  · exact measure_ball_two_le_same x r


-- @@ L300-306 verbatim
lemma measureReal_ball_two_le_same_iterate (x : X) (r : ℝ) (n : ℕ) :
    μ.real (ball x ((2 ^ n) * r)) ≤ A ^ n * μ.real (ball x r) := by
  induction n with
  | zero => simp
  | succ m ih =>
      simp_rw [add_comm m 1, pow_add, pow_one, mul_assoc]
      exact le_trans (measureReal_ball_two_le_same x _) (by gcongr)


-- @@ L308-310 verbatim
lemma measureReal_ball_pos [μ.IsOpenPosMeasure] (x : X) {r : ℝ} (hr : 0 < r) :
    0 < μ.real (ball x r) :=
  toReal_pos ((measure_ball_pos μ x hr).ne') (measure_ball_lt_top.ne)


-- @@ L312-324 verbatim
variable (μ) in
lemma one_le_A [Nonempty X] [μ.IsOpenPosMeasure] : 1 ≤ A := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have : 0 < μ.real (ball x 1) := measureReal_ball_pos x (by linarith)
  apply le_of_mul_le_mul_right _ this
  simp only [val_eq_coe, NNReal.coe_one, one_mul]
  calc
    μ.real (ball x 1)
      ≤ μ.real (ball x (2 * 1)) := by
        rw [mul_one]
        exact ENNReal.toReal_mono (measure_ball_lt_top.ne)
          (μ.mono (ball_subset_ball (by linarith)))
    _ ≤ A * μ.real (ball x 1) := measureReal_ball_two_le_same x 1


-- @@ L326-330 verbatim
variable (μ) in
lemma A_pos [Nonempty X] [μ.IsOpenPosMeasure] : 0 < A := by
  calc
    0 < 1 := by norm_num
    _ ≤ A := one_le_A μ


-- @@ L332-335 verbatim
variable (μ) in
lemma A_pos' [Nonempty X] [μ.IsOpenPosMeasure] : 0 < (A : ℝ≥0∞) := by
  rw [ENNReal.coe_pos]
  exact A_pos μ


-- @@ L337-339 verbatim
variable (μ) in
lemma As_pos [Nonempty X] [μ.IsOpenPosMeasure] (s : ℝ) : 0 < As A s :=
  pow_pos (A_pos μ) ⌈Real.logb 2 s⌉₊


-- @@ L341-343 verbatim
variable (μ) in
lemma As_pos' [Nonempty X] [μ.IsOpenPosMeasure] (s : ℝ) : 0 < (As A s : ℝ≥0∞) := by
  rw [ENNReal.coe_pos]; exact As_pos μ s


-- @@ L345-351 verbatim
lemma measureReal_ball_four_le_same (x : X) (r : ℝ) :
    μ.real (ball x (4 * r)) ≤ A ^ 2 * μ.real (ball x r) := by
  calc μ.real (ball x (4 * r))
      = μ.real (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * μ.real (ball x (2 * r)) := measureReal_ball_two_le_same ..
    _ ≤ A * (A * μ.real (ball x r)) := by gcongr; exact measureReal_ball_two_le_same ..
    _ = A ^ 2 * μ.real (ball x r) := by ring_nf


-- @@ L353-365 verbatim
lemma measureReal_ball_le_same (x : X) {r s r' : ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
    μ.real (ball x r') ≤ As A s * μ.real (ball x r) := by
  have hz := measure_ball_le_same (μ := μ) x hsp hs
  have hbr': μ (ball x r') ≠ ⊤ := by finiteness
  have hbr: μ (ball x r) ≠ ⊤ := by finiteness
  have hAs : (As A s: ℝ≥0∞) ≠ ⊤ := by finiteness
  rw [← ENNReal.ofReal_toReal hbr, ← ENNReal.ofReal_toReal hbr',
    ← ENNReal.ofReal_toReal hAs, ← ENNReal.ofReal_mul] at hz
  · simp only [coe_toReal] at hz
    rw [← ENNReal.ofReal_le_ofReal_iff]
    · exact hz
    positivity
  · simp only [coe_toReal, zero_le_coe]


-- @@ L367-395 verbatim
/-- Version of `measureReal_ball_le_same` without ceiling function. -/
lemma measureReal_ball_le_same' (x : X) {r t : ℝ} (ht : 0 < t) (h't : t ≤ 1) :
    μ.real (ball x r) ≤ A * t ^ (- Real.logb 2 A) * μ.real (ball x (t * r)) := by
  rcases lt_or_ge A 1 with hA | hA
  · simp [eq_zero_of_isDoubling_lt_one μ hA]
  have : r = t⁻¹ * (t * r) := (eq_inv_mul_iff_mul_eq₀ ht.ne').mpr rfl
  apply (measureReal_ball_le_same x (inv_pos_of_pos ht) this.le).trans
  gcongr
  simp only [As, Real.logb_inv, NNReal.coe_pow]
  have : t = 2 ^ (Real.logb 2 t) := by rw [Real.rpow_logb (by norm_num) (by norm_num) ht]
  conv_rhs => rw [this]
  have : (A : ℝ) = 2 ^ (Real.logb 2 (A : ℝ)) := by
    rw [Real.rpow_logb (by norm_num) (by norm_num)]
    apply zero_lt_one.trans_le hA
  nth_rewrite 1 2 [this]
  rw [← Real.rpow_mul zero_le_two, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
    ← Real.rpow_add zero_lt_two]
  apply (Real.rpow_le_rpow_left_iff one_lt_two).2
  have : (⌈-Real.logb 2 t⌉₊ : ℝ) < -Real.logb 2 t + 1 := by
    apply Nat.ceil_lt_add_one
    simp only [Left.nonneg_neg_iff]
    rw [Real.logb_nonpos_iff one_lt_two ht]
    exact h't
  calc
  Real.logb 2 ↑A * ↑⌈-Real.logb 2 t⌉₊
  _ ≤ Real.logb 2 ↑A * (-Real.logb 2 t + 1) := by
    gcongr
    exact Real.logb_nonneg one_lt_two hA
  _ = _ := by ring


-- @@ L397-401 verbatim
lemma measureNNReal_ball_le_of_dist_le' {x x' : X} {r r' s : ℝ} (hs : 0 < s)
    (h : dist x x' + r' ≤ s * r) :
    (μ (ball x' r')).toNNReal ≤ As A s * (μ (ball x r)).toNNReal := by
  simp only [← ENNReal.coe_le_coe, coe_mul, ENNReal.coe_toNNReal measure_ball_ne_top]
  exact measure_ball_le_of_dist_le' hs h


-- @@ L403-403 verbatim
end PseudoMetric


-- @@ L405-405 verbatim
section Normed


-- @@ L407-407 verbatim
open Module


-- @@ L409-411 verbatim
lemma Subsingleton.ball_eq {α} [PseudoMetricSpace α] [Subsingleton α] {x : α} {r : ℝ} :
    ball x r = if r > 0 then {x} else ∅ := by
  ext y; cases Subsingleton.elim x y; simp


-- @@ L413-421 verbatim
instance InnerProductSpace.IsDoubling {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    IsDoubling (volume : Measure E) (2 ^ finrank ℝ E) where
  measure_ball_two_le_same x r := by
    obtain hE|hE := subsingleton_or_nontrivial E
    · simp_rw [Subsingleton.ball_eq, finrank_zero_of_subsingleton]; simp
    simp_rw [InnerProductSpace.volume_ball, ofReal_mul zero_le_two, ← ENNReal.rpow_natCast,
      ENNReal.mul_rpow_of_ne_top ofReal_ne_top ofReal_ne_top, ENNReal.rpow_natCast, mul_assoc]
    simp


-- @@ L423-423 verbatim
end Normed


-- @@ L425-425 verbatim
end MeasureTheory
