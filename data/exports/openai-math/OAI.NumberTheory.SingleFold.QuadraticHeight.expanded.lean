import OAI.NumberTheory.SingleFold.EllipticHeight


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SingleFold.QuadraticLimit


-- @@ L7-7 verbatim
universe u


-- @@ L9-9 verbatim
open Filter Topology


-- @@ L11-11 verbatim
variable {A : Type u} [AddCommGroup A]


-- @@ L13-14 verbatim
noncomputable def sequence (h : A → ℝ) (P : A) (n : ℕ) : ℝ :=
  (1/4 : ℝ)^n * h ((2^n) • P)


-- @@ L16-16 verbatim
variable (h : A → ℝ) (C : ℝ)

-- @@ L17-17 verbatim
variable (hzero : h 0 = 0)

-- @@ L18-18 verbatim
variable (hpara : ∀ P Q, |h (P+Q)+h (P-Q)-2*(h P+h Q)| ≤ C)


-- @@ L20-37 verbatim
include hzero hpara in
lemma step_bound (P : A) (n : ℕ) :
    dist (sequence h P n) (sequence h P (n+1)) ≤ (C/4)*(1/4:ℝ)^n := by
  have hb := hpara ((2^n) • P) ((2^n) • P)
  rw [sub_self, hzero, add_zero] at hb
  have hd : (2^(n+1)) • P = (2^n) • P + (2^n) • P := by
    rw [pow_succ, mul_comm, mul_nsmul, two_nsmul, nsmul_add]
  rw [Real.dist_eq, sequence, sequence, hd, pow_succ]
  have he : (1/4:ℝ)^n * h ((2^n) • P) -
      ((1/4:ℝ)^n * (1/4)) * h ((2^n) • P + (2^n) • P) =
      -((1/4:ℝ)^n / 4) *
        (h ((2^n) • P + (2^n) • P) - 2*(h ((2^n) • P)+h ((2^n) • P))) := by ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  calc
    (1/4:ℝ)^n / 4 * |h ((2^n) • P + (2^n) • P) -
        2*(h ((2^n) • P)+h ((2^n) • P))| ≤ (1/4:ℝ)^n / 4 * C :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring


-- @@ L39-41 verbatim
include hzero hpara in
lemma sequence_cauchy (P : A) : CauchySeq (sequence h P) :=
  cauchySeq_of_le_geometric (1/4:ℝ) (C/4) (by norm_num) (step_bound h C hzero hpara P)


-- @@ L43-43 verbatim
noncomputable def limit (h : A → ℝ) (P : A) : ℝ := limUnder atTop (sequence h P)


-- @@ L45-47 verbatim
include hzero hpara in
lemma tendsto_sequence (P : A) : Tendsto (sequence h P) atTop (𝓝 (limit h P)) :=
  (sequence_cauchy h C hzero hpara P).tendsto_limUnder


-- @@ L49-54 verbatim
include hzero hpara in
lemma error_bound (P : A) : |h P - limit h P| ≤ C/3 := by
  have hh := dist_le_of_le_geometric_of_tendsto₀ (1/4:ℝ) (C/4) (by norm_num)
    (step_bound h C hzero hpara P) (tendsto_sequence h C hzero hpara P)
  norm_num [sequence, Real.dist_eq] at hh
  linarith


-- @@ L56-61 verbatim
include hzero hpara in
lemma limit_zero : limit h (0:A) = 0 := by
  apply tendsto_nhds_unique (tendsto_sequence h C hzero hpara 0)
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)) using 1
  ext n
  simp [sequence, hzero]


-- @@ L63-66 verbatim
include hzero hpara in
lemma limit_nonneg (hnonneg : ∀ P, 0 ≤ h P) (P : A) : 0 ≤ limit h P := by
  exact ge_of_tendsto (tendsto_sequence h C hzero hpara P)
    (Eventually.of_forall fun n => mul_nonneg (by positivity) (hnonneg _))


-- @@ L68-93 verbatim
include hzero hpara in
lemma limit_parallelogram (P Q : A) :
    limit h (P+Q)+limit h (P-Q) = 2*(limit h P+limit h Q) := by
  let f : ℕ → ℝ := fun n => sequence h (P+Q) n + sequence h (P-Q) n -
    2*(sequence h P n + sequence h Q n)
  have hf : Tendsto f atTop (𝓝 (limit h (P+Q)+limit h (P-Q)-
      2*(limit h P+limit h Q))) :=
    ((tendsto_sequence h C hzero hpara (P+Q)).add
      (tendsto_sequence h C hzero hpara (P-Q))).sub
      (tendsto_const_nhds.mul ((tendsto_sequence h C hzero hpara P).add
        (tendsto_sequence h C hzero hpara Q)))
  have hbound (n : ℕ) : |f n| ≤ C*(1/4:ℝ)^n := by
    have hp := hpara ((2^n) • P) ((2^n) • Q)
    have he : f n = (1/4:ℝ)^n * (h ((2^n) • P + (2^n) • Q) +
        h ((2^n) • P - (2^n) • Q) - 2*(h ((2^n) • P)+h ((2^n) • Q))) := by
      dsimp [f, sequence]
      rw [nsmul_add, nsmul_sub]
      ring
    rw [he, abs_mul, abs_of_nonneg (by positivity), mul_comm C]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hz : Tendsto (fun n : ℕ => C*(1/4:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1/4:ℝ) < 1)).const_mul C
  have hf0 : Tendsto f atTop (𝓝 0) := squeeze_zero_norm (fun n => hbound n) hz
  have := tendsto_nhds_unique hf hf0
  linarith


-- @@ L95-106 verbatim
include hzero hpara in
lemma limit_nsmul (P : A) (n : ℕ) : limit h (n • P) = (n:ℝ)^2 * limit h P := by
  induction n using Nat.twoStepInduction with
  | zero => simp [limit_zero h C hzero hpara]
  | one => simp
  | more n hn hn1 =>
    have hp := limit_parallelogram h C hzero hpara ((n+1) • P) P
    have ha : (n+1) • P + P = (n+2) • P := by simp [add_nsmul]; abel
    have hs : (n+1) • P - P = n • P := by simp [add_nsmul]
    rw [ha, hs, hn, hn1] at hp
    push_cast at hp ⊢
    nlinarith


-- @@ L108-112 verbatim
include hzero hpara in
lemma limit_neg (P : A) : limit h (-P) = limit h P := by
  have hp := limit_parallelogram h C hzero hpara 0 P
  simp only [zero_add, zero_sub, limit_zero h C hzero hpara, zero_add] at hp
  linarith


-- @@ L114-123 verbatim
include hzero hpara in
lemma limit_zsmul (P : A) (n : ℤ) : limit h (n • P) = (n:ℝ)^2 * limit h P := by
  cases n with
  | ofNat n => simpa using limit_nsmul h C hzero hpara P n
  | negSucc n =>
    rw [Int.negSucc_eq, neg_smul, limit_neg h C hzero hpara]
    rw [← Nat.cast_add_one, natCast_zsmul]
    rw [limit_nsmul h C hzero hpara]
    push_cast
    ring


-- @@ L125-125 verbatim
end SingleFold.QuadraticLimit


-- @@ L127-127 verbatim
namespace SingleFold.CurveHeight


-- @@ L129-129 verbatim
open WeierstrassCurve.Affine.Point

-- @@ L130-130 verbatim
open Filter Topology


-- @@ L132-134 verbatim
@[simp] lemma naiveHeight_zero : naiveHeight (0:E.Point) = 0 := by
  rw [naiveHeight, xRep_zero, Height.logHeight_swap, ← Height.logHeight₁_eq_logHeight]
  simp


-- @@ L136-136 verbatim
lemma naiveHeight_nonneg (P : E.Point) : 0 ≤ naiveHeight P := Height.logHeight_nonneg _


-- @@ L138-140 verbatim
lemma naiveHeight_some {x y : ℚ} (h : E.Nonsingular x y) :
    naiveHeight (some x y h) = Real.log (max x.num.natAbs x.den : ℕ) := by
  rw [naiveHeight, xRep_some, ← Height.logHeight₁_eq_logHeight, Rat.logHeight₁_eq_log_max]


-- @@ L142-150 verbatim
lemma finite_x_fiber (x : ℚ) : {P : E.Point | P.xRep = ![x,1]}.Finite := by
  by_cases hn : {P : E.Point | P.xRep = ![x,1]}.Nonempty
  · obtain ⟨P,hP⟩ := hn
    apply (Set.finite_singleton P |>.union (Set.finite_singleton (-P))).subset
    intro Q hQ
    have he := xRep_eq_xRep_iff.mp (hQ.trans hP.symm)
    simpa [or_comm] using he
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty


-- @@ L152-165 verbatim
instance : Northcott naiveHeight where
  finite_le B := by
    have hs := Northcott.finite_le (h := Height.logHeight₁ (K := ℚ)) B
    have ht := hs.biUnion (fun x _ => finite_x_fiber x)
    apply (Set.finite_singleton (0:E.Point) |>.union ht).subset
    intro P hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      right
      apply Set.mem_iUnion.mpr
      refine ⟨x, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · simpa [naiveHeight, ← Height.logHeight₁_eq_logHeight] using hP
      · exact xRep_some h


-- @@ L167-168 verbatim
noncomputable def canonicalHeight (P : E.Point) : ℝ :=
  (1/2:ℝ) * QuadraticLimit.limit naiveHeight P


-- @@ L170-175 verbatim
lemma canonicalHeight_limit (P : E.Point) :
    Tendsto (fun n : ℕ => (1/2:ℝ) * (1/4:ℝ)^n * naiveHeight ((2^n) • P))
      atTop (𝓝 (canonicalHeight P)) := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  simpa [canonicalHeight, QuadraticLimit.sequence, mul_assoc] using
    (QuadraticLimit.tendsto_sequence naiveHeight C naiveHeight_zero hC P).const_mul (1/2:ℝ)


-- @@ L177-180 verbatim
lemma canonicalHeight_nonneg (P : E.Point) : 0 ≤ canonicalHeight P := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  exact mul_nonneg (by norm_num)
    (QuadraticLimit.limit_nonneg naiveHeight C naiveHeight_zero hC naiveHeight_nonneg P)


-- @@ L182-184 verbatim
@[simp] lemma canonicalHeight_zero : canonicalHeight (0:E.Point) = 0 := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  simp [canonicalHeight, QuadraticLimit.limit_zero naiveHeight C naiveHeight_zero hC]


-- @@ L186-191 verbatim
lemma canonicalHeight_zsmul (P : E.Point) (n : ℤ) :
    canonicalHeight (n • P) = (n:ℝ)^2 * canonicalHeight P := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  unfold canonicalHeight
  rw [QuadraticLimit.limit_zsmul naiveHeight C naiveHeight_zero hC]
  ring


-- @@ L193-195 verbatim
lemma canonicalHeight_nsmul (P : E.Point) (n : ℕ) :
    canonicalHeight (n • P) = (n:ℝ)^2 * canonicalHeight P := by
  simpa using canonicalHeight_zsmul P (n:ℤ)


-- @@ L197-207 verbatim
theorem uniform_height : ∃ c : ℝ, 0 < c ∧ ∀ P : E.Point,
    |naiveHeight P - 2*canonicalHeight P| ≤ c := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  refine ⟨|C|/3+1, by positivity, ?_⟩
  intro P
  have hh := QuadraticLimit.error_bound naiveHeight C naiveHeight_zero hC P
  have he : 2*canonicalHeight P = QuadraticLimit.limit naiveHeight P := by
    unfold canonicalHeight
    ring
  rw [he]
  exact hh.trans (by linarith [le_abs_self C])


-- @@ L209-220 verbatim
theorem canonicalHeight_pos {P : E.Point} (hP : ¬IsOfFinAddOrder P) :
    0 < canonicalHeight P := by
  by_contra hn
  have hz : canonicalHeight P = 0 := le_antisymm (le_of_not_gt hn) (canonicalHeight_nonneg P)
  obtain ⟨c,hc,hbound⟩ := uniform_height
  have hm (n : ℕ) : naiveHeight (n • P) ≤ c := by
    have hh := hbound (n • P)
    rw [canonicalHeight_nsmul, hz, mul_zero, mul_zero, sub_zero] at hh
    exact (le_abs_self _).trans hh
  have hi : Function.Injective (fun n : ℕ => n • P) :=
    (injective_nsmul_iff_not_isOfFinAddOrder).mpr hP
  exact (Set.infinite_of_injective_forall_mem hi hm) (Northcott.finite_le c)


-- @@ L222-222 verbatim
end SingleFold.CurveHeight


-- @@ L224-224 verbatim
end OAI
