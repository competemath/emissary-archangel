import OAI.Probability.EntangledGames.FiniteProbability


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_ι u_α u_β u_n u_m


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L9-9 verbatim
open Matrix

-- @@ L10-10 verbatim
namespace ThresholdParallelRepetition

-- @@ L11-11 verbatim
namespace ScalarEntropy


-- @@ L13-30 verbatim
lemma negMulLog_subprob {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1)
    (ht : ∀ i, 0 ≤ t i) :
    (∑ i, w i * Real.negMulLog (t i)) ≤ Real.negMulLog (∑ i, w i*t i) := by
  let W : Option ι → ℝ := fun i => i.elim (1-∑ j, w j) w
  let T : Option ι → ℝ := fun i => i.elim 0 t
  have hW : ∀ i, 0 ≤ W i := by
    intro i; cases i with
    | none => exact sub_nonneg.mpr hs
    | some i => exact hw i
  have hsum : ∑ i, W i = 1 := by simp [W, Fintype.sum_option]
  have hT : ∀ i, T i ∈ Set.Ici (0 : ℝ) := by
    intro i; cases i with
    | none => change (0 : ℝ) ≤ 0; rfl
    | some i => exact ht i
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := W) (p := T) (fun i _ => hW i) hsum (fun i _ => hT i)
  simpa [W, T, Fintype.sum_option] using h


-- @@ L32-45 verbatim
lemma hellinger_le_entropy {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t-1)^2 ≤ t*Real.log t-t+1 := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  by_cases hz : t = 0
  · simp [hz]
  have hp : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz))
  have h := Real.self_sub_one_le_mul_log (le_of_lt hp)
  have hl : Real.log t = 2*Real.log (Real.sqrt t) := by
    have he : t = (Real.sqrt t)^2 := hsq.symm
    rw [he, Real.log_pow]
    norm_num
  rw [hl]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr h)]


-- @@ L47-68 verbatim
lemma weighted_negMulLog_le {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ i, w i ≤ d) (hp : 0 < p)
    (hm : ∑ i, w i*t i = p) :
    (∑ i, w i*Real.negMulLog (t i)) ≤ p*Real.log (d/p) := by
  have hw' : ∀ i, 0 ≤ w i/d := fun i => div_nonneg (hw i) hd.le
  have hs' : ∑ i, w i/d ≤ 1 := by rw [← Finset.sum_div]; exact (div_le_one hd).mpr hs
  have h := negMulLog_subprob (fun i => w i/d) t hw' hs' ht
  have hm' : (∑ i, w i/d*t i) = p/d := by
    simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div, hm]
  rw [hm'] at h
  have hleft : (∑ i, w i/d*Real.negMulLog (t i)) =
      (∑ i, w i*Real.negMulLog (t i))/d := by
    simp_rw [div_mul_eq_mul_div]; rw [Finset.sum_div]
  rw [hleft] at h
  have h := (div_le_iff₀ hd).mp h
  have he : Real.negMulLog (p/d)*d = p*Real.log (d/p) := by
    change -(p/d)*Real.log (p/d)*d = p*Real.log (d/p)
    rw [Real.log_div hp.ne' hd.ne', Real.log_div hd.ne' hp.ne']
    field_simp
    ring
  exact h.trans_eq he


-- @@ L70-70 verbatim
open FiniteProbability

-- @@ L71-71 verbatim
variable {α : Type u_α} {β : Type u_β} [Fintype α] [Fintype β]


-- @@ L73-84 verbatim
lemma avg_entropy_jensen (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    p.avg f * Real.log (p.avg f) ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := negMulLog_subprob p.weight f p.nonneg p.total.le hf
  change -(∑ x, p.weight x*f x)*Real.log (∑ x, p.weight x*f x) ≥ _ at h
  have he : (∑ x, p.weight x*Real.negMulLog (f x)) =
      -(p.avg (fun x => f x*Real.log (f x))) := by
    simp only [Real.negMulLog_def, Law.avg, smul_eq_mul, mul_neg, ← mul_assoc, neg_mul,
      Finset.sum_neg_distrib]
  rw [he] at h
  change p.avg f*Real.log (p.avg f) ≤ _
  dsimp only [Law.avg, smul_eq_mul] at *
  linarith


-- @@ L86-89 verbatim
lemma avg_entropy_nonneg (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ht : p.avg f = 1) : 0 ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := avg_entropy_jensen p f hf
  simpa [ht] using h


-- @@ L91-101 verbatim
lemma avg_hellinger_le_entropy (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ht : p.avg f = 1) :
    p.avg (fun x => (Real.sqrt (f x)-1)^2) ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := p.avg_mono fun x => hellinger_le_entropy (hf x)
  have he : p.avg (fun x => f x*Real.log (f x)-f x+1) =
      p.avg (fun x => f x*Real.log (f x)) := by
    simp only [Law.avg, smul_eq_mul, mul_add, mul_sub, mul_one,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, p.total]
    change _ - p.avg f + 1 = _
    rw [ht]; ring
  exact h.trans_eq he


-- @@ L103-109 verbatim
lemma first_density_entropy_le [DecidableEq β] (p : Law (α×β)) (b₀ : β)
    (f : α×β → ℝ) (hf : ∀ z, 0 ≤ f z) :
    p.first.avg (fun x => (p.givenFirst b₀ x).avg (fun y => f (x,y)) *
      Real.log ((p.givenFirst b₀ x).avg (fun y => f (x,y)))) ≤
      p.avg (fun z => f z*Real.log (f z)) := by
  rw [Law.disintegrate_first p b₀]
  exact p.first.avg_mono fun x => avg_entropy_jensen _ _ (fun y => hf (x,y))


-- @@ L111-117 verbatim
lemma second_density_entropy_le [DecidableEq α] (p : Law (α×β)) (a₀ : α)
    (f : α×β → ℝ) (hf : ∀ z, 0 ≤ f z) :
    p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y)) *
      Real.log ((p.givenSecond a₀ y).avg (fun x => f (x,y)))) ≤
      p.avg (fun z => f z*Real.log (f z)) := by
  rw [Law.disintegrate_second p a₀]
  exact p.second.avg_mono fun y => avg_entropy_jensen _ _ (fun x => hf (x,y))


-- @@ L119-119 verbatim
end ScalarEntropy

-- @@ L120-120 verbatim
namespace OperatorEntropy

-- @@ L121-121 verbatim
open Resolvent QuantumSampling

-- @@ L122-122 verbatim
variable {n : Type u_n} [Fintype n] [DecidableEq n]


-- @@ L124-136 verbatim
lemma effectEntropy_nonpos {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    effectEntropy A ≤ 0 := by
  rw [effectEntropy]
  have hz : cfc (fun _ : ℝ => (0 : ℝ)) A = 0 := by simp
  rw [← hz]
  apply (cfc_le_iff _ _ A (hf := Real.continuous_mul_log.continuousOn) (ha := hA.isHermitian)).mpr
  intro t ht
  have ht0 := spectrum_nonneg hA ht
  have ht1 : t ≤ 1 := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i,rfl⟩ := ht
    exact eigenvalues_le_one hA hA1 i
  exact Real.mul_log_nonpos ht0 ht1


-- @@ L138-144 verbatim
lemma spectralLinear_sum (U : Matrix n n ℂ) (v : n → ℝ) :
    spectralLinear U v = ∑ i, v i • spectralLinear U (Pi.single i 1) := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul]


-- @@ L146-153 verbatim
lemma spectralLinear_single_pos (U : Matrix n n ℂ) (i : n) :
    (spectralLinear U (Pi.single i 1)).PosSemidef := by
  rw [spectralLinear_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro j
  simp only [Pi.single_apply]
  split_ifs <;> simp


-- @@ L155-157 verbatim
lemma spectralLinear_one (U : Matrix n n ℂ) (hU : U*Uᴴ=1) :
    spectralLinear U (fun _ => 1) = 1 := by
  simp [spectralLinear_apply, Matrix.diagonal_one, hU]


-- @@ L159-185 verbatim
lemma functional_entropy_lower (Φ : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (hΦ : ∀ A : Matrix n n ℂ, A.PosSemidef → 0 ≤ Φ A)
    (hmass : Φ 1 ≤ 1) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    -Φ (effectEntropy A) ≤ Real.negMulLog (Φ A) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let w : n → ℝ := fun i => Φ (spectralLinear U (Pi.single i 1))
  have hw : ∀ i, 0 ≤ w i := fun i => hΦ _ (spectralLinear_single_pos U i)
  have hU : U*Uᴴ=1 := Unitary.mul_star_self_of_mem hA.isHermitian.eigenvectorUnitary.property
  have hone : ∑ i, w i = Φ 1 := by
    rw [← spectralLinear_one U hU, spectralLinear_sum]
    simp only [map_sum, map_smul, smul_eq_mul, one_mul, w]
  have heval (f : ℝ → ℝ) : Φ (cfc f A) = ∑ i, w i*f (hA.isHermitian.eigenvalues i) := by
    rw [cfc_eq_spectralLinear hA.isHermitian, spectralLinear_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hid : Φ A = ∑ i, w i*hA.isHermitian.eigenvalues i := by
    have h := heval id
    erw [cfc_id' ℝ A hA.isHermitian] at h
    exact h
  have hh := ScalarEntropy.negMulLog_subprob w hA.isHermitian.eigenvalues hw
    (hone.trans_le hmass) hA.eigenvalues_nonneg
  rw [← hid] at hh
  rw [effectEntropy, heval]
  convert hh using 1
  simp only [Real.negMulLog_def, mul_neg, neg_mul, Finset.sum_neg_distrib]


-- @@ L187-187 verbatim
variable {m : Type u_m} [Fintype m] [DecidableEq m]


-- @@ L189-192 verbatim
omit [DecidableEq n] [DecidableEq m] in
lemma prob_smul_left (C : Matrix m n ℂ) (r : ℝ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (r • A) B = r*prob C A B := by
  simp [prob, eval_eq_trace, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]

-- @@ L193-196 verbatim
omit [DecidableEq n] [DecidableEq m] in
lemma prob_smul_right (C : Matrix m n ℂ) (r : ℝ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C A (r • B) = r*prob C A B := by
  simp [prob, eval_eq_trace, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul]


-- @@ L198-201 verbatim
def probLeft (C : Matrix m n ℂ) (B : Matrix n n ℂ) : Matrix m m ℂ →ₗ[ℝ] ℝ where
  toFun A := prob C A B
  map_add' A A' := prob_add_left C A A' B
  map_smul' r A := prob_smul_left C r A B


-- @@ L203-206 verbatim
def probRight (C : Matrix m n ℂ) (A : Matrix m m ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun B := prob C A B
  map_add' B B' := prob_add_right C A B B'
  map_smul' r B := prob_smul_right C r A B


-- @@ L208-213 verbatim
omit [DecidableEq n] [DecidableEq m] in
lemma prob_mono_left (C : Matrix m n ℂ) {A A' : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hB : B.PosSemidef) (hA : A ≤ A') : prob C A B ≤ prob C A' B := by
  have h := prob_nonneg (C := C) (show (A'-A).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA)) hB
  rw [prob_sub_left] at h
  linarith

-- @@ L214-219 verbatim
omit [DecidableEq n] [DecidableEq m] in
lemma prob_mono_right (C : Matrix m n ℂ) {A : Matrix m m ℂ} {B B' : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B ≤ B') : prob C A B ≤ prob C A B' := by
  have h := prob_nonneg (C := C) hA (show (B'-B).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB))
  rw [prob_sub_right] at h
  linarith


-- @@ L221-226 verbatim
lemma prob_entropy_left_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hB1 : B ≤ 1) :
    -prob C (effectEntropy A) B ≤ Real.negMulLog (prob C A B) := by
  apply functional_entropy_lower (probLeft C B) (fun T hT => prob_nonneg hT hB) _ hA
  exact ((prob_mono_right C Matrix.PosSemidef.one hB1).trans_eq (prob_one C)).trans hC


-- @@ L228-233 verbatim
lemma prob_entropy_right_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (hB : B.PosSemidef) :
    -prob C A (effectEntropy B) ≤ Real.negMulLog (prob C A B) := by
  apply functional_entropy_lower (probRight C A) (fun T hT => prob_nonneg hA hT) _ hB
  exact ((prob_mono_left C Matrix.PosSemidef.one hA1).trans_eq (prob_one C)).trans hC


-- @@ L235-235 verbatim
end OperatorEntropy

-- @@ L236-236 verbatim
end ThresholdParallelRepetition


-- @@ L238-238 verbatim
end


-- @@ L240-240 verbatim
end OAI
