import OAI.Analysis.LipschitzEquivalence.GraphEquivalence


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uIndex uE


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace LipschitzCounterexample


-- @@ L10-10 verbatim
namespace HilbertSlots

-- @@ L11-11 verbatim
open scoped ENNReal NNReal InnerProductSpace

-- @@ L12-12 verbatim
open Filter Topology

-- @@ L13-14 verbatim
variable {ι : Type uIndex} {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]


-- @@ L16-16 verbatim
abbrev HilbertSum (E : ι → Type uE) [∀ i, NormedAddCommGroup (E i)] := lp E 2


-- @@ L18-20 verbatim
omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem norm_sq_tsum (x : HilbertSum E) : ‖x‖^2 = ∑' i, ‖x i‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x


-- @@ L22-24 verbatim
omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem summable_norm_sq (x : HilbertSum E) : Summable (fun i => ‖x i‖^2) := by
  simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable


-- @@ L26-26 verbatim
variable (ξ : ∀ i, E i) (hξ : ∀ i, ‖ξ i‖ = 1)


-- @@ L28-35 verbatim
def embed : lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] HilbertSum E where
  toFun a := ⟨fun i => a i • ξ i, a.2.mono' (fun i => by simp [norm_smul, hξ])⟩
  map_add' a b := by apply lp.ext; funext i; exact add_smul _ _ _
  map_smul' c a := by apply lp.ext; funext i; exact mul_smul _ _ _
  norm_map' a := by
    apply le_antisymm <;> apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    · intro i; change ‖a i • ξ i‖ ≤ ‖a i‖; simp [norm_smul, hξ]
    · intro i; change ‖a i‖ ≤ ‖a i • ξ i‖; simp [norm_smul, hξ]


-- @@ L37-38 verbatim
@[simp] theorem embed_apply (a : lp (fun _ : ι => ℝ) 2) (i : ι) :
    embed ξ hξ a i = a i • ξ i := rfl


-- @@ L40-51 verbatim
def coeff : HilbertSum E →L[ℝ] lp (fun _ : ι => ℝ) 2 :=
  ({ toFun u := ⟨fun i => ⟪ξ i, u i⟫_ℝ, u.2.mono' (fun i => by
        simpa [hξ] using norm_inner_le_norm (𝕜 := ℝ) (ξ i) (u i))⟩
     map_add' u v := by apply lp.ext; funext i; exact inner_add_right _ _ _
     map_smul' c u := by
       apply lp.ext; funext i
       exact real_inner_smul_right _ _ _ } : HilbertSum E →ₗ[ℝ] lp (fun _ : ι => ℝ) 2).mkContinuous
    1 (fun u => by
      simp only [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      simpa [hξ] using norm_inner_le_norm (𝕜 := ℝ) (ξ i) (u i))


-- @@ L53-54 verbatim
@[simp] theorem coeff_apply (u : HilbertSum E) (i : ι) :
    coeff ξ hξ u i = ⟪ξ i, u i⟫_ℝ := rfl


-- @@ L56-58 verbatim
include hξ in
theorem inner_slot_self (i : ι) : ⟪ξ i, ξ i⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, hξ]; norm_num


-- @@ L60-63 verbatim
@[simp] theorem coeff_embed (a : lp (fun _ : ι => ℝ) 2) :
    coeff ξ hξ (embed ξ hξ a) = a := by
  apply lp.ext; funext i
  simp [real_inner_smul_right, hξ]


-- @@ L65-66 verbatim
def perp : HilbertSum E →L[ℝ] HilbertSum E :=
  ContinuousLinearMap.id ℝ _ - (embed ξ hξ).toContinuousLinearMap.comp (coeff ξ hξ)


-- @@ L68-69 verbatim
@[simp] theorem perp_apply (u : HilbertSum E) (i : ι) :
    perp ξ hξ u i = u i - ⟪ξ i, u i⟫_ℝ • ξ i := rfl


-- @@ L71-73 verbatim
@[simp] theorem coeff_perp (u : HilbertSum E) : coeff ξ hξ (perp ξ hξ u) = 0 := by
  apply lp.ext; funext i
  simp [inner_sub_right, real_inner_smul_right, hξ]


-- @@ L75-78 verbatim
@[simp] theorem perp_embed (a : lp (fun _ : ι => ℝ) 2) :
    perp ξ hξ (embed ξ hξ a) = 0 := by
  change embed ξ hξ a - embed ξ hξ (coeff ξ hξ (embed ξ hξ a)) = 0
  rw [coeff_embed, sub_self]


-- @@ L80-82 verbatim
@[simp] theorem perp_perp (u : HilbertSum E) : perp ξ hξ (perp ξ hξ u) = perp ξ hξ u := by
  change perp ξ hξ u - embed ξ hξ (coeff ξ hξ (perp ξ hξ u)) = _
  rw [coeff_perp, map_zero, sub_zero]


-- @@ L84-87 verbatim
theorem perp_add_embed (u : HilbertSum E) :
    perp ξ hξ u + embed ξ hξ (coeff ξ hξ u) = u := by
  change (u - embed ξ hξ (coeff ξ hξ u)) + embed ξ hξ (coeff ξ hξ u) = u
  abel


-- @@ L89-96 verbatim
theorem inner_perp_embed (u : HilbertSum E) (a : lp (fun _ : ι => ℝ) 2) :
    ⟪perp ξ hξ u, embed ξ hξ a⟫_ℝ = 0 := by
  change (∑' i, ⟪perp ξ hξ u i, embed ξ hξ a i⟫_ℝ) = 0
  have he : ∀ i, ⟪perp ξ hξ u i, embed ξ hξ a i⟫_ℝ = 0 := by
    intro i
    simp [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (u i) (ξ i), hξ]
  simp_rw [he]; exact tsum_zero


-- @@ L98-101 verbatim
theorem norm_perp_add_embed_sq (u : HilbertSum E) (a : lp (fun _ : ι => ℝ) 2) :
    ‖perp ξ hξ u + embed ξ hξ a‖^2 = ‖perp ξ hξ u‖^2 + ‖a‖^2 := by
  rw [norm_add_sq_real, inner_perp_embed, (embed ξ hξ).norm_map]
  ring


-- @@ L103-105 verbatim
theorem norm_perp_sq (u : HilbertSum E) :
    ‖perp ξ hξ u‖^2 + ‖coeff ξ hξ u‖^2 = ‖u‖^2 := by
  rw [← norm_perp_add_embed_sq, perp_add_embed]


-- @@ L107-107 verbatim
end HilbertSlots


-- @@ L109-109 verbatim
namespace HilbertSlots

-- @@ L110-110 verbatim
open scoped ENNReal NNReal InnerProductSpace


-- @@ L112-113 verbatim
def interleaveRaw (v a : RealL2) (n : ℕ) : ℝ :=
  Sum.elim (fun i => v i) (fun i => a i) (Equiv.natSumNatEquivNat.symm n)


-- @@ L115-118 verbatim
@[simp] theorem interleaveRaw_even (v a : RealL2) (n : ℕ) :
    interleaveRaw v a (2*n) = v n := by
  change Sum.elim _ _ (Equiv.natSumNatEquivNat.symm (Equiv.natSumNatEquivNat (Sum.inl n))) = _
  rw [Equiv.symm_apply_apply]; rfl


-- @@ L120-123 verbatim
@[simp] theorem interleaveRaw_odd (v a : RealL2) (n : ℕ) :
    interleaveRaw v a (2*n+1) = a n := by
  change Sum.elim _ _ (Equiv.natSumNatEquivNat.symm (Equiv.natSumNatEquivNat (Sum.inr n))) = _
  rw [Equiv.symm_apply_apply]; rfl


-- @@ L125-132 verbatim
theorem interleave_hasSum (v a : RealL2) :
    HasSum (fun n => ‖interleaveRaw v a n‖^2) (‖v‖^2 + ‖a‖^2) := by
  apply (Equiv.natSumNatEquivNat.hasSum_iff).1
  apply HasSum.sum
  · simpa [Function.comp_def] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v)
  · simpa [Function.comp_def] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a)


-- @@ L134-135 verbatim
def interleaveSeq (v a : RealL2) : RealL2 :=
  ⟨interleaveRaw v a, memℓp_gen (by simpa using (interleave_hasSum v a).summable)⟩


-- @@ L137-155 verbatim
def interleave : WithLp 2 (RealL2 × RealL2) →ₗᵢ[ℝ] RealL2 where
  toFun x := interleaveSeq x.fst x.snd
  map_add' x y := by
    apply lp.ext; funext n
    change interleaveRaw (x+y).fst (x+y).snd n = interleaveRaw x.fst x.snd n + interleaveRaw y.fst y.snd n
    rcases Equiv.natSumNatEquivNat.surjective n with ⟨i, rfl⟩
    cases i <;> simp [interleaveRaw]
  map_smul' c x := by
    apply lp.ext; funext n
    change interleaveRaw (c • x).fst (c • x).snd n = c * interleaveRaw x.fst x.snd n
    rcases Equiv.natSumNatEquivNat.surjective n with ⟨i, rfl⟩
    cases i <;> simp [interleaveRaw]
  norm_map' x := by
    change ‖(interleaveSeq x.fst x.snd)‖ = ‖x‖
    have he : ‖(interleaveSeq x.fst x.snd)‖^2 = ‖x.fst‖^2 + ‖x.snd‖^2 := by
      rw [norm_sq_tsum]
      exact (interleave_hasSum x.fst x.snd).tsum_eq
    have hx := WithLp.prod_norm_sq_eq_of_L2 x
    nlinarith [norm_nonneg (interleaveSeq x.fst x.snd), norm_nonneg x]


-- @@ L157-158 verbatim
@[simp] theorem interleave_even (x : WithLp 2 (RealL2 × RealL2)) (n : ℕ) :
    interleave x (2*n) = x.fst n := interleaveRaw_even ..

-- @@ L159-160 verbatim
@[simp] theorem interleave_odd (x : WithLp 2 (RealL2 × RealL2)) (n : ℕ) :
    interleave x (2*n+1) = x.snd n := interleaveRaw_odd ..


-- @@ L162-164 verbatim
def subsequence (f : ℕ → ℕ) (hf : Function.Injective f) (a : RealL2) : RealL2 :=
  ⟨fun i => a (f i), memℓp_gen (by
    simpa [Function.comp_def] using (summable_norm_sq a).comp_injective hf)⟩


-- @@ L166-167 verbatim
@[simp] theorem subsequence_apply (f : ℕ → ℕ) (hf : Function.Injective f)
    (a : RealL2) (i : ℕ) : subsequence f hf a i = a (f i) := rfl


-- @@ L169-171 verbatim
def split (a : RealL2) : WithLp 2 (RealL2 × RealL2) :=
  WithLp.toLp 2 (subsequence (fun i => 2*i) (by intro i j h; dsimp at h; omega) a,
    subsequence (fun i => 2*i+1) (by intro i j h; dsimp at h; omega) a)


-- @@ L173-176 verbatim
@[simp] theorem interleave_split (a : RealL2) : interleave (split a) = a := by
  apply lp.ext; funext n
  rcases Equiv.natSumNatEquivNat.surjective n with ⟨i, rfl⟩
  cases i <;> simp [split, subsequence]


-- @@ L178-182 verbatim
@[simp] theorem split_interleave (a : WithLp 2 (RealL2 × RealL2)) : split (interleave a) = a := by
  apply (WithLp.equiv 2 (RealL2 × RealL2)).injective
  apply Prod.ext <;> (apply lp.ext; funext i)
  · exact interleave_even a i
  · exact interleave_odd a i


-- @@ L184-188 verbatim
def interleaveEquiv : WithLp 2 (RealL2 × RealL2) ≃ₗᵢ[ℝ] RealL2 :=
  { interleave with
    invFun := split
    left_inv := split_interleave
    right_inv := interleave_split }


-- @@ L190-191 verbatim
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  (ξ : ∀ i, E i) (hξ : ∀ i, ‖ξ i‖ = 1)


-- @@ L193-198 verbatim
def frozenCLM : WithLp 2 (HilbertSum E × RealL2) →L[ℝ] HilbertSum E :=
  (perp ξ hξ).comp (WithLp.fstL 2 ℝ (HilbertSum E) RealL2) +
    (embed ξ hξ).toContinuousLinearMap.comp (interleave.toContinuousLinearMap.comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm.toContinuousLinearMap.comp
        ((WithLp.sndL 2 ℝ (HilbertSum E) RealL2).prod
          ((coeff ξ hξ).comp (WithLp.fstL 2 ℝ (HilbertSum E) RealL2)))))


-- @@ L200-214 verbatim
def frozen : WithLp 2 (HilbertSum E × RealL2) →ₗᵢ[ℝ] HilbertSum E :=
  { (frozenCLM ξ hξ).toLinearMap with
    norm_map' := fun x => by
      change ‖perp ξ hξ x.fst + embed ξ hξ
        (interleave (WithLp.toLp 2 (x.snd, coeff ξ hξ x.fst)))‖ = ‖x‖
      have ht := norm_perp_add_embed_sq ξ hξ x.fst
        (interleave (WithLp.toLp 2 (x.snd, coeff ξ hξ x.fst)))
      rw [interleave.norm_map, WithLp.prod_norm_sq_eq_of_L2] at ht
      have hu := norm_perp_sq ξ hξ x.fst
      have hx := WithLp.prod_norm_sq_eq_of_L2 x
      change ‖perp ξ hξ x.fst + embed ξ hξ
        (interleave (WithLp.toLp 2 (x.snd, coeff ξ hξ x.fst)))‖^2 =
        ‖perp ξ hξ x.fst‖^2 + (‖x.snd‖^2+‖coeff ξ hξ x.fst‖^2) at ht
      nlinarith [norm_nonneg (perp ξ hξ x.fst + embed ξ hξ
        (interleave (WithLp.toLp 2 (x.snd, coeff ξ hξ x.fst)))), norm_nonneg x] }


-- @@ L216-218 verbatim
def frozenInv (y : HilbertSum E) : WithLp 2 (HilbertSum E × RealL2) :=
  WithLp.toLp 2 (perp ξ hξ y + embed ξ hξ (split (coeff ξ hξ y)).snd,
    (split (coeff ξ hξ y)).fst)


-- @@ L220-226 verbatim
theorem frozen_right_inv (y : HilbertSum E) : frozen ξ hξ (frozenInv ξ hξ y) = y := by
  change perp ξ hξ (perp ξ hξ y + embed ξ hξ (split (coeff ξ hξ y)).snd) +
    embed ξ hξ (interleave (WithLp.toLp 2 ((split (coeff ξ hξ y)).fst,
      coeff ξ hξ (perp ξ hξ y + embed ξ hξ (split (coeff ξ hξ y)).snd)))) = y
  simp only [map_add, perp_perp, perp_embed, add_zero, coeff_perp, coeff_embed, zero_add]
  rw [show WithLp.toLp 2 ((split (coeff ξ hξ y)).fst, (split (coeff ξ hξ y)).snd) =
    split (coeff ξ hξ y) by rfl, interleave_split, perp_add_embed]


-- @@ L228-229 verbatim
def frozenEquiv : WithLp 2 (HilbertSum E × RealL2) ≃ₗᵢ[ℝ] HilbertSum E :=
  LinearIsometryEquiv.ofSurjective (frozen ξ hξ) (fun y => ⟨frozenInv ξ hξ y, frozen_right_inv ξ hξ y⟩)


-- @@ L231-231 verbatim
end HilbertSlots


-- @@ L233-233 verbatim
namespace HilbertSlots

-- @@ L234-234 verbatim
open scoped ENNReal NNReal InnerProductSpace

-- @@ L235-235 verbatim
open Filter Topology

-- @@ L236-237 verbatim
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  (ξ : ∀ i, E i) (hξ : ∀ i, ‖ξ i‖ = 1)


-- @@ L239-245 verbatim
theorem frozen_apply (x : WithLp 2 (HilbertSum E × RealL2)) (n : ℕ) :
    frozen ξ hξ x n = x.fst n +
      (interleaveRaw x.snd (coeff ξ hξ x.fst) n - ⟪ξ n, x.fst n⟫_ℝ) • ξ n := by
  change (x.fst n - ⟪ξ n, x.fst n⟫_ℝ • ξ n) +
    interleaveRaw x.snd (coeff ξ hξ x.fst) n • ξ n = _
  rw [sub_smul]
  abel


-- @@ L247-249 verbatim
@[simp] theorem frozenInv_fst (y : HilbertSum E) (n : ℕ) :
    (frozenInv ξ hξ y).fst n =
      y n - ⟪ξ n, y n⟫_ℝ • ξ n + ⟪ξ (2*n+1), y (2*n+1)⟫_ℝ • ξ n := rfl


-- @@ L251-252 verbatim
@[simp] theorem frozenInv_snd (y : HilbertSum E) (n : ℕ) :
    (frozenInv ξ hξ y).snd n = ⟪ξ (2*n), y (2*n)⟫_ℝ := rfl


-- @@ L254-255 verbatim
theorem norm_frozenInv (y : HilbertSum E) : ‖frozenInv ξ hξ y‖ = ‖y‖ := by
  rw [← (frozen ξ hξ).norm_map, frozen_right_inv]


-- @@ L257-264 verbatim
theorem frozenInv_fst_sq (y : HilbertSum E) (n : ℕ) :
    ‖(frozenInv ξ hξ y).fst n‖^2 = ‖y n‖^2 - (coeff ξ hξ y n)^2 +
      (coeff ξ hξ y (2*n+1))^2 := by
  rw [frozenInv_fst, norm_add_sq_real, norm_sub_sq_real]
  simp only [coeff_apply, norm_smul, hξ, mul_one, Real.norm_eq_abs, sq_abs,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm (y n) (ξ n), real_inner_self_eq_norm_sq]
  ring


-- @@ L266-274 verbatim
omit ξ hξ in
theorem sum_pairs (b : ℕ → ℝ) (s : ℕ) :
    (∑ m ∈ Finset.range s, (b (2*m) + b (2*m+1))) = ∑ n ∈ Finset.range (2*s), b n := by
  induction s with
  | zero => simp
  | succ s hs =>
    rw [Finset.sum_range_succ, hs]
    rw [show 2*(s+1) = (2*s+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    ring


-- @@ L276-293 verbatim
theorem inverse_prefix_energy (y : HilbertSum E) (s : ℕ) :
    (∑ n ∈ Finset.range s, ‖y n‖^2) ≤
      ∑ m ∈ Finset.range s, (‖(frozenInv ξ hξ y).fst m‖^2 + ‖(frozenInv ξ hξ y).snd m‖^2) := by
  have he : (∑ m ∈ Finset.range s,
      (‖(frozenInv ξ hξ y).fst m‖^2 + ‖(frozenInv ξ hξ y).snd m‖^2)) =
      (∑ m ∈ Finset.range s, ‖y m‖^2) - (∑ m ∈ Finset.range s, (coeff ξ hξ y m)^2) +
        ∑ m ∈ Finset.range (2*s), (coeff ξ hξ y m)^2 := by
    rw [← sum_pairs (fun m => (coeff ξ hξ y m)^2) s]
    simp_rw [frozenInv_fst_sq, frozenInv_snd, Real.norm_eq_abs, sq_abs]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, coeff_apply]
    ring
  rw [he]
  have hm : (∑ m ∈ Finset.range s, (coeff ξ hξ y m)^2) ≤
      ∑ m ∈ Finset.range (2*s), (coeff ξ hξ y m)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i hi hnot; exact sq_nonneg _
  linarith


-- @@ L295-309 verbatim
theorem inverse_tail_energy (y : HilbertSum E) (s : ℕ) :
    (∑' m, (‖(frozenInv ξ hξ y).fst (m+s)‖^2 +
      ‖(frozenInv ξ hξ y).snd (m+s)‖^2)) ≤ ∑' n, ‖y (n+s)‖^2 := by
  have hsum := summable_norm_sq (frozenInv ξ hξ y).fst
  have hv := summable_norm_sq (frozenInv ξ hξ y).snd
  have htot : (∑' m, (‖(frozenInv ξ hξ y).fst m‖^2 +
      ‖(frozenInv ξ hξ y).snd m‖^2)) = ‖y‖^2 := by
    rw [hsum.tsum_add hv, ← norm_sq_tsum, ← norm_sq_tsum,
      ← WithLp.prod_norm_sq_eq_of_L2, norm_frozenInv]
  have hx := (hsum.add hv).sum_add_tsum_nat_add s
  have hy := (summable_norm_sq y).sum_add_tsum_nat_add s
  rw [htot] at hx
  rw [← norm_sq_tsum] at hy
  have hp := inverse_prefix_energy ξ hξ y s
  linarith


-- @@ L311-313 verbatim
def moving (w : WithLp 2 (HilbertSum E × RealL2) → ∀ i, E i)
    (hw : ∀ x i, ‖w x i‖ = 1) (x : WithLp 2 (HilbertSum E × RealL2)) : HilbertSum E :=
  frozen (w x) (hw x) x


-- @@ L315-318 verbatim
omit ξ hξ in
@[simp] theorem norm_moving (w : WithLp 2 (HilbertSum E × RealL2) → ∀ i, E i)
    (hw : ∀ x i, ‖w x i‖ = 1) (x : WithLp 2 (HilbertSum E × RealL2)) :
    ‖moving w hw x‖ = ‖x‖ := (frozen (w x) (hw x)).norm_map x


-- @@ L320-324 verbatim
omit ξ hξ in
@[simp] theorem moving_zero (w : WithLp 2 (HilbertSum E × RealL2) → ∀ i, E i)
    (hw : ∀ x i, ‖w x i‖ = 1) : moving w hw 0 = 0 := by
  apply norm_eq_zero.mp
  rw [norm_moving, norm_zero]


-- @@ L326-326 verbatim
end HilbertSlots


-- @@ L328-328 verbatim
end LipschitzCounterexample

-- @@ L329-329 verbatim
end


-- @@ L331-331 verbatim
end OAI
