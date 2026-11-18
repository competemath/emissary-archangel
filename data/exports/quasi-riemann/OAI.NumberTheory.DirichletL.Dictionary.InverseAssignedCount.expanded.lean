import OAI.NumberTheory.DirichletL.Moments.SourceMass


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.DetectorDictionaryInverseAssignedCount

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-12 verbatim
def assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) : Finset (ι → Ideal O) := Fintype.piFinset L


-- @@ L14-17 verbatim
@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (q : ι → Ideal O) :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]


-- @@ L19-19 verbatim
def assignedConstant (K : ℕ) (b : ℝ) : ℝ := (128*b)^K


-- @@ L21-24 verbatim
theorem assignedConstant_pos (K : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity


-- @@ L26-33 verbatim
theorem list_card_le (L : Finset (Ideal O)) {H : ℝ} (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  exact (CenteredMomentSourceMass.mem_idealBall H I).mpr (hL I hI)


-- @@ L35-54 verbatim
theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)


-- @@ L56-57 verbatim
def assignedCoefficient {ι : Type*} [Fintype ι]
    (a : ι → Ideal O → ℂ) (q : ι → Ideal O) : ℂ := ∏ i, a i (q i)


-- @@ L59-66 verbatim
theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (a : ι → Ideal O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (q : ι → Ideal O) (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod₀ (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))


-- @@ L68-81 verbatim
theorem restricted_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL


-- @@ L83-96 verbatim
theorem restricted_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp


-- @@ L98-107 verbatim
theorem restricted_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT


-- @@ L109-121 verbatim
theorem slots_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : σ → Ideal O → ℂ) (ha : ∀ i ∈ J, ∀ I ∈ L i, ‖a i I‖ ≤ 1)
    (T : Finset (J → Ideal O)) (hT : T ⊆ assignedTuples (fun i : J => L i)) :
    (∑ q ∈ T, ‖assignedCoefficient (fun i : J => a i) q‖) * U^(-(∑ i ∈ J, ell i)) ≤
      assignedConstant K b := by
  simpa only [Finset.sum_coe_sort] using
    restricted_normalized_mass_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI) (fun i : J => a i)
      (fun i I hI => ha i i.property I hI) T hT


-- @@ L123-130 verbatim
theorem assigned_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1) :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)


-- @@ L132-141 verbatim
theorem slots_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples (fun i : J => L i)).card : ℝ) ≤
      assignedConstant K b * U^(∑ i ∈ J, ell i) := by
  simpa only [Finset.sum_coe_sort] using
    assigned_card_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI)


-- @@ L143-149 verbatim
theorem assignedTuples_eq_empty {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (i : ι) (hi : L i = ∅) :
    assignedTuples L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := (mem_assignedTuples L q).mp hq i
  simp only [hi, Finset.notMem_empty] at h


-- @@ L151-153 verbatim
theorem assignedTuples_card_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (L : ι → Finset (Ideal O)) : (assignedTuples L).card = 1 := by
  simp [assignedTuples]


-- @@ L155-155 verbatim
end SevenEighths.DetectorDictionaryInverseAssignedCount


-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end OAI
