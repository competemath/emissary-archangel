import TubalTensor.RingStructure.Classification.Canonical


-- @@ L3-15 verbatim
/-!
  TubalTensor/RingStructure/Classification/Prop12.lean
  Proposition 13: Classification of tubal rings by realness.

  Main results:
  - `canonical_starM_coord`: componentwise multiplication at real indices
  - `coordProj`: coordinate projection as ℝ-algebra homomorphism
  - `algHom_canonical_eq_coordProj`: classification of AlgHoms to ℝ
  - `realness_of_algEquiv`: isomorphic implies same realness
  - `KM_algEquiv_of_realness_eq`: same realness implies isomorphic (Proposition 13)
  - `KM_algEquiv_iff_realness_eq`: iff version (Proposition 13)
  - `KM_ringEquiv_iff_realness_eq`: ring isomorphism version
-/


-- @@ L17-17 verbatim
namespace TubalTensor


-- @@ L19-19 verbatim
open Complex Matrix


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-29 verbatim
/-! ## Canonical ring coordinate properties (for reverse direction of Prop 12)

For i < m in the canonical ring, the identity block of M ensures:
- `(M *ᵥ v) i = v i` and `(M⁻¹ *ᵥ v) i = v i`
- `(a ⋆_M b) i = a i * b i` (componentwise multiplication)
- `(unitTube) i = 1`
-/


-- @@ L31-38 verbatim
/-- For i < m, `canonicalEquiv` maps `Sum.inl ⟨i, hi⟩` to `i`. -/
private theorem canonicalEquiv_inl_val {m k : ℕ} (hk : m + 2 * k = n)
    (i : Fin n) (hi : i.val < m) :
    canonicalEquiv m k hk (Sum.inl ⟨i.val, hi⟩) = i := by
  apply Fin.ext
  simp only [canonicalEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, Fin.val_castAdd,
    Equiv.refl_apply]


-- @@ L40-45 verbatim
/-- For i < m, `canonicalEquiv.symm i = Sum.inl ⟨i, hi⟩`. -/
private theorem canonicalEquiv_symm_lt {m k : ℕ} (hk : m + 2 * k = n)
    (i : Fin n) (hi : i.val < m) :
    (canonicalEquiv m k hk).symm i = Sum.inl ⟨i.val, hi⟩ := by
  apply_fun canonicalEquiv m k hk using (canonicalEquiv m k hk).injective
  rw [Equiv.apply_symm_apply, canonicalEquiv_inl_val hk i hi]


-- @@ L47-64 verbatim
/-- For i < m, row i of `canonicalM` acts as identity: `(canonicalM *ᵥ v) i = v i`. -/
private theorem canonicalM_mulVec_coord (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (v : Fin n → ℂ) (i : Fin n) (hi : i.val < m) :
    (canonicalM n m hm hpar *ᵥ v) i = v i := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  simp only [Matrix.mulVec, dotProduct]
  rw [show ∑ j, canonicalM n m hm hpar i j * v j =
      ∑ x, canonicalM_block m k ((canonicalEquiv m k hk).symm i) x *
        v (canonicalEquiv m k hk x) from
    Fintype.sum_equiv (canonicalEquiv m k hk).symm _ _ (fun j => by
      simp only [canonicalM, Matrix.submatrix_apply, Equiv.apply_symm_apply]; rfl)]
  rw [canonicalEquiv_symm_lt hk i hi, Fintype.sum_sum_type]
  simp only [canonicalM_block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    Matrix.one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  exact congr_arg v (canonicalEquiv_inl_val hk i hi)


-- @@ L66-83 verbatim
/-- For i < m, row i of `canonicalMinv` acts as identity: `(canonicalMinv *ᵥ v) i = v i`. -/
private theorem canonicalMinv_mulVec_coord (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (v : Fin n → ℂ) (i : Fin n) (hi : i.val < m) :
    (canonicalMinv n m hm hpar *ᵥ v) i = v i := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  simp only [Matrix.mulVec, dotProduct]
  rw [show ∑ j, canonicalMinv n m hm hpar i j * v j =
      ∑ x, canonicalMinv_block m k ((canonicalEquiv m k hk).symm i) x *
        v (canonicalEquiv m k hk x) from
    Fintype.sum_equiv (canonicalEquiv m k hk).symm _ _ (fun j => by
      simp only [canonicalMinv, Matrix.submatrix_apply, Equiv.apply_symm_apply]; rfl)]
  rw [canonicalEquiv_symm_lt hk i hi, Fintype.sum_sum_type]
  simp only [canonicalMinv_block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    Matrix.one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  exact congr_arg v (canonicalEquiv_inl_val hk i hi)


-- @@ L85-97 verbatim
/-- For i < m, the ⋆_M product in the canonical ring is componentwise:
    `(a ⋆_M b) i = a i * b i`. -/
theorem canonical_starM_coord (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (a b : Fin n → ℝ) (i : Fin n) (hi : i.val < m) :
    starM (canonicalTubalData n m hm hpar) a b i = a i * b i := by
  show ((canonicalTubalData n m hm hpar).applyMinv
    ((canonicalTubalData n m hm hpar).applyM (toComplex a) ∘ₕ
     (canonicalTubalData n m hm hpar).applyM (toComplex b)) i).re = _
  simp only [TubalData.applyMinv, TubalData.applyM, canonicalTubalData]
  rw [canonicalMinv_mulVec_coord m hm hpar _ i hi, vecHadamard_apply,
      canonicalM_mulVec_coord m hm hpar (toComplex a) i hi,
      canonicalM_mulVec_coord m hm hpar (toComplex b) i hi,
      toComplex_apply, toComplex_apply, ← Complex.ofReal_mul, Complex.ofReal_re]


-- @@ L99-105 verbatim
/-- For i < m, the unit tube of the canonical ring has `(unitTube td) i = 1`. -/
theorem canonical_unitTube_coord (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i : Fin n) (hi : i.val < m) :
    unitTube (canonicalTubalData n m hm hpar) i = 1 := by
  show ((canonicalTubalData n m hm hpar).applyMinv (allOnes n) i).re = 1
  simp only [TubalData.applyMinv, canonicalTubalData]
  rw [canonicalMinv_mulVec_coord m hm hpar _ i hi, allOnes_apply, Complex.one_re]


-- @@ L107-107 verbatim
/-! ## Coordinate projections as AlgHoms (for reverse direction of Prop 12) -/


-- @@ L109-121 verbatim
/-- Coordinate projection: for `i < m`, the map `a ↦ a i` is an ℝ-algebra homomorphism
    from the canonical ring to ℝ. -/
noncomputable def coordProj (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i : Fin n) (hi : i.val < m) :
    KM n (canonicalTubalData n m hm hpar) →ₐ[ℝ] ℝ where
  toFun a := KM.toFun a i
  map_one' := by simp [canonical_unitTube_coord m hm hpar i hi]
  map_mul' a b := by simp [canonical_starM_coord m hm hpar _ _ i hi]
  map_zero' := by simp
  map_add' _ _ := by simp
  commutes' r := by
    change (r • unitTube (canonicalTubalData n m hm hpar)) i = r
    rw [Pi.smul_apply, smul_eq_mul, canonical_unitTube_coord m hm hpar i hi, mul_one]


-- @@ L123-126 verbatim
@[simp]
theorem coordProj_apply (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i : Fin n) (hi : i.val < m) (a : KM n (canonicalTubalData n m hm hpar)) :
    coordProj m hm hpar i hi a = KM.toFun a i := rfl


-- @@ L128-136 verbatim
/-- Coordinate projections are injective on indices: if `coordProj i = coordProj j`
    then `i = j`. -/
theorem coordProj_injective (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i j : Fin n) (hi : i.val < m) (hj : j.val < m)
    (h : coordProj m hm hpar i hi = coordProj m hm hpar j hj) : i = j := by
  by_contra hij
  have h1 := DFunLike.congr_fun h (KM.ofFun (fun k => if k = i then (1 : ℝ) else 0))
  simp only [coordProj_apply, KM.toFun_ofFun, if_neg (Ne.symm hij)] at h1
  exact one_ne_zero h1


-- @@ L138-138 verbatim
/-! ## Off-diagonal block structure (for pair-index computations) -/


-- @@ L140-153 verbatim
/-- For i ≥ m, `canonicalEquiv.symm i` lands in the `Sum.inr` (pair) component. -/
private theorem canonicalEquiv_symm_ge {m k : ℕ} (hk : m + 2 * k = n)
    (i : Fin n) (hi : i.val ≥ m) :
    ∃ (r : Fin 2) (b : Fin k), (canonicalEquiv m k hk).symm i = Sum.inr (r, b) := by
  rcases h : (canonicalEquiv m k hk).symm i with a | ⟨r, b⟩
  · exfalso
    have h1 : canonicalEquiv m k hk (Sum.inl a) = i := by
      rw [← h, Equiv.apply_symm_apply]
    have h2 := congr_arg Fin.val h1
    simp only [canonicalEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, Fin.val_castAdd,
      Equiv.refl_apply] at h2
    omega
  · exact ⟨r, b, rfl⟩


-- @@ L155-164 verbatim
/-- Off-diagonal block of canonical matrix is zero: M_{j,i} = 0 for pair j ≥ m, real i < m. -/
private theorem canonicalM_pair_real_zero (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (j i : Fin n) (hj : j.val ≥ m) (hi : i.val < m) :
    canonicalM n m hm hpar j i = 0 := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  obtain ⟨r, b, hrb⟩ := canonicalEquiv_symm_ge hk j hj
  show canonicalM_block m k _ _ = 0
  rw [hrb, canonicalEquiv_symm_lt hk i hi]
  simp [canonicalM_block, fromBlocks_apply₂₁]


-- @@ L166-175 verbatim
/-- Off-diagonal block of canonical matrix is zero: M_{i,j} = 0 for real i < m, pair j ≥ m. -/
private theorem canonicalM_real_pair_zero (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i j : Fin n) (hi : i.val < m) (hj : j.val ≥ m) :
    canonicalM n m hm hpar i j = 0 := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  obtain ⟨r, b, hrb⟩ := canonicalEquiv_symm_ge hk j hj
  show canonicalM_block m k _ _ = 0
  rw [canonicalEquiv_symm_lt hk i hi, hrb]
  simp [canonicalM_block, fromBlocks_apply₁₂]


-- @@ L177-186 verbatim
/-- Off-diagonal block of inverse canonical matrix: M⁻¹_{j,i} = 0 for pair j ≥ m, real i < m. -/
private theorem canonicalMinv_pair_real_zero (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (j i : Fin n) (hj : j.val ≥ m) (hi : i.val < m) :
    canonicalMinv n m hm hpar j i = 0 := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  obtain ⟨r, b, hrb⟩ := canonicalEquiv_symm_ge hk j hj
  show canonicalMinv_block m k _ _ = 0
  rw [hrb, canonicalEquiv_symm_lt hk i hi]
  simp [canonicalMinv_block, fromBlocks_apply₂₁]


-- @@ L188-197 verbatim
/-- Off-diagonal block of inverse: M⁻¹_{i,j} = 0 for real i < m, pair j ≥ m. -/
private theorem canonicalMinv_real_pair_zero (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i j : Fin n) (hi : i.val < m) (hj : j.val ≥ m) :
    canonicalMinv n m hm hpar i j = 0 := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  obtain ⟨r, b, hrb⟩ := canonicalEquiv_symm_ge hk j hj
  show canonicalMinv_block m k _ _ = 0
  rw [canonicalEquiv_symm_lt hk i hi, hrb]
  simp [canonicalMinv_block, fromBlocks_apply₁₂]


-- @@ L199-199 verbatim
/-! ## Standard basis idempotent property -/


-- @@ L201-252 verbatim
/-- For i < m in the canonical ring, `Pi.single i 1 ⋆_M a = a i • Pi.single i 1`.
    This means each standard basis vector is a "primitive absorbing idempotent". -/
theorem stdBasis_mul_canonical (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (i : Fin n) (hi : i.val < m) (a : Fin n → ℝ) :
    starM (canonicalTubalData n m hm hpar) (fun k => if k = i then 1 else 0) a =
    fun j => a i * (if j = i then 1 else 0) := by
  set td := canonicalTubalData n m hm hpar
  set ei := fun k => if k = i then (1 : ℝ) else 0
  -- Key: (M *ᵥ toComplex ei)_k = 0 for all k ≥ m
  have hMe : ∀ k : Fin n, k.val ≥ m →
      (canonicalM n m hm hpar *ᵥ toComplex ei) k = 0 := by
    intro k hk
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l.val < m
    · rw [canonicalM_pair_real_zero m hm hpar k l hk hl, zero_mul]
    · push Not at hl
      have : toComplex ei l = 0 := by
        simp [ei, toComplex_apply, show ¬(l = i) from fun h => by omega]
      rw [this, mul_zero]
  -- Hadamard product is 0 at all pair indices
  have hHad : ∀ k : Fin n, k.val ≥ m →
      ((canonicalM n m hm hpar *ᵥ toComplex ei) ∘ₕ
       (canonicalM n m hm hpar *ᵥ toComplex a)) k = 0 := by
    intro k hk; rw [vecHadamard_apply, hMe k hk, zero_mul]
  ext j
  by_cases hj : j.val < m
  · rw [canonical_starM_coord m hm hpar _ a j hj]
    simp only [ei, ite_mul, one_mul, zero_mul]
    by_cases hij : j = i <;> simp [hij]
  · push Not at hj
    -- For j ≥ m: (e_i ⋆_M a)_j = 0
    show ((canonicalTubalData n m hm hpar).applyMinv
      ((canonicalTubalData n m hm hpar).applyM (toComplex ei) ∘ₕ
       (canonicalTubalData n m hm hpar).applyM (toComplex a)) j).re = _
    simp only [TubalData.applyMinv, TubalData.applyM, canonicalTubalData]
    -- (M⁻¹ *ᵥ had)_j = ∑_k M⁻¹_{j,k} * had_k = 0
    -- because M⁻¹_{j,k} = 0 for k < m (off-diagonal), and had_k = 0 for k ≥ m
    have hMinv : (canonicalMinv n m hm hpar *ᵥ
      ((canonicalM n m hm hpar *ᵥ toComplex ei) ∘ₕ
       (canonicalM n m hm hpar *ᵥ toComplex a))) j = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k.val < m
      · rw [canonicalMinv_pair_real_zero m hm hpar j k hj hk, zero_mul]
      · push Not at hk
        rw [hHad k hk, mul_zero]
    rw [hMinv, Complex.zero_re]
    -- RHS: a i * 0 = 0
    simp [show ¬(j = i) from fun h => by omega]


-- @@ L254-254 verbatim
/-! ## Pair block entry lemmas -/


-- @@ L256-263 verbatim
private theorem canonicalM_pair_same (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (r s : Fin 2) (b : Fin ((n - m) / 2)) :
    canonicalM n m hm hpar
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (r, b)))
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (s, b))) =
    conjPairBlock r s := by
  show canonicalM_block m _ _ _ = _
  simp [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]


-- @@ L265-272 verbatim
private theorem canonicalMinv_pair_same (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (r s : Fin 2) (b : Fin ((n - m) / 2)) :
    canonicalMinv n m hm hpar
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (r, b)))
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (s, b))) =
    conjPairBlockInv r s := by
  show canonicalMinv_block m _ _ _ = _
  simp [canonicalMinv_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]


-- @@ L274-280 verbatim
private theorem canonicalM_pair_diff (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (r s : Fin 2) (b b' : Fin ((n - m) / 2)) (hbb : b ≠ b') :
    canonicalM n m hm hpar
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (r, b)))
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (s, b'))) = 0 := by
  show canonicalM_block m _ _ _ = _
  simp [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_ne _ _ _ hbb]


-- @@ L282-288 verbatim
private theorem canonicalMinv_pair_diff (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (r s : Fin 2) (b b' : Fin ((n - m) / 2)) (hbb : b ≠ b') :
    canonicalMinv n m hm hpar
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (r, b)))
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (s, b'))) = 0 := by
  show canonicalMinv_block m _ _ _ = _
  simp [canonicalMinv_block, fromBlocks_apply₂₂, blockDiagonal_apply_ne _ _ _ hbb]


-- @@ L290-290 verbatim
/-! ## Pair basis square computation -/


-- @@ L292-301 verbatim
set_option maxHeartbeats 800000 in
private theorem pair_sq_sum_re (r s : Fin 2) :
    (∑ t : Fin 2, conjPairBlockInv s t * (conjPairBlock t r) ^ 2).re =
    if s = 0 then (if r = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)) else 0 := by
  simp only [Fin.sum_univ_two, conjPairBlockInv, conjPairBlock, sq]
  fin_cases s <;> fin_cases r <;> simp_all <;> {
    have hsq2 := Real.mul_self_sqrt (show (2:ℝ) ≥ 0 by norm_num)
    have hsq_ne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
    nlinarith [hsq2] }


-- @@ L303-310 verbatim
/-- The Fin n value of a pair index is ≥ m. -/
private theorem canonicalEquiv_inr_ge {m k : ℕ} (hk : m + 2 * k = n)
    (r : Fin 2) (b : Fin k) :
    (canonicalEquiv m k hk (Sum.inr (r, b))).val ≥ m := by
  by_contra h; push Not at h
  have := canonicalEquiv_symm_lt hk (canonicalEquiv m k hk (Sum.inr (r, b))) h
  rw [Equiv.symm_apply_apply] at this
  exact absurd this (by nofun)


-- @@ L312-356 verbatim
/-- MulVec of M⁻¹ at pair indices: the block diagonal structure means only
    the same pair block contributes. -/
private theorem canonicalMinv_mulVec_pair_coord (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (v : Fin n → ℂ) (s : Fin 2) (b : Fin ((n - m) / 2)) :
    (canonicalMinv n m hm hpar *ᵥ v)
      (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (s, b))) =
    ∑ t : Fin 2, conjPairBlockInv s t *
      v (canonicalEquiv m ((n - m) / 2) (by omega) (Sum.inr (t, b))) := by
  have hk : m + 2 * ((n - m) / 2) = n := by omega
  -- Expand mulVec at the pair index
  show ∑ j, canonicalMinv n m hm hpar
    (canonicalEquiv m ((n - m) / 2) hk (Sum.inr (s, b))) j * v j = _
  -- Reindex the sum via canonicalEquiv
  rw [show ∑ j, canonicalMinv n m hm hpar
      (canonicalEquiv m ((n - m) / 2) hk (Sum.inr (s, b))) j * v j =
    ∑ x, canonicalMinv_block m ((n - m) / 2) (Sum.inr (s, b)) x *
      v (canonicalEquiv m ((n - m) / 2) hk x) from
    Fintype.sum_equiv (canonicalEquiv m ((n - m) / 2) hk).symm _ _ (fun j => by
      simp only [canonicalMinv, Matrix.submatrix_apply, Equiv.apply_symm_apply,
        Equiv.symm_apply_apply])]
  rw [Fintype.sum_sum_type]
  -- Real part = 0
  have hreal : ∑ a : Fin m,
      canonicalMinv_block m ((n - m) / 2) (Sum.inr (s, b)) (Sum.inl a) *
      v (canonicalEquiv m ((n - m) / 2) hk (Sum.inl a)) = 0 := by
    apply Finset.sum_eq_zero; intro a _
    simp [canonicalMinv_block, fromBlocks_apply₂₁]
  rw [hreal, zero_add]
  -- Pair part: split product type and extract b = b case
  rw [show ∑ x : Fin 2 × Fin ((n - m) / 2),
      canonicalMinv_block m ((n - m) / 2) (Sum.inr (s, b)) (Sum.inr x) *
      v (canonicalEquiv m ((n - m) / 2) hk (Sum.inr x)) =
    ∑ t : Fin 2, ∑ b' : Fin ((n - m) / 2),
      canonicalMinv_block m ((n - m) / 2) (Sum.inr (s, b)) (Sum.inr (t, b')) *
      v (canonicalEquiv m ((n - m) / 2) hk (Sum.inr (t, b'))) from
    Fintype.sum_prod_type _]
  congr 1; ext t
  -- Only b' = b survives: blockDiagonal is zero for different blocks
  rw [Finset.sum_eq_single b]
  · -- b' = b term
    simp only [canonicalMinv_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]
  · intro b' _ hb'
    simp only [canonicalMinv_block, fromBlocks_apply₂₂]
    rw [blockDiagonal_apply_ne _ s t hb'.symm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h


-- @@ L358-459 verbatim
set_option maxHeartbeats 800000 in
/-- Standard basis vector e_j squared in the canonical ring, for pair index j:
    the result is supported only on the first pair index j0, with value ±1/√2. -/
private theorem pair_basis_sq (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (b : Fin ((n - m) / 2)) (r : Fin 2) :
    let k := (n - m) / 2
    let hk : m + 2 * k = n := by omega
    let jr := canonicalEquiv m k hk (Sum.inr (r, b))
    let j0 := canonicalEquiv m k hk (Sum.inr ((0 : Fin 2), b))
    let td := canonicalTubalData n m hm hpar
    (KM.ofFun (fun l => if l = jr then (1 : ℝ) else 0) : KM n td) *
    (KM.ofFun (fun l => if l = jr then (1 : ℝ) else 0) : KM n td) =
    (if r = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)) •
    (KM.ofFun (fun l => if l = j0 then (1 : ℝ) else 0) : KM n td) := by
  have hk : m + 2 * ((n - m) / 2) = n := by omega
  have hjr_ge : (canonicalEquiv m ((n-m)/2) hk (Sum.inr (r, b))).val ≥ m :=
    canonicalEquiv_inr_ge hk r b
  -- toComplex of basis vector = complex basis vector
  have htoC : ∀ jr : Fin n, toComplex (fun l => if l = jr then (1 : ℝ) else 0) =
      fun l => if l = jr then (1 : ℂ) else 0 := by
    intro jr; ext l; simp only [toComplex_apply]; split_ifs <;> simp
  -- Column extraction: (M *ᵥ e_jr)_k = M_{k,jr}
  have hMcol : ∀ (jr : Fin n) (k : Fin n),
      (canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1 : ℂ) else 0)) k =
      canonicalM n m hm hpar k jr := by
    intro jr k; simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single jr (fun j _ h => by simp [h]) (by simp)]; simp
  -- had vector properties (parametrized by jr)
  have hHad_eq : ∀ (jr : Fin n) (k : Fin n),
      ((canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1:ℂ) else 0)) ∘ₕ
       (canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1:ℂ) else 0))) k =
      (canonicalM n m hm hpar k jr) ^ 2 := by
    intro jr k; simp only [vecHadamard_apply, hMcol, sq]
  -- Abbreviate the specific jr and j0
  set jr := canonicalEquiv m ((n-m)/2) hk (Sum.inr (r, b))
  set j0 := canonicalEquiv m ((n-m)/2) hk (Sum.inr ((0 : Fin 2), b))
  -- Coordinate-by-coordinate proof
  ext l
  -- Convert goal to explicit form (bypass missing toFun_smul_real simp lemma)
  show starM (canonicalTubalData n m hm hpar)
    (fun l => if l = jr then 1 else 0) (fun l => if l = jr then 1 else 0) l =
    (if r = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)) *
    (if l = j0 then 1 else 0)
  by_cases hl : l.val < m
  · -- Real index: use canonical_starM_coord
    rw [canonical_starM_coord m hm hpar _ _ l hl]
    have hlr : ¬(l = jr) := fun h => by omega
    have hl0 : ¬(l = j0) := fun h => by
      have := canonicalEquiv_inr_ge hk 0 b; omega
    simp [if_neg hlr, if_neg hl0]
  · -- Pair index
    push Not at hl
    -- Unfold starM to complex form
    show (starMC (canonicalTubalData n m hm hpar)
      (toComplex (fun l => if l = jr then (1:ℝ) else 0))
      (toComplex (fun l => if l = jr then (1:ℝ) else 0)) l).re = _
    simp only [starMC, TubalData.applyMinv, TubalData.applyM, canonicalTubalData, htoC]
    -- Hadamard at different pair blocks is 0
    have hHad_diff : ∀ (t : Fin 2) (b' : Fin ((n-m)/2)), b' ≠ b →
        ((canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1:ℂ) else 0)) ∘ₕ
         (canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1:ℂ) else 0)))
          (canonicalEquiv m ((n-m)/2) hk (Sum.inr (t, b'))) = 0 := by
      intro t b' hbb; rw [hHad_eq, canonicalM_pair_diff m hm hpar t r b' b hbb,
        zero_pow (by norm_num : 2 ≠ 0)]
    -- Decompose l as pair index
    obtain ⟨s, b', hrb'⟩ := canonicalEquiv_symm_ge hk l hl
    have hl_eq : l = canonicalEquiv m ((n-m)/2) hk (Sum.inr (s, b')) := by
      have := (canonicalEquiv m ((n-m)/2) hk).apply_symm_apply l
      rw [hrb'] at this; exact this.symm
    -- Apply block diagonal structure of M⁻¹
    rw [hl_eq, canonicalMinv_mulVec_pair_coord m hm hpar _ s b']
    by_cases hbb : b' = b
    · -- Same pair: use pair_sq_sum_re
      rw [hbb]
      -- Replace had values with conjPairBlock squares
      have hHP : ∀ t : Fin 2,
          ((canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1:ℂ) else 0)) ∘ₕ
           (canonicalM n m hm hpar *ᵥ (fun l => if l = jr then (1:ℂ) else 0)))
            (canonicalEquiv m ((n-m)/2) hk (Sum.inr (t, b))) =
          (conjPairBlock t r) ^ 2 := by
        intro t; rw [hHad_eq]; congr 1; exact canonicalM_pair_same m hm hpar t r b
      simp_rw [hHP]
      rw [show (∑ t, conjPairBlockInv s t * (conjPairBlock t r) ^ 2).re =
        if s = 0 then (if r = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)) else 0
        from pair_sq_sum_re r s]
      -- Match with RHS
      by_cases hs : s = 0
      · subst hs
        have : canonicalEquiv m ((n-m)/2) hk (Sum.inr ((0 : Fin 2), b)) = j0 := rfl
        simp [if_pos this]
      · have hs1 : s = 1 := by fin_cases s <;> simp_all
        subst hs1
        simp only [show ¬((1 : Fin 2) = (0 : Fin 2)) from by decide, ite_false]
        have : canonicalEquiv m ((n-m)/2) hk (Sum.inr ((1:Fin 2), b)) ≠ j0 := by
          intro h; have := (canonicalEquiv m ((n-m)/2) hk).injective h; simp at this
        simp only [if_neg this, mul_zero]
    · -- Different pair: both sides are 0
      simp_rw [hHad_diff _ b' hbb, mul_zero, Finset.sum_const_zero, Complex.zero_re]
      have : canonicalEquiv m ((n-m)/2) hk (Sum.inr (s, b')) ≠ j0 := by
        intro h; have := (canonicalEquiv m ((n-m)/2) hk).injective h
        simp at this; exact hbb this.2
      simp [if_neg this]


-- @@ L461-461 verbatim
/-! ## Pair basis zero: AlgHom sends pair basis vectors to 0 -/


-- @@ L463-503 verbatim
/-- For any pair index j ≥ m, every ℝ-algebra homomorphism φ : KM → ℝ
    sends the standard basis vector e_j to 0. -/
private theorem algHom_pair_basis_zero (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (φ : KM n (canonicalTubalData n m hm hpar) →ₐ[ℝ] ℝ)
    (j : Fin n) (hj : j.val ≥ m) :
    φ (KM.ofFun (fun l => if l = j then 1 else 0)) = 0 := by
  let td := canonicalTubalData n m hm hpar
  set kk := (n - m) / 2
  have hk : m + 2 * kk = n := by omega
  obtain ⟨r, b, hrb⟩ := canonicalEquiv_symm_ge hk j hj
  have hj_eq : j = canonicalEquiv m kk hk (Sum.inr (r, b)) := by
    have := (canonicalEquiv m kk hk).apply_symm_apply j
    rw [hrb] at this; exact this.symm
  -- Parametrized basis vectors for each pair component
  let e_ : Fin 2 → KM n td := fun s =>
    KM.ofFun (fun l => if l = canonicalEquiv m kk hk (Sum.inr (s, b)) then (1 : ℝ) else 0)
  -- Pair square computations
  have hsq0 : e_ 0 * e_ 0 = (1 / Real.sqrt 2) • e_ 0 := pair_basis_sq m hm hpar b 0
  have hsq1 : e_ 1 * e_ 1 = (-(1 / Real.sqrt 2)) • e_ 0 := pair_basis_sq m hm hpar b 1
  -- Algebraic argument: φ(e_ 0) and φ(e_ 1) must both be 0
  have hφsq0 : φ (e_ 0) ^ 2 = (1 / Real.sqrt 2) * φ (e_ 0) := by
    have h := map_mul φ (e_ 0) (e_ 0); rw [hsq0, map_smul, smul_eq_mul] at h
    linarith [sq (φ (e_ 0))]
  have hφsq1 : φ (e_ 1) ^ 2 = (-(1 / Real.sqrt 2)) * φ (e_ 0) := by
    have h := map_mul φ (e_ 1) (e_ 1); rw [hsq1, map_smul, smul_eq_mul] at h
    linarith [sq (φ (e_ 1))]
  have hφ0 : φ (e_ 0) = 0 := by
    by_contra hne
    have hval : φ (e_ 0) = 1 / Real.sqrt 2 := by
      have h : φ (e_ 0) * (φ (e_ 0) - 1 / Real.sqrt 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hne
      · linarith
    rw [hval] at hφsq1
    nlinarith [sq_nonneg (φ (e_ 1)), (show (0 : ℝ) < 1 / Real.sqrt 2 from by positivity)]
  have hφ1 : φ (e_ 1) = 0 := by
    rw [hφ0, mul_zero] at hφsq1
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp (by linarith [sq_nonneg (φ (e_ 1))])
  -- The original basis vector e_j equals e_ r via hj_eq
  have : φ (e_ r) = 0 := by fin_cases r <;> assumption
  convert this using 2; ext l; simp only [KM.ofFun, e_]; rw [hj_eq]


-- @@ L505-505 verbatim
/-! ## AlgHom classification -/


-- @@ L507-551 verbatim
/-- Any ℝ-algebra homomorphism from the canonical ring to ℝ equals
    some coordinate projection `coordProj i` for `i < m`. -/
theorem algHom_canonical_eq_coordProj (m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2)
    (φ : KM n (canonicalTubalData n m hm hpar) →ₐ[ℝ] ℝ) :
    ∃ (i : Fin n) (hi : i.val < m), φ = coordProj m hm hpar i hi := by
  -- Standard basis vectors
  let e_ : Fin n → KM n (canonicalTubalData n m hm hpar) :=
    fun i => KM.ofFun (fun l => if l = i then 1 else 0)
  -- Key: for i < m, e_i * a = a(i) • e_i (from stdBasis_mul_canonical)
  have hprod : ∀ (i : Fin n) (hi : i.val < m)
      (a : KM n (canonicalTubalData n m hm hpar)),
      e_ i * a = KM.toFun a i • e_ i := by
    intro i hi a; ext l
    exact congr_fun (stdBasis_mul_canonical m hm hpar i hi (KM.toFun a)) l
  -- Consequence: φ(e_i) * φ(a) = a(i) * φ(e_i)
  have hkey : ∀ (i : Fin n) (hi : i.val < m)
      (a : KM n (canonicalTubalData n m hm hpar)),
      φ (e_ i) * φ a = KM.toFun a i * φ (e_ i) := by
    intro i hi a
    have h := map_mul φ (e_ i) a
    rw [hprod i hi a, map_smul, smul_eq_mul] at h; linarith
  -- Case 1: some φ(e_{i₀}) ≠ 0 for i₀ < m → φ = coordProj i₀
  by_cases hex : ∃ (i : Fin n) (hi : i.val < m), φ (e_ i) ≠ 0
  · obtain ⟨i₀, hi₀, hne⟩ := hex
    refine ⟨i₀, hi₀, AlgHom.ext (fun a => ?_)⟩
    rw [coordProj_apply]
    exact mul_left_cancel₀ hne ((hkey i₀ hi₀ a).trans (mul_comm _ _))
  · -- Case 2: all φ(e_i) = 0 → contradiction with φ(1) = 1
    push Not at hex; exfalso
    have hall : ∀ i : Fin n, φ (e_ i) = 0 := by
      intro i
      by_cases hi : i.val < m
      · exact hex i hi
      · exact algHom_pair_basis_zero m hm hpar φ i (by omega)
    -- φ vanishes on all standard basis vectors, so φ = 0 as a linear map
    have hφ_zero : φ.toLinearMap = 0 := by
      apply (Pi.basisFun ℝ (Fin n)).ext; intro i
      show φ (Pi.basisFun ℝ (Fin n) i) = 0
      have : Pi.basisFun ℝ (Fin n) i = e_ i := by
        ext l; simp [Pi.basisFun_apply, Pi.single_apply, e_, KM.ofFun, eq_comm]
      rw [this]; exact hall i
    have : φ 1 = 0 := by
      have h := LinearMap.congr_fun hφ_zero 1
      simp [AlgHom.toLinearMap_apply] at h
    linarith [map_one φ]


-- @@ L553-553 verbatim
/-! ## Reverse direction: isomorphic implies same realness -/


-- @@ L555-615 verbatim
/-- If `KM n td₁ ≃ₐ[ℝ] KM n td₂`, then `realness td₁ = realness td₂`. -/
theorem realness_of_algEquiv (td₁ td₂ : TubalData n)
    (h : Nonempty (KM n td₁ ≃ₐ[ℝ] KM n td₂)) :
    realness td₁ = realness td₂ := by
  set m₁ := realness td₁
  set m₂ := realness td₂
  -- Get isomorphisms to canonical rings
  obtain ⟨iso₁⟩ := KM_algEquiv_canonical td₁
  obtain ⟨iso₂⟩ := KM_algEquiv_canonical td₂
  obtain ⟨ψ⟩ := h
  -- Compose: canonical(m₁) ≃ₐ[ℝ] canonical(m₂)
  set ctd₁ := canonicalTubalData n m₁ (realness_le td₁) (realness_parity td₁)
  set ctd₂ := canonicalTubalData n m₂ (realness_le td₂) (realness_parity td₂)
  set ψ' : KM n ctd₁ ≃ₐ[ℝ] KM n ctd₂ := iso₁.symm.trans (ψ.trans iso₂)
  -- Injection {i < m₂} → {i < m₁}: for each i < m₂, coordProj₂ i ∘ ψ' is an AlgHom to ℝ
  -- By classification, it equals some coordProj₁ f(i) for f(i) < m₁
  have hinj : ∀ (i : Fin n) (hi : i.val < m₂),
      ∃ (j : Fin n) (hj : j.val < m₁),
        (coordProj m₂ (realness_le td₂) (realness_parity td₂) i hi).comp ψ'.toAlgHom =
        coordProj m₁ (realness_le td₁) (realness_parity td₁) j hj := by
    intro i hi
    exact algHom_canonical_eq_coordProj m₁ (realness_le td₁) (realness_parity td₁) _
  -- Key lemma: if canonical(m_s) ≃ₐ canonical(m_t), then m_t ≤ m_s
  -- (by pulling back coordProj's and using AlgHom classification)
  suffices key : ∀ (m_s m_t : ℕ) (hms : m_s ≤ n) (hps : n % 2 = m_s % 2)
      (hmt : m_t ≤ n) (hpt : n % 2 = m_t % 2),
      Nonempty (KM n (canonicalTubalData n m_s hms hps) ≃ₐ[ℝ]
       KM n (canonicalTubalData n m_t hmt hpt)) → m_t ≤ m_s by
    exact le_antisymm (key _ _ _ _ _ _ ⟨ψ'.symm⟩) (key _ _ _ _ _ _ ⟨ψ'⟩)
  intro m_s m_t hms hps hmt hpt ⟨φ⟩
  by_contra h_lt; push Not at h_lt
  -- For each i : Fin m_t, compose coordProj_t with φ to get AlgHom → ℝ
  -- By classification, it's coordProj_s(f(i)) for some f(i) < m_s
  have hf : ∀ (i : Fin m_t),
      ∃ (j : Fin n) (hj : j.val < m_s),
        (coordProj m_t hmt hpt ⟨i.val, by omega⟩ i.isLt).comp φ.toAlgHom =
        coordProj m_s hms hps j hj :=
    fun i => algHom_canonical_eq_coordProj m_s hms hps
      ((coordProj m_t hmt hpt ⟨i.val, by omega⟩ i.isLt).comp φ.toAlgHom)
  choose f hf_lt hf_eq using hf
  -- Build injection Fin m_t → Fin m_s
  set g : Fin m_t → Fin m_s := fun i => ⟨(f i).val, hf_lt i⟩
  -- g is injective
  have g_inj : Function.Injective g := by
    intro a b hab
    have hv : (g a).val = (g b).val := congr_arg Fin.val hab
    have hfab : f a = f b := Fin.ext hv
    -- Work pointwise via change to match comp form, avoiding coercion mismatch
    have hcp : coordProj m_t hmt hpt ⟨a.val, by omega⟩ a.isLt =
               coordProj m_t hmt hpt ⟨b.val, by omega⟩ b.isLt := by
      apply AlgHom.ext; intro y; obtain ⟨x, rfl⟩ := φ.surjective y
      have ha := AlgHom.congr_fun (hf_eq a) x
      have hb := AlgHom.congr_fun (hf_eq b) x
      change ((coordProj m_t hmt hpt ⟨a.val, _⟩ a.isLt).comp φ.toAlgHom) x =
             ((coordProj m_t hmt hpt ⟨b.val, _⟩ b.isLt).comp φ.toAlgHom) x
      rw [ha, hb]; simp only [coordProj_apply]; rw [hfab]
    have h := coordProj_injective m_t hmt hpt _ _ a.isLt b.isLt hcp
    have hv2 := congr_arg Fin.val h
    exact Fin.ext hv2
  -- Fin m_t injects into Fin m_s, but m_t > m_s — contradiction
  exact absurd (Fintype.card_le_of_injective g g_inj) (by simp; omega)


-- @@ L617-617 verbatim
/-! ## Proposition 13: same realness implies isomorphic -/


-- @@ L619-635 verbatim
/-- **Proposition 13**: If two tubal rings K_M and K_{M'} have the same realness,
    they are isomorphic as ℝ-algebras. -/
theorem KM_algEquiv_of_realness_eq (td₁ td₂ : TubalData n) (h : realness td₁ = realness td₂) :
    Nonempty (KM n td₁ ≃ₐ[ℝ] KM n td₂) := by
  obtain ⟨iso₁⟩ := KM_algEquiv_canonical td₁
  obtain ⟨iso₂⟩ := KM_algEquiv_canonical td₂
  -- The canonical targets are equal because realness td₁ = realness td₂
  have hctd : canonicalTubalData n (realness td₁) (realness_le td₁) (realness_parity td₁) =
    canonicalTubalData n (realness td₂) (realness_le td₂) (realness_parity td₂) := by
    -- Generalize to allow subst
    suffices ∀ (a b : ℕ) (hab : a = b) (ha : a ≤ n) (hb : b ≤ n)
        (hpa : n % 2 = a % 2) (hpb : n % 2 = b % 2),
        canonicalTubalData n a ha hpa = canonicalTubalData n b hb hpb from
      this _ _ h _ _ _ _
    intro a b hab; subst hab; intros; rfl
  rw [hctd] at iso₁
  exact ⟨iso₁.trans iso₂.symm⟩


-- @@ L637-640 verbatim
/-- **Proposition 13 (iff)**: Two tubal rings are isomorphic iff they have the same realness. -/
theorem KM_algEquiv_iff_realness_eq (td₁ td₂ : TubalData n) :
    Nonempty (KM n td₁ ≃ₐ[ℝ] KM n td₂) ↔ realness td₁ = realness td₂ :=
  ⟨realness_of_algEquiv td₁ td₂, KM_algEquiv_of_realness_eq td₁ td₂⟩


-- @@ L642-645 verbatim
/-! ## Ring isomorphism versions

Every ℝ-algebra isomorphism is a ring isomorphism, so the classification
results hold for ring isomorphisms as well. -/


-- @@ L647-651 verbatim
/-- **Proposition 66 (ring version)**: K_M is ring-isomorphic to K_{n,m}. -/
theorem KM_ringEquiv_canonical (td : TubalData n) :
    Nonempty (KM n td ≃+* KM n (canonicalTubalData n (realness td)
      (realness_le td) (realness_parity td))) :=
  (KM_algEquiv_canonical td).map AlgEquiv.toRingEquiv


-- @@ L653-657 verbatim
/-- **Proposition 13 (ring version, backward)**: Same realness implies ring-isomorphic. -/
theorem KM_ringEquiv_of_realness_eq (td₁ td₂ : TubalData n)
    (h : realness td₁ = realness td₂) :
    Nonempty (KM n td₁ ≃+* KM n td₂) :=
  (KM_algEquiv_of_realness_eq td₁ td₂ h).map AlgEquiv.toRingEquiv


-- @@ L659-664 verbatim
/-- Any ring homomorphism from KM to ℝ is automatically ℝ-linear, hence an AlgHom.
    This uses the fact that the only ring endomorphism of ℝ is the identity. -/
private noncomputable def ringHom_toAlgHom (td : TubalData n)
    (φ : KM n td →+* ℝ) : KM n td →ₐ[ℝ] ℝ :=
  { φ with commutes' := fun r =>
      Real.ringHom_apply (φ.comp (algebraMap ℝ (KM n td))) r }


-- @@ L666-669 verbatim
/-- `ringHom_toAlgHom` agrees with the original ring hom on all inputs. -/
private theorem ringHom_toAlgHom_apply (td : TubalData n)
    (φ : KM n td →+* ℝ) (x : KM n td) :
    ringHom_toAlgHom td φ x = φ x := rfl


-- @@ L671-712 verbatim
/-- **Proposition 13 (ring version, forward)**: Ring-isomorphic implies same realness. -/
theorem realness_of_ringEquiv (td₁ td₂ : TubalData n)
    (h : Nonempty (KM n td₁ ≃+* KM n td₂)) :
    realness td₁ = realness td₂ := by
  obtain ⟨f⟩ := h
  set m₁ := realness td₁; set m₂ := realness td₂
  obtain ⟨iso₁⟩ := KM_algEquiv_canonical td₁
  obtain ⟨iso₂⟩ := KM_algEquiv_canonical td₂
  set ψ' : KM n (canonicalTubalData n m₁ (realness_le td₁) (realness_parity td₁)) ≃+*
            KM n (canonicalTubalData n m₂ (realness_le td₂) (realness_parity td₂)) :=
    iso₁.symm.toRingEquiv.trans (f.trans iso₂.toRingEquiv)
  suffices key : ∀ (m_s m_t : ℕ) (hms : m_s ≤ n) (hps : n % 2 = m_s % 2)
      (hmt : m_t ≤ n) (hpt : n % 2 = m_t % 2),
      Nonempty (KM n (canonicalTubalData n m_s hms hps) ≃+*
       KM n (canonicalTubalData n m_t hmt hpt)) → m_t ≤ m_s by
    exact le_antisymm (key _ _ _ _ _ _ ⟨ψ'.symm⟩) (key _ _ _ _ _ _ ⟨ψ'⟩)
  intro m_s m_t hms hps hmt hpt ⟨φ⟩
  by_contra h_lt; push Not at h_lt
  -- For each i < m_t, coordProj_t(i) ∘ φ is a RingHom to ℝ.
  -- By ringHom_toAlgHom + classification, it equals some coordProj_s(f(i)).
  -- For each i < m_t, build an AlgHom from canonical(m_s) to ℝ and classify it
  let mkAlgHom (i : Fin m_t) : KM n (canonicalTubalData n m_s hms hps) →ₐ[ℝ] ℝ :=
    ringHom_toAlgHom _
      ((coordProj m_t hmt hpt ⟨i.val, by omega⟩ i.isLt).toRingHom.comp φ.toRingHom)
  have hf : ∀ (i : Fin m_t),
      ∃ (j : Fin n) (hj : j.val < m_s), mkAlgHom i = coordProj m_s hms hps j hj :=
    fun i => algHom_canonical_eq_coordProj m_s hms hps (mkAlgHom i)
  choose f' hf_lt hf_eq using hf
  set g : Fin m_t → Fin m_s := fun i => ⟨(f' i).val, hf_lt i⟩
  have g_inj : Function.Injective g := by
    intro a b hab
    have hv : (g a).val = (g b).val := congr_arg Fin.val hab
    have hfab : f' a = f' b := Fin.ext hv
    have hcp : coordProj m_t hmt hpt ⟨a.val, by omega⟩ a.isLt =
               coordProj m_t hmt hpt ⟨b.val, by omega⟩ b.isLt := by
      apply AlgHom.ext; intro y; obtain ⟨x, rfl⟩ := φ.surjective y
      show mkAlgHom a x = mkAlgHom b x
      rw [AlgHom.congr_fun (hf_eq a) x, AlgHom.congr_fun (hf_eq b) x]
      simp only [coordProj_apply, hfab]
    have h := congr_arg Fin.val (coordProj_injective m_t hmt hpt _ _ a.isLt b.isLt hcp)
    exact Fin.ext h
  exact absurd (Fintype.card_le_of_injective g g_inj) (by simp; omega)


-- @@ L714-717 verbatim
/-- **Proposition 13 (ring iff)**: Two tubal rings are ring-isomorphic iff same realness. -/
theorem KM_ringEquiv_iff_realness_eq (td₁ td₂ : TubalData n) :
    Nonempty (KM n td₁ ≃+* KM n td₂) ↔ realness td₁ = realness td₂ :=
  ⟨realness_of_ringEquiv td₁ td₂, fun h => KM_ringEquiv_of_realness_eq td₁ td₂ h⟩



-- @@ L720-720 verbatim
end TubalTensor
