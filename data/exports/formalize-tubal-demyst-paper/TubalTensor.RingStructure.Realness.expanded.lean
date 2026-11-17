import TubalTensor.Defs.StarMProduct


-- @@ L3-13 verbatim
/-!
  TubalTensor/RingStructure/Realness.lean
  Lemmas 65, 66, 67 (= full proof of Lemma 2).

  The main results here establish that the ⋆_M product preserves real vectors
  when M satisfies the realness condition (IsRealPaired).

  Core theorem: If M is real-paired and v has real-paired structure
  (real entries for real rows, conjugate entries for conjugate-pair rows),
  then M⁻¹v is a real vector.
-/


-- @@ L15-15 verbatim
namespace TubalTensor


-- @@ L17-17 verbatim
open Complex Matrix Finset


-- @@ L19-19 verbatim
variable {n : ℕ}


-- @@ L21-30 verbatim
/-! ## Core realness theorem

  Proof idea: Let c = M⁻¹v. Define w = conj(c). Show Mw = v = Mc.
  By injectivity of M, w = c, so c is real.

  To show Mw = v:
  - If row i of M is real: (Mw)_i = ∑_j M_{ij} conj(c_j) = conj(∑_j M_{ij} c_j) = conj(v_i) = v_i.
  - If rows i,k are conj pair: conj((Mw)_i) = ∑_j M_{kj} c_j = v_k = conj(v_i),
    so (Mw)_i = v_i.
-/


-- @@ L32-43 verbatim
/-- For a real row of M, conjugating the vector argument doesn't change the matrix-vector product
    (up to conjugation of the result). -/
private theorem mulVec_conj_real_row (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (i : Fin n) (hreal : IsRealRow M i) :
    ∑ j, M i j * starRingEnd ℂ (c j) = starRingEnd ℂ (∑ j, M i j * c j) := by
  rw [map_sum]
  congr 1; ext j
  rw [map_mul]
  -- LHS: M_{ij} * conj(c_j), RHS: conj(M_{ij}) * conj(c_j)
  -- Since row i is real, M_{ij} = conj(M_{ij})
  congr 1
  rw [starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr (hreal j)]


-- @@ L45-60 verbatim
/-- For conjugate-pair rows i,k of M, the matrix-vector product with conj(c) at row i
    equals the conjugate of the product at row k with c. -/
private theorem mulVec_conj_pair_row (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (i k : Fin n) (hconj : IsConjRow M i k) :
    starRingEnd ℂ (∑ j, M i j * starRingEnd ℂ (c j)) = ∑ j, M k j * c j := by
  rw [map_sum]
  congr 1; ext j
  rw [map_mul]
  -- LHS: conj(M_{ij}) * conj(conj(c_j)) = conj(M_{ij}) * c_j
  -- Need: conj(M_{ij}) = M_{kj} and conj(conj(c_j)) = c_j
  conv_lhs =>
    rw [show starRingEnd ℂ (starRingEnd ℂ (c j)) = c j from by
      rw [starRingEnd_apply, starRingEnd_apply, star_star]]
  congr 1
  rw [starRingEnd_apply, star_def]
  exact (hconj j).symm


-- @@ L62-103 verbatim
/-- Core lemma: M⁻¹ applied to a vector with real-paired structure gives a real vector.
    This encapsulates the content of Lemmas 65 and 67 (forward direction of Lemma 2). -/
theorem applyMinv_real_of_pairedStructure (td : TubalData n) (v : Fin n → ℂ)
    (hv : HasRealPairedStructure td v) :
    IsRealVec (td.applyMinv v) := by
  -- Let c = M⁻¹v
  set c := td.applyMinv v with hc_def
  -- We have Mc = v
  have hMc : td.applyM c = v := td.applyM_applyMinv v
  -- Define w = conj(c)
  set w : Fin n → ℂ := fun j => starRingEnd ℂ (c j) with hw_def
  -- Show Mw = v, then w = c by injectivity, then c is real
  suffices hMw : td.applyM w = v by
    have heq := td.applyM_injective (hMw.trans hMc.symm)
    intro j
    have hj := congr_fun heq j
    -- hj says w j = c j, i.e., conj(c j) = c j
    show (c j).im = 0
    have : starRingEnd ℂ (c j) = c j := hj
    rwa [starRingEnd_apply, star_def, Complex.conj_eq_iff_im] at this
  -- Prove Mw = v
  ext i
  simp only [TubalData.applyM_apply, hw_def]
  -- Use the real-paired structure of M
  rcases td.hM_real i with hreal | ⟨k, hki, hconj_row, _⟩
  · -- Case 1: Row i is real
    -- ∑_j M_{ij} conj(c_j) = conj(∑_j M_{ij} c_j) = conj(v_i) = v_i
    rw [mulVec_conj_real_row td.M c i hreal]
    -- conj(∑_j M_{ij} c_j) = v_i
    have hMci := congr_fun hMc i
    simp only [TubalData.applyM_apply] at hMci
    rw [hMci, starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr (hv.1 i hreal)]
  · -- Case 2: Rows i, k are conjugate pairs
    -- conj(∑_j M_{ij} conj(c_j)) = ∑_j M_{kj} c_j = v_k = conj(v_i)
    -- So ∑_j M_{ij} conj(c_j) = v_i
    apply_fun starRingEnd ℂ using (starRingEnd ℂ).injective
    rw [mulVec_conj_pair_row td.M c i k hconj_row]
    -- Now need: ∑_j M_{kj} c_j = conj(v_i)
    -- We know (Mc)_k = v_k and v_k = conj(v_i)
    have hMck := congr_fun hMc k
    simp only [TubalData.applyM_apply] at hMck
    rw [hMck, hv.2 i k hki hconj_row]


-- @@ L105-105 verbatim
/-! ## Lemma 63: Column structure of M⁻¹ mirrors row structure of M -/


-- @@ L107-118 verbatim
/-- If M is invertible and rows i, j are identical (i ≠ j), we get a contradiction.
    The proof uses M * M⁻¹ = I: diagonal entry (i,i) = 1 but (j,i) = 0,
    yet row-equality forces them to be equal. -/
private theorem identical_rows_absurd (td : TubalData n)
    {i j : Fin n} (hne : i ≠ j) (hrows : ∀ l, td.M i l = td.M j l) : False := by
  have h1 : (td.M * td.M_inv) i i = 1 := by
    simp [td.hM_right_inv]
  have h2 : (td.M * td.M_inv) j i = 0 := by
    simp [td.hM_right_inv, Matrix.one_apply, if_neg (Ne.symm hne)]
  have heq : (td.M * td.M_inv) i i = (td.M * td.M_inv) j i := by
    simp only [Matrix.mul_apply]; congr 1; ext l; rw [hrows]
  rw [heq] at h1; exact one_ne_zero (h1.symm ▸ h2)


-- @@ L120-136 verbatim
/-- A real row cannot be the conjugate partner of a different row.
    If row j is real and IsConjRow M i j (i.e., M j l = conj(M i l)), then rows i,j
    are identical, contradicting invertibility. -/
private theorem real_row_not_conj_partner (td : TubalData n)
    {i j : Fin n} (hj : IsRealRow td.M j) (hne : i ≠ j)
    (hconj : IsConjRow td.M i j) : False := by
  exact identical_rows_absurd td hne (fun l => by
    -- hconj l : M j l = conj(M i l)
    -- hj l : (M j l).im = 0
    -- conj(M i l) has im = 0 (from hconj l and hj l), so M i l has im = 0
    -- Therefore conj(M i l) = M i l, and M j l = M i l
    have him : (starRingEnd ℂ (td.M i l)).im = 0 := by
      rw [← hconj l]; exact hj l
    rw [starRingEnd_apply, star_def, Complex.conj_im, neg_eq_zero] at him
    have : starRingEnd ℂ (td.M i l) = td.M i l := by
      rw [starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr him]
    rw [hconj l, this])


-- @@ L138-142 verbatim
/-- Column j of M⁻¹ equals M⁻¹ applied to the j-th standard basis vector. -/
private theorem Minv_col_eq_applyMinv_single (td : TubalData n) (j i : Fin n) :
    td.M_inv i j = td.applyMinv (Pi.single j 1) i := by
  simp [TubalData.applyMinv_apply, Pi.single, Function.update,
    Finset.mem_univ, eq_comm]


-- @@ L144-163 verbatim
/-- Standard basis vector for a real row has paired structure. -/
private theorem single_hasPairedStructure_of_realRow (td : TubalData n)
    {j : Fin n} (hj : IsRealRow td.M j) :
    HasRealPairedStructure td (Pi.single j (1 : ℂ)) := by
  constructor
  · intro i _
    simp [Pi.single, Function.update]
    split <;> simp
  · intro i k hki hconj
    -- IsConjRow M i k means M k l = conj(M i l). Since i,k are a conj pair,
    -- neither equals j (j is real). So Pi.single j 1 is 0 at both i and k.
    have hi_ne_j : i ≠ j := by
      intro h; subst h
      -- IsConjRow M j k, and row j is real → contradiction
      exact real_row_not_conj_partner td hj hki (isConjRow_symm hconj)
    have hk_ne_j : k ≠ j := by
      intro h; subst h
      -- IsConjRow M i j, and row j is real → contradiction
      exact real_row_not_conj_partner td hj hki.symm hconj
    simp [Pi.single, Function.update, hi_ne_j, hk_ne_j]


-- @@ L165-171 verbatim
/-- Lemma 63, Part 1 (helper): If row j of M is real, then column j of M⁻¹ is real. -/
private theorem Minv_col_real_of_realRow (td : TubalData n) {j : Fin n}
    (hj : IsRealRow td.M j) :
    ∀ i : Fin n, (td.M_inv i j).im = 0 := by
  intro i
  rw [Minv_col_eq_applyMinv_single]
  exact applyMinv_real_of_pairedStructure td _ (single_hasPairedStructure_of_realRow td hj) i


-- @@ L173-182 verbatim
/-- The j-th column of M⁻¹, viewed as a function, satisfies M * col_j = e_j. -/
private theorem applyM_Minv_col (td : TubalData n) (j : Fin n) :
    td.applyM (fun i => td.M_inv i j) = Pi.single j 1 := by
  funext i
  simp only [TubalData.applyM_apply]
  -- ∑_l M_{i,l} * M⁻¹_{l,j} = (M * M⁻¹)_{i,j}
  have : ∑ l, td.M i l * td.M_inv l j = (td.M * td.M_inv) i j := by
    simp [Matrix.mul_apply]
  rw [this, td.hM_right_inv, Matrix.one_apply]
  simp [Pi.single, Function.update, eq_comm]


-- @@ L184-275 verbatim
/-- Lemma 63, Part 2 (helper): If rows j, k of M are conjugate (j ≠ k),
    then columns j, k of M⁻¹ are conjugate. -/
private theorem Minv_col_conj_of_conjRow (td : TubalData n) {j k : Fin n}
    (hjk : j ≠ k) (hconj : IsConjRow td.M j k) :
    ∀ i : Fin n, td.M_inv i k = starRingEnd ℂ (td.M_inv i j) := by
  -- Strategy: define w_i = conj(M⁻¹_{i,j}). Show M * w = e_k.
  -- Since M * col_k = e_k too, by injectivity w = col_k, giving the result.
  set cj : Fin n → ℂ := fun i => td.M_inv i j
  set ck : Fin n → ℂ := fun i => td.M_inv i k
  set w : Fin n → ℂ := fun i => starRingEnd ℂ (cj i)
  have hMcj : td.applyM cj = Pi.single j 1 := applyM_Minv_col td j
  have hMck : td.applyM ck = Pi.single k 1 := applyM_Minv_col td k
  -- Show M * w = e_k, then w = ck by injectivity
  suffices hMw : td.applyM w = Pi.single k 1 by
    have heq := td.applyM_injective (hMw.trans hMck.symm)
    intro i
    have := congr_fun heq i
    -- this : w i = ck i, i.e., conj(cj i) = ck i, i.e., conj(M⁻¹_{i,j}) = M⁻¹_{i,k}
    exact this.symm
  -- Prove M * w = e_k row by row
  funext i
  simp only [TubalData.applyM_apply, w]
  rcases td.hM_real i with hreal | ⟨i', hii', hconj_row, huniq⟩
  · -- Case 1: Row i is real
    rw [mulVec_conj_real_row td.M cj i hreal]
    have hMcj_i := congr_fun hMcj i
    simp only [TubalData.applyM_apply] at hMcj_i
    rw [hMcj_i]
    -- A real row can't equal j or k (both are in a conj pair)
    have hi_ne_j : i ≠ j := by
      intro h; subst h
      -- hconj : IsConjRow M j k (row k = conj(row j))
      -- isConjRow_symm: IsConjRow M k j (row j = conj(row k))
      -- real_row_not_conj_partner needs: IsRealRow M j, k ≠ j, IsConjRow M k j
      exact real_row_not_conj_partner td hreal hjk.symm (isConjRow_symm hconj)
    have hi_ne_k : i ≠ k := by
      intro h; subst h
      -- hconj : IsConjRow M j k. After subst i=k, row i=k is real.
      -- Need: IsRealRow M k, j ≠ k, IsConjRow M j k
      exact real_row_not_conj_partner td hreal hjk hconj
    simp [Pi.single, Function.update, hi_ne_j, hi_ne_k]
  · -- Case 2: Row i has conjugate pair i'
    apply_fun starRingEnd ℂ using (starRingEnd ℂ).injective
    rw [mulVec_conj_pair_row td.M cj i i' hconj_row]
    have hMcj_i' := congr_fun hMcj i'
    simp only [TubalData.applyM_apply] at hMcj_i'
    rw [hMcj_i']
    -- Need: Pi.single j 1 i' = conj(Pi.single k 1 i)
    by_cases hij : i = j
    · -- i = j, so i' = k by uniqueness (both are conj partners of row j)
      subst hij
      have hi'k : i' = k := by
        by_contra h
        -- i' and k are both conj of row j (IsConjRow M j i' and IsConjRow M j k)
        -- So rows i' and k are identical → contradiction
        exact identical_rows_absurd td h (fun l => by
          rw [hconj_row l, hconj l])
      rw [hi'k]
      simp [Pi.single, Function.update, hjk, Ne.symm hjk]
    · by_cases hik : i = k
      · -- i = k, so i' = j
        subst hik
        have hi'j : i' = j := by
          by_contra h
          -- IsConjRow M k i' (hconj_row) means row i' = conj(row k)
          -- isConjRow_symm hconj gives IsConjRow M k j, meaning row j = conj(row k)
          -- So rows i' and j are identical → contradiction
          exact identical_rows_absurd td h (fun l => by
            rw [hconj_row l, (isConjRow_symm hconj) l])
        rw [hi'j]
        simp [Pi.single, Function.update]
      · -- i ∉ {j, k}
        have hi'_ne_j : i' ≠ j := by
          intro h; subst h
          -- i' = j means IsConjRow M i j (row j = conj(row i))
          -- Also IsConjRow M j k (row k = conj(row j) = conj(conj(row i)) = row i)
          -- So rows i and k identical, but i ≠ k → contradiction
          exact identical_rows_absurd td hik (fun l => by
            have h1 := hconj_row l  -- td.M j l = starRingEnd ℂ (td.M i l)
            have h2 := hconj l      -- td.M k l = starRingEnd ℂ (td.M j l)
            rw [h2, h1, starRingEnd_apply, starRingEnd_apply, star_star])
        have hi'_ne_k : i' ≠ k := by
          intro h; subst h
          -- i' = k means IsConjRow M i k (row k = conj(row i))
          -- Also IsConjRow M j k (row k = conj(row j))
          -- So conj(row i) = conj(row j), meaning row i = row j, but i ≠ j → contradiction
          exact identical_rows_absurd td hij (fun l => by
            have h1 := hconj_row l  -- td.M k l = starRingEnd ℂ (td.M i l)
            have h2 := hconj l      -- td.M k l = starRingEnd ℂ (td.M j l)
            have : starRingEnd ℂ (td.M i l) = starRingEnd ℂ (td.M j l) := by rw [← h1, ← h2]
            exact (starRingEnd ℂ).injective this)
        simp [Pi.single, Function.update, hik, hi'_ne_j]


-- @@ L277-295 verbatim
/-- **Lemma 63**: The column structure of M⁻¹ mirrors the row structure of M.
    If rows j, k of M are conjugate (IsConjRow M j k), then columns j, k of M⁻¹
    are also conjugate: M⁻¹ᵢₖ = conj(M⁻¹ᵢⱼ) for all i.
    Special case j = k: if row j is real, then column j of M⁻¹ is real. -/
theorem Minv_col_conj_of_row_conj (td : TubalData n) {j k : Fin n}
    (h : IsConjRow td.M j k) :
    ∀ i : Fin n, td.M_inv i k = starRingEnd ℂ (td.M_inv i j) := by
  by_cases hjk : j = k
  · subst hjk
    -- IsConjRow M j j means row j is real
    have hreal : IsRealRow td.M j := by
      intro l
      have := h l  -- M j l = conj(M j l)
      rw [starRingEnd_apply, star_def, eq_comm, Complex.conj_eq_iff_im] at this
      exact this
    intro i
    have him := Minv_col_real_of_realRow td hreal i
    rw [starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr him]
  · exact Minv_col_conj_of_conjRow td hjk h


-- @@ L297-297 verbatim
/-! ## Lemma 64: M⁻¹M̄ is real -/


-- @@ L299-315 verbatim
/-- The conjugated column vector (fun i => conj(M i j)) has paired structure. -/
private theorem conjCol_hasPairedStructure (td : TubalData n) (j : Fin n) :
    HasRealPairedStructure td (fun i => starRingEnd ℂ (td.M i j)) := by
  constructor
  · intro i hreal
    -- If row i is real, then (M i j).im = 0, so conj(M i j).im = 0
    show (starRingEnd ℂ (td.M i j)).im = 0
    have h := hreal j
    rw [starRingEnd_apply, star_def, Complex.conj_im, neg_eq_zero]
    exact h
  · intro i k hki hconj
    -- Need: (fun i => conj(M i j)) k = conj((fun i => conj(M i j)) i)
    -- i.e., conj(M k j) = conj(conj(M i j))
    -- From IsConjRow M i k: M k j = conj(M i j)
    -- So conj(M k j) = conj(conj(M i j)). Done.
    show starRingEnd ℂ (td.M k j) = starRingEnd ℂ (starRingEnd ℂ (td.M i j))
    congr 1; exact hconj j


-- @@ L317-325 verbatim
/-- **Lemma 64**: M⁻¹M̄ is a real matrix.
    Every entry of M⁻¹ · conj(M) has zero imaginary part. -/
theorem Minv_mul_conjM_real (td : TubalData n) (i j : Fin n) :
    ((td.M_inv * td.M.map (starRingEnd ℂ)) i j).im = 0 := by
  -- Unfold to the sum form: (M⁻¹ * M̄)_{ij} = ∑_l M⁻¹_{il} * conj(M_{lj})
  simp only [Matrix.mul_apply, Matrix.map_apply]
  -- Column j of M̄ has paired structure, so M⁻¹ applied to it is real
  exact applyMinv_real_of_pairedStructure td
    (fun l => starRingEnd ℂ (td.M l j)) (conjCol_hasPairedStructure td j) i


-- @@ L327-327 verbatim
/-! ## Lemma 2/67 (reverse direction): if ⋆_M preserves ℝⁿ then M is IsRealPaired -/


-- @@ L329-340 verbatim
/-- If rows i, j of an invertible matrix are identical (i ≠ j), contradiction. -/
private theorem identical_rows_absurd_raw
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hM_right : M * M_inv = 1)
    {i j : Fin n} (hne : i ≠ j) (hrows : ∀ l, M i l = M j l) : False := by
  have h1 : (M * M_inv) i i = 1 := by
    rw [hM_right]; simp
  have h2 : (M * M_inv) j i = 0 := by
    rw [hM_right]; simp [Ne.symm hne]
  have heq : (M * M_inv) i i = (M * M_inv) j i := by
    simp only [Matrix.mul_apply]; congr 1; ext l; rw [hrows]
  rw [heq] at h1; exact one_ne_zero (h1.symm.trans h2)


-- @@ L342-351 verbatim
/-- M *ᵥ toComplex(Pi.single j 1) extracts column j of M. -/
private theorem mulVec_toComplex_single
    (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    M *ᵥ toComplex (Pi.single j 1) = fun i => M i j := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [toComplex_apply, Pi.single_eq_same]
  · intro l _ hlj; simp [toComplex_apply, Pi.single_eq_of_ne hlj]
  · intro habs; exact absurd (Finset.mem_univ j) habs


-- @@ L353-377 verbatim
/-- For real a, the entry (M⁻¹ diag(Ma) M)_{ij} is real. -/
private theorem Ra_entry_real
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hpres : ∀ a b : Fin n → ℝ,
      IsRealVec (M_inv *ᵥ ((M *ᵥ toComplex a) ∘ₕ (M *ᵥ toComplex b))))
    (a : Fin n → ℝ) (i j : Fin n) :
    ((M_inv * Matrix.diagonal (M *ᵥ toComplex a) * M) i j).im = 0 := by
  -- Specialize b = Pi.single j 1: the j-th entry of the result vector
  have hcol := hpres a (Pi.single j 1) i
  -- M * toComplex(e_j) = column j of M
  rw [mulVec_toComplex_single] at hcol
  -- (M_inv *ᵥ (Ma ∘ₕ col_j))_i is real
  -- Ma ∘ₕ col_j = diag(Ma) * col_j, so M_inv *ᵥ (diag(Ma) *ᵥ col_j) = (M_inv * diag(Ma)) *ᵥ col_j
  -- This equals (M_inv * diag(Ma) * M)_{i,j} since (A *ᵥ col_j)_i = sum_l A_{il} M_{lj} = (A*M)_{ij}
  -- (M_inv * diag(Ma) * M)_{ij} = sum_l M_inv_{il} * (Ma)_l * M_{lj}
  -- (M_inv *ᵥ (Ma ∘ₕ col_j))_i = sum_l M_inv_{il} * ((Ma)_l * M_{lj})
  suffices hsuff : (M_inv * Matrix.diagonal (M *ᵥ toComplex a) * M) i j =
      (M_inv *ᵥ ((M *ᵥ toComplex a) ∘ₕ fun l => M l j)) i by
    rw [hsuff]; exact hcol
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, vecHadamard_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_eq_single l]
  · simp; ring
  · intro m _ hml; simp [hml]
  · intro habs; exact absurd (Finset.mem_univ l) habs


-- @@ L379-414 verbatim
/-- The matrix equation: R_k = conj(R_k) entrywise, where R_k = M⁻¹ diag(col_k M) M.
    As a matrix: M⁻¹ diag(col_k M) M = conj(M⁻¹) diag(col_k conj(M)) conj(M). -/
private theorem Rk_eq_conj_Rk
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hRa : ∀ (a : Fin n → ℝ) (i j : Fin n),
      ((M_inv * Matrix.diagonal (M *ᵥ toComplex a) * M) i j).im = 0)
    (k : Fin n) :
    M_inv * Matrix.diagonal (fun l => M l k) * M =
    M_inv.map (starRingEnd ℂ) * Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) *
      M.map (starRingEnd ℂ) := by
  ext i' j'
  have h := hRa (Pi.single k 1) i' j'
  rw [mulVec_toComplex_single] at h
  -- The entry is real, so it equals its conjugate
  have hself : starRingEnd ℂ ((M_inv * Matrix.diagonal (fun l => M l k) * M) i' j') =
      (M_inv * Matrix.diagonal (fun l => M l k) * M) i' j' := by
    rw [starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr h]
  -- Compute the conjugate of (M_inv * diag * M)_{i'j'}
  -- = conj(sum_l (sum_m M_inv_{i'm} * diag_m) * M_{lj'})
  -- = sum_l conj(M_inv_{i'l}) * conj(M l k) * conj(M_{lj'})  [when diag collapses]
  -- = (conj(M_inv) * diag(conj col_k) * conj(M))_{i'j'}
  -- Both sides equal when expanded entrywise
  -- LHS (after conj = self): (M_inv * diag(col_k) * M)_{i'j'}
  -- RHS: (conj(M_inv) * diag(conj col_k) * conj(M))_{i'j'}
  -- = conj of (M_inv * diag(col_k) * M)_{i'j'} = LHS (by hself)
  symm; rw [← hself]
  -- Need: conj((M_inv * diag(col_k) * M)_{i'j'}) = (conj(M_inv) * diag(conj col_k) * conj(M))_{i'j'}
  -- This follows from: conj(A * B * C) = conj(A) * conj(B) * conj(C) as matrices
  have : (M_inv * Matrix.diagonal (fun l => M l k) * M).map (starRingEnd ℂ) =
      M_inv.map (starRingEnd ℂ) * Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) *
        M.map (starRingEnd ℂ) := by
    rw [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_mul (f := starRingEnd ℂ)]
    congr 1; congr 1
    ext a b
    simp [Matrix.diagonal_apply, Matrix.map_apply, apply_ite (starRingEnd ℂ), map_zero]
  rw [← this, Matrix.map_apply]


-- @@ L416-456 verbatim
/-- Core identity: N_{ij} * M_{jk} = conj(M_{ik}) * N_{ij} where N = conj(M) * M⁻¹. -/
private theorem N_entry_identity
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (_hM_left : M_inv * M = 1) (hM_right : M * M_inv = 1)
    (hRa : ∀ (a : Fin n → ℝ) (i j : Fin n),
      ((M_inv * Matrix.diagonal (M *ᵥ toComplex a) * M) i j).im = 0)
    (i j k : Fin n) :
    (M.map (starRingEnd ℂ) * M_inv) i j * M j k =
    starRingEnd ℂ (M i k) * (M.map (starRingEnd ℂ) * M_inv) i j := by
  set N := M.map (starRingEnd ℂ) * M_inv with hN_def
  have hconj_inv' : M.map (starRingEnd ℂ) * M_inv.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul (f := starRingEnd ℂ), hM_right,
      Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)]
  -- From Rk_eq_conj_Rk: M_inv * diag(col_k) * M = conj(M_inv) * diag(conj col_k) * conj(M)
  have hmat_eq := Rk_eq_conj_Rk hRa k
  -- Post-multiply by M_inv: M_inv * diag(col_k) = conj(M_inv) * diag(conj col_k) * conj(M) * M_inv
  have h1 : M_inv * Matrix.diagonal (fun l => M l k) =
      M_inv.map (starRingEnd ℂ) * Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) *
        M.map (starRingEnd ℂ) * M_inv := by
    have step1 : M_inv * Matrix.diagonal (fun l => M l k) =
        (M_inv * Matrix.diagonal (fun l => M l k) * M) * M_inv := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hM_right, Matrix.mul_one]
    rw [step1, hmat_eq]
  -- Pre-multiply by conj(M): N * diag(col_k) = diag(conj col_k) * N
  have h2 : N * Matrix.diagonal (fun l => M l k) =
      Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) * N := by
    calc N * Matrix.diagonal (fun l => M l k)
        = M.map (starRingEnd ℂ) * (M_inv * Matrix.diagonal (fun l => M l k)) := by
          rw [hN_def, Matrix.mul_assoc]
      _ = M.map (starRingEnd ℂ) * (M_inv.map (starRingEnd ℂ) *
            Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) *
            M.map (starRingEnd ℂ) * M_inv) := by rw [h1]
      _ = (M.map (starRingEnd ℂ) * M_inv.map (starRingEnd ℂ)) *
            Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) *
            (M.map (starRingEnd ℂ) * M_inv) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun l => starRingEnd ℂ (M l k)) * N := by
          rw [hconj_inv', Matrix.one_mul, hN_def]
  -- Extract the (i, j) entry
  have h3 := congr_fun (congr_fun h2 i) j
  rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3


-- @@ L458-475 verbatim
/-- If N_{ij} ≠ 0, then rows i and j of M are conjugate. -/
private theorem conjRow_of_N_nonzero
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    {i j : Fin n}
    (hN : ∀ k, (M.map (starRingEnd ℂ) * M_inv) i j * M j k =
               starRingEnd ℂ (M i k) * (M.map (starRingEnd ℂ) * M_inv) i j)
    (hne : (M.map (starRingEnd ℂ) * M_inv) i j ≠ 0) :
    IsConjRow M i j := by
  intro k
  have h := hN k
  -- N_{ij} * M_{jk} = conj(M_{ik}) * N_{ij}, cancel N_{ij} ≠ 0
  -- h : N_{ij} * M_{jk} = conj(M_{ik}) * N_{ij}
  -- Since ℂ is commutative: M_{jk} * N_{ij} = conj(M_{ik}) * N_{ij}
  -- Cancel N_{ij}: M_{jk} = conj(M_{ik})
  have h' : M j k * (M.map (starRingEnd ℂ) * M_inv) i j =
      starRingEnd ℂ (M i k) * (M.map (starRingEnd ℂ) * M_inv) i j := by
    rw [mul_comm]; exact h
  exact mul_right_cancel₀ hne h'


-- @@ L477-505 verbatim
/-- Each row of N = conj(M) * M⁻¹ has at least one nonzero entry. -/
private theorem N_row_has_nonzero
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hM_left : M_inv * M = 1) (hM_right : M * M_inv = 1)
    (i : Fin n) :
    ∃ j, (M.map (starRingEnd ℂ) * M_inv) i j ≠ 0 := by
  by_contra h
  push Not at h
  set N := M.map (starRingEnd ℂ) * M_inv
  -- N * (M * conj(M_inv)) = 1
  have hN_right : N * (M * M_inv.map (starRingEnd ℂ)) = 1 := by
    show M.map (starRingEnd ℂ) * M_inv * (M * M_inv.map (starRingEnd ℂ)) = 1
    calc M.map (starRingEnd ℂ) * M_inv * (M * M_inv.map (starRingEnd ℂ))
        = M.map (starRingEnd ℂ) * (M_inv * M) * M_inv.map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = M.map (starRingEnd ℂ) * M_inv.map (starRingEnd ℂ) := by
          rw [hM_left, Matrix.mul_one]
      _ = 1 := by
          rw [← Matrix.map_mul (f := starRingEnd ℂ), hM_right,
            Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)]
  -- Row i of N is zero: (N * anything)_{i, i} = 0
  have h1 : (N * (M * M_inv.map (starRingEnd ℂ))) i i = 1 := by
    rw [hN_right]; simp
  have h2 : (N * (M * M_inv.map (starRingEnd ℂ))) i i = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rw [h l, zero_mul]
  exact one_ne_zero (h1.symm.trans h2)


-- @@ L507-520 verbatim
/-- Each row of N has at most one nonzero entry. -/
private theorem N_row_unique_nonzero
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hM_right : M * M_inv = 1)
    (hNid : ∀ i j k, (M.map (starRingEnd ℂ) * M_inv) i j * M j k =
               starRingEnd ℂ (M i k) * (M.map (starRingEnd ℂ) * M_inv) i j)
    {i j l : Fin n}
    (hj : (M.map (starRingEnd ℂ) * M_inv) i j ≠ 0)
    (hl : (M.map (starRingEnd ℂ) * M_inv) i l ≠ 0) :
    j = l := by
  by_contra hjl
  have hcj := conjRow_of_N_nonzero (hNid i j) hj
  have hcl := conjRow_of_N_nonzero (hNid i l) hl
  exact identical_rows_absurd_raw hM_right hjl (fun k => by rw [hcj k, hcl k])


-- @@ L522-545 verbatim
/-- **Lemma 2/67 (reverse direction)**: If M is invertible and ⋆_M preserves ℝⁿ,
    then M is IsRealPaired. -/
theorem isRealPaired_of_starM_preserves_reals
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hM_left : M_inv * M = 1) (hM_right : M * M_inv = 1)
    (hpres : ∀ a b : Fin n → ℝ,
      IsRealVec (M_inv *ᵥ ((M *ᵥ toComplex a) ∘ₕ (M *ᵥ toComplex b)))) :
    IsRealPaired M := by
  have hRa := Ra_entry_real hpres
  have hNid := N_entry_identity hM_left hM_right hRa
  intro i
  obtain ⟨j, hj⟩ := N_row_has_nonzero hM_left hM_right i
  have hconj_ij := conjRow_of_N_nonzero (hNid i j) hj
  by_cases hij : j = i
  · -- j = i: row i is conjugate to itself → real
    subst hij; left; intro l
    have := hconj_ij l
    rw [starRingEnd_apply, star_def, eq_comm, Complex.conj_eq_iff_im] at this
    exact this
  · -- j ≠ i: row i has conjugate partner j
    right
    exact ⟨j, hij, hconj_ij, fun l _ hconj_il => by
      by_contra hjl
      exact identical_rows_absurd_raw hM_right hjl (fun k => by rw [hconj_ij k, hconj_il k])⟩


-- @@ L547-547 verbatim
/-! ## Main realness results -/


-- @@ L549-556 verbatim
/-- The ⋆_M product of real vectors is real (forward direction of Lemma 2 / Lemma 65).
    When M satisfies IsRealPaired, starMC td (toComplex a) (toComplex b) is a real vector. -/
theorem starMC_real (td : TubalData n) (a b : Fin n → ℝ) :
    IsRealVec (starMC td (toComplex a) (toComplex b)) := by
  apply applyMinv_real_of_pairedStructure
  exact vecHadamard_hasPairedStructure
    (applyM_toComplex_hasPairedStructure td a)
    (applyM_toComplex_hasPairedStructure td b)


-- @@ L558-570 verbatim
/-- **Lemma 2 / Lemma 65 (bundled iff)**: ⋆_M preserves ℝⁿ if and only if M is IsRealPaired.
    This combines the forward direction (starMC_real) and the reverse direction
    (isRealPaired_of_starM_preserves_reals). -/
theorem starM_preserves_reals_iff_isRealPaired
    {M M_inv : Matrix (Fin n) (Fin n) ℂ}
    (hM_left : M_inv * M = 1) (hM_right : M * M_inv = 1) :
    (∀ a b : Fin n → ℝ,
      IsRealVec (M_inv *ᵥ ((M *ᵥ toComplex a) ∘ₕ (M *ᵥ toComplex b)))) ↔
    IsRealPaired M := by
  constructor
  · exact isRealPaired_of_starM_preserves_reals hM_left hM_right
  · intro hRP a b
    exact starMC_real ⟨M, M_inv, hM_left, hM_right, hRP⟩ a b


-- @@ L572-576 verbatim
/-- The ⋆_M product via vecRe equals the complex version on real inputs. -/
theorem starM_eq_starMC (td : TubalData n) (a b : Fin n → ℝ) :
    toComplex (starM td a b) = starMC td (toComplex a) (toComplex b) := by
  apply toComplex_vecRe
  exact starMC_real td a b


-- @@ L578-585 verbatim
/-- The unit element eM = M⁻¹ 𝟙 is real. -/
theorem eM_isReal (td : TubalData n) :
    IsRealVec (td.applyMinv (allOnes n)) := by
  apply applyMinv_real_of_pairedStructure
  constructor
  · intro _ _; simp
  · intro i k _ hconj
    simp only [allOnes_apply, starRingEnd_apply, star_one]


-- @@ L587-589 verbatim
/-- M⁻¹ applied to the all-ones vector, as a real vector. -/
noncomputable def unitTube (td : TubalData n) : Fin n → ℝ :=
  vecRe (td.applyMinv (allOnes n))


-- @@ L591-594 verbatim
theorem toComplex_unitTube (td : TubalData n) :
    toComplex (unitTube td) = td.applyMinv (allOnes n) := by
  apply toComplex_vecRe
  exact eM_isReal td


-- @@ L596-596 verbatim
end TubalTensor
