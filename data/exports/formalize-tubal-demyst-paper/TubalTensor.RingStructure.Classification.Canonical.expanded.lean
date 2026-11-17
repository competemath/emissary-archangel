import TubalTensor.RingStructure.Classification.Realness


-- @@ L3-14 verbatim
/-!
  TubalTensor/RingStructure/Classification/Canonical.lean
  Canonical tubal matrix M_{n,m}, transport lemma, and Proposition 66.

  Main results:
  - `transportAlgEquiv`: if td₁.M = td₂.M * R_ℂ for real invertible R, then KM n td₁ ≃ₐ[ℝ] KM n td₂
  - `canonicalM`: the canonical tubal matrix M_{n,m} (Section 10.1)
  - `canonicalTubalData`: bundled TubalData for the canonical matrix
  - `realness_parity`: n % 2 = realness td % 2
  - `permuteAlgEquiv`: algebra isomorphism via row permutation
  - `KM_algEquiv_canonical`: KM n td is isomorphic to the canonical KM (Proposition 66)
-/


-- @@ L16-16 verbatim
namespace TubalTensor


-- @@ L18-18 verbatim
open Complex Matrix


-- @@ L20-20 verbatim
variable {n : ℕ}


-- @@ L22-22 verbatim
/-! ## Helper lemmas for real matrix–complex vector interplay -/


-- @@ L24-30 verbatim
/-- Complexification of a real matrix-vector product. -/
theorem toComplex_mulVec_real (R : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    toComplex (R *ᵥ a) = R.map ((↑) : ℝ → ℂ) *ᵥ toComplex a := by
  ext i
  simp only [toComplex_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl


-- @@ L32-39 verbatim
/-- A real matrix commutes with taking real parts. -/
theorem mulVec_vecRe_real (R : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) :
    R *ᵥ vecRe w = vecRe (R.map ((↑) : ℝ → ℂ) *ᵥ w) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecRe_apply, Matrix.map_apply]
  simp only [Complex.re_sum]
  congr 1; ext j
  exact (Complex.re_ofReal_mul _ _).symm


-- @@ L41-47 verbatim
/-- The map (↑ : ℝ → ℂ) applied to a matrix respects multiplication. -/
theorem map_ofReal_mul (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).map ((↑) : ℝ → ℂ) = A.map ((↑) : ℝ → ℂ) * B.map ((↑) : ℝ → ℂ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  push_cast
  rfl


-- @@ L49-56 verbatim
/-- The identity matrix maps to the identity matrix. -/
theorem map_ofReal_one :
    (1 : Matrix (Fin n) (Fin n) ℝ).map ((↑) : ℝ → ℂ) = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs with h
  · simp
  · simp


-- @@ L58-60 verbatim
/-- A complex number with zero imaginary part equals its real part cast to ℂ. -/
private theorem ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : (z.re : ℂ) = z := by
  apply Complex.ext <;> simp [h]


-- @@ L62-69 verbatim
/-- If all entries of a complex matrix have zero imaginary part, then it equals
    the complexification of the matrix of real parts. -/
theorem map_ofReal_re_of_im_zero {A : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, (A i j).im = 0) :
    (Matrix.of (fun i j => (A i j).re)).map ((↑) : ℝ → ℂ) = A := by
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  exact ofReal_re_of_im_zero (h i j)


-- @@ L71-110 verbatim
/-- If all entries of a complex matrix have zero imaginary part, then
    its inverse (given by Ainv) also has real entries. -/
theorem inv_real_of_real {A Ainv : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, (A i j).im = 0)
    (hL : Ainv * A = 1) (hR : A * Ainv = 1) :
    ∀ i j, (Ainv i j).im = 0 := by
  -- A is fixed by entry-wise conjugation (since entries are real)
  have hAconj : A.map (starRingEnd ℂ) = A := by
    ext i j; simp only [Matrix.map_apply]
    rw [starRingEnd_apply, star_def]
    exact Complex.conj_eq_iff_im.mpr (hA i j)
  -- Entry-wise conjugation preserves matrix multiplication
  have map_mul_conj : ∀ (X Y : Matrix (Fin n) (Fin n) ℂ),
      (X * Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) * Y.map (starRingEnd ℂ) := by
    intro X Y; ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  -- Entry-wise conjugation preserves identity
  have map_one_conj : (1 : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = 1 := by
    ext i j; rw [Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [map_one, map_zero]
  -- conj(Ainv) * A = 1
  have hconjL : Ainv.map (starRingEnd ℂ) * A = 1 := by
    calc Ainv.map (starRingEnd ℂ) * A
        = Ainv.map (starRingEnd ℂ) * A.map (starRingEnd ℂ) := by rw [hAconj]
      _ = (Ainv * A).map (starRingEnd ℂ) := (map_mul_conj Ainv A).symm
      _ = (1 : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) := by rw [hL]
      _ = 1 := map_one_conj
  -- By uniqueness of left inverse: conj(Ainv) = Ainv
  have heq : Ainv.map (starRingEnd ℂ) = Ainv :=
    calc Ainv.map (starRingEnd ℂ)
        = Ainv.map (starRingEnd ℂ) * 1 := (mul_one _).symm
      _ = Ainv.map (starRingEnd ℂ) * (A * Ainv) := by rw [hR]
      _ = (Ainv.map (starRingEnd ℂ) * A) * Ainv := (mul_assoc _ _ _).symm
      _ = 1 * Ainv := by rw [hconjL]
      _ = Ainv := one_mul _
  -- Extract: conj z = z implies z.im = 0
  intro i j
  have hij := congr_fun₂ heq i j
  rw [Matrix.map_apply, starRingEnd_apply, star_def] at hij
  exact Complex.conj_eq_iff_im.mp hij


-- @@ L112-116 verbatim
/-! ## Transport Lemma: the core of Propositions 68 and 12

  If td₁.M = td₂.M * R_ℂ for a real invertible matrix R,
  then the map x ↦ R *ᵥ x is an ℝ-algebra isomorphism KM n td₁ ≃ₐ[ℝ] KM n td₂.
-/


-- @@ L118-204 verbatim
/-- Transport lemma: if two TubalData are related by a real invertible change-of-basis,
    then their KM rings are isomorphic ℝ-algebras. -/
noncomputable def transportAlgEquiv (td₁ td₂ : TubalData n)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (R_inv : Matrix (Fin n) (Fin n) ℝ)
    (hRR : R_inv * R = 1)
    (hRR' : R * R_inv = 1)
    (hM : td₁.M = td₂.M * R.map ((↑) : ℝ → ℂ)) :
    KM n td₁ ≃ₐ[ℝ] KM n td₂ := by
  set R_ℂ := R.map ((↑) : ℝ → ℂ)
  -- Key derived fact: R_ℂ * td₁.M_inv = td₂.M_inv
  have hMinv : R_ℂ * td₁.M_inv = td₂.M_inv := by
    have h1 : td₂.M_inv * td₁.M = R_ℂ := by
      calc td₂.M_inv * td₁.M
          = td₂.M_inv * (td₂.M * R_ℂ) := by rw [hM]
        _ = (td₂.M_inv * td₂.M) * R_ℂ := by rw [mul_assoc]
        _ = 1 * R_ℂ := by rw [td₂.hM_left_inv]
        _ = R_ℂ := one_mul _
    calc R_ℂ * td₁.M_inv
        = td₂.M_inv * td₁.M * td₁.M_inv := by rw [h1]
      _ = td₂.M_inv * (td₁.M * td₁.M_inv) := by rw [mul_assoc]
      _ = td₂.M_inv * 1 := by rw [td₁.hM_right_inv]
      _ = td₂.M_inv := mul_one _
  -- td₁.M *ᵥ v = td₂.M *ᵥ (R_ℂ *ᵥ v)
  have hM_mulVec : ∀ v : Fin n → ℂ,
      td₁.M *ᵥ v = td₂.M *ᵥ (R_ℂ *ᵥ v) := by
    intro v
    -- td₁.M *ᵥ v = (td₂.M * R_ℂ) *ᵥ v = td₂.M *ᵥ (R_ℂ *ᵥ v)
    conv_lhs => rw [hM]
    exact (mulVec_mulVec v td₂.M R_ℂ).symm
  -- R_ℂ *ᵥ (M₁_inv *ᵥ w) = M₂_inv *ᵥ w
  have hMinv_mulVec : ∀ w : Fin n → ℂ,
      R_ℂ *ᵥ (td₁.M_inv *ᵥ w) = td₂.M_inv *ᵥ w := by
    intro w
    -- R_ℂ *ᵥ (M₁⁻¹ *ᵥ w) = (R_ℂ * M₁⁻¹) *ᵥ w = M₂⁻¹ *ᵥ w
    rw [mulVec_mulVec w R_ℂ td₁.M_inv, hMinv]
  -- R *ᵥ preserves the ⋆_M product (complex level first)
  have hMul_C : ∀ (a b : Fin n → ℂ),
      R_ℂ *ᵥ starMC td₁ a b = starMC td₂ (R_ℂ *ᵥ a) (R_ℂ *ᵥ b) := by
    intro a b
    simp only [starMC, TubalData.applyMinv, TubalData.applyM]
    rw [hMinv_mulVec]
    congr 1; congr 1 <;> exact (hM_mulVec _)
  -- R *ᵥ preserves the ⋆_M product (real level)
  have hMul : ∀ (a b : Fin n → ℝ),
      R *ᵥ (starM td₁ a b) = starM td₂ (R *ᵥ a) (R *ᵥ b) := by
    intro a b
    apply toComplex_injective
    rw [toComplex_mulVec_real, starM_eq_starMC, hMul_C, starM_eq_starMC,
        toComplex_mulVec_real, toComplex_mulVec_real]
  -- R *ᵥ preserves the unit element
  have hOne : R *ᵥ unitTube td₁ = unitTube td₂ := by
    apply toComplex_injective
    rw [toComplex_mulVec_real, toComplex_unitTube, toComplex_unitTube]
    show R_ℂ *ᵥ (td₁.M_inv *ᵥ allOnes n) = td₂.M_inv *ᵥ allOnes n
    exact hMinv_mulVec _
  -- Bijectivity from R_inv * R = 1 and R * R_inv = 1
  have hLI : ∀ a : KM n td₁, R_inv *ᵥ (R *ᵥ KM.toFun a) = KM.toFun a := by
    intro a
    rw [mulVec_mulVec (KM.toFun a) R_inv R, hRR, one_mulVec]
  have hRI : ∀ b : KM n td₂, R *ᵥ (R_inv *ᵥ KM.toFun b) = KM.toFun b := by
    intro b
    rw [mulVec_mulVec (KM.toFun b) R R_inv, hRR', one_mulVec]
  -- Construct the AlgEquiv
  exact {
    toFun := fun (a : KM n td₁) => KM.ofFun (R *ᵥ KM.toFun a)
    invFun := fun (b : KM n td₂) => KM.ofFun (R_inv *ᵥ KM.toFun b)
    left_inv := fun a => by
      show KM.ofFun (R_inv *ᵥ (R *ᵥ KM.toFun a)) = a
      exact congr_arg KM.ofFun (hLI a)
    right_inv := fun b => by
      show KM.ofFun (R *ᵥ (R_inv *ᵥ KM.toFun b)) = b
      exact congr_arg KM.ofFun (hRI b)
    map_mul' := fun a b => by
      show KM.ofFun (R *ᵥ starM td₁ (KM.toFun a) (KM.toFun b)) =
        KM.ofFun (starM td₂ (R *ᵥ KM.toFun a) (R *ᵥ KM.toFun b))
      exact congr_arg KM.ofFun (hMul _ _)
    map_add' := fun a b => by
      show KM.ofFun (R *ᵥ (KM.toFun a + KM.toFun b)) =
        KM.ofFun (R *ᵥ KM.toFun a + R *ᵥ KM.toFun b)
      exact congr_arg KM.ofFun (mulVec_add _ _ _)
    commutes' := fun r => by
      show KM.ofFun (R *ᵥ KM.toFun (algebraMap ℝ (KM n td₁) r)) =
        algebraMap ℝ (KM n td₂) r
      change KM.ofFun (R *ᵥ (r • unitTube td₁)) = KM.ofFun (r • unitTube td₂)
      exact congr_arg KM.ofFun (by rw [mulVec_smul, hOne])
  }


-- @@ L206-206 verbatim
/-! ## Block-matrix building blocks for canonical M_{n,m} -/


-- @@ L208-212 verbatim
/-- The 2×2 conjugate-pair block F₂.
    Row 0 = [1/√2, -i/√2], Row 1 = [1/√2, i/√2]. -/
noncomputable def conjPairBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / ↑(Real.sqrt 2), -Complex.I / ↑(Real.sqrt 2);
     1 / ↑(Real.sqrt 2),  Complex.I / ↑(Real.sqrt 2)]


-- @@ L214-218 verbatim
/-- The inverse of the 2×2 conjugate-pair block.
    Row 0 = [1/√2, 1/√2], Row 1 = [i/√2, -i/√2]. -/
noncomputable def conjPairBlockInv : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / ↑(Real.sqrt 2),  1 / ↑(Real.sqrt 2);
     Complex.I / ↑(Real.sqrt 2), -Complex.I / ↑(Real.sqrt 2)]


-- @@ L220-221 verbatim
private theorem sqrt2_cast_ne_zero : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (2 : ℝ) > 0)


-- @@ L223-225 verbatim
private theorem sqrt2_cast_mul_self : (↑(Real.sqrt 2) : ℂ) * ↑(Real.sqrt 2) = 2 := by
  have := Real.mul_self_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
  exact_mod_cast this


-- @@ L227-228 verbatim
private theorem inv_sqrt2_sq : ((↑(Real.sqrt 2) : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
  rw [sq, ← mul_inv, sqrt2_cast_mul_self]


-- @@ L230-230 verbatim
private theorem sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

-- @@ L231-231 verbatim
private theorem sqrt2_nonneg : (0 : ℝ) ≤ 2 := by norm_num


-- @@ L233-236 verbatim
private theorem conjPairBlock_mul_aux (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (_hA : A = conjPairBlockInv ∨ A = conjPairBlock)
    (_hB : B = conjPairBlock ∨ B = conjPairBlockInv)
    (h : A * B = 1) : A * B = 1 := h


-- @@ L238-249 verbatim
theorem conjPairBlockInv_mul_conjPairBlock :
    conjPairBlockInv * conjPairBlock = 1 := by
  ext i j
  simp only [conjPairBlockInv, conjPairBlock, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp_all <;> apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_ofReal, Complex.neg_re, Complex.neg_im,
      Real.mul_self_sqrt sqrt2_nonneg] <;>
    field_simp <;>
    nlinarith [Real.mul_self_sqrt sqrt2_nonneg]


-- @@ L251-262 verbatim
theorem conjPairBlock_mul_conjPairBlockInv :
    conjPairBlock * conjPairBlockInv = 1 := by
  ext i j
  simp only [conjPairBlock, conjPairBlockInv, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp_all <;> apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_ofReal, Complex.neg_re, Complex.neg_im,
      Real.mul_self_sqrt sqrt2_nonneg] <;>
    field_simp <;>
    nlinarith [Real.mul_self_sqrt sqrt2_nonneg]


-- @@ L264-268 verbatim
/-- Block-form canonical matrix on the sum index type `Fin m ⊕ (Fin 2 × Fin k)`.
    Top-left: identity. Bottom-right: block-diagonal of F₂ copies. -/
noncomputable def canonicalM_block (m k : ℕ) :
    Matrix (Fin m ⊕ (Fin 2 × Fin k)) (Fin m ⊕ (Fin 2 × Fin k)) ℂ :=
  fromBlocks 1 0 0 (blockDiagonal (fun _ : Fin k => conjPairBlock))


-- @@ L270-273 verbatim
/-- Block-form inverse canonical matrix. -/
noncomputable def canonicalMinv_block (m k : ℕ) :
    Matrix (Fin m ⊕ (Fin 2 × Fin k)) (Fin m ⊕ (Fin 2 × Fin k)) ℂ :=
  fromBlocks 1 0 0 (blockDiagonal (fun _ : Fin k => conjPairBlockInv))


-- @@ L275-282 verbatim
theorem canonicalMinv_block_mul (m k : ℕ) :
    canonicalMinv_block m k * canonicalM_block m k = 1 := by
  unfold canonicalMinv_block canonicalM_block
  rw [fromBlocks_multiply, ← blockDiagonal_mul]
  simp [conjPairBlockInv_mul_conjPairBlock]
  show fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0
    (blockDiagonal (1 : Fin k → Matrix (Fin 2) (Fin 2) ℂ)) = 1
  rw [blockDiagonal_one]; exact fromBlocks_one


-- @@ L284-291 verbatim
theorem canonicalM_block_mul_inv (m k : ℕ) :
    canonicalM_block m k * canonicalMinv_block m k = 1 := by
  unfold canonicalM_block canonicalMinv_block
  rw [fromBlocks_multiply, ← blockDiagonal_mul]
  simp [conjPairBlock_mul_conjPairBlockInv]
  show fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0
    (blockDiagonal (1 : Fin k → Matrix (Fin 2) (Fin 2) ℂ)) = 1
  rw [blockDiagonal_one]; exact fromBlocks_one


-- @@ L293-293 verbatim
/-! ## Index equivalence for block structure -/


-- @@ L295-302 verbatim
/-- The index equivalence `Fin m ⊕ (Fin 2 × Fin k) ≃ Fin n` for the canonical matrix,
    where `k = (n - m) / 2`. Maps:
    - `Sum.inl i` → index `i` (first m indices, identity rows)
    - `Sum.inr (a, b)` → conjugate-pair rows (via `finProdFinEquiv` then `finSumFinEquiv`) -/
noncomputable def canonicalEquiv (m k : ℕ) (h : m + 2 * k = n) :
    Fin m ⊕ (Fin 2 × Fin k) ≃ Fin n :=
  ((Equiv.sumCongr (Equiv.refl (Fin m)) finProdFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))


-- @@ L304-304 verbatim
/-! ## Canonical tubal matrix M_{n,m} (Section 10.1) — block-matrix redesign -/


-- @@ L306-312 verbatim
/-- The canonical tubal matrix M_{n,m}, defined via block structure:
    `[[I_m, 0], [0, blockDiag(F₂)]]` reindexed to `Fin n` via `canonicalEquiv`. -/
noncomputable def canonicalM (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    Matrix (Fin n) (Fin n) ℂ :=
  (canonicalM_block m ((n - m) / 2)).submatrix
    (canonicalEquiv m ((n - m) / 2) (by omega)).symm
    (canonicalEquiv m ((n - m) / 2) (by omega)).symm


-- @@ L314-319 verbatim
/-- The inverse of the canonical tubal matrix M_{n,m}. -/
noncomputable def canonicalMinv (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    Matrix (Fin n) (Fin n) ℂ :=
  (canonicalMinv_block m ((n - m) / 2)).submatrix
    (canonicalEquiv m ((n - m) / 2) (by omega)).symm
    (canonicalEquiv m ((n - m) / 2) (by omega)).symm


-- @@ L321-324 verbatim
/-- Row 1 of F₂ is the entrywise conjugate of row 0. -/
private theorem conjPairBlock_conj_rows :
    ∀ j : Fin 2, conjPairBlock 1 j = starRingEnd ℂ (conjPairBlock 0 j) := by
  intro j; fin_cases j <;> simp [conjPairBlock]


-- @@ L326-331 verbatim
/-- Row 0 of F₂ is the entrywise conjugate of row 1. -/
private theorem conjPairBlock_conj_rows' :
    ∀ j : Fin 2, conjPairBlock 0 j = starRingEnd ℂ (conjPairBlock 1 j) := by
  intro j
  have h := conjPairBlock_conj_rows j
  rw [h, starRingEnd_apply, starRingEnd_apply, star_star]


-- @@ L333-339 verbatim
/-- Each row of F₂ has a non-real entry (at column 1). -/
private theorem conjPairBlock_not_allReal (r : Fin 2) :
    (conjPairBlock r 1).im ≠ 0 := by
  have hsqrt : (Real.sqrt 2)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (2 : ℝ) > 0)))
  fin_cases r <;> simp [conjPairBlock, Complex.div_ofReal, Complex.neg_im, Complex.I_im,
    Complex.I_re]


-- @@ L341-461 verbatim
/-- The canonical matrix is real-paired: first m rows are real,
    remaining rows come in conjugate pairs. -/
theorem canonicalM_isRealPaired (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    IsRealPaired (canonicalM n m hm hpar) := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  set e := canonicalEquiv m k hk
  -- Every entry factors through the block structure
  have entry_eq : ∀ i j, canonicalM n m hm hpar i j =
      canonicalM_block m k (e.symm i) (e.symm j) := fun _ _ => rfl
  intro i
  rcases h : e.symm i with a | ⟨r, b⟩
  · -- Identity row: all entries are real
    left; intro j
    rw [entry_eq, h]
    rcases h' : e.symm j with c | ⟨s, d⟩
    · simp [canonicalM_block, fromBlocks_apply₁₁, one_apply]
      split_ifs <;> simp
    · simp [canonicalM_block, fromBlocks_apply₁₂, Matrix.zero_apply]
  · -- Conjugate-pair row
    right
    -- Partner: the other Fin 2 index at the same block
    have hr_other : ∀ (r : Fin 2), ∃ r' : Fin 2, r' ≠ r ∧
        (∀ j, conjPairBlock r' j = starRingEnd ℂ (conjPairBlock r j)) := by
      intro r; fin_cases r
      · exact ⟨1, by decide, conjPairBlock_conj_rows⟩
      · exact ⟨0, by decide, conjPairBlock_conj_rows'⟩
    obtain ⟨r', hr'_ne, hr'_conj⟩ := hr_other r
    refine ⟨e (Sum.inr (r', b)), ?_, ?_, ?_⟩
    · -- partner ≠ i
      intro heq
      have := congr_arg e.symm heq
      simp at this; rw [h] at this
      exact absurd (congr_arg Prod.fst (Sum.inr.inj this)) hr'_ne
    · -- IsConjRow
      intro j
      rw [entry_eq, entry_eq, h]
      simp only [Equiv.symm_apply_apply]
      rcases h' : e.symm j with c | ⟨s, d⟩
      · simp [canonicalM_block, fromBlocks_apply₂₁]
      · simp only [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply]
        split
        · next hbd => subst hbd; exact hr'_conj _
        · simp [starRingEnd_apply]
    · -- Uniqueness
      intro l hl hconj
      -- Use column j₁ = e(Sum.inr (1, b)) to distinguish
      have h_entry_l : ∀ j, canonicalM n m hm hpar l j =
          canonicalM_block m k (e.symm l) (e.symm j) := fun _ => rfl
      -- Row i has a non-real entry, so conj partner l can't be an identity row
      -- Look at a specific column to pin down e.symm l
      set j₁ := e (Sum.inr (1, b))
      have hj₁ : e.symm j₁ = Sum.inr (1, b) := by simp [j₁]
      -- Entry of row i at j₁
      have hi_j₁ : canonicalM n m hm hpar i j₁ =
          conjPairBlock r 1 := by
        rw [entry_eq, h, hj₁]
        simp [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]
      -- Entry of row l at j₁ must be conj of that
      have hl_j₁ : canonicalM n m hm hpar l j₁ =
          starRingEnd ℂ (conjPairBlock r 1) := by
        rw [show canonicalM n m hm hpar l j₁ = starRingEnd ℂ (canonicalM n m hm hpar i j₁)
            from hconj j₁, hi_j₁]
      -- Also look at j₀
      set j₀ := e (Sum.inr (0, b))
      have hj₀ : e.symm j₀ = Sum.inr (0, b) := by simp [j₀]
      have hi_j₀ : canonicalM n m hm hpar i j₀ = conjPairBlock r 0 := by
        rw [entry_eq, h, hj₀]
        simp [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]
      have hl_j₀ : canonicalM n m hm hpar l j₀ =
          starRingEnd ℂ (conjPairBlock r 0) := by
        rw [show canonicalM n m hm hpar l j₀ = starRingEnd ℂ (canonicalM n m hm hpar i j₀)
            from hconj j₀, hi_j₀]
      -- Now case-split on e.symm l
      rcases hl_eq : e.symm l with a' | ⟨r'', b'⟩
      · -- l is an identity row → entry at j₁ is 0, but should be nonzero
        exfalso
        have : canonicalM n m hm hpar l j₁ = 0 := by
          rw [h_entry_l, hl_eq, hj₁]
          simp [canonicalM_block, fromBlocks_apply₁₂]
        rw [this] at hl_j₁
        have : (starRingEnd ℂ (conjPairBlock r 1)).im ≠ 0 := by
          rw [starRingEnd_apply, star_def, Complex.conj_im, neg_ne_zero]
          exact conjPairBlock_not_allReal r
        rw [← hl_j₁] at this; exact this (by simp)
      · -- l is a block row at (r'', b')
        -- Entry at j₀: if b' ≠ b then 0, contradicts nonzero
        have hb'_eq : b' = b := by
          by_contra hne
          have : canonicalM n m hm hpar l j₀ = 0 := by
            rw [h_entry_l, hl_eq, hj₀]
            simp [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_ne _ _ _ hne]
          rw [this] at hl_j₀
          have hzero : conjPairBlock r 0 = 0 := by
            rwa [eq_comm, map_eq_zero_iff _ (starRingEnd ℂ).injective] at hl_j₀
          -- But F₂ r 0 = 1/√2 ≠ 0
          have : (1 : ℂ) / ↑(Real.sqrt 2) = 0 := by
            fin_cases r <;> simp [conjPairBlock] at hzero
          exact (div_ne_zero one_ne_zero sqrt2_cast_ne_zero) this
        -- Entry at j₁ with b' = b: F₂ r'' 1 = conj(F₂ r 1)
        have hl_j₁' : conjPairBlock r'' 1 = starRingEnd ℂ (conjPairBlock r 1) := by
          have : canonicalM n m hm hpar l j₁ = conjPairBlock r'' 1 := by
            rw [h_entry_l, hl_eq, hj₁]; rw [hb'_eq]
            simp [canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]
          rw [← this]; exact hl_j₁
        -- conjPairBlock r'' 1 = conjPairBlock r' 1
        have hgoal : conjPairBlock r'' 1 = conjPairBlock r' 1 := by
          rw [hl_j₁', hr'_conj 1]
        -- F₂ has distinct entries at column 1 for different row indices
        have hr''_eq : r'' = r' := by
          by_contra h_ne
          have : conjPairBlock r'' 1 ≠ conjPairBlock r' 1 := by
            fin_cases r'' <;> fin_cases r' <;> (try exact absurd rfl h_ne) <;>
              intro heq <;> simp [conjPairBlock] at heq <;>
              have := congr_arg Complex.im heq <;>
              simp [Complex.I_im, Complex.neg_im] at this <;>
              linarith [Real.sqrt_pos_of_pos (show (2 : ℝ) > 0 by norm_num)]
          exact this hgoal
        -- Now e.symm l = Sum.inr (r', b), so l = e(Sum.inr(r', b)) = partner
        calc l = e (e.symm l) := (Equiv.apply_symm_apply e l).symm
          _ = e (Sum.inr (r', b)) := by rw [hl_eq, hb'_eq, hr''_eq]


-- @@ L463-467 verbatim
/-- The canonical inverse is a left inverse. -/
theorem canonicalMinv_mul_canonicalM (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    canonicalMinv n m hm hpar * canonicalM n m hm hpar = 1 := by
  simp only [canonicalMinv, canonicalM]
  rw [submatrix_mul_equiv, canonicalMinv_block_mul, submatrix_one_equiv]


-- @@ L469-473 verbatim
/-- The canonical inverse is a right inverse. -/
theorem canonicalM_mul_canonicalMinv (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    canonicalM n m hm hpar * canonicalMinv n m hm hpar = 1 := by
  simp only [canonicalM, canonicalMinv]
  rw [submatrix_mul_equiv, canonicalM_block_mul_inv, submatrix_one_equiv]


-- @@ L475-482 verbatim
/-- Bundle the canonical matrix into TubalData. -/
noncomputable def canonicalTubalData (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    TubalData n where
  M := canonicalM n m hm hpar
  M_inv := canonicalMinv n m hm hpar
  hM_left_inv := canonicalMinv_mul_canonicalM n m hm hpar
  hM_right_inv := canonicalM_mul_canonicalMinv n m hm hpar
  hM_real := canonicalM_isRealPaired n m hm hpar


-- @@ L484-526 verbatim
/-- The realness of the canonical TubalData is m. -/
theorem realness_canonicalTubalData (n m : ℕ) (hm : m ≤ n) (hpar : n % 2 = m % 2) :
    realness (canonicalTubalData n m hm hpar) = m := by
  set k := (n - m) / 2
  have hk : m + 2 * k = n := by omega
  set e := canonicalEquiv m k hk
  -- A row i is real iff e.symm i is in the identity block (Sum.inl)
  have not_real_of_inr : ∀ (i : Fin n) (r : Fin 2) (b : Fin k),
      e.symm i = Sum.inr (r, b) → ¬∀ j, ((canonicalM n m hm hpar) i j).im = 0 := by
    intro i r b hi hreal
    have h1 : (canonicalM n m hm hpar i (e (Sum.inr (1, b)))).im = 0 := hreal _
    have h2 : canonicalM n m hm hpar i (e (Sum.inr (1, b))) = conjPairBlock r 1 := by
      show canonicalM_block m k (e.symm i) (e.symm (e (Sum.inr (1, b)))) = _
      simp [hi, canonicalM_block, fromBlocks_apply₂₂, blockDiagonal_apply_eq]
    rw [h2] at h1
    exact conjPairBlock_not_allReal r h1
  have real_of_inl : ∀ (i : Fin n) (a : Fin m),
      e.symm i = Sum.inl a → ∀ j, ((canonicalM n m hm hpar) i j).im = 0 := by
    intro i a hi j
    show (canonicalM_block m k (e.symm i) (e.symm j)).im = 0
    rw [hi]
    rcases h' : e.symm j with c | ⟨s, d⟩
    · simp [canonicalM_block, fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · simp [canonicalM_block, fromBlocks_apply₁₂, Matrix.zero_apply]
  -- The real-row set bijects with Fin m
  suffices h : Finset.univ.filter (fun i : Fin n =>
      ∀ j, ((canonicalTubalData n m hm hpar).M i j).im = 0) =
      Finset.univ.image (fun a : Fin m => e (Sum.inl a)) by
    unfold realness; rw [h]
    rw [Finset.card_image_of_injective _ (fun a₁ a₂ h => by
      have := e.injective h; exact Sum.inl_injective this)]
    exact Finset.card_fin m
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    canonicalTubalData]
  constructor
  · intro hreal
    rcases hi : e.symm i with a | ⟨r, b⟩
    · exact ⟨a, by rw [← hi, Equiv.apply_symm_apply]⟩
    · exact absurd hreal (not_real_of_inr i r b hi)
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact real_of_inl _ a (by simp)


-- @@ L528-528 verbatim
/-! ## Proposition 66: K_M is isomorphic to the canonical K_{n,m} -/


-- @@ L530-616 verbatim
/-- Parity of realness matches parity of n.
    Non-real rows come in conjugate pairs, so n - realness is even. -/
theorem realness_parity (td : TubalData n) : n % 2 = realness td % 2 := by
  classical
  -- T = non-real rows
  set T := Finset.univ.filter (fun i : Fin n => ¬∀ j, (td.M i j).im = 0)
  -- Count: realness + T.card = n
  have hcount : realness td + T.card = n := by
    show (Finset.univ.filter (fun i => ∀ j, (td.M i j).im = 0)).card +
      (Finset.univ.filter (fun i => ¬∀ j, (td.M i j).im = 0)).card = n
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr (fun _ _ hp hnp => absurd hp hnp)),
      Finset.filter_union_filter_not_eq, Finset.card_fin]
  suffices h : 2 ∣ T.card by omega
  -- Helper: extract ¬IsRealRow from T membership
  have mem_T : ∀ i ∈ T, ¬IsRealRow td.M i := fun i hi =>
    (Finset.mem_filter.mp hi).2
  -- For each non-real row, get its unique conjugate partner (also non-real)
  have partner_exists : ∀ i : Fin n, ¬IsRealRow td.M i →
      ∃ k : Fin n, k ≠ i ∧ ¬IsRealRow td.M k ∧ IsConjRow td.M i k ∧
        ∀ l, l ≠ i → IsConjRow td.M i l → l = k := by
    intro i hi
    rcases td.hM_real i with hri | ⟨k, hk_ne, hk_conj, huniq⟩
    · exact absurd hri hi
    · refine ⟨k, hk_ne, ?_, hk_conj, huniq⟩
      intro hk_real; exact hi (fun j => by
        have hc := hk_conj j; have hr := hk_real j
        rw [hc, starRingEnd_apply, star_def, Complex.conj_im] at hr; linarith)
  -- Define partner function σ
  set σ : Fin n → Fin n := fun i =>
    if h : IsRealRow td.M i then i else (partner_exists i h).choose with σ_def
  have hσ_ne : ∀ i, ¬IsRealRow td.M i → σ i ≠ i := fun i hi => by
    simp only [σ_def, dif_neg hi]; exact (partner_exists i hi).choose_spec.1
  have hσ_nonreal : ∀ i, ¬IsRealRow td.M i → ¬IsRealRow td.M (σ i) := fun i hi => by
    simp only [σ_def, dif_neg hi]; exact (partner_exists i hi).choose_spec.2.1
  have hσ_conj : ∀ i, ¬IsRealRow td.M i → IsConjRow td.M i (σ i) := fun i hi => by
    simp only [σ_def, dif_neg hi]; exact (partner_exists i hi).choose_spec.2.2.1
  have hσ_uniq : ∀ i, ¬IsRealRow td.M i → ∀ l, l ≠ i → IsConjRow td.M i l → l = σ i :=
    fun i hi => by
      simp only [σ_def, dif_neg hi]; exact (partner_exists i hi).choose_spec.2.2.2
  -- σ is an involution
  have hσ_invol : ∀ i, σ (σ i) = i := by
    intro i
    by_cases hi : IsRealRow td.M i
    · simp only [σ_def, dif_pos hi]
    · exact (hσ_uniq (σ i) (hσ_nonreal i hi) i (hσ_ne i hi).symm
        (isConjRow_symm (hσ_conj i hi))).symm
  -- σ maps T to T, is injective, and has no fixed points
  have hσ_mem : ∀ i ∈ T, σ i ∈ T := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ_nonreal i (mem_T i hi)⟩
  have hσ_inj : Set.InjOn σ ↑T := by
    intro i _ j _ hij; have := congr_arg σ hij; rwa [hσ_invol, hσ_invol] at this
  have hσ_fpf : ∀ i ∈ T, σ i ≠ i := fun i hi => hσ_ne i (mem_T i hi)
  -- Split T into L (i.val < σ(i).val) and U (σ(i).val < i.val)
  set L := T.filter (fun i => i.val < (σ i).val)
  set U := T.filter (fun i => (σ i).val < i.val)
  have hLU_disj : Disjoint L U :=
    Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hLU_cover : L ∪ U = T := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hL | hU
      · exact (Finset.mem_filter.mp hL).1
      · exact (Finset.mem_filter.mp hU).1
    · intro hi
      have hne : i.val ≠ (σ i).val := fun h => hσ_fpf i hi (Fin.ext h.symm)
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, h⟩))
  -- σ bijects L ↔ U
  have hσ_L_to_U : ∀ i ∈ L, σ i ∈ U := fun i hi => by
    have ⟨hiT, hlt⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hσ_mem i hiT, by rw [hσ_invol]; exact hlt⟩
  have hσ_U_to_L : ∀ i ∈ U, σ i ∈ L := fun i hi => by
    have ⟨hiT, hlt⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hσ_mem i hiT, by rw [hσ_invol]; exact hlt⟩
  have hcard_eq : L.card = U.card := le_antisymm
    (Finset.card_le_card_of_injOn σ hσ_L_to_U
      (hσ_inj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ T))))
    (Finset.card_le_card_of_injOn σ hσ_U_to_L
      (hσ_inj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ T))))
  -- T.card = 2 * L.card
  rw [show T.card = L.card + U.card from by
    rw [← Finset.card_union_of_disjoint hLU_disj, hLU_cover]]
  exact ⟨L.card, by omega⟩


-- @@ L618-622 verbatim
/-! ## Permuting TubalData (infrastructure for Proposition 66)

The paper's proof of Proposition 66 uses a WLOG argument: permute rows of M so
that real rows come first and conjugate pairs are adjacent. We formalize this
by defining permuted TubalData and proving realness is preserved. -/


-- @@ L624-653 verbatim
/-- Permuting a TubalData by simultaneously reindexing rows and columns via σ.
    This corresponds to a change of basis in the tube space ℝⁿ. -/
noncomputable def permuteTubalData (td : TubalData n) (σ : Equiv.Perm (Fin n)) :
    TubalData n where
  M := td.M.submatrix σ σ
  M_inv := td.M_inv.submatrix σ σ
  hM_left_inv := by rw [submatrix_mul_equiv, td.hM_left_inv, submatrix_one_equiv]
  hM_right_inv := by rw [submatrix_mul_equiv, td.hM_right_inv, submatrix_one_equiv]
  hM_real := by
    intro i
    rcases td.hM_real (σ i) with hreal | ⟨k₀, hk₀_ne, hk₀_conj, hk₀_uniq⟩
    · -- σ i is a real row → i is real in the permuted matrix
      left; intro j; exact hreal (σ j)
    · -- σ i has conjugate partner k₀ → σ⁻¹(k₀) is the partner in the permuted matrix
      right
      refine ⟨σ.symm k₀, ?_, ?_, ?_⟩
      · -- σ.symm k₀ ≠ i
        intro heq; exact hk₀_ne (by rw [← σ.apply_symm_apply k₀, heq])
      · -- IsConjRow
        intro j
        show td.M (σ (σ.symm k₀)) (σ j) = starRingEnd ℂ (td.M (σ i) (σ j))
        rw [σ.apply_symm_apply]; exact hk₀_conj (σ j)
      · -- Uniqueness
        intro l hl_ne hl_conj
        have h1 : σ l ≠ σ i := fun h => hl_ne (σ.injective h)
        have h2 : IsConjRow td.M (σ i) (σ l) := fun j' => by
          have := hl_conj (σ.symm j')
          simp only [submatrix_apply, Equiv.apply_symm_apply] at this
          exact this
        exact σ.injective (by rw [σ.apply_symm_apply]; exact hk₀_uniq (σ l) h1 h2)


-- @@ L655-670 verbatim
/-- Realness is invariant under permutation: the number of real rows doesn't change. -/
theorem realness_permute (td : TubalData n) (σ : Equiv.Perm (Fin n)) :
    realness (permuteTubalData td σ) = realness td := by
  simp only [realness, permuteTubalData, submatrix_apply]
  -- Column surjectivity: quantifying over σ j is the same as quantifying over all j
  have h_col : ∀ i, (∀ j, (td.M (σ i) (σ j)).im = 0) ↔ (∀ j, (td.M (σ i) j).im = 0) :=
    fun i => ⟨fun h j => σ.apply_symm_apply j ▸ h (σ.symm j), fun h j => h (σ j)⟩
  simp_rw [h_col]
  -- σ bijects the two filter sets: {i | P (σ i)} has the same card as {i | P i}
  rw [show Finset.univ.filter (fun i => ∀ j, (td.M (σ i) j).im = 0) =
      (Finset.univ.filter (fun i => ∀ j, (td.M i j).im = 0)).map σ.symm.toEmbedding from by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Equiv.toEmbedding_apply]
    exact ⟨fun hi => ⟨σ i, hi, σ.symm_apply_apply i⟩,
           fun ⟨_, ha, hai⟩ => by subst hai; rwa [σ.apply_symm_apply]⟩]
  exact Finset.card_map _


-- @@ L672-672 verbatim
/-! ## Step C: Algebra isomorphism via permutation -/


-- @@ L674-679 verbatim
/-- M.submatrix σ σ *ᵥ (v ∘ σ) = (M *ᵥ v) ∘ σ. -/
private theorem submatrix_mulVec_comp_perm (M : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → ℂ) :
    M.submatrix σ σ *ᵥ (v ∘ ⇑σ) = (M *ᵥ v) ∘ ⇑σ := by
  have h : (v ∘ ⇑σ) ∘ ⇑σ.symm = v := by ext i; simp
  rw [submatrix_mulVec_equiv, h]


-- @@ L681-683 verbatim
private theorem vecHadamard_comp_perm (σ : Equiv.Perm (Fin n)) (u v : Fin n → ℂ) :
    (u ∘ ⇑σ) ∘ₕ (v ∘ ⇑σ) = (u ∘ₕ v) ∘ ⇑σ := by
  ext i; simp [vecHadamard_apply]


-- @@ L685-692 verbatim
private theorem starMC_comp_perm (td : TubalData n) (σ : Equiv.Perm (Fin n))
    (a b : Fin n → ℂ) :
    starMC (permuteTubalData td σ) (a ∘ ⇑σ) (b ∘ ⇑σ) = (starMC td a b) ∘ ⇑σ := by
  show (td.M_inv.submatrix σ σ) *ᵥ
    ((td.M.submatrix σ σ *ᵥ (a ∘ ⇑σ)) ∘ₕ (td.M.submatrix σ σ *ᵥ (b ∘ ⇑σ))) =
    (td.M_inv *ᵥ (td.M *ᵥ a ∘ₕ td.M *ᵥ b)) ∘ ⇑σ
  rw [submatrix_mulVec_comp_perm, submatrix_mulVec_comp_perm,
      vecHadamard_comp_perm, submatrix_mulVec_comp_perm]


-- @@ L694-699 verbatim
private theorem starM_comp_perm (td : TubalData n) (σ : Equiv.Perm (Fin n))
    (a b : Fin n → ℝ) :
    starM (permuteTubalData td σ) (a ∘ ⇑σ) (b ∘ ⇑σ) = (starM td a b) ∘ ⇑σ := by
  show vecRe (starMC (permuteTubalData td σ) ((toComplex a) ∘ ⇑σ) ((toComplex b) ∘ ⇑σ)) =
    (vecRe (starMC td (toComplex a) (toComplex b))) ∘ ⇑σ
  rw [starMC_comp_perm]; ext; rfl


-- @@ L701-709 verbatim
private theorem unitTube_comp_perm (td : TubalData n) (σ : Equiv.Perm (Fin n)) :
    unitTube (permuteTubalData td σ) = (unitTube td) ∘ ⇑σ := by
  apply toComplex_injective
  rw [toComplex_unitTube]
  show (td.M_inv.submatrix σ σ) *ᵥ allOnes n = toComplex ((unitTube td) ∘ ⇑σ)
  conv_rhs => rw [show toComplex ((unitTube td) ∘ ⇑σ) =
    (toComplex (unitTube td)) ∘ ⇑σ from rfl, toComplex_unitTube]
  rw [show (allOnes n : Fin n → ℂ) = allOnes n ∘ ⇑σ from by ext; simp [allOnes]]
  exact submatrix_mulVec_comp_perm _ _ _


-- @@ L711-735 verbatim
/-- Algebra isomorphism KM n td ≃ₐ[ℝ] KM n (permuteTubalData td σ) via a ↦ a ∘ σ. -/
noncomputable def permuteAlgEquiv (td : TubalData n) (σ : Equiv.Perm (Fin n)) :
    KM n td ≃ₐ[ℝ] KM n (permuteTubalData td σ) := {
  toFun := fun a => KM.ofFun (KM.toFun a ∘ ⇑σ)
  invFun := fun b => KM.ofFun (KM.toFun b ∘ ⇑σ.symm)
  left_inv := fun a => by
    ext i; simp only [KM.toFun_ofFun, Function.comp_apply, Equiv.apply_symm_apply]
  right_inv := fun b => by
    ext i; simp only [KM.toFun_ofFun, Function.comp_apply, Equiv.symm_apply_apply]
  map_mul' := fun a b => by
    show KM.ofFun (starM td (KM.toFun a) (KM.toFun b) ∘ ⇑σ) =
      KM.ofFun (starM (permuteTubalData td σ) (KM.toFun a ∘ ⇑σ) (KM.toFun b ∘ ⇑σ))
    exact congr_arg KM.ofFun (starM_comp_perm td σ _ _).symm
  map_add' := fun a b => by
    show KM.ofFun ((KM.toFun a + KM.toFun b) ∘ ⇑σ) =
      KM.ofFun (KM.toFun a ∘ ⇑σ + KM.toFun b ∘ ⇑σ)
    rfl
  commutes' := fun r => by
    show KM.ofFun (KM.toFun (algebraMap ℝ (KM n td) r) ∘ ⇑σ) =
      algebraMap ℝ (KM n (permuteTubalData td σ)) r
    change KM.ofFun ((r • unitTube td) ∘ ⇑σ) =
      KM.ofFun (r • unitTube (permuteTubalData td σ))
    rw [show (r • unitTube td) ∘ ⇑σ = r • ((unitTube td) ∘ ⇑σ) from rfl,
        unitTube_comp_perm]
}


-- @@ L737-737 verbatim
/-! ## Step D: Reordering permutation for Proposition 66 -/


-- @@ L739-741 verbatim
private theorem realness_block_sum (td : TubalData n) :
    realness td + 2 * ((n - realness td) / 2) = n := by
  have := realness_parity td; have := realness_le td; omega


-- @@ L743-952 verbatim
/-- There exists a permutation σ such that in td.M ∘ σ, the first m rows are real
    and the remaining rows are correctly paired conjugate rows matching canonicalEquiv. -/
theorem exists_ordering_perm (td : TubalData n) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ i : Fin n, i.val < realness td → IsRealRow td.M (σ i)) ∧
      (∀ i : Fin n, realness td ≤ i.val → ¬IsRealRow td.M (σ i)) ∧
      (∀ b : Fin ((n - realness td) / 2),
        let e := canonicalEquiv (realness td) _ (realness_block_sum td)
        IsConjRow td.M (σ (e (Sum.inr (0, b)))) (σ (e (Sum.inr (1, b))))) := by
  classical
  set m := realness td with m_def
  set k := (n - m) / 2
  have hk : m + 2 * k = n := realness_block_sum td
  set e := canonicalEquiv m k hk
  -- Partner function for non-real rows
  set isReal := fun i : Fin n => ∀ j, (td.M i j).im = 0 with isReal_def
  have partner_data : ∀ i, ¬isReal i →
      ∃ j, j ≠ i ∧ ¬isReal j ∧ IsConjRow td.M i j ∧
        (∀ l, l ≠ i → IsConjRow td.M i l → l = j) := by
    intro i hi
    rcases td.hM_real i with hri | ⟨j, hne, hconj, huniq⟩
    · exact absurd hri hi
    refine ⟨j, hne, ?_, hconj, huniq⟩
    intro hj; exact hi (fun c => by
      have hc := hconj c; have hr := hj c
      rw [hc, starRingEnd_apply, star_def, Complex.conj_im] at hr; linarith)
  set p : Fin n → Fin n := fun i =>
    if h : isReal i then i else (partner_data i h).choose
  have hp_ne : ∀ i, ¬isReal i → p i ≠ i := fun i hi => by
    simp only [p, dif_neg hi]; exact (partner_data i hi).choose_spec.1
  have hp_nonreal : ∀ i, ¬isReal i → ¬isReal (p i) := fun i hi => by
    simp only [p, dif_neg hi]; exact (partner_data i hi).choose_spec.2.1
  have hp_conj : ∀ i, ¬isReal i → IsConjRow td.M i (p i) := fun i hi => by
    simp only [p, dif_neg hi]; exact (partner_data i hi).choose_spec.2.2.1
  have hp_uniq : ∀ i, ¬isReal i → ∀ l, l ≠ i → IsConjRow td.M i l → l = p i := fun i hi => by
    simp only [p, dif_neg hi]; exact (partner_data i hi).choose_spec.2.2.2
  have hp_invol : ∀ i, p (p i) = i := by
    intro i; by_cases hi : isReal i
    · simp only [p, dif_pos hi]
    · exact (hp_uniq (p i) (hp_nonreal i hi) i (hp_ne i hi).symm
        (isConjRow_symm (hp_conj i hi))).symm
  -- Sets: real rows R, representatives L (smaller element of each non-real pair)
  set R := Finset.univ.filter isReal
  set L := Finset.univ.filter (fun i => ¬isReal i ∧ i.val < (p i).val)
  have hR_card : R.card = m := rfl
  -- L.card = k (each non-real pair contributes exactly one element to L)
  have hp_inj_global : Function.Injective p := fun i j hij => by
    have := congr_arg p hij; rwa [hp_invol, hp_invol] at this
  have hL_card : L.card = k := by
    -- NR = non-real rows; L = {i | ¬real ∧ i < p(i)}, U = {i | ¬real ∧ p(i) < i}
    set NR := Finset.univ.filter (fun i : Fin n => ¬isReal i)
    set U := Finset.univ.filter (fun i => ¬isReal i ∧ (p i).val < i.val)
    have hNR_card : NR.card = n - m := by
      have h1 : R ∪ NR = Finset.univ := by
        ext i; constructor
        · intro _; exact Finset.mem_univ _
        · intro _; rw [Finset.mem_union]
          by_cases h : isReal i
          · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have h2 : Disjoint R NR :=
        Finset.disjoint_filter.mpr (fun _ _ h h' => h' h)
      have h3 := Finset.card_union_of_disjoint h2
      rw [h1, Finset.card_univ, Fintype.card_fin] at h3; omega
    have hLU_disj : Disjoint L U :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by have := h1.2; have := h2.2; omega)
    have hLU_cover : L ∪ U = NR := by
      ext i; constructor
      · intro hi
        rcases Finset.mem_union.mp hi with hL | hU
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp hL).2.1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp hU).2.1⟩
      · intro hi
        have hni := (Finset.mem_filter.mp hi).2
        have hne : i.val ≠ (p i).val := fun h => hp_ne i hni (Fin.ext h.symm)
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hni, h⟩))
        · exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hni, h⟩))
    have hσ_L_to_U : ∀ i ∈ L, p i ∈ U := fun i hi => by
      obtain ⟨_, hni, hlt⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hp_nonreal i hni, by rw [hp_invol]; exact hlt⟩
    have hσ_U_to_L : ∀ i ∈ U, p i ∈ L := fun i hi => by
      obtain ⟨_, hni, hlt⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hp_nonreal i hni, by rw [hp_invol]; exact hlt⟩
    have hcard_eq : L.card = U.card := le_antisymm
      (Finset.card_le_card_of_injOn p hσ_L_to_U hp_inj_global.injOn)
      (Finset.card_le_card_of_injOn p hσ_U_to_L hp_inj_global.injOn)
    have : NR.card = L.card + U.card := by
      rw [← Finset.card_union_of_disjoint hLU_disj, hLU_cover]
    omega
  -- Enumerations
  let r_enum := (R.equivFinOfCardEq hR_card).symm  -- Fin m ≃ ↥R
  let l_enum := (L.equivFinOfCardEq hL_card).symm  -- Fin k ≃ ↥L
  -- Build g : Fin m ⊕ (Fin 2 × Fin k) → Fin n
  let g : Fin m ⊕ (Fin 2 × Fin k) → Fin n := fun x =>
    match x with
    | Sum.inl a => (r_enum a).val
    | Sum.inr (r, b) =>
      if r = (0 : Fin 2) then (l_enum b).val else p (l_enum b).val
  -- g is injective (hence bijective on finite sets of same size)
  have g_inj : Function.Injective g := by
    intro x y hxy
    match x, y with
    | Sum.inl a₁, Sum.inl a₂ =>
      exact congr_arg Sum.inl (r_enum.injective (Subtype.val_injective hxy))
    | Sum.inl a, Sum.inr (r, b) =>
      exfalso
      have ha := (r_enum a).property  -- a is in R (real)
      have := Finset.mem_filter.mp ha
      have hb : ¬isReal (g (Sum.inr (r, b))) := by
        simp only [g]; split_ifs with hr
        · exact (Finset.mem_filter.mp (l_enum b).property).2.1
        · exact hp_nonreal _ (Finset.mem_filter.mp (l_enum b).property).2.1
      rw [← hxy] at hb; exact hb this.2
    | Sum.inr (r, b), Sum.inl a =>
      exfalso
      have ha := (r_enum a).property
      have := Finset.mem_filter.mp ha
      have hb : ¬isReal (g (Sum.inr (r, b))) := by
        simp only [g]; split_ifs with hr
        · exact (Finset.mem_filter.mp (l_enum b).property).2.1
        · exact hp_nonreal _ (Finset.mem_filter.mp (l_enum b).property).2.1
      rw [hxy] at hb; exact hb this.2
    | Sum.inr (r₁, b₁), Sum.inr (r₂, b₂) =>
      simp only [g] at hxy
      have hb₁_prop := (Finset.mem_filter.mp (l_enum b₁).property).2
      have hb₂_prop := (Finset.mem_filter.mp (l_enum b₂).property).2
      split_ifs at hxy with h₁ h₂
      · -- both r = 0
        have := l_enum.injective (Subtype.val_injective hxy)
        rw [h₁, h₂]; exact congr_arg₂ (fun r b => Sum.inr (r, b)) rfl this
      · -- r₁ = 0, r₂ ≠ 0: l_enum b₁ = p(l_enum b₂)
        exfalso; have := hb₁_prop.2  -- (l_enum b₁).val < p(l_enum b₁).val
        rw [hxy] at this  -- p(l_enum b₂).val < p(p(l_enum b₂).val)
        rw [hp_invol] at this; exact Nat.lt_asymm this hb₂_prop.2
      · -- r₁ ≠ 0, r₂ = 0: symmetric
        exfalso; have := hb₂_prop.2
        rw [← hxy] at this; rw [hp_invol] at this; exact Nat.lt_asymm this hb₁_prop.2
      · -- both r ≠ 0: p(l_enum b₁) = p(l_enum b₂)
        have hinj := congr_arg p hxy; rw [hp_invol, hp_invol] at hinj
        have hbeq := l_enum.injective (Subtype.val_injective hinj)
        have hreq : r₁ = r₂ := by omega
        exact congr_arg₂ (fun r b => Sum.inr (r, b)) hreq hbeq
  -- Build σ directly as g ∘ e.symm : Fin n → Fin n
  let σ_fun : Fin n → Fin n := g ∘ ⇑e.symm
  have σ_inj : Function.Injective σ_fun :=
    Function.Injective.comp g_inj e.symm.injective
  have σ_bij : Function.Bijective σ_fun :=
    Finite.injective_iff_bijective.mp σ_inj
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective σ_fun σ_bij
  -- Helper: σ agrees with g ∘ e.symm
  have hσ_apply : ∀ i, σ i = g (e.symm i) := fun _ => rfl
  -- Helper: canonicalEquiv maps Sum.inl to positions < m
  have he_inl_lt : ∀ a : Fin m, (e (Sum.inl a)).val < m := by
    intro a
    show (canonicalEquiv m k hk (Sum.inl a)).val < m
    unfold canonicalEquiv
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
      finCongr_apply, Fin.val_cast]
    exact a.isLt
  -- Helper: canonicalEquiv maps Sum.inr to positions ≥ m
  have he_inr_ge : ∀ x : Fin 2 × Fin k, m ≤ (e (Sum.inr x)).val := by
    intro ⟨r, b⟩
    show m ≤ (canonicalEquiv m k hk (Sum.inr (r, b))).val
    unfold canonicalEquiv
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_natAdd]
    omega
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- Real rows at positions < m
    intro i hi
    rw [hσ_apply]
    have he : ∃ a : Fin m, e.symm i = Sum.inl a := by
      rcases h : e.symm i with a | ⟨r, b⟩
      · exact ⟨a, rfl⟩
      · exfalso
        have hi_eq : i = e (Sum.inr (r, b)) := by rw [← h, Equiv.apply_symm_apply]
        have := he_inr_ge (r, b)
        omega
    obtain ⟨a, ha⟩ := he
    rw [ha]; show isReal (g (Sum.inl a))
    exact (Finset.mem_filter.mp (r_enum a).property).2
  · -- Non-real rows at positions ≥ m
    intro i hi
    rw [hσ_apply]
    have he : ∃ r b, e.symm i = Sum.inr (r, b) := by
      rcases h : e.symm i with a | ⟨r, b⟩
      · exfalso
        have hi_eq : i = e (Sum.inl a) := by rw [← h, Equiv.apply_symm_apply]
        have := he_inl_lt a
        exact Nat.not_lt.mpr hi (by omega)
      · exact ⟨r, b, rfl⟩
    obtain ⟨r, b, hrb⟩ := he
    rw [hrb]; show ¬isReal (g (Sum.inr (r, b)))
    simp only [g]; split_ifs with hr
    · exact (Finset.mem_filter.mp (l_enum b).property).2.1
    · exact hp_nonreal _ (Finset.mem_filter.mp (l_enum b).property).2.1
  · -- Conjugate pairing
    intro b
    simp only [hσ_apply, Equiv.symm_apply_apply]
    show IsConjRow td.M (g (Sum.inr (0, b))) (g (Sum.inr (1, b)))
    simp only [g, ite_true,
      show ¬((1 : Fin 2) = 0) from by decide, ite_false]
    exact hp_conj _ (Finset.mem_filter.mp (l_enum b).property).2.1


-- @@ L954-957 verbatim
/-! ## Step E: ordered canonical transition

When real rows are at positions 0..m-1 and conjugate pairs align with canonicalEquiv,
`canonicalMinv * td.M` is a real invertible matrix. -/


-- @@ L959-976 verbatim
/-- F₂⁻¹ applied to [z, conj(z)] gives real entries. -/
private theorem conjPairBlockInv_conj_real (z : ℂ) (r : Fin 2) :
    (conjPairBlockInv r 0 * z + conjPairBlockInv r 1 * starRingEnd ℂ z).im = 0 := by
  have hconj : starRingEnd ℂ z = ⟨z.re, -z.im⟩ := by
    rw [starRingEnd_apply, star_def]
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  rw [hconj]
  fin_cases r
  · -- r = 0: entries are 1/√2 and 1/√2
    show (1 / (↑(Real.sqrt 2) : ℂ) * z + 1 / ↑(Real.sqrt 2) * ⟨z.re, -z.im⟩).im = 0
    simp only [Complex.add_im, Complex.mul_im, Complex.div_ofReal, Complex.one_re, Complex.one_im]
    ring
  · -- r = 1: entries are I/√2 and -I/√2
    show (Complex.I / (↑(Real.sqrt 2) : ℂ) * z +
      -Complex.I / ↑(Real.sqrt 2) * ⟨z.re, -z.im⟩).im = 0
    simp only [Complex.add_im, Complex.mul_im, Complex.div_ofReal, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    ring


-- @@ L978-1051 verbatim
/-- Core block computation: when real rows come first and conjugate pairs
    align with canonicalEquiv, `canonicalMinv * td.M` is real. -/
private theorem product_im_eq_zero (td : TubalData n)
    (h_real : ∀ i : Fin n, i.val < realness td → IsRealRow td.M i)
    (h_paired : ∀ b : Fin ((n - realness td) / 2),
      let e := canonicalEquiv (realness td) ((n - realness td) / 2) (realness_block_sum td)
      IsConjRow td.M (e (Sum.inr (0, b))) (e (Sum.inr (1, b))))
    (i j : Fin n) :
    ((canonicalMinv n (realness td) (realness_le td) (realness_parity td) * td.M) i j).im = 0 := by
  set m := realness td
  set k := (n - m) / 2
  have hk : m + 2 * k = n := realness_block_sum td
  set e := canonicalEquiv m k hk
  -- The product factors through block coordinates
  -- canonicalMinv[i,l] = canonicalMinv_block[e.symm i, e.symm l]
  -- Case split on block position of row i
  rcases h_block : e.symm i with a | ⟨r, b⟩
  · -- Identity block row: sum reduces to td.M[i,j] which is real
    have hi_eq : i = e (Sum.inl a) := by rw [← Equiv.apply_symm_apply e i, h_block]
    show ((canonicalMinv n m _ _ * td.M) i j).im = 0
    simp only [Matrix.mul_apply]
    -- Replace canonicalMinv entries, reindex, and simplify
    have hcMinv_entry : ∀ l, canonicalMinv n m (realness_le td) (realness_parity td) i l =
        canonicalMinv_block m k (Sum.inl a) (e.symm l) :=
      fun l => by show canonicalMinv_block m k (e.symm i) (e.symm l) = _; rw [h_block]
    simp_rw [hcMinv_entry]
    -- Simplify the sum (without .im wrapper)
    have hsum_val : ∑ l, canonicalMinv_block m k (Sum.inl a) (e.symm l) * td.M l j =
        td.M (e (Sum.inl a)) j := by
      rw [show ∑ l, canonicalMinv_block m k (Sum.inl a) (e.symm l) * td.M l j =
          ∑ x, canonicalMinv_block m k (Sum.inl a) x * td.M (e x) j from
        Fintype.sum_equiv e.symm _ _ (fun l => by simp [Equiv.apply_symm_apply])]
      rw [Fintype.sum_sum_type]
      simp only [canonicalMinv_block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        Matrix.one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_const_zero, add_zero]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    rw [hsum_val]
    -- Entry is real
    have ha_val : (e (Sum.inl a)).val < m := by
      show (canonicalEquiv m k hk (Sum.inl a)).val < m
      unfold canonicalEquiv
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
        finCongr_apply, Fin.val_cast]
      exact a.isLt
    exact h_real _ (hi_eq ▸ ha_val) j
  · -- F₂⁻¹ block row: sum reduces to F₂⁻¹[r,0]*row₀ + F₂⁻¹[r,1]*row₁
    show ((canonicalMinv n m _ _ * td.M) i j).im = 0
    simp only [Matrix.mul_apply]
    have hcMinv_entry : ∀ l, canonicalMinv n m (realness_le td) (realness_parity td) i l =
        canonicalMinv_block m k (Sum.inr (r, b)) (e.symm l) :=
      fun l => by show canonicalMinv_block m k (e.symm i) (e.symm l) = _; rw [h_block]
    simp_rw [hcMinv_entry]
    -- Simplify the sum to conjPairBlockInv entries
    have hsum_val : ∑ l, canonicalMinv_block m k (Sum.inr (r, b)) (e.symm l) * td.M l j =
        ∑ s : Fin 2, conjPairBlockInv r s * td.M (e (Sum.inr (s, b))) j := by
      rw [show ∑ l, canonicalMinv_block m k (Sum.inr (r, b)) (e.symm l) * td.M l j =
          ∑ x, canonicalMinv_block m k (Sum.inr (r, b)) x * td.M (e x) j from
        Fintype.sum_equiv e.symm _ _ (fun l => by simp [Equiv.apply_symm_apply])]
      rw [Fintype.sum_sum_type]
      simp only [canonicalMinv_block, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
        blockDiagonal_apply, ite_mul]
      rw [show ∑ x : Fin 2 × Fin k,
          (if b = x.2 then conjPairBlockInv r x.1 * td.M (e (Sum.inr x)) j else 0) =
        ∑ s : Fin 2, conjPairBlockInv r s * td.M (e (Sum.inr (s, b))) j from by
        rw [Fintype.sum_prod_type]
        congr 1; ext s; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]]
    rw [hsum_val, Fin.sum_univ_two]
    -- Use conjugate pairing
    have hconj : td.M (e (Sum.inr (1, b))) j =
        starRingEnd ℂ (td.M (e (Sum.inr (0, b))) j) := h_paired ⟨b.val, b.isLt⟩ j
    rw [hconj]
    exact conjPairBlockInv_conj_real _ r


-- @@ L1053-1142 verbatim
/-- When real rows come first and pairs align with canonicalEquiv, there exists
    a real invertible R with td.M = canonicalM * R_ℂ. -/
theorem ordered_canonical_transition (td : TubalData n)
    (h_real : ∀ i : Fin n, i.val < realness td → IsRealRow td.M i)
    (h_paired : ∀ b : Fin ((n - realness td) / 2),
      let e := canonicalEquiv (realness td) ((n - realness td) / 2) (realness_block_sum td)
      IsConjRow td.M (e (Sum.inr (0, b))) (e (Sum.inr (1, b)))) :
    ∃ (R S : Matrix (Fin n) (Fin n) ℝ),
      S * R = 1 ∧ R * S = 1 ∧
      td.M = (canonicalM n (realness td) (realness_le td) (realness_parity td)) *
        R.map ((↑) : ℝ → ℂ) := by
  set cMinv := canonicalMinv n (realness td) (realness_le td) (realness_parity td)
  set cM := canonicalM n (realness td) (realness_le td) (realness_parity td)
  set P := cMinv * td.M
  -- P is real
  have hP_real : ∀ i j, (P i j).im = 0 := product_im_eq_zero td h_real h_paired
  -- Define R as the real part of P
  set R := P.map Complex.re
  -- R.map (↑) = P since P is real
  have hR_cast : R.map ((↑) : ℝ → ℂ) = P := by
    ext i j; simp only [R, Matrix.map_apply]
    exact Complex.ext (by rfl) (by simp [hP_real i j])
  -- Define S similarly from the inverse product
  set Q := td.M_inv * cM
  have hQ_real : ∀ i j, (Q i j).im = 0 := by
    intro i j
    -- Show Q * P = 1 and P * Q = 1
    have hQP : Q * P = 1 := by
      show td.M_inv * cM * (cMinv * td.M) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc cM cMinv,
        canonicalM_mul_canonicalMinv, Matrix.one_mul, td.hM_left_inv]
    have hPQ : P * Q = 1 := by
      show cMinv * td.M * (td.M_inv * cM) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc td.M td.M_inv,
        td.hM_right_inv, Matrix.one_mul, canonicalMinv_mul_canonicalM]
    have hQR : Q * R.map ((↑) : ℝ → ℂ) = 1 := hR_cast ▸ hQP
    have hRQ : R.map ((↑) : ℝ → ℂ) * Q = 1 := hR_cast ▸ hPQ
    -- Show conj(Q) is also a left inverse of R_ℂ
    have hconjQ_R : Q.map (starRingEnd ℂ) * R.map ((↑) : ℝ → ℂ) = 1 := by
      have hR_conj : R.map ((↑) : ℝ → ℂ) = (R.map ((↑) : ℝ → ℂ)).map (starRingEnd ℂ) := by
        ext a b; simp only [Matrix.map_apply]; rw [starRingEnd_apply, star_def, Complex.conj_ofReal]
      conv_lhs => rw [hR_conj]
      rw [← Matrix.map_mul (f := starRingEnd ℂ), hQR]
      ext a b; simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs with h
      · subst h; rw [starRingEnd_apply, star_def]; simp
      · rw [starRingEnd_apply, star_def]; simp
    -- Q and conj(Q) are both left inverses of R_ℂ, and R_ℂ has a right inverse → Q = conj(Q)
    have hQ_eq_conj : Q i j = (starRingEnd ℂ) (Q i j) := by
      have h1 : Q = Q.map (starRingEnd ℂ) := by
        calc Q = Q * 1 := (Matrix.mul_one _).symm
          _ = Q * (R.map (↑) * Q) := by rw [hRQ]
          _ = (Q * R.map (↑)) * Q := (Matrix.mul_assoc _ _ _).symm
          _ = 1 * Q := by rw [hQR]
          _ = (Q.map (starRingEnd ℂ) * R.map (↑)) * Q := by rw [hconjQ_R]
          _ = Q.map (starRingEnd ℂ) * (R.map (↑) * Q) := Matrix.mul_assoc _ _ _
          _ = Q.map (starRingEnd ℂ) * 1 := by rw [hRQ]
          _ = Q.map (starRingEnd ℂ) := Matrix.mul_one _
      exact congr_fun (congr_fun h1 i) j
    rw [starRingEnd_apply, star_def] at hQ_eq_conj
    rwa [eq_comm, Complex.conj_eq_iff_im] at hQ_eq_conj
  set S := Q.map Complex.re
  have hS_cast : S.map ((↑) : ℝ → ℂ) = Q := by
    ext i j; simp only [S, Matrix.map_apply]
    exact Complex.ext (by rfl) (by simp [hQ_real i j])
  -- Helper: casting preserves multiplication
  have map_mul_cast (A B : Matrix (Fin n) (Fin n) ℝ) :
      (A * B).map ((↑) : ℝ → ℂ) = A.map ((↑) : ℝ → ℂ) * B.map ((↑) : ℝ → ℂ) := by
    ext i j; simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  -- Helper: real cast is injective on matrices
  have cast_inj (A B : Matrix (Fin n) (Fin n) ℝ) (h : A.map ((↑) : ℝ → ℂ) = B.map (↑)) :
      A = B := by ext i j; exact Complex.ofReal_injective (congr_fun (congr_fun h i) j)
  refine ⟨R, S, ?_, ?_, ?_⟩
  · -- S * R = 1
    apply cast_inj
    rw [map_mul_cast, hS_cast, hR_cast, Matrix.map_one ((↑) : ℝ → ℂ) Complex.ofReal_zero Complex.ofReal_one]
    show td.M_inv * cM * (cMinv * td.M) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc cM cMinv,
      canonicalM_mul_canonicalMinv, Matrix.one_mul, td.hM_left_inv]
  · -- R * S = 1
    apply cast_inj
    rw [map_mul_cast, hR_cast, hS_cast, Matrix.map_one ((↑) : ℝ → ℂ) Complex.ofReal_zero Complex.ofReal_one]
    show cMinv * td.M * (td.M_inv * cM) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc td.M td.M_inv,
      td.hM_right_inv, Matrix.one_mul, canonicalMinv_mul_canonicalM]
  · -- td.M = cM * R_ℂ
    calc td.M = 1 * td.M := (Matrix.one_mul _).symm
      _ = (cM * cMinv) * td.M := by rw [canonicalM_mul_canonicalMinv]
      _ = cM * (cMinv * td.M) := by rw [Matrix.mul_assoc]
      _ = cM * R.map ((↑) : ℝ → ℂ) := by rw [hR_cast]


-- @@ L1144-1144 verbatim
/-! ## Proposition 66: K_M is isomorphic to the canonical K_{n,m} -/


-- @@ L1146-1194 verbatim
/-- **Proposition 66**: K_M is isomorphic (as ℝ-algebra) to the canonical K_{n,m}
    where m = realness(M). -/
theorem KM_algEquiv_canonical (td : TubalData n) :
    Nonempty (KM n td ≃ₐ[ℝ] KM n (canonicalTubalData n (realness td)
      (realness_le td) (realness_parity td))) := by
  -- Step 1: Get ordering permutation
  obtain ⟨σ, h_real_σ, _, h_paired_σ⟩ := exists_ordering_perm td
  -- Step 2: iso₁ via permutation
  have iso₁ := permuteAlgEquiv td σ
  -- Step 3: Translate hypotheses to permuted data
  -- Key identity: realness is invariant under permutation
  have hrp : realness (permuteTubalData td σ) = realness td := realness_permute td σ
  have h_real_perm : ∀ i, i.val < realness (permuteTubalData td σ) →
      IsRealRow (permuteTubalData td σ).M i := by
    rw [hrp]; intro i hi j; exact h_real_σ i hi (σ j)
  have h_paired_perm : ∀ b : Fin ((n - realness (permuteTubalData td σ)) / 2),
      let e := canonicalEquiv (realness (permuteTubalData td σ)) _
        (realness_block_sum (permuteTubalData td σ))
      IsConjRow (permuteTubalData td σ).M (e (Sum.inr (0, b))) (e (Sum.inr (1, b))) := by
    intro b e j
    -- Cast b to the right Fin type using hrp
    set b' : Fin ((n - realness td) / 2) := ⟨b.val, by rw [← hrp]; exact b.isLt⟩
    -- Show the canonical equivs agree on Fin n outputs
    suffices hce : ∀ s, e (Sum.inr (s, b)) =
        canonicalEquiv (realness td) _ (realness_block_sum td) (Sum.inr (s, b')) by
      -- Rewrite BEFORE any simp that might unfold e
      rw [hce 1, hce 0]
      -- Now goal uses canonicalEquiv (realness td) and (permuteTubalData td σ).M
      -- which is definitionally td.M (σ ·) (σ ·)
      exact h_paired_σ b' (σ j)
    intro s; apply Fin.ext
    -- Both sides have val = m + b.val + k * s.val
    simp only [e, b', canonicalEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd,
      finCongr_apply, Fin.val_cast, finProdFinEquiv, hrp]
    rfl
  -- Step 4: Get R, S from ordered transition
  obtain ⟨R, S, hSR, hRS, hM⟩ := ordered_canonical_transition _ h_real_perm h_paired_perm
  -- Step 5: Match realness: canonicalTubalData uses realness = realness td
  have hctd_eq : canonicalTubalData n (realness (permuteTubalData td σ))
      (realness_le _) (realness_parity _) =
      canonicalTubalData n (realness td) (realness_le td) (realness_parity td) := by
    suffices ∀ (a b : ℕ) (hab : a = b) (ha : a ≤ n) (hb : b ≤ n)
        (hpa : n % 2 = a % 2) (hpb : n % 2 = b % 2),
        canonicalTubalData n a ha hpa = canonicalTubalData n b hb hpb from
      this _ _ hrp _ _ _ _
    intro a b hab; subst hab; intros; rfl
  -- Step 6: Compose isomorphisms
  exact ⟨iso₁.trans (hctd_eq ▸ transportAlgEquiv _ _ R S hSR hRS hM)⟩



-- @@ L1197-1197 verbatim
end TubalTensor
