import TubalTensor.MainTheorem.RepMatrix
import TubalTensor.Prerequisites.JointDiag
import TubalTensor.Defs.Basic


-- @@ L5-11 verbatim
/-!
  TubalTensor/MainTheorem/Diagonalizable.lean
  Definitions 48, 49, 51; Lemmas 50, 52, 53, 54; Proposition 54.

  We define diagonalizability concepts for tubal ring elements directly via their
  representation matrices R_a. This makes Lemmas 50 and 52 definitional.
-/


-- @@ L13-13 verbatim
namespace TubalTensor


-- @@ L15-15 verbatim
open Matrix Complex BigOperators


-- @@ L17-17 verbatim
variable {n : ℕ} (tr : TubalRing n)


-- @@ L19-23 verbatim
/-! ## Extension of multiplication to complex operands

  The paper (Section 9.2) extends the tubal ring multiplication to complex operands:
  for `a ∈ ℝⁿ` and `b ∈ ℂⁿ`, define `a · b := a · Re(b) + i(a · Im(b))`.
  We then prove `a · b = R_a b` (as complex vectors). -/


-- @@ L25-28 verbatim
/-- Extension of tubal ring multiplication to complex operands:
    `a · b := a · Re(b) + i · (a · Im(b))` for `a : ℝⁿ`, `b : ℂⁿ`. -/
def mulComplex (a : TubalCarrier n) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ↑(tr.mul a (fun j => (b j).re) i) + ↑(tr.mul a (fun j => (b j).im) i) * I


-- @@ L30-37 verbatim
/-- `mulComplex` agrees with `tr.mul` on real vectors (via `toComplex`). -/
theorem mulComplex_toComplex (a x : TubalCarrier n) :
    mulComplex tr a (toComplex x) = toComplex (tr.mul a x) := by
  ext i
  simp only [mulComplex, toComplex_apply, Complex.ofReal_re, Complex.ofReal_im]
  have : tr.mul a (fun _ => 0) i = 0 := by
    rw [show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl]; exact congr_fun (tr.mul_zero a) i
  simp [this]


-- @@ L39-57 verbatim
/-- **Key theorem**: `a · b = R_a b` for complex `b`. The extension of multiplication
    to complex operands equals the action of the representation matrix. -/
theorem mulComplex_eq_repMatrix_mulVec (a : TubalCarrier n) (b : Fin n → ℂ) :
    mulComplex tr a b = (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ b := by
  ext i
  simp only [mulComplex, mulVec, dotProduct, Matrix.map_apply, repMatrix_apply]
  -- Rewrite tr.mul as sums via repMatrix_mulVec
  conv_lhs =>
    rw [show tr.mul a (fun j => (b j).re) =
          repMatrix tr a *ᵥ (fun j => (b j).re) from (repMatrix_mulVec tr a _).symm,
        show tr.mul a (fun j => (b j).im) =
          repMatrix tr a *ᵥ (fun j => (b j).im) from (repMatrix_mulVec tr a _).symm]
  simp only [mulVec, dotProduct, repMatrix_apply]
  -- LHS: ↑(Σ_j R i j * re bⱼ) + ↑(Σ_j R i j * im bⱼ) * I
  -- RHS: Σ_j ↑(R i j) * bⱼ
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1; ext j
  rw [mul_assoc, ← mul_add, Complex.re_add_im]


-- @@ L59-59 verbatim
/-! ## Definition 47: Eigenvectors of ring elements -/


-- @@ L61-66 verbatim
/-- **Definition 47**: `x ∈ ℂⁿ` is an eigenvector of `a` with eigenvalue `μ` if
    `a · x = μ x` (using the complex extension of multiplication).
    By `mulComplex_eq_repMatrix_mulVec`, this is the same as `(μ, x)` being
    an eigenpair of `R_a`. -/
def IsEigenpair (a : TubalCarrier n) (μ : ℂ) (x : Fin n → ℂ) : Prop :=
  x ≠ 0 ∧ mulComplex tr a x = μ • x


-- @@ L68-73 verbatim
/-- Eigenpairs via the complex extension are the same as eigenpairs of `R_a`. -/
theorem IsEigenpair_iff_repMatrix (a : TubalCarrier n) (μ : ℂ) (x : Fin n → ℂ) :
    IsEigenpair tr a μ x ↔
      x ≠ 0 ∧ (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ x = μ • x := by
  unfold IsEigenpair
  rw [mulComplex_eq_repMatrix_mulVec]


-- @@ L75-75 verbatim
/-! ## Definition 48: Diagonalizable elements -/


-- @@ L77-83 verbatim
/-- **Definition 48**: An element `a` is *diagonalizable* if there exist `n` linearly
    independent eigenvectors in `ℂⁿ`. That is, there exist vectors `v₁, …, vₙ` and
    eigenvalues `μ₁, …, μₙ` such that the `vⱼ` are linearly independent over `ℂ`
    and each `(μⱼ, vⱼ)` is an eigenpair of `a`. -/
def IsDiag (a : TubalCarrier n) : Prop :=
  ∃ (v : Fin n → Fin n → ℂ) (μ : Fin n → ℂ),
    LinearIndependent ℂ v ∧ ∀ j, IsEigenpair tr a (μ j) (v j)


-- @@ L85-87 verbatim
/-! ## Lemma 49: Diagonalizable iff R_a is diagonalizable

  Helpers for the proof: column extraction, linear independence from invertibility. -/


-- @@ L89-91 verbatim
/-- Column j of a matrix as a vector. -/
private def col {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) : Fin m → ℂ :=
  fun i => A i j


-- @@ L93-97 verbatim
/-- Extracting column j via mulVec with standard basis vector. -/
private theorem mulVec_single_eq_col {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    A *ᵥ Pi.single j 1 = col A j := by
  ext i
  simp [mulVec, dotProduct, col, Pi.single_apply, Finset.sum_ite_eq']


-- @@ L99-119 verbatim
/-- If A * B = 1 then columns of B are linearly independent. -/
private theorem linearIndependent_cols_of_mul_eq_one {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℂ) (h : A * B = 1) :
    LinearIndependent ℂ (col B) := by
  -- col B j = B.mulVecLin (Pi.single j 1)
  have hcol_eq : col B = fun j => B.mulVecLin (Pi.single j 1) := by
    ext j i; simp [col]
  rw [hcol_eq]
  -- B.mulVecLin is injective (A is a left inverse)
  have hInj : Function.Injective B.mulVecLin := by
    intro u v huv
    have : A.mulVecLin (B.mulVecLin u) = A.mulVecLin (B.mulVecLin v) := congr_arg _ huv
    simp only [Matrix.mulVecLin_apply, mulVec_mulVec, h, one_mulVec] at this
    exact this
  -- Standard basis Pi.single · 1 is linearly independent
  have hStd : LinearIndependent ℂ (fun i => Pi.single i (1 : ℂ) : Fin m → Fin m → ℂ) := by
    have := (Pi.basisFun ℂ (Fin m)).linearIndependent
    rwa [show ⇑(Pi.basisFun ℂ (Fin m)) = fun i => Pi.single i (1 : ℂ) from by
      ext i j; simp [Pi.basisFun_apply]] at this
  -- Injective linear map preserves linear independence
  exact hStd.map' B.mulVecLin (LinearMap.ker_eq_bot_of_injective hInj)


-- @@ L121-127 verbatim
/-- diagonal(d) *ᵥ eⱼ = dⱼ • eⱼ. -/
private theorem diagonal_mulVec_single' {m : ℕ} (d : Fin m → ℂ) (j : Fin m) :
    Matrix.diagonal d *ᵥ (Pi.single j 1 : Fin m → ℂ) = d j • (Pi.single j 1 : Fin m → ℂ) := by
  ext i
  simp only [mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply,
    Pi.smul_apply, smul_eq_mul]
  split <;> simp [*]


-- @@ L129-210 verbatim
/-- **Lemma 49**: `a` is diagonalizable (n lin. indep. eigenvectors) if and only if
    `R_a` is diagonalizable over ℂ (∃ invertible S, diagonal D with A_ℂ = S D S⁻¹).

    Forward: eigenvectors as columns of S, eigenvalues as diagonal of D, invertibility
    from `linearIndependent_cols_iff_isUnit`, then A_ℂ S = S D → A_ℂ = S D S⁻¹.
    Backward: columns of S are eigenvectors with eigenvalues D j j. -/
theorem IsDiag_iff_isMatDiag (a : TubalCarrier n) :
    IsDiag tr a ↔ IsMatDiag (repMatrix tr a) := by
  unfold IsDiag IsMatDiag
  constructor
  · -- Forward: n lin. indep. eigenvectors → ∃ S, D with IsUnit S, D.IsDiag, R = S D S⁻¹
    intro ⟨v, μ, hli, heig⟩
    -- S has eigenvectors as columns: S i j = v j i
    set S : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => v j i) with hS_def
    -- D = diagonal(μ)
    set D := Matrix.diagonal μ with hD_def
    -- Eigenvector condition as R_a_ℂ *ᵥ v j = μ j • v j
    have heig' : ∀ j, (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ v j = μ j • v j := by
      intro j; rw [← mulComplex_eq_repMatrix_mulVec]; exact (heig j).2
    -- Columns of S = v
    have hcol : S.col = v := by
      ext j i; simp [Matrix.col, Matrix.transpose_apply, S, Matrix.of_apply]
    -- S is invertible (linearIndependent_cols_iff_isUnit)
    have hSu : IsUnit S :=
      linearIndependent_cols_iff_isUnit.mp (hcol ▸ hli)
    have hSS : S * S⁻¹ = 1 :=
      mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
    -- A_ℂ * S = S * D (column j: A_ℂ * v j = μ j • v j = (S * D) * eⱼ)
    have hAS_eq_SD : (repMatrix tr a).map ((↑) : ℝ → ℂ) * S = S * D := by
      ext i j
      simp only [Matrix.mul_apply, hS_def, Matrix.of_apply, hD_def, Matrix.diagonal_apply]
      have : ∑ k, (repMatrix tr a).map ((↑) : ℝ → ℂ) i k * v j k =
          ((repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ v j) i := rfl
      rw [this, heig']
      simp [Finset.sum_ite_eq', mul_comm]
    -- A_ℂ = S * D * S⁻¹ (multiply on right by S⁻¹)
    exact ⟨S, D, hSu, Matrix.isDiag_diagonal μ, by
      calc (repMatrix tr a).map ((↑) : ℝ → ℂ)
          = (repMatrix tr a).map ((↑) : ℝ → ℂ) * (S * S⁻¹) := by rw [hSS, mul_one]
        _ = S * D * S⁻¹ := by rw [← mul_assoc, hAS_eq_SD]⟩
  · -- Backward: ∃ S, D with IsUnit S, D.IsDiag, R = S D S⁻¹ → n lin. indep. eigenvectors
    intro ⟨S, D, hSu, hDdiag, hRSD⟩
    -- Eigenvectors: columns of S. Eigenvalues: diagonal entries of D.
    -- From R = S D S⁻¹: R S = S D (multiply on right by S, using S⁻¹ S = 1).
    -- So R (col j of S) = S D eⱼ = S (Dⱼⱼ eⱼ) = Dⱼⱼ (col j of S).
    rw [Matrix.isUnit_iff_isUnit_det] at hSu
    have hSS : S * S⁻¹ = 1 := mul_nonsing_inv S hSu
    have hSinv : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
    refine ⟨col S, fun j => D j j, ?_, ?_⟩
    · -- Columns of S are linearly independent (S⁻¹ is a left inverse)
      exact linearIndependent_cols_of_mul_eq_one S⁻¹ S hSinv
    · -- Each column is an eigenpair
      intro j
      constructor
      · -- v j ≠ 0: column j of S is nonzero (since S⁻¹ * S = 1)
        intro h
        have : (S⁻¹ * S) j j = 0 := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_eq_zero (fun k _ => by
            have := congr_fun h k; simp [col] at this; simp [this])
        rw [hSinv, Matrix.one_apply_eq] at this
        exact one_ne_zero this
      · -- mulComplex a (col S j) = D j j • col S j
        rw [mulComplex_eq_repMatrix_mulVec]
        -- R * S = S * D (from R = S D S⁻¹, multiply right by S)
        set R := (repMatrix tr a).map ((↑) : ℝ → ℂ)
        have hR_S : R * S = S * D := by
          rw [show R = S * D * S⁻¹ from hRSD, mul_assoc, hSinv, mul_one]
        show R *ᵥ col S j = D j j • col S j
        rw [← mulVec_single_eq_col S, mulVec_mulVec, hR_S]
        rw [← mulVec_mulVec]
        -- D *ᵥ eⱼ = Dⱼⱼ • eⱼ (D is diagonal)
        have hD_basis : D *ᵥ (Pi.single j 1 : Fin n → ℂ) =
            D j j • (Pi.single j 1 : Fin n → ℂ) := by
          ext i
          simp only [mulVec, dotProduct, Pi.single_apply,
            Pi.smul_apply, smul_eq_mul]
          by_cases hij : i = j
          · subst hij; simp
          · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
            rw [hDdiag hij]; simp [hij]
        rw [hD_basis, mulVec_smul, mulVec_single_eq_col]


-- @@ L212-216 verbatim
/-! ## Definition 50 & Lemma 51: Jointly diagonalizable sets

  We define joint diagonalizability via representation matrices.
  Lemma 51 ("S is jointly diag iff Rep(S) is jointly diag") is then definitional.
-/


-- @@ L218-219 verbatim
/-- A set `S ⊆ ℝⁿ` is *diagonalizable* if every element of `S` is diagonalizable. -/
def SetDiag (S : Set (TubalCarrier n)) : Prop := ∀ a ∈ S, IsDiag tr a


-- @@ L221-222 verbatim
/-- A tubal ring is *diagonalizable* if every element is diagonalizable. -/
def RingDiag : Prop := ∀ a : TubalCarrier n, IsDiag tr a


-- @@ L224-229 verbatim
/-- **Definition 50 (joint diag)**: `S ⊆ ℝⁿ` is *jointly diagonalizable* if there exist
    `n` linearly independent vectors that are eigenvectors for *all* `a ∈ S`. -/
def IsJointlyDiag (S : Set (TubalCarrier n)) : Prop :=
  ∃ (v : Fin n → Fin n → ℂ),
    LinearIndependent ℂ v ∧
    ∀ a ∈ S, ∃ μ : Fin n → ℂ, ∀ j, IsEigenpair tr a (μ j) (v j)


-- @@ L231-232 verbatim
/-- The tubal ring is *jointly diagonalizable* if `Set.univ` is jointly diagonalizable. -/
def RingJointlyDiag : Prop := IsJointlyDiag tr Set.univ


-- @@ L234-234 verbatim
/-! ## Lemma 51: Jointly diag ↔ Rep(S) jointly mat-diag -/


-- @@ L236-301 verbatim
/-- **Lemma 51**: `S` is jointly diagonalizable if and only if `Rep(S)` is jointly
    matrix-diagonalizable (∃ single invertible P diagonalizing all R_a for a ∈ S). -/
theorem IsJointlyDiag_iff_isJointlyMatDiag (S : Set (TubalCarrier n)) :
    IsJointlyDiag tr S ↔ IsJointlyMatDiag (repMatrix tr '' S) := by
  unfold IsJointlyDiag IsJointlyMatDiag
  constructor
  · -- Forward: common eigenbasis → single P diagonalizing all R_a
    intro ⟨v, hli, heig⟩
    set P : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => v j i)
    have hcol : P.col = v := by
      ext j i; simp [Matrix.col, Matrix.transpose_apply, P, Matrix.of_apply]
    have hPu : IsUnit P := linearIndependent_cols_iff_isUnit.mp (hcol ▸ hli)
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
    have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P hPdet
    refine ⟨P, hPu, ?_⟩
    intro A hA
    obtain ⟨a, haS, rfl⟩ := hA
    obtain ⟨μ, hμ⟩ := heig a haS
    refine ⟨Matrix.diagonal μ, Matrix.isDiag_diagonal μ, ?_⟩
    have hAP : (repMatrix tr a).map ((↑) : ℝ → ℂ) * P = P * Matrix.diagonal μ := by
      ext i j'
      simp only [Matrix.mul_apply, Matrix.diagonal_apply]
      -- LHS: ∑ k, R i k * (v j' k) = (R *ᵥ v j') i
      change ∑ k, (repMatrix tr a).map ((↑) : ℝ → ℂ) i k * v j' k =
        ∑ k, v k i * if k = j' then μ k else 0
      have : ∑ k, (repMatrix tr a).map ((↑) : ℝ → ℂ) i k * v j' k =
          ((repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ v j') i := rfl
      rw [this, ← mulComplex_eq_repMatrix_mulVec, (hμ j').2]
      simp [Finset.sum_ite_eq', mul_comm]
    calc (repMatrix tr a).map ((↑) : ℝ → ℂ)
        = (repMatrix tr a).map ((↑) : ℝ → ℂ) * (P * P⁻¹) := by rw [hPP, mul_one]
      _ = P * Matrix.diagonal μ * P⁻¹ := by rw [← mul_assoc, hAP]
  · -- Backward: single P diagonalizing all R_a → common eigenbasis
    intro ⟨P, hPu, hdiag⟩
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
    have hPinv : P⁻¹ * P = 1 := nonsing_inv_mul P hPdet
    refine ⟨col P, ?_, ?_⟩
    · exact linearIndependent_cols_of_mul_eq_one P⁻¹ P hPinv
    · intro a haS
      obtain ⟨D, hDdiag, hRD⟩ := hdiag (repMatrix tr a) ⟨a, haS, rfl⟩
      have hRP : (repMatrix tr a).map ((↑) : ℝ → ℂ) * P = P * D := by
        rw [hRD, mul_assoc, hPinv, mul_one]
      refine ⟨fun j => D j j, fun j => ?_⟩
      constructor
      · -- col P j ≠ 0
        intro h
        have : (P⁻¹ * P) j j = 0 := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_eq_zero (fun k _ => by
            have := congr_fun h k; simp [col] at this; simp [this])
        rw [hPinv, Matrix.one_apply_eq] at this
        exact one_ne_zero this
      · -- mulComplex a (col P j) = D j j • col P j
        rw [mulComplex_eq_repMatrix_mulVec]
        show (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ col P j = D j j • col P j
        rw [← mulVec_single_eq_col P, mulVec_mulVec, hRP, ← mulVec_mulVec]
        have hD_basis : D *ᵥ (Pi.single j 1 : Fin n → ℂ) =
            D j j • (Pi.single j 1 : Fin n → ℂ) := by
          ext i
          simp only [mulVec, dotProduct, Pi.single_apply,
            Pi.smul_apply, smul_eq_mul]
          by_cases hij : i = j
          · subst hij; simp
          · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
            rw [hDdiag hij]; simp [hij]
        rw [hD_basis, mulVec_smul, mulVec_single_eq_col]


-- @@ L303-307 verbatim
/-! ## Lemma 52: Diagonalizable ⟹ Jointly diagonalizable

  In a tubal ring, if S is diagonalizable then S is jointly diagonalizable.
  The proof uses: Rep(S) consists of commuting diagonalizable matrices
  (commutativity from Corollary 44, diag by assumption) → Lemma 38. -/


-- @@ L309-323 verbatim
/-- **Lemma 52**: In a tubal ring, if a set `S` is diagonalizable, then it is
    jointly diagonalizable. -/
theorem jointly_diag_of_diag (S : Set (TubalCarrier n)) (hS : SetDiag tr S) :
    IsJointlyDiag tr S := by
  rw [IsJointlyDiag_iff_isJointlyMatDiag]
  apply jointly_diag_of_commuting
  · -- Every R_a for a ∈ S is diagonalizable (convert via Lemma 49)
    intro A hA
    obtain ⟨a, haS, rfl⟩ := hA
    exact (IsDiag_iff_isMatDiag tr a).mp (hS a haS)
  · -- R_a * R_b = R_b * R_a for all a, b ∈ S (commutativity)
    intro A hA B hB
    obtain ⟨a, _, rfl⟩ := hA
    obtain ⟨b, _, rfl⟩ := hB
    exact repMatrix_comm tr a b


-- @@ L325-328 verbatim
/-- Corollary: if the ring is diagonalizable, it is jointly diagonalizable. -/
theorem RingJointlyDiag_of_RingDiag (hd : RingDiag tr) : RingJointlyDiag tr := by
  apply jointly_diag_of_diag
  intro a _; exact hd a


-- @@ L330-335 verbatim
/-! ## Lemma 53: Span preserves diagonalizability

  If S is diagonalizable, then span(S) is diagonalizable. The proof uses:
  S is jointly diag → ∃ P diagonalizing all R_a for a ∈ S →
  for b ∈ span(S), R_b = Σ αⱼ R_{aⱼ}, so P R_b P⁻¹ = Σ αⱼ (P R_{aⱼ} P⁻¹)
  is a sum of diagonal matrices, hence diagonal. -/


-- @@ L337-345 verbatim
/-- Helper: if `P A P⁻¹` is diagonal and `P B P⁻¹` is diagonal then
    `P (A+B) P⁻¹` is diagonal. -/
private theorem conj_map_add {m : ℕ} (P P_inv : Matrix (Fin m) (Fin m) ℂ)
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    P * (A + B).map ((↑) : ℝ → ℂ) * P_inv =
      P * A.map ((↑) : ℝ → ℂ) * P_inv + P * B.map ((↑) : ℝ → ℂ) * P_inv := by
  have hmap : (A + B).map ((↑) : ℝ → ℂ) =
      A.map ((↑) : ℝ → ℂ) + B.map ((↑) : ℝ → ℂ) := by ext i j; simp
  rw [hmap, mul_add, add_mul]


-- @@ L347-353 verbatim
private theorem conj_map_smul {m : ℕ} (P P_inv : Matrix (Fin m) (Fin m) ℂ)
    (r : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    P * (r • A).map ((↑) : ℝ → ℂ) * P_inv =
      (r : ℂ) • (P * A.map ((↑) : ℝ → ℂ) * P_inv) := by
  have hmap : (r • A).map ((↑) : ℝ → ℂ) = (r : ℂ) • A.map ((↑) : ℝ → ℂ) := by
    ext i j; simp
  rw [hmap, mul_smul_comm, smul_mul_assoc]


-- @@ L355-402 verbatim
/-- **Lemma 53**: If `S` is diagonalizable, then `Submodule.span ℝ S` is diagonalizable. -/
theorem diag_span (S : Set (TubalCarrier n)) (hS : SetDiag tr S) :
    SetDiag tr (Submodule.span ℝ S : Set (TubalCarrier n)) := by
  -- S is jointly diag → convert to matrix form → get a common diagonalizer P
  obtain ⟨P, hPu, hdiag⟩ :=
    (IsJointlyDiag_iff_isJointlyMatDiag tr S).mp (jointly_diag_of_diag tr S hS)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P hPdet
  have hPinv : P⁻¹ * P = 1 := nonsing_inv_mul P hPdet
  have hPinvu : IsUnit P⁻¹ := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact Matrix.isUnit_nonsing_inv_det P hPdet
  -- Show every element of span(S) is diagonalizable using P as diagonalizer
  intro b hb
  rw [IsDiag_iff_isMatDiag]
  -- Use S = P. D_b = P⁻¹ * R_b_ℂ * P. Show D_b is diagonal, then R_b_ℂ = P * D_b * P⁻¹.
  refine ⟨P, P⁻¹ * (repMatrix tr b).map ((↑) : ℝ → ℂ) * P, hPu, ?_, ?_⟩
  · -- P⁻¹ * R_b_ℂ * P is diagonal — by span induction
    induction hb using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨D, hDdiag, hRD⟩ := hdiag (repMatrix tr a) ⟨a, ha, rfl⟩
      -- R_a_ℂ = P * D * P⁻¹, so P⁻¹ * R_a_ℂ * P = D
      have : P⁻¹ * (repMatrix tr a).map ((↑) : ℝ → ℂ) * P = D := by
        calc P⁻¹ * (repMatrix tr a).map ((↑) : ℝ → ℂ) * P
            = P⁻¹ * (P * D * P⁻¹) * P := by rw [hRD]
          _ = P⁻¹ * P * D * (P⁻¹ * P) := by simp only [mul_assoc]
          _ = 1 * D * 1 := by rw [hPinv]
          _ = D := by rw [one_mul, mul_one]
      rw [this]; exact hDdiag
    | zero =>
      simp only [repMatrix_zero]
      intro i j hij; simp
    | add a b _ _ iha ihb =>
      rw [repMatrix_add]
      have hmap : (repMatrix tr a + repMatrix tr b).map ((↑) : ℝ → ℂ) =
          (repMatrix tr a).map ((↑) : ℝ → ℂ) + (repMatrix tr b).map ((↑) : ℝ → ℂ) := by
        ext i j; simp
      rw [hmap, mul_add, add_mul]; exact iha.add ihb
    | smul r a _ iha =>
      rw [repMatrix_smul]
      have hmap : (r • repMatrix tr a).map ((↑) : ℝ → ℂ) =
          (r : ℂ) • (repMatrix tr a).map ((↑) : ℝ → ℂ) := by ext i j; simp
      rw [hmap, mul_smul_comm, smul_mul_assoc]; exact iha.smul _
  · -- R_b_ℂ = P * (P⁻¹ * R_b_ℂ * P) * P⁻¹
    set R := (repMatrix tr b).map ((↑) : ℝ → ℂ)
    have : P * (P⁻¹ * R * P) * P⁻¹ = R := by
      have h1 : P * (P⁻¹ * R * P) = P * P⁻¹ * R * P := by simp only [mul_assoc]
      rw [h1, hPP, one_mul, mul_assoc, hPP, mul_one]
    exact this.symm


-- @@ L404-408 verbatim
/-! ## Proposition 54: Diagonalizable ⟺ ⋆_M form

  A tubal ring is diagonalizable if and only if there exists an invertible M ∈ ℂ^{n×n}
  such that a · b = M⁻¹(Ma • Mb) for all a, b ∈ ℝⁿ.
-/


-- @@ L410-413 verbatim
/-- diag(v) *ᵥ w = v ∘ₕ w (diagonal matrix action = Hadamard product). -/
private theorem diagonal_mulVec_eq_had {m : ℕ} (v w : Fin m → ℂ) :
    Matrix.diagonal v *ᵥ w = v ∘ₕ w := by
  ext i; simp [mulVec, dotProduct, Matrix.diagonal_apply, vecHadamard_apply]


-- @@ L415-418 verbatim
/-- toComplex(Pi.single j 1) = Pi.single j 1 as ℂ-vectors. -/
private theorem toComplex_single (j : Fin n) :
    toComplex (Pi.single j (1 : ℝ)) = (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
  ext i; simp [toComplex_apply, Pi.single_apply]; split <;> simp


-- @@ L420-425 verbatim
/-- The ⋆_M form: `a · b = M⁻¹(Ma • Mb)` where `•` is the Hadamard product. -/
def HasStarMForm : Prop :=
  ∃ (M : Matrix (Fin n) (Fin n) ℂ), IsUnit M ∧
    ∀ a b : TubalCarrier n,
      toComplex (tr.mul a b) =
        M⁻¹ *ᵥ (vecHadamard (M *ᵥ toComplex a) (M *ᵥ toComplex b))


-- @@ L427-493 verbatim
/-- **Proposition 54 (backward direction)**: If there exists an invertible M with
    `a · b = M⁻¹(Ma • Mb)`, then the tubal ring is diagonalizable.

    Proof: From the ⋆_M form, for all real x:
    R_a_ℂ (toComplex x) = M⁻¹ diag(Ma) M (toComplex x).
    Since real basis vectors span ℂⁿ, R_a_ℂ = M⁻¹ diag(Ma) M.
    With S = M⁻¹: R_a_ℂ = S * diag(Ma) * S⁻¹, so R_a is diagonalizable. -/
theorem RingDiag_of_starMForm (h : HasStarMForm tr) : RingDiag tr := by
  obtain ⟨M, hMu, hmul⟩ := h
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMu
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv M hMdet
  have hMinv : M⁻¹ * M = 1 := nonsing_inv_mul M hMdet
  intro a
  rw [IsDiag_iff_isMatDiag]
  -- S = M⁻¹ diagonalizes R_a. D = diagonal(M *ᵥ toComplex a).
  set Ma := M *ᵥ toComplex a
  refine ⟨M⁻¹, Matrix.diagonal Ma, ?_, Matrix.isDiag_diagonal Ma, ?_⟩
  · -- M⁻¹ is a unit
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_nonsing_inv_det M hMdet
  · -- R_a_ℂ = M⁻¹ * diag(Ma) * (M⁻¹)⁻¹ = M⁻¹ * diag(Ma) * M
    rw [nonsing_inv_nonsing_inv M hMdet]
    -- Show: R_a_ℂ = M⁻¹ * diag(Ma) * M
    -- Strategy: both sides agree on toComplex(eⱼ) for all j (real basis = ℂ basis).
    -- LHS: R_a_ℂ (toComplex eⱼ) = toComplex(R_a eⱼ) = toComplex(a · eⱼ)
    -- RHS: M⁻¹ diag(Ma) M (toComplex eⱼ) = M⁻¹ (Ma • M(toComplex eⱼ))
    -- By ⋆_M formula: toComplex(a · eⱼ) = M⁻¹ (Ma • M(toComplex eⱼ)). ✓
    -- Two matrices are equal iff they agree on all standard basis vectors.
    -- For eⱼ: LHS *ᵥ toComplex(eⱼ) = toComplex(R_a eⱼ) = toComplex(a · eⱼ)
    --         RHS *ᵥ toComplex(eⱼ) = M⁻¹ diag(Ma) M toComplex(eⱼ) = M⁻¹(Ma • M(toComplex eⱼ))
    -- These are equal by the ⋆_M formula.
    -- Show the matrices agree on every column (= mulVec with eⱼ).
    suffices h : ∀ j, (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ (Pi.single j 1 : Fin n → ℂ) =
        (M⁻¹ * Matrix.diagonal Ma * M) *ᵥ (Pi.single j 1 : Fin n → ℂ) by
      ext i j
      -- (A *ᵥ eⱼ) i = A i j (column extraction)
      have hl := congr_fun (h j) i
      simpa [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ] using hl
    intro j
    -- LHS: R_a_ℂ *ᵥ toComplex(eⱼ) = toComplex(R_a *ᵥ eⱼ) = toComplex(a · eⱼ)
    have hlhs : (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ (Pi.single j 1 : Fin n → ℂ) =
        toComplex (tr.mul a (Pi.single j 1)) := by
      -- Pi.single j 1 : Fin n → ℂ = toComplex(Pi.single j 1 : TubalCarrier n)
      -- R_a.map ↑ *ᵥ toComplex(x) = toComplex(R_a *ᵥ x) and R_a *ᵥ x = a · x
      funext i
      simp [mulVec, dotProduct, Matrix.map_apply, toComplex_apply, repMatrix_apply,
        Pi.single_apply, Finset.sum_ite_eq']
    have hrhs : (M⁻¹ * Matrix.diagonal Ma * M) *ᵥ (Pi.single j 1 : Fin n → ℂ) =
        M⁻¹ *ᵥ (Ma ∘ₕ (M *ᵥ toComplex (Pi.single j 1))) := by
      -- (M⁻¹ * diag(Ma) * M) *ᵥ eⱼ
      -- = M⁻¹ *ᵥ (diag(Ma) *ᵥ (M *ᵥ eⱼ))      [by mulVec_mulVec twice]
      -- = M⁻¹ *ᵥ (Ma ∘ₕ (M *ᵥ eⱼ))             [by diagonal_mulVec_eq_had]
      -- = M⁻¹ *ᵥ (Ma ∘ₕ (M *ᵥ toComplex eⱼ))    [by toComplex_single]
      rw [toComplex_single, mul_assoc]
      -- Goal: (M⁻¹ * (diag Ma * M)) *ᵥ eⱼ = M⁻¹ *ᵥ (Ma ∘ₕ M *ᵥ eⱼ)
      -- Use: (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) [mulVec_mulVec in reverse]
      conv_lhs => rw [show (M⁻¹ * (Matrix.diagonal Ma * M)) *ᵥ Pi.single j 1 =
        M⁻¹ *ᵥ ((Matrix.diagonal Ma * M) *ᵥ Pi.single j 1) from by
          rw [mulVec_mulVec]]
      congr 1
      rw [show (Matrix.diagonal Ma * M) *ᵥ Pi.single j 1 =
        Matrix.diagonal Ma *ᵥ (M *ᵥ Pi.single j 1) from by rw [mulVec_mulVec]]
      exact diagonal_mulVec_eq_had Ma (M *ᵥ Pi.single j 1)
    rw [hlhs, hrhs]
    -- Now use ⋆_M formula: toComplex(a · eⱼ) = M⁻¹(Ma • M(toComplex eⱼ))
    exact hmul a (Pi.single j 1)


-- @@ L495-685 verbatim
/-- **Proposition 54 (forward direction)**: If the tubal ring is diagonalizable,
    there exists an invertible M with `a · b = M⁻¹(Ma • Mb)`.

    Proof (following the paper):
    1. Ring is jointly diag (Lemma 52) → ∃ S with S R_a S⁻¹ = D_a for all a.
    2. Define Ma := diag entries of D_a = S R_a S⁻¹ 𝟙. Map a ↦ Ma is linear.
    3. Λ_a = diag(Ma), R_a = S⁻¹ diag(Ma) S.
    4. a · b = R_a b = S⁻¹(Ma • Sb).
    5. x = x · e = S⁻¹(Mx • Se) = S⁻¹ diag(Se) Mx for all x.
       So S⁻¹ diag(Se) M = I, all entries of Se nonzero, S = diag(Se) M.
    6. a · b = S⁻¹(Ma • Sb) = M⁻¹(Ma • Mb) after rescaling. -/
theorem starMForm_of_RingDiag (hd : RingDiag tr) : HasStarMForm tr := by
  -- Step 1: Ring is jointly diag → get P with R_a_ℂ = P * D_a * P⁻¹ for all a.
  have hjd := RingJointlyDiag_of_RingDiag tr hd
  obtain ⟨P, hPu, hdiag_all⟩ :=
    (IsJointlyDiag_iff_isJointlyMatDiag tr Set.univ).mp hjd
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P hPdet
  have hPinv : P⁻¹ * P = 1 := nonsing_inv_mul P hPdet
  -- For each a, get D_a diagonal with R_a_ℂ = P * D_a * P⁻¹
  -- We use Set.univ, so the image is all repMatrix tr a
  have hdiag : ∀ a : TubalCarrier n, ∃ D : Matrix (Fin n) (Fin n) ℂ,
      D.IsDiag ∧ (repMatrix tr a).map ((↑) : ℝ → ℂ) = P * D * P⁻¹ := by
    intro a; exact hdiag_all (repMatrix tr a) ⟨a, Set.mem_univ _, rfl⟩
  -- Step 2: Define M. Column j of M = diagonal entries of D_{eⱼ}.
  -- M i j = (P⁻¹ * R_{eⱼ}_ℂ * P) i i
  -- We use the Choose function to pick D for each a.
  set getD : TubalCarrier n → Matrix (Fin n) (Fin n) ℂ := fun a => (hdiag a).choose
  have hgetD_diag : ∀ a, (getD a).IsDiag := fun a => (hdiag a).choose_spec.1
  have hgetD_eq : ∀ a, (repMatrix tr a).map ((↑) : ℝ → ℂ) = P * getD a * P⁻¹ :=
    fun a => (hdiag a).choose_spec.2
  -- d_a = diagonal entries of D_a
  set d : TubalCarrier n → (Fin n → ℂ) := fun a i => getD a i i
  -- D_a = diagonal(d_a) since D_a is diagonal
  have hD_eq_diag : ∀ a, getD a = Matrix.diagonal (d a) := by
    intro a; ext i j
    simp only [Matrix.diagonal_apply, d]
    by_cases h : i = j
    · subst h; simp
    · simp [hgetD_diag a h, h]
  -- Step 3: Define M and prove Ma = d_a.
  -- Key: d a i = (P⁻¹ * R_a_ℂ * P) i i is ℝ-linear in a (entry-by-entry).
  -- Basis decomposition: tr.mul a v = ∑ⱼ aⱼ • tr.mul eⱼ v
  have hmul_basis : ∀ (a : TubalCarrier n) (v : TubalCarrier n),
      tr.mul a v = ∑ j : Fin n, a j • tr.mul (Pi.single j 1) v := by
    intro a v
    have ha : a = ∑ j : Fin n, a j • (Pi.single j 1 : TubalCarrier n) := by
      ext m; simp [Finset.sum_apply, Pi.single_apply]
    calc tr.mul a v = tr.mul v a := tr.mul_comm a v
      _ = (tr.mulLeftLinear v) a := rfl
      _ = (tr.mulLeftLinear v) (∑ j, a j • (Pi.single j 1 : TubalCarrier n)) :=
          congr_arg _ ha
      _ = ∑ j, a j • tr.mul (Pi.single j 1) v := by
          rw [map_sum]; apply Finset.sum_congr rfl; intro j _
          -- Goal: (tr.mulLeftLinear v) (a j • Pi.single j 1) = a j • tr.mul (Pi.single j 1) v
          rw [TubalRing.mulLeftLinear_apply]
          -- tr.mul v (a j • Pi.single j 1) = a j • tr.mul (Pi.single j 1) v
          have := tr.smul_mul (a j) (Pi.single j 1 : TubalCarrier n) v
          rw [tr.mul_comm v]; exact this
  -- Define M: M i j = d(eⱼ) i
  set M : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => d (Pi.single j 1) i) with hM_def
  -- Ma = d_a: prove entry-by-entry via the canonical form d a i = (P⁻¹ R_a_ℂ P) i i
  have hMa : ∀ a : TubalCarrier n, M *ᵥ toComplex a = d a := by
    intro a; funext i
    simp only [mulVec, dotProduct, hM_def, Matrix.of_apply, toComplex_apply]
    -- Goal: ∑ⱼ d(eⱼ) i * ↑(aⱼ) = d a i
    -- i.e., ∑ⱼ getD(eⱼ) i i * ↑(aⱼ) = getD(a) i i
    -- Use: getD a = P⁻¹ * R_a_ℂ * P, so getD(a) i i = ∑ₖₗ P⁻¹ i k * ↑(R_a k l) * P l i
    -- Each R_a k l = tr.mul a (eₗ) k = ∑ⱼ aⱼ * tr.mul (eⱼ)(eₗ) k [by hmul_basis]
    -- Substitute and rearrange sums → equals LHS.
    -- Step A: Canonical form for both sides
    have hd_can : ∀ b, d b i = (P⁻¹ * (repMatrix tr b).map ((↑) : ℝ → ℂ) * P) i i := by
      intro b
      show getD b i i = _
      have key : P⁻¹ * (repMatrix tr b).map ((↑) : ℝ → ℂ) * P = getD b := by
        rw [hgetD_eq b]; simp only [mul_assoc]
        rw [hPinv, mul_one, ← mul_assoc P⁻¹ P, hPinv, one_mul]
      rw [key.symm]
    -- Step B: Expand both sides using matrix mul entries
    simp_rw [hd_can]
    simp only [Matrix.mul_apply, Matrix.map_apply, repMatrix_apply]
    -- Step C: Use hmul_basis to decompose tr.mul a (eₗ) k
    -- The RHS has tr.mul a (Pi.single ? 1) ?. Rewrite using hmul_basis.
    simp_rw [hmul_basis a]
    simp only [TubalCarrier.sum_apply, TubalCarrier.smul_apply,
      Complex.ofReal_sum, Complex.ofReal_mul]
    -- Now both sides are multi-index sums over the same terms. Rearrange.
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- Both sides are triple sums ∑∑∑ over the same terms in different order.
    -- LHS order: ∑ⱼ ∑ₖ ∑ₗ, RHS order: ∑ₖ ∑ₗ ∑ⱼ. Rearrange LHS to match.
    rw [Finset.sum_comm]          -- swap outermost: ∑ⱼ ∑ₖ → ∑ₖ ∑ⱼ
    congr 1; ext k
    rw [Finset.sum_comm]          -- swap inner: ∑ⱼ ∑ₗ → ∑ₗ ∑ⱼ
    congr 1; ext l
    congr 1; ext x; ring
  -- Step 4: R_a_ℂ = P * diag(Ma) * P⁻¹
  have hR_diag : ∀ a : TubalCarrier n,
      (repMatrix tr a).map ((↑) : ℝ → ℂ) = P * Matrix.diagonal (M *ᵥ toComplex a) * P⁻¹ := by
    intro a; rw [hMa, ← hD_eq_diag, hgetD_eq]
  -- Step 5: For any real b, R_a_ℂ *ᵥ toComplex(b) = P *ᵥ (Ma ∘ₕ (P⁻¹ *ᵥ toComplex b))
  have hR_action : ∀ a b : TubalCarrier n,
      (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ toComplex b =
        P *ᵥ ((M *ᵥ toComplex a) ∘ₕ (P⁻¹ *ᵥ toComplex b)) := by
    intro a b
    -- R_a_ℂ *ᵥ b = (P * diag(Ma) * P⁻¹) *ᵥ b = P *ᵥ (Ma ∘ₕ (P⁻¹ *ᵥ b))
    rw [hR_diag a, mul_assoc]
    -- Now: (P * (diag(Ma) * P⁻¹)) *ᵥ toComplex b = P *ᵥ (Ma ∘ₕ (P⁻¹ *ᵥ toComplex b))
    simp only [← mulVec_mulVec]
    rw [diagonal_mulVec_eq_had]
  -- Step 6: Unit element. R_e *ᵥ x = x, so e acts as identity.
  -- Use: toComplex(x) = toComplex(x · e) = R_x_ℂ *ᵥ toComplex(e)
  --    = P *ᵥ (Mx ∘ₕ (P⁻¹ *ᵥ toComplex e))  [by hR_action]
  -- Define β = P⁻¹ *ᵥ toComplex(tr.one)
  set β := P⁻¹ *ᵥ toComplex tr.one
  -- Helper: R_a.map ↑ *ᵥ toComplex b = toComplex(R_a *ᵥ b) = toComplex(a · b)
  have map_mulVec_toComplex : ∀ (a b : TubalCarrier n),
      (repMatrix tr a).map ((↑) : ℝ → ℂ) *ᵥ toComplex b = toComplex (tr.mul a b) := by
    intro a b
    -- R_a.map ↑ *ᵥ toComplex(b) and toComplex(R_a *ᵥ b) agree entry-by-entry
    -- using: repMatrix_mulVec and the ring hom property of ↑
    funext i
    simp only [mulVec, dotProduct, Matrix.map_apply, toComplex_apply, repMatrix_apply]
    -- ∑ x, ↑(R_a i x) * ↑(b x) = ↑(a · b) i, i.e., (R_a *ᵥ b) i cast to ℂ
    -- repMatrix_mulVec: R_a *ᵥ b = a · b
    have := congr_arg (fun v => (↑(v i) : ℂ)) (repMatrix_mulVec tr a b)
    simp only [mulVec, dotProduct, repMatrix_apply, Complex.ofReal_sum,
      Complex.ofReal_mul] at this
    exact this
  have hunit : ∀ x : TubalCarrier n,
      toComplex x = P *ᵥ ((M *ᵥ toComplex x) ∘ₕ β) := by
    intro x
    have h1 := hR_action x tr.one
    rw [map_mulVec_toComplex, tr.mul_one] at h1
    exact h1
  -- Step 7: P⁻¹ *ᵥ toComplex(b) = (Mb) ∘ₕ β (from hunit applied to b, then P⁻¹)
  have hPinv_b : ∀ b : TubalCarrier n,
      P⁻¹ *ᵥ toComplex b = (M *ᵥ toComplex b) ∘ₕ β := by
    intro b
    have := hunit b
    -- toComplex b = P *ᵥ ((Mb) ∘ₕ β), apply P⁻¹
    calc P⁻¹ *ᵥ toComplex b
        = P⁻¹ *ᵥ (P *ᵥ ((M *ᵥ toComplex b) ∘ₕ β)) := by congr 1
      _ = (P⁻¹ * P) *ᵥ ((M *ᵥ toComplex b) ∘ₕ β) := by rw [mulVec_mulVec]
      _ = (M *ᵥ toComplex b) ∘ₕ β := by rw [hPinv, one_mulVec]
  -- Step 8: toComplex(a · b) = (P * diag β) *ᵥ (Ma ∘ₕ Mb)
  have hformula : ∀ a b : TubalCarrier n,
      toComplex (tr.mul a b) = (P * Matrix.diagonal β) *ᵥ
        ((M *ᵥ toComplex a) ∘ₕ (M *ᵥ toComplex b)) := by
    intro a b
    have h1 := hR_action a b
    rw [map_mulVec_toComplex, hPinv_b] at h1
    -- h1: toComplex(a·b) = P *ᵥ (Ma ∘ₕ (Mb ∘ₕ β))
    rw [h1]
    -- P *ᵥ (Ma ∘ₕ (Mb ∘ₕ β)) = (P * diag β) *ᵥ (Ma ∘ₕ Mb)
    -- Rearrange: Ma ∘ₕ (Mb ∘ₕ β) = β ∘ₕ (Ma ∘ₕ Mb) = diag(β) *ᵥ (Ma ∘ₕ Mb)
    rw [show (M *ᵥ toComplex a) ∘ₕ ((M *ᵥ toComplex b) ∘ₕ β) =
        β ∘ₕ ((M *ᵥ toComplex a) ∘ₕ (M *ᵥ toComplex b)) from by
      ext k; simp [vecHadamard_apply]; ring,
      ← diagonal_mulVec_eq_had, mulVec_mulVec]
  -- Step 9: (P * diag β) * M = I (from hunit on basis vectors)
  have hNM : (P * Matrix.diagonal β) * M = 1 := by
    ext i j
    -- From hunit(eⱼ): toComplex(eⱼ) = P *ᵥ (M(toComplex eⱼ) ∘ₕ β)
    -- = (P * diag β) *ᵥ (M *ᵥ toComplex eⱼ) = ((P * diag β) * M) *ᵥ toComplex eⱼ
    have h := hunit (Pi.single j 1)
    -- Rewrite h: toComplex(eⱼ) = P *ᵥ (M(toComplex eⱼ) ∘ₕ β) = (P * diag β) *ᵥ M(toComplex eⱼ)
    rw [show P *ᵥ ((M *ᵥ toComplex (Pi.single j 1)) ∘ₕ β) =
        (P * Matrix.diagonal β) *ᵥ (M *ᵥ toComplex (Pi.single j 1)) from by
      rw [show (M *ᵥ toComplex (Pi.single j 1)) ∘ₕ β =
          β ∘ₕ (M *ᵥ toComplex (Pi.single j 1)) from vecHadamard_comm _ _]
      rw [← diagonal_mulVec_eq_had, mulVec_mulVec]] at h
    -- h: toComplex(eⱼ) = ((P * diag β) * M) *ᵥ toComplex(eⱼ)
    rw [mulVec_mulVec] at h
    -- Extract entry (i,j)
    have hi := congr_fun h i
    simp only [mulVec, dotProduct, toComplex_apply, Pi.single_apply,
      apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one, Complex.ofReal_zero,
      mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Matrix.one_apply] at hi ⊢
    exact hi.symm
  -- Step 10: M is invertible
  have hMu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_det_of_left_inverse hNM
  -- Step 11: M⁻¹ = P * diag β
  have hMinv : M⁻¹ = P * Matrix.diagonal β := by
    have hMdet := (Matrix.isUnit_iff_isUnit_det M).mp hMu
    exact inv_eq_left_inv hNM
  -- Conclude: ∃ M, IsUnit M ∧ toComplex(a · b) = M⁻¹ *ᵥ (Ma ∘ₕ Mb)
  exact ⟨M, hMu, fun a b => by rw [hMinv]; exact hformula a b⟩


-- @@ L687-690 verbatim
/-- **Proposition 54**: A tubal ring is diagonalizable if and only if there exists
    an invertible M ∈ ℂ^{n×n} such that `a · b = M⁻¹(Ma • Mb)` for all `a, b`. -/
theorem RingDiag_iff_starMForm : RingDiag tr ↔ HasStarMForm tr :=
  ⟨starMForm_of_RingDiag tr, RingDiag_of_starMForm tr⟩


-- @@ L692-692 verbatim
end TubalTensor
