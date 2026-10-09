import OAI.Probability.EntangledGames.MeasurementTransport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_m u_n u_p u_q


-- @@ L7-7 verbatim
open scoped BigOperators ComplexOrder

-- @@ L8-8 verbatim
open scoped MatrixOrder

-- @@ L9-9 verbatim
open Matrix

-- @@ L10-10 verbatim
open MeasureTheory Filter Set

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open scoped Matrix.Norms.Elementwise


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L16-16 verbatim
open Matrix


-- @@ L18-18 verbatim
namespace ThresholdParallelRepetition.QuantumSampling

-- @@ L19-19 verbatim
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]


-- @@ L21-21 verbatim
def hsSq (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)


-- @@ L23-24 verbatim
lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _


-- @@ L26-28 verbatim
lemma hsSq_conjTranspose (M : Matrix m n ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm


-- @@ L30-38 verbatim
lemma hsSq_eq_trace (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, hsSq]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [Complex.mul_re, Complex.normSq_apply]


-- @@ L40-41 verbatim
lemma hsSq_eq_trace' (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (M * Mᴴ)).re := by
  rw [← hsSq_conjTranspose M, hsSq_eq_trace, Matrix.conjTranspose_conjTranspose]


-- @@ L43-47 verbatim
lemma hsSq_mul_left {U : Matrix m m ℂ} [DecidableEq m] (hU : Uᴴ * U = 1)
    (M : Matrix m n ℂ) : hsSq (U * M) = hsSq M := by
  rw [hsSq_eq_trace, Matrix.conjTranspose_mul]
  rw [show (Mᴴ * Uᴴ) * (U * M) = Mᴴ * (Uᴴ * U) * M by simp only [Matrix.mul_assoc],
    hU, Matrix.mul_one, ← hsSq_eq_trace]


-- @@ L49-53 verbatim
lemma hsSq_mul_right {U : Matrix n n ℂ} [DecidableEq n] (hU : U * Uᴴ = 1)
    (M : Matrix m n ℂ) : hsSq (M * U) = hsSq M := by
  rw [← hsSq_conjTranspose, Matrix.conjTranspose_mul]
  rw [hsSq_mul_left (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU),
    hsSq_conjTranspose]


-- @@ L55-91 verbatim
lemma hsSq_spectral_mixed [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    hsSq (cfc f A - cfc g B) =
      ∑ i, ∑ j, (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  have hUU' : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have hVV : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  have hVV' : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  have hf : cfc f A = U * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ := by
    erw [hA.cfc_eq]
    rfl
  have hg : cfc g B = V * Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ)) * Vᴴ := by
    erw [hB.cfc_eq]
    rfl
  have hmixed : Uᴴ * (cfc f A - cfc g B) * V =
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * (Uᴴ * V) -
      (Uᴴ * V) * Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ)) := by
    rw [hf, hg, Matrix.mul_sub, Matrix.sub_mul]
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    simp only [Matrix.mul_assoc, hVV', Matrix.mul_one]
  rw [← hsSq_mul_left (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hUU)
      (cfc f A - cfc g B),
    ← hsSq_mul_right hVV (Uᴴ * (cfc f A - cfc g B)), hmixed]
  unfold hsSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_comm ((Uᴴ * V) i j), ← sub_mul, ← Complex.ofReal_sub, Complex.normSq_mul,
    Complex.normSq_ofReal]
  simp only [pow_two]
  rfl


-- @@ L93-106 verbatim
lemma hsSq_cfc_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ)
    (hf : ∀ s t : ℝ, (f s - f t)^2 ≤ L * (s - t)^2) :
    hsSq (cfc f A - cfc f B) ≤ L * hsSq (A - B) := by
  have hident := hsSq_spectral_mixed hA hB (fun x => x) (fun x => x)
  erw [cfc_id' ℝ A hA, cfc_id' ℝ B hB] at hident
  rw [hsSq_spectral_mixed hA hB, hident, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (hf (hA.eigenvalues i) (hB.eigenvalues j)) (Complex.normSq_nonneg _)


-- @@ L108-114 verbatim
lemma hsSq_abs_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hsSq (cfc (fun t : ℝ => |t|) A - cfc (fun t : ℝ => |t|) B) ≤ hsSq (A - B) := by
  simpa using hsSq_cfc_sub_le hA hB (fun t : ℝ => |t|) 1 (fun s t => by
    have h := abs_abs_sub_abs_le_abs_sub s t
    nlinarith [sq_nonneg (|s-t| - |(|s| - |t|)|), abs_nonneg (s-t), abs_nonneg (|s|-|t|),
      sq_abs (s-t), sq_abs (|s|-|t|)])


-- @@ L116-116 verbatim
lemma hsSq_zero : hsSq (0 : Matrix m n ℂ) = 0 := by simp [hsSq]


-- @@ L118-124 verbatim
lemma hsSq_blocks {q : Type u_q} [Fintype q] (A : Matrix m n ℂ) (B : Matrix m p ℂ)
    (C : Matrix q n ℂ) (D : Matrix q p ℂ) :
    hsSq (Matrix.fromBlocks A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  simp only [hsSq, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring


-- @@ L126-132 verbatim
omit [Fintype m] [Fintype n] [Fintype p] in
lemma fromBlocks_sub {q : Type u_q} (A A' : Matrix m n ℂ) (B B' : Matrix m p ℂ)
    (C C' : Matrix q n ℂ) (D D' : Matrix q p ℂ) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A-A') (B-B') (C-C') (D-D') := by
  ext i j
  cases i <;> cases j <;> rfl


-- @@ L134-145 verbatim
lemma block_diagonal_pos [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  have hRa := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hRb := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hR : (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B))ᴴ *
      (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B)) = Matrix.fromBlocks A 0 0 B := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hRa, hRb,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  rw [← hR]
  exact Matrix.posSemidef_conjTranspose_mul_self _


-- @@ L147-148 verbatim
def dilation (M : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 M Mᴴ 0


-- @@ L150-154 verbatim
omit [Fintype m] [Fintype n] in
lemma dilation_isHermitian (M : Matrix m n ℂ) : (dilation M).IsHermitian := by
  unfold Matrix.IsHermitian dilation
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_conjTranspose]


-- @@ L156-168 verbatim
lemma abs_square [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun t : ℝ => |t|) A * cfc (fun t : ℝ => |t|) A = A * A := by
  erw [← cfc_mul (fun t : ℝ => |t|) (fun t : ℝ => |t|) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun t : ℝ => t * t) A := by
      apply cfc_congr
      intro t _
      nlinarith [sq_abs t]
    _ = cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => t) A := by
      erw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by erw [cfc_id' ℝ A hA]


-- @@ L170-173 verbatim
lemma abs_eq_sqrt_square [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun t : ℝ => |t|) A = CFC.sqrt (A * A) := by
  apply Eq.symm
  exact CFC.sqrt_unique (abs_square hA) (cfc_nonneg fun t _ => abs_nonneg t)


-- @@ L175-183 verbatim
lemma sqrt_block_diagonal [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  have hpos : 0 ≤ Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) :=
    (block_diagonal_pos (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg
  apply CFC.sqrt_unique _ hpos
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]


-- @@ L185-192 verbatim
lemma abs_dilation [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) :
    cfc (fun t : ℝ => |t|) (dilation M) =
      Matrix.fromBlocks (CFC.sqrt (M * Mᴴ)) 0 0 (CFC.sqrt (Mᴴ * M)) := by
  rw [abs_eq_sqrt_square (dilation_isHermitian M)]
  unfold dilation
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  exact sqrt_block_diagonal (Matrix.posSemidef_self_mul_conjTranspose M)
    (Matrix.posSemidef_conjTranspose_mul_self M)


-- @@ L194-200 verbatim
theorem hsSq_right_absolute_sub_le [DecidableEq m] [DecidableEq n] (M N : Matrix m n ℂ) :
    hsSq (CFC.sqrt (Mᴴ * M) - CFC.sqrt (Nᴴ * N)) ≤ 2 * hsSq (M - N) := by
  have h := hsSq_abs_sub_le (dilation_isHermitian M) (dilation_isHermitian N)
  rw [abs_dilation M, abs_dilation N] at h
  simp only [dilation, fromBlocks_sub, sub_self, hsSq_blocks, hsSq_zero, zero_add, add_zero] at h
  rw [← Matrix.conjTranspose_sub, hsSq_conjTranspose] at h
  linarith [hsSq_nonneg (CFC.sqrt (M * Mᴴ) - CFC.sqrt (N * Nᴴ))]


-- @@ L202-202 verbatim
end ThresholdParallelRepetition.QuantumSampling


-- @@ L204-204 verbatim
end


-- @@ L206-206 verbatim
end OAI
