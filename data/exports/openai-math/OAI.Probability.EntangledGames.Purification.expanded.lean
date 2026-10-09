import OAI.Probability.EntangledGames.SpectralEntropy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_n u_α u_m u_p u_J u_R


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
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology

-- @@ L16-16 verbatim
open Matrix MeasureTheory Filter Set

-- @@ L17-17 verbatim
namespace ThresholdParallelRepetition.Resolvent

-- @@ L18-18 verbatim
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci rectContinuousENorm

-- @@ L19-19 verbatim
variable {n : Type u_n} [Fintype n] [DecidableEq n]


-- @@ L21-25 verbatim
lemma integral_matrix_apply {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {m : Type u_m} {p : Type u_p} [Fintype m] [Fintype p] {f : α → Matrix m p ℂ}
    (hf : Integrable f μ) (i : m) (j : p) :
    (∫ s, f s ∂μ) i j = ∫ s, f s i j ∂μ := by
  erw [eval_integral (fun i => hf.eval i), eval_integral (fun j => (hf.eval i).eval j)]


-- @@ L27-27 verbatim
variable {J : Type u_J} [Fintype J] [DecidableEq J]


-- @@ L29-30 verbatim
def commonKernel (A : J → Matrix n n ℂ) (s : ℝ) : Matrix n (J × n) ℂ :=
  fun r v => purificationKernel (A v.1) s r v.2


-- @@ L32-33 verbatim
def commonGram (A : J → Matrix n n ℂ) : Matrix (J × n) (J × n) ℂ :=
  ∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s


-- @@ L35-38 verbatim
omit [DecidableEq J] in
lemma commonGram_integrable (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) :
    IntegrableOn (fun s : ℝ => (commonKernel A s)ᴴ * commonKernel A s) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;> exact kernel_entry_memLp (hA j.1) i j.2


-- @@ L40-42 verbatim
lemma commonGram_posSemidef (A : J → Matrix n n ℂ) : (commonGram A).PosSemidef := by
  apply integral_matrix_nonneg
  exact Filter.Eventually.of_forall fun s => posSemidef_conjTranspose_mul_self (commonKernel A s)


-- @@ L44-52 verbatim
omit [DecidableEq J] in
lemma commonGram_block (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (commonGram A).submatrix (fun i => (j, i)) (fun i => (k, i)) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  ext i l
  change (∫ s : ℝ in Ioi 0, (commonKernel A s)ᴴ * commonKernel A s) (j, i) (k, l) = _
  rw [integral_matrix_apply (commonGram_integrable A hA),
    integral_matrix_apply (kernel_cross_integrable (hA j) (hA k))]
  rfl


-- @@ L54-55 verbatim
def finitePurification (A : J → Matrix n n ℂ) (j : J) : Matrix (J × n) n ℂ :=
  (CFC.sqrt (commonGram A)).submatrix id (fun i => (j, i))


-- @@ L57-68 verbatim
lemma finitePurification_product (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j)ᴴ * finitePurification A k =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s := by
  have hh := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (commonGram A))).isHermitian.eq
  unfold finitePurification
  rw [Matrix.conjTranspose_submatrix]
  change (CFC.sqrt (commonGram A))ᴴ.submatrix (fun i => (j, i)) (Equiv.refl (J × n)) *
      (CFC.sqrt (commonGram A)).submatrix (Equiv.refl (J × n)) (fun i => (k, i)) = _
  rw [Matrix.submatrix_mul_equiv, hh,
    CFC.sqrt_mul_sqrt_self (commonGram A) (commonGram_posSemidef A).nonneg]
  exact commonGram_block A hA j k


-- @@ L70-73 verbatim
lemma finitePurification_self (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j : J) :
    (finitePurification A j)ᴴ * finitePurification A j = A j := by
  rw [finitePurification_product A hA, kernel_square_integral (hA j)]


-- @@ L75-96 verbatim
lemma finitePurification_distance (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j - finitePurification A k)ᴴ *
      (finitePurification A j - finitePurification A k) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) := by
  conv_lhs => rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  have hd (s : ℝ) :
      (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) =
      ((purificationKernel (A j) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s) -
      ((purificationKernel (A k) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A k) s)ᴴ * purificationKernel (A k) s) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp_rw [hd]
  erw [integral_sub ((kernel_cross_integrable (hA j) (hA j)).sub
      (kernel_cross_integrable (hA j) (hA k)))
      ((kernel_cross_integrable (hA k) (hA j)).sub (kernel_cross_integrable (hA k) (hA k))),
    integral_sub (kernel_cross_integrable (hA j) (hA j)) (kernel_cross_integrable (hA j) (hA k)),
    integral_sub (kernel_cross_integrable (hA k) (hA j)) (kernel_cross_integrable (hA k) (hA k))]
  simp only [finitePurification_product A hA]


-- @@ L98-108 verbatim
lemma finitePurification_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (e : R → J) (w : R → ℝ) (k : J)
    (hw0 : ∀ r, 0 ≤ w r) (hw : ∑ r, w r = 1)
    (hmean : ∑ r, w r • A (e r) = A k) :
    (∑ r, w r • ((finitePurification A (e r) - finitePurification A k)ᴴ *
      (finitePurification A (e r) - finitePurification A k))) ≤
      (∑ r, w r • effectEntropy (A (e r))) - effectEntropy (A k) := by
  simp_rw [finitePurification_distance A hA]
  exact weighted_distance_jensen (A ∘ e) w (A k) (fun r => hA (e r))
    (fun r => hA1 (e r)) (hA k) (hA1 k) hw0 hw hmean


-- @@ L110-116 verbatim
theorem finite_common_purification (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) :
    ∃ F : J → Matrix (J × n) n ℂ,
      (∀ j, (F j)ᴴ * F j = A j) ∧
      ∀ j k, (F j)ᴴ * F k =
        ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s :=
  ⟨finitePurification A, finitePurification_self A hA, finitePurification_product A hA⟩


-- @@ L118-118 verbatim
end ThresholdParallelRepetition.Resolvent


-- @@ L120-120 verbatim
end


-- @@ L122-122 verbatim
end OAI
