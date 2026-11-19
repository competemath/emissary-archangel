/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Grunbaum.Maximizer
import ProjectionConstants.ChalmersLewicki.Absolute


-- @@ L9-30 verbatim
/-!
# The formula of Chalmers and Lewicki for `n = 2`

Let `Π₂ = λ_ℝ(2)` be the maximal absolute projection constant of two-dimensional real normed
spaces and `Π(2, d) = λ_ℝ(2, d)` the maximal relative projection constant of two-dimensional
subspaces of `ℓ∞^d` (`ProjectionConstants.maxProjConst` and
`ProjectionConstants.maxRelProjConst`). The formula of Chalmers and Lewicki, in the form of
[JFA, Theorem 2.1], states

`Π(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }`   and   `Π₂ = sup_d Π(2, d)`.

We deduce it from the version `λ_ℝ(m, N) = max ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` of *Projection constants in
Lean* (`ProjectionConstants.maxRelProjConst_eq_clConst`): an orthonormal pair `u, v` gives the
orthogonal projection `P = uuᵀ + vvᵀ` with `uᵀAu + vᵀAv = ∑ᵢⱼ Aᵢⱼ Pᵢⱼ`, and for fixed `P` and
`tᵢ = √dᵢ` the best sign matrix is the sign pattern of `P`.

## Main results

* `Grunbaum.clConst_two_eq_supConfigs` : `sup ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| = Π(2, ι)`;
* `Grunbaum.maxRelProjConst_two_eq_supConfigs` : `Π(2, d) = λ_ℝ(2, d)`;
* `Grunbaum.maxProjConst_two_eq_iSup` : `Π₂ = λ_ℝ(2) = sup_d Π(2, d)`.
-/


-- @@ L32-32 verbatim
open Finset Matrix ProjectionConstants


-- @@ L34-34 verbatim
namespace Grunbaum


-- @@ L36-36 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L38-40 verbatim
/-- The matrix `uuᵀ + vvᵀ`; for an orthonormal pair it is the orthogonal projection onto the
plane spanned by `u` and `v`. -/
def projPair (u v : ι → ℝ) : Matrix ι ι ℝ := of fun i j => u i * u j + v i * v j


-- @@ L42-43 verbatim
omit [Fintype ι] in
lemma projPair_apply (u v : ι → ℝ) (i j : ι) : projPair u v i j = u i * u j + v i * v j := rfl


-- @@ L45-46 verbatim
/-- The `2 × ι` matrix with rows `u` and `v`. -/
def rowsPair (u v : ι → ℝ) : Matrix (Fin 2) ι ℝ := of ![u, v]


-- @@ L48-56 verbatim
lemma rowsPair_mul_conjTranspose {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    rowsPair u v * (rowsPair u v)ᴴ = 1 := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [rowsPair, mul_apply, dotProduct] using h.norm_left
  · simpa [rowsPair, mul_apply, dotProduct] using h.orth
  · simpa [rowsPair, mul_apply, dotProduct, dotProduct_comm] using
      (dotProduct_comm u v ▸ h.orth : v ⬝ᵥ u = 0)
  · simpa [rowsPair, mul_apply, dotProduct] using h.norm_right


-- @@ L58-62 verbatim
omit [Fintype ι] in
lemma conjTranspose_rowsPair_mul (u v : ι → ℝ) :
    (rowsPair u v)ᴴ * rowsPair u v = projPair u v := by
  ext i j
  simp [rowsPair, projPair, mul_apply, Fin.sum_univ_two]


-- @@ L64-68 verbatim
/-- For an orthonormal pair, `uuᵀ + vvᵀ ∈ 𝒫₂`. -/
lemma projPair_mem_orthProjs {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    projPair u v ∈ orthProjs ℝ ι 2 := by
  rw [← conjTranspose_rowsPair_mul]
  exact conjTranspose_mul_self_mem_orthProjs (rowsPair_mul_conjTranspose h)


-- @@ L70-80 verbatim
/-- Every `P ∈ 𝒫₂` is `uuᵀ + vvᵀ` for an orthonormal pair `u, v`. -/
lemma exists_projPair_eq {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι 2) :
    ∃ u v, IsOrthonormalPair u v ∧ projPair u v = P := by
  classical
  obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
  refine ⟨U 0, U 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [mul_apply, dotProduct] using congrFun (congrFun hU 0) 0
  · simpa [mul_apply, dotProduct] using congrFun (congrFun hU 1) 1
  · simpa [mul_apply, dotProduct] using congrFun (congrFun hU 0) 1
  · ext i j
    simp [projPair, mul_apply, Fin.sum_univ_two]


-- @@ L82-85 verbatim
/-- `uᵀAu + vᵀAv = ∑ᵢⱼ Aᵢⱼ Pᵢⱼ` for `P = uuᵀ + vvᵀ`. -/
lemma fanValue_eq_sum_projPair (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    fanValue A u v = ∑ i, ∑ j, A i j * projPair u v i j :=
  fanValue_eq_sum A u v


-- @@ L87-88 verbatim
lemma isUnitWeight_sqrt {w : ι → ℝ} (hw : IsWeight w) : IsUnitWeight fun i => √(w i) :=
  ⟨fun _ => Real.sqrt_nonneg _, by simp [Real.sq_sqrt (hw.nonneg _), hw.sum_eq]⟩


-- @@ L90-106 verbatim
/-- `π₂(√D S √D) ≤ sup ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`. -/
theorem sumTopTwo_weightedMatrix_le_clConst {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : π₂ (weightedMatrix S w) ≤ clConst ℝ ι 2 := by
  refine sumTopTwo_le' clConst_nonneg fun u v huv => ?_
  refine le_trans ?_ (le_clConst (isUnitWeight_sqrt hw) (projPair_mem_orthProjs huv))
  rw [fanValue_eq_sum_projPair]
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  have h1 : S i j * projPair u v i j ≤ |projPair u v i j| := by
    rcases hS.sign i j with h | h
    · rw [h, one_mul]; exact le_abs_self _
    · rw [h, neg_one_mul]; exact neg_le_abs _
  have h2 : 0 ≤ √(w i) * √(w j) := by positivity
  calc weightedMatrix S w i j * projPair u v i j
      = (√(w i) * √(w j)) * (S i j * projPair u v i j) := by
        simp only [weightedMatrix, of_apply]; ring
    _ ≤ (√(w i) * √(w j)) * |projPair u v i j| := mul_le_mul_of_nonneg_left h1 h2
    _ = √(w i) * √(w j) * ‖projPair u v i j‖ := by rw [Real.norm_eq_abs]


-- @@ L108-110 verbatim
/-- The sign pattern `Sgn(P)` of a real matrix, with the convention `sgn 0 = 1`. -/
noncomputable def signPattern (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  of fun i j => if 0 ≤ P i j then 1 else -1


-- @@ L112-122 verbatim
omit [Fintype ι] in
lemma isSignMatrix_signPattern {u v : ι → ℝ} : IsSignMatrix (signPattern (projPair u v)) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · have h : projPair u v j i = projPair u v i j := by simp only [projPair_apply]; ring
    simp only [signPattern, of_apply, h]
  · simp only [signPattern, of_apply]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [signPattern, projPair, of_apply]
    exact ite_eq_left (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))


-- @@ L124-129 verbatim
omit [Fintype ι] in
lemma signPattern_mul_self (P : Matrix ι ι ℝ) (i j : ι) : signPattern P i j * P i j = |P i j| := by
  simp only [signPattern, of_apply]
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.mp h)]


-- @@ L131-147 verbatim
/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ Π(2, ι)` for every unit weight `t` and every `P ∈ 𝒫₂`. -/
theorem weightedAbsSum_le_supConfigs {t : ι → ℝ} (ht : IsUnitWeight t)
    {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι 2) : weightedAbsSum t P ≤ supConfigs ι := by
  obtain ⟨u, v, huv, rfl⟩ := exists_projPair_eq hP
  set w : ι → ℝ := fun i => t i ^ 2 with hw_def
  have hw : IsWeight w := ⟨fun i => sq_nonneg _, ht.sum_sq⟩
  have e : weightedAbsSum t (projPair u v) =
      fanValue (weightedMatrix (signPattern (projPair u v)) w) u v := by
    rw [fanValue_eq_sum_projPair]
    unfold weightedAbsSum
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [weightedMatrix, of_apply, hw_def, Real.sqrt_sq (ht.nonneg _), Real.norm_eq_abs,
      ← signPattern_mul_self]
    ring
  rw [e]
  exact (fanValue_le_sumTopTwo _ huv).trans
    (sumTopTwo_le_supConfigs isSignMatrix_signPattern hw)


-- @@ L149-152 verbatim
/-- `sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖ = 1, P ∈ 𝒫₂ } = Π(2, ι)`. -/
theorem clConst_two_eq_supConfigs : clConst ℝ ι 2 = supConfigs ι :=
  le_antisymm (clConst_le supConfigs_nonneg fun _ _ ht hP => weightedAbsSum_le_supConfigs ht hP)
    (supConfigs_le clConst_nonneg fun _ _ hS hw => sumTopTwo_weightedMatrix_le_clConst hS hw)


-- @@ L154-158 verbatim
/-- **The formula of Chalmers and Lewicki** ([JFA, Theorem 2.1] for `n = 2`):
`Π(2, d) = λ_ℝ(2, d) = max { π₂(√D S √D) : S ∈ 𝒜_d, D ∈ 𝒟_d }`. -/
theorem maxRelProjConst_two_eq_supConfigs (d : ℕ) :
    maxRelProjConst ℝ 2 d = supConfigs (Fin d) := by
  rw [maxRelProjConst_eq_clConst, clConst_two_eq_supConfigs]


-- @@ L160-163 verbatim
/-- `Π₂ = λ_ℝ(2) = sup_d Π(2, d)`. -/
theorem maxProjConst_two_eq_iSup : maxProjConst ℝ 2 = ⨆ d : ℕ, supConfigs (Fin d) := by
  rw [maxProjConst_eq_iSup_maxRelProjConst]
  simp_rw [maxRelProjConst_two_eq_supConfigs]


-- @@ L165-168 verbatim
lemma bddAbove_range_supConfigs : BddAbove (Set.range fun d : ℕ => supConfigs (Fin d)) :=
  ⟨2, by
    rintro _ ⟨d, rfl⟩
    exact supConfigs_le (by norm_num) fun _ _ hS hw => sumTopTwo_weightedMatrix_le_two hS hw⟩


-- @@ L170-173 verbatim
lemma supConfigs_le_maxProjConst_two (ι : Type*) [Fintype ι] :
    supConfigs ι ≤ maxProjConst ℝ 2 := by
  rw [maxProjConst_two_eq_iSup, ← supConfigs_congr (Fintype.equivFin ι).symm]
  exact le_ciSup bddAbove_range_supConfigs _


-- @@ L175-178 verbatim
lemma maxProjConst_two_le {c : ℝ} (h : ∀ d : ℕ, supConfigs (Fin d) ≤ c) :
    maxProjConst ℝ 2 ≤ c := by
  rw [maxProjConst_two_eq_iSup]
  exact ciSup_le h


-- @@ L180-180 verbatim
end Grunbaum
