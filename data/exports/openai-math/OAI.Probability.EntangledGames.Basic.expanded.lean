import OAI.Probability.EntangledGames.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators ComplexOrder


-- @@ L8-8 verbatim
namespace ThresholdParallelRepetition


-- @@ L10-10 verbatim
open scoped Kronecker

-- @@ L11-11 verbatim
open Matrix


-- @@ L13-13 verbatim
namespace Strategy

-- @@ L14-14 verbatim
variable {X Y A B : Type} [Fintype A] [Fintype B]


-- @@ L16-20 verbatim
lemma born_eq_quadratic (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b =
      (star S.state ⬝ᵥ ((S.alice x a ⊗ₖ S.bob y b) *ᵥ S.state)).re := by
  simp only [born, dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Pi.star_apply,
    Finset.mul_sum, ← mul_assoc, Complex.re_sum]


-- @@ L22-26 verbatim
lemma born_nonneg (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b := by
  rw [born_eq_quadratic]
  exact (Complex.nonneg_iff.mp
    (((S.alice_pos x a).kronecker (S.bob_pos y b)).dotProduct_mulVec_nonneg S.state)).1


-- @@ L28-37 verbatim
lemma total_effect (S : Strategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.alice x a ⊗ₖ S.bob y b = 1 := by
  classical
  calc
    _ = (∑ a, S.alice x a) ⊗ₖ (∑ b, S.bob y b) := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = 1 := by rw [S.alice_total, S.bob_total, Matrix.one_kronecker_one]


-- @@ L39-48 verbatim
lemma born_sum (S : Strategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.born x y a b = 1 := by
  simp_rw [born_eq_quadratic]
  simp_rw [← Complex.re_sum, ← dotProduct_sum, ← Matrix.sum_mulVec]
  rw [total_effect, Matrix.one_mulVec]
  rw [dotProduct, Complex.re_sum]
  convert S.state_unit using 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.normSq, Complex.mul_re]


-- @@ L50-56 verbatim
lemma born_le_one (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b ≤ 1 := by
  classical
  rw [← born_sum S x y]
  exact (Finset.single_le_sum (fun b' _ => born_nonneg S x y a b') (Finset.mem_univ b)).trans
    (Finset.single_le_sum (fun a' _ => Finset.sum_nonneg
      (fun b' _ => born_nonneg S x y a' b')) (Finset.mem_univ a))


-- @@ L58-58 verbatim
end Strategy


-- @@ L60-60 verbatim
namespace Strategy


-- @@ L62-81 verbatim
def deterministic {X Y A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a₀ : A) (b₀ : B) : Strategy X Y A B where
  dimA := 0
  dimB := 0
  state := fun _ => 1
  state_unit := by simp
  alice := fun _ a => if a = a₀ then 1 else 0
  bob := fun _ b => if b = b₀ then 1 else 0
  alice_pos := by
    intro _ a
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  bob_pos := by
    intro _ b
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  alice_total := by intro _; simp
  bob_total := by intro _; simp


-- @@ L83-83 verbatim
end Strategy


-- @@ L85-94 verbatim
lemma successProbability_nonneg {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : 0 ≤ successProbability G S := by
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (G.questionProb_nonneg z)
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact S.born_nonneg _ _ _ _
  · exact le_rfl


-- @@ L96-111 verbatim
lemma successProbability_le_one {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ 1 := by
  calc
    successProbability G S ≤ ∑ z, G.questionProb z *
        ∑ w : Fin (a + 1) × Fin (b + 1), S.born z.1 z.2 w.1 w.2 := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (G.questionProb_nonneg z)
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact le_rfl
      · exact S.born_nonneg _ _ _ _
    _ = 1 := by
      simp_rw [Fintype.sum_prod_type, S.born_sum, mul_one]
      simpa only [Fintype.sum_prod_type] using G.questionProb_sum


-- @@ L113-119 verbatim
lemma entangledValue_nonneg {x y a b : ℕ} (G : Game x y a b) :
    0 ≤ entangledValue G := by
  let S : SingleStrategy x y a b := Strategy.deterministic 0 0
  exact (successProbability_nonneg G S).trans (le_csSup
    (show BddAbove (Set.range (successProbability G)) from
      ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩)
    (Set.mem_range_self S))


-- @@ L121-124 verbatim
lemma successProbability_le_value {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ entangledValue G := by
  exact le_csSup ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩
    (Set.mem_range_self S)


-- @@ L126-132 verbatim
lemma entangledValue_le_one {x y a b : ℕ} (G : Game x y a b) :
    entangledValue G ≤ 1 := by
  apply csSup_le
  · exact ⟨_, Set.mem_range_self (Strategy.deterministic (X := Fin (x + 1))
      (Y := Fin (y + 1)) (0 : Fin (a + 1)) (0 : Fin (b + 1)))⟩
  · rintro _ ⟨S, rfl⟩
    exact successProbability_le_one G S


-- @@ L134-134 verbatim
end ThresholdParallelRepetition


-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
end OAI
