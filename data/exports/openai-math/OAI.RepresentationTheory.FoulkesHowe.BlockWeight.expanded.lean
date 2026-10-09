import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators


-- @@ L8-8 verbatim
namespace Problem346

-- @@ L9-9 verbatim
namespace PolynomialWeights


-- @@ L11-11 verbatim
open MvPolynomial


-- @@ L13-13 verbatim
variable {R σ : Type*} [CommSemiring R] [Fintype σ]


-- @@ L15-18 verbatim
/-- The Euler derivation associated with natural-number weights. -/
def weightedEuler (w : σ → ℕ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  ∑ i : σ, (w i) • ((X i : MvPolynomial σ R) • pderiv i)


-- @@ L20-26 verbatim
@[simp] theorem weightedEuler_apply (w : σ → ℕ) (f : MvPolynomial σ R) :
    weightedEuler w f = ∑ i : σ, w i • (X i * pderiv i f) := by
  classical
  unfold weightedEuler
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, Derivation.smul_apply, ih, smul_eq_mul]


-- @@ L28-31 verbatim
@[simp] theorem weightedEuler_X (w : σ → ℕ) (i : σ) :
    weightedEuler (R := R) w (X i) = w i • X i := by
  classical
  simp [weightedEuler_apply, Pi.single_apply]


-- @@ L33-38 verbatim
/-- Euler's identity, expressed using a bundled derivation. -/
theorem weightedEuler_of_homogeneous (w : σ → ℕ) {n : ℕ}
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w n) :
    weightedEuler w f = n • f := by
  rw [weightedEuler_apply]
  exact hf.sum_weight_X_mul_pderiv


-- @@ L40-46 verbatim
/-- Any derivation with the prescribed diagonal action on generators is Euler. -/
theorem derivation_eq_weightedEuler (w : σ → ℕ)
    (N : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hN : ∀ i, N (X i) = w i • X i) : N = weightedEuler w := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [hN, weightedEuler_X]


-- @@ L48-55 verbatim
/-- A homogeneous polynomial is an eigenvector for its weighted Euler derivation. -/
theorem derivation_homogeneous_eigenvalue (w : σ → ℕ)
    (N : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hN : ∀ i, N (X i) = w i • X i)
    {n : ℕ} {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w n) :
    N f = n • f := by
  rw [derivation_eq_weightedEuler w N hN]
  exact weightedEuler_of_homogeneous w hf


-- @@ L57-57 verbatim
section Blocks


-- @@ L59-59 verbatim
variable {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq β]


-- @@ L61-62 verbatim
/-- Weight one on one coordinate block, and zero on all spectator blocks. -/
def blockWeight (u : β) (ki : β × ι) : ℕ := if ki.1 = u then 1 else 0


-- @@ L64-66 verbatim
/-- A polynomial is homogeneous of the specified degree in one block. -/
def IsBlockHomogeneous (u : β) (f : MvPolynomial (β × ι) R) (n : ℕ) : Prop :=
  f.IsWeightedHomogeneous (blockWeight u) n


-- @@ L68-70 verbatim
omit [Fintype β] [Fintype ι] in
@[simp] theorem blockWeight_apply (u k : β) (i : ι) :
    blockWeight u (k, i) = if k = u then 1 else 0 := rfl


-- @@ L72-80 verbatim
theorem block_euler_eigenvalue (u : β)
    (N : Derivation R (MvPolynomial (β × ι) R) (MvPolynomial (β × ι) R))
    (hN : ∀ k i, N (X (k, i)) = if k = u then X (k, i) else 0)
    {n : ℕ} {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) :
    N f = n • f := by
  apply derivation_homogeneous_eigenvalue (blockWeight u) N _ hf
  rintro ⟨k, i⟩
  simp only [hN, blockWeight_apply]
  split_ifs <;> simp


-- @@ L82-94 verbatim
/-- The difference of block counting operators has the difference of the block degrees
as eigenvalue. This is the weight used by the positive-weight shift lemma. -/
theorem block_difference_eigenvalue (u v : β)
    (Nu Nv : Derivation ℂ (MvPolynomial (β × ι) ℂ) (MvPolynomial (β × ι) ℂ))
    (hu : ∀ k i, Nu (X (k, i)) = if k = u then X (k, i) else 0)
    (hv : ∀ k i, Nv (X (k, i)) = if k = v then X (k, i) else 0)
    {p q : ℕ} {f : MvPolynomial (β × ι) ℂ}
    (hp : IsBlockHomogeneous u f p) (hq : IsBlockHomogeneous v f q) :
    (Nu - Nv) f = ((p : ℂ) - (q : ℂ)) • f := by
  change Nu f - Nv f = _
  rw [block_euler_eigenvalue u Nu hu hp, block_euler_eigenvalue v Nv hv hq]
  rw [sub_smul]
  simp only [Nat.cast_smul_eq_nsmul]


-- @@ L96-104 verbatim
theorem block_difference_nat_eigenvalue (u v : β)
    (Nu Nv : Derivation ℂ (MvPolynomial (β × ι) ℂ) (MvPolynomial (β × ι) ℂ))
    (hu : ∀ k i, Nu (X (k, i)) = if k = u then X (k, i) else 0)
    (hv : ∀ k i, Nv (X (k, i)) = if k = v then X (k, i) else 0)
    {p q : ℕ} (hpq : q ≤ p) {f : MvPolynomial (β × ι) ℂ}
    (hp : IsBlockHomogeneous u f p) (hq : IsBlockHomogeneous v f q) :
    (Nu - Nv) f = ((p - q : ℕ) : ℂ) • f := by
  rw [Nat.cast_sub hpq]
  exact block_difference_eigenvalue u v Nu Nv hu hv hp hq


-- @@ L106-113 verbatim
omit [Fintype β] [Fintype ι] in
/-- Differentiating in a block lowers its degree by one, provided that degree is positive. -/
theorem block_pderiv_source {u : β} {n : ℕ} {f : MvPolynomial (β × ι) R}
    (hf : IsBlockHomogeneous u f n) (hn : 0 < n) (i : ι) :
    IsBlockHomogeneous u (pderiv (u, i) f) (n - 1) := by
  apply IsWeightedHomogeneous.pderiv hf
  simp only [blockWeight_apply]
  exact Nat.sub_add_cancel hn


-- @@ L115-121 verbatim
omit [Fintype β] [Fintype ι] in
/-- Differentiating in another block leaves the indicated block degree unchanged. -/
theorem block_pderiv_other {u k : β} (hku : k ≠ u) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) (i : ι) :
    IsBlockHomogeneous u (pderiv (k, i) f) n := by
  apply IsWeightedHomogeneous.pderiv hf
  simp [blockWeight_apply, hku]


-- @@ L123-134 verbatim
omit [Fintype β] in
/-- A directional shift lowers its source block degree by one. -/
theorem block_shift_degree_source {u v : β} (huv : u ≠ v) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) (hn : 0 < n) :
    IsBlockHomogeneous u (∑ i : ι, X (v, i) * pderiv (u, i) f) (n - 1) := by
  apply (weightedHomogeneousSubmodule R (blockWeight u) (n - 1)).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight u) 0 := by
    simpa [blockWeight_apply, Ne.symm huv] using
      (isWeightedHomogeneous_X (R := R) (blockWeight u) (v, i))
  simpa using hx.mul (block_pderiv_source hf hn i)


-- @@ L136-147 verbatim
omit [Fintype β] in
/-- A directional shift raises its destination block degree by one. -/
theorem block_shift_degree_destination {u v : β} (huv : u ≠ v) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous v f n) :
    IsBlockHomogeneous v (∑ i : ι, X (v, i) * pderiv (u, i) f) (n + 1) := by
  apply (weightedHomogeneousSubmodule R (blockWeight v) (n + 1)).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight v) 1 := by
    simpa [blockWeight_apply] using
      (isWeightedHomogeneous_X (R := R) (blockWeight v) (v, i))
  simpa [Nat.add_comm] using hx.mul (block_pderiv_other huv hf i)


-- @@ L149-160 verbatim
omit [Fintype β] in
/-- A directional shift leaves every spectator block degree unchanged. -/
theorem block_shift_degree_spectator {u v k : β} (huk : u ≠ k) (hvk : v ≠ k)
    {n : ℕ} {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous k f n) :
    IsBlockHomogeneous k (∑ i : ι, X (v, i) * pderiv (u, i) f) n := by
  apply (weightedHomogeneousSubmodule R (blockWeight k) n).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight k) 0 := by
    simpa [blockWeight_apply, hvk] using
      (isWeightedHomogeneous_X (R := R) (blockWeight k) (v, i))
  simpa using hx.mul (block_pderiv_other huk hf i)


-- @@ L162-162 verbatim
end Blocks


-- @@ L164-164 verbatim
end PolynomialWeights

-- @@ L165-165 verbatim
end Problem346


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end OAI
