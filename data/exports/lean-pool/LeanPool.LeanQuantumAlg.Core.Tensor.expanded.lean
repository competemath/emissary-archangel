/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Core.Gate
public import LeanPool.LeanQuantumAlg.Util.FinPow


-- @@ L12-18 verbatim
/-!
# Tensor products of vectors, states, operators, and gates

Raw tensor products are defined at the `StateVector` and `HilbertOperator`
layers. `PureState.tensor` and `Gate.tensor` wrap these raw tensors with the
normalization/unitarity proofs needed to stay in their semantic types.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace QuantumAlg


-- @@ L24-24 verbatim
open Kronecker


-- @@ L26-26 verbatim
variable {m n : ℕ}


-- @@ L28-28 verbatim
namespace StateVector


-- @@ L30-30 verbatim
section


-- @@ L32-34 verbatim
/-- Tensor product of raw Hilbert-space vectors. -/
noncomputable def tensor (ψ : StateVector m) (φ : StateVector n) : StateVector (m + n) :=
  WithLp.toLp 2 fun i => ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2


-- @@ L36-40 verbatim
@[simp]
theorem tensor_apply (ψ : StateVector m) (φ : StateVector n)
    (i : Fin (2 ^ (m + n))) :
    tensor ψ φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl


-- @@ L42-45 verbatim
theorem tensor_apply_prod (ψ : StateVector m) (φ : StateVector n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    tensor ψ φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]


-- @@ L47-53 verbatim
@[simp]
theorem add_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    tensor (ψ + ψ') φ = tensor ψ φ + tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ + ψ') φ i = (tensor ψ φ + tensor ψ' φ) i
  simp [add_mul]


-- @@ L55-61 verbatim
@[simp]
theorem sub_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    tensor (ψ - ψ') φ = tensor ψ φ - tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ - ψ') φ i = (tensor ψ φ - tensor ψ' φ) i
  simp [sub_mul]


-- @@ L63-69 verbatim
@[simp]
theorem smul_tensor (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    tensor (c • ψ) φ = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (c • ψ) φ i = (c • tensor ψ φ) i
  simp [mul_assoc]


-- @@ L71-77 verbatim
@[simp]
theorem tensor_add (ψ : StateVector m) (φ φ' : StateVector n) :
    tensor ψ (φ + φ') = tensor ψ φ + tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ + φ') i = (tensor ψ φ + tensor ψ φ') i
  simp [mul_add]


-- @@ L79-85 verbatim
@[simp]
theorem tensor_sub (ψ : StateVector m) (φ φ' : StateVector n) :
    tensor ψ (φ - φ') = tensor ψ φ - tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ - φ') i = (tensor ψ φ - tensor ψ φ') i
  simp [mul_sub]


-- @@ L87-93 verbatim
@[simp]
theorem tensor_smul (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    tensor ψ (c • φ) = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (c • φ) i = (c • tensor ψ φ) i
  simp [mul_left_comm]


-- @@ L95-100 verbatim
@[simp]
theorem neg_tensor (ψ : StateVector m) (φ : StateVector n) :
    tensor (-ψ) φ = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  simp_all


-- @@ L102-107 verbatim
@[simp]
theorem tensor_neg (ψ : StateVector m) (φ : StateVector n) :
    tensor ψ (-φ) = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  simp_all


-- @@ L109-114 verbatim
@[simp]
theorem zero_tensor (φ : StateVector n) :
    tensor (0 : StateVector m) φ = 0 := by
  apply WithLp.ofLp_injective
  funext i
  simp_all


-- @@ L116-121 verbatim
@[simp]
theorem tensor_zero (ψ : StateVector m) :
    tensor ψ (0 : StateVector n) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  simp_all


-- @@ L123-134 verbatim
/-- The norm is multiplicative under tensor products. -/
theorem norm_tensor (ψ : StateVector m) (φ : StateVector n) :
    ‖tensor ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i, ‖ψ i‖ ^ 2 from
      Finset.sum_nonneg fun i _ => sq_nonneg ‖ψ i‖)]
  congr 1
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => ‖tensor ψ φ i‖ ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]


-- @@ L136-146 verbatim
/-- The inner product factors over tensor products. -/
theorem inner_tensor_tensor (ψ ψ' : StateVector m) (φ φ' : StateVector n) :
    inner ℂ (tensor ψ φ) (tensor ψ' φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => tensor ψ' φ' i * starRingEnd ℂ (tensor ψ φ i)),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, tensor_apply, Equiv.symm_apply_apply, map_mul,
    mul_mul_mul_comm]


-- @@ L148-148 verbatim
end


-- @@ L150-150 verbatim
end StateVector


-- @@ L152-152 verbatim
namespace PureState


-- @@ L154-154 verbatim
section


-- @@ L156-159 verbatim
/-- Tensor product of pure states. -/
noncomputable def tensor (ψ : PureState m) (φ : PureState n) : PureState (m + n) :=
  ofVec (StateVector.tensor (ψ : StateVector m) (φ : StateVector n)) (by
    rw [StateVector.norm_tensor, ψ.norm_eq_one, φ.norm_eq_one, one_mul])


-- @@ L161-167 verbatim
@[simp]
theorem tensor_apply (ψ : PureState m) (φ : PureState n)
    (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 := by
  change StateVector.tensor (ψ : StateVector m) (φ : StateVector n) i
      = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2
  rfl


-- @@ L169-174 verbatim
theorem tensor_apply_prod (ψ : PureState m) (φ : PureState n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

-- Compatibility names for linear raw-vector tensor proofs.

-- @@ L175-177 verbatim
theorem add_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    StateVector.tensor (ψ + ψ') φ = StateVector.tensor ψ φ + StateVector.tensor ψ' φ :=
  StateVector.add_tensor ψ ψ' φ


-- @@ L179-181 verbatim
theorem sub_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    StateVector.tensor (ψ - ψ') φ = StateVector.tensor ψ φ - StateVector.tensor ψ' φ :=
  StateVector.sub_tensor ψ ψ' φ


-- @@ L183-185 verbatim
theorem smul_tensor (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor (c • ψ) φ = c • StateVector.tensor ψ φ :=
  StateVector.smul_tensor c ψ φ


-- @@ L187-189 verbatim
theorem tensor_add (ψ : StateVector m) (φ φ' : StateVector n) :
    StateVector.tensor ψ (φ + φ') = StateVector.tensor ψ φ + StateVector.tensor ψ φ' :=
  StateVector.tensor_add ψ φ φ'


-- @@ L191-193 verbatim
theorem tensor_sub (ψ : StateVector m) (φ φ' : StateVector n) :
    StateVector.tensor ψ (φ - φ') = StateVector.tensor ψ φ - StateVector.tensor ψ φ' :=
  StateVector.tensor_sub ψ φ φ'


-- @@ L195-197 verbatim
theorem tensor_smul (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor ψ (c • φ) = c • StateVector.tensor ψ φ :=
  StateVector.tensor_smul c ψ φ


-- @@ L199-201 verbatim
theorem neg_tensor (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor (-ψ) φ = -StateVector.tensor ψ φ :=
  StateVector.neg_tensor ψ φ


-- @@ L203-205 verbatim
theorem tensor_neg (ψ : StateVector m) (φ : StateVector n) :
    StateVector.tensor ψ (-φ) = -StateVector.tensor ψ φ :=
  StateVector.tensor_neg ψ φ


-- @@ L207-209 verbatim
theorem zero_tensor (φ : StateVector n) :
    StateVector.tensor (0 : StateVector m) φ = 0 :=
  StateVector.zero_tensor φ


-- @@ L211-213 verbatim
theorem tensor_zero (ψ : StateVector m) :
    StateVector.tensor ψ (0 : StateVector n) = 0 :=
  StateVector.tensor_zero ψ


-- @@ L215-230 verbatim
/-- Basis kets tensor to basis kets: `|x⟩ ⊗ |y⟩ = |xy⟩`. -/
theorem tensor_ket (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    (ket x).tensor (ket y) = ket (prodEquiv (x, y)) := by
  ext i
  rw [tensor_apply, ket_apply, ket_apply, ket_apply]
  by_cases h : i = prodEquiv (x, y)
  · simp_all
  · have h' : ¬((prodEquiv.symm i).1 = x ∧ (prodEquiv.symm i).2 = y) := by
      rintro ⟨h1, h2⟩
      exact h (by
        rw [← Equiv.apply_symm_apply (prodEquiv (m := m) (n := n)) i]
        exact congrArg prodEquiv (Prod.ext h1 h2))
    rw [ite_eq_right h]
    rcases not_and_or.mp h' with h1 | h2
    · rw [ite_eq_right h1, zero_mul]
    · rw [ite_eq_right h2, mul_zero]


-- @@ L232-236 verbatim
theorem norm_tensor (ψ : PureState m) (φ : PureState n) :
    ‖ψ.tensor φ‖ = ‖ψ‖ * ‖φ‖ := by
  change ‖StateVector.tensor (ψ : StateVector m) (φ : StateVector n)‖
      = ‖(ψ : StateVector m)‖ * ‖(φ : StateVector n)‖
  rw [StateVector.norm_tensor]


-- @@ L238-246 verbatim
theorem inner_tensor_tensor (ψ ψ' : PureState m) (φ φ' : PureState n) :
    inner ℂ (ψ.tensor φ) (ψ'.tensor φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  change inner ℂ
      (StateVector.tensor (ψ : StateVector m) (φ : StateVector n))
      (StateVector.tensor (ψ' : StateVector m) (φ' : StateVector n))
    = inner ℂ (ψ : StateVector m) (ψ' : StateVector m)
      * inner ℂ (φ : StateVector n) (φ' : StateVector n)
  rw [StateVector.inner_tensor_tensor]


-- @@ L248-248 verbatim
end


-- @@ L250-250 verbatim
end PureState


-- @@ L252-252 verbatim
namespace HilbertOperator


-- @@ L254-254 verbatim
section


-- @@ L256-259 verbatim
/-- Tensor product of Hilbert-space operators. -/
noncomputable def tensor
    (G : HilbertOperator m) (K : HilbertOperator n) : HilbertOperator (m + n) :=
  Matrix.reindex prodEquiv prodEquiv (G ⊗ₖ K)


-- @@ L261-266 verbatim
@[simp]
theorem tensor_apply (G : HilbertOperator m) (K : HilbertOperator n)
    (i j : Fin (2 ^ (m + n))) :
    tensor G K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl


-- @@ L268-272 verbatim
@[simp]
theorem zero_tensor (K : HilbertOperator n) :
    tensor (0 : HilbertOperator m) K = 0 := by
  ext i j
  simp [tensor_apply]


-- @@ L274-278 verbatim
@[simp]
theorem tensor_zero (G : HilbertOperator m) :
    tensor G (0 : HilbertOperator n) = 0 := by
  ext i j
  simp [tensor_apply]


-- @@ L280-283 verbatim
theorem add_tensor (G G' : HilbertOperator m) (K : HilbertOperator n) :
    tensor (G + G') K = tensor G K + tensor G' K := by
  ext i j
  simp [tensor_apply, add_mul]


-- @@ L285-288 verbatim
theorem tensor_add (G : HilbertOperator m) (K K' : HilbertOperator n) :
    tensor G (K + K') = tensor G K + tensor G K' := by
  ext i j
  simp [tensor_apply, mul_add]


-- @@ L290-294 verbatim
theorem tensor_mul_tensor (G G' : HilbertOperator m) (K K' : HilbertOperator n) :
    tensor G K * tensor G' K' = tensor (G * G') (K * K') := by
  rw [tensor, tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]


-- @@ L296-299 verbatim
theorem conjTranspose_tensor (G : HilbertOperator m) (K : HilbertOperator n) :
    (tensor G K).conjTranspose = tensor G.conjTranspose K.conjTranspose := by
  rw [tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]


-- @@ L301-304 verbatim
@[simp]
theorem one_tensor_one : tensor (1 : HilbertOperator m) (1 : HilbertOperator n) = 1 := by
  rw [tensor, Matrix.one_kronecker_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]


-- @@ L306-314 verbatim
theorem tensor_mem_unitaryGroup {G : HilbertOperator m} {K : HilbertOperator n}
    (hG : G ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    tensor G K ∈ Matrix.unitaryGroup (Fin (2 ^ (m + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hG hK ⊢
  rw [tensor, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, hG, hK, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]


-- @@ L316-331 verbatim
theorem tensor_applyVec_tensor (G : HilbertOperator m) (K : HilbertOperator n)
    (ψ : StateVector m) (φ : StateVector n) :
    applyVec (tensor G K) (StateVector.tensor ψ φ)
      = StateVector.tensor (applyVec G ψ) (applyVec K φ) := by
  apply WithLp.ofLp_injective
  funext i
  change applyVec (tensor G K) (StateVector.tensor ψ φ) i
      = StateVector.tensor (applyVec G ψ) (applyVec K φ) i
  rw [StateVector.tensor_apply, applyVec_apply, applyVec_apply, applyVec_apply,
    Finset.sum_mul_sum,
    ← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun j => tensor G K i j * StateVector.tensor ψ φ j),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, StateVector.tensor_apply, Equiv.symm_apply_apply,
    mul_mul_mul_comm]


-- @@ L333-333 verbatim
end


-- @@ L335-335 verbatim
end HilbertOperator


-- @@ L337-337 verbatim
namespace Gate


-- @@ L339-339 verbatim
noncomputable section


-- @@ L341-344 verbatim
/-- Tensor product of unitary gates. -/
def tensor (G : Gate m) (K : Gate n) : Gate (m + n) :=
  ofUnitary (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n))
    (HilbertOperator.tensor_mem_unitaryGroup G.unitary K.unitary)


-- @@ L346-351 verbatim
@[simp]
theorem tensor_apply (G : Gate m) (K : Gate n)
    (i j : Fin (2 ^ (m + n))) :
    G.tensor K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl


-- @@ L353-360 verbatim
theorem tensor_mul_tensor (G G' : Gate m) (K K' : Gate n) :
    G.tensor K * G'.tensor K' = tensor (G * G') (K * K') := by
  ext i j
  change (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n)
        * HilbertOperator.tensor (G' : HilbertOperator m) (K' : HilbertOperator n)) i j
      = HilbertOperator.tensor ((G : HilbertOperator m) * (G' : HilbertOperator m))
          ((K : HilbertOperator n) * (K' : HilbertOperator n)) i j
  rw [HilbertOperator.tensor_mul_tensor]


-- @@ L362-365 verbatim
theorem conjTranspose_tensor (G : Gate m) (K : Gate n) :
    (G.tensor K).conjTranspose = tensor G.conjTranspose K.conjTranspose := by
  ext i j
  simp_all


-- @@ L367-372 verbatim
@[simp]
theorem one_tensor_one : (1 : Gate m).tensor (1 : Gate n) = 1 := by
  ext i j
  change HilbertOperator.tensor (1 : HilbertOperator m) (1 : HilbertOperator n) i j
      = (1 : HilbertOperator (m + n)) i j
  rw [HilbertOperator.one_tensor_one]


-- @@ L374-379 verbatim
theorem tensor_mem_unitaryGroup {G : Gate m} {K : Gate n}
    (_hG : (G : HilbertOperator m) ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (_hK : (K : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    (G.tensor K : HilbertOperator (m + n))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (m + n))) ℂ :=
  (G.tensor K).unitary


-- @@ L381-391 verbatim
theorem tensor_apply_tensor (G : Gate m) (K : Gate n)
    (ψ : PureState m) (φ : PureState n) :
    (G.tensor K).apply (ψ.tensor φ) = (G.apply ψ).tensor (K.apply φ) := by
  ext i
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n))
      (StateVector.tensor (ψ : StateVector m) (φ : StateVector n)) i
    = StateVector.tensor
      (HilbertOperator.applyVec (G : HilbertOperator m) (ψ : StateVector m))
      (HilbertOperator.applyVec (K : HilbertOperator n) (φ : StateVector n)) i
  rw [HilbertOperator.tensor_applyVec_tensor]


-- @@ L393-398 verbatim
theorem tensor_applyVec_tensor (G : Gate m) (K : Gate n)
    (ψ : StateVector m) (φ : StateVector n) :
    (G.tensor K).applyVec (StateVector.tensor ψ φ)
      = StateVector.tensor (G.applyVec ψ) (K.applyVec φ) := by
  exact HilbertOperator.tensor_applyVec_tensor (G : HilbertOperator m)
    (K : HilbertOperator n) ψ φ


-- @@ L400-400 verbatim
end


-- @@ L402-402 verbatim
end Gate


-- @@ L404-404 verbatim
end QuantumAlg
