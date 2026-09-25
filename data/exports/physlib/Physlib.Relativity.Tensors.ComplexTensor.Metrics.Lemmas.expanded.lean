/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Units.Basic

-- @@ L10-14 verbatim
/-!

## Basic lemmas regarding metrics

-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Matrix

-- @@ L19-19 verbatim
open MatrixGroups

-- @@ L20-20 verbatim
open Complex

-- @@ L21-21 verbatim
open TensorProduct

-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace complexLorentzTensor

-- @@ L25-25 verbatim
open TensorSpecies

-- @@ L26-26 verbatim
open Tensor

-- @@ L27-31 verbatim
/-!

## Symmetry properties

-/


-- @@ L33-41 verbatim
/-- The covariant metric is symmetric `{η' | μ ν = η' | ν μ}ᵀ`. -/
lemma coMetric_symm : {η' | μ ν = η' | ν μ}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply]
  rw [coMetric_eq_ofRat, ofRat_basis_repr_apply, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide


-- @@ L43-51 verbatim
/-- The contravariant metric is symmetric `{η | μ ν = η | ν μ}ᵀ`. -/
lemma contrMetric_symm : {η | μ ν = η | ν μ}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply]
  rw [contrMetric_eq_ofRat, ofRat_basis_repr_apply, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide


-- @@ L53-61 verbatim
/-- The left metric is antisymmetric `{εL | α α' = - εL | α' α}ᵀ`. -/
lemma leftMetric_antisymm : {εL | α α' = - (εL| α' α)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply]
  rw [leftMetric_eq_ofRat, ofRat_basis_repr_apply, ← map_neg, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide


-- @@ L63-71 verbatim
/-- The right metric is antisymmetric `{εR | β β' = - εR | β' β}ᵀ`. -/
lemma rightMetric_antisymm : {εR | β β' = - (εR| β' β)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply]
  rw [rightMetric_eq_ofRat, ofRat_basis_repr_apply, ← map_neg, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide


-- @@ L73-81 verbatim
/-- The dual-left metric is antisymmetric `{εL' | α α' = - εL' | α' α}ᵀ`. -/
lemma dualLeftMetric_antisymm : {εL' | α α' = - (εL' | α' α)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply]
  rw [dualLeftMetric_eq_ofRat, ofRat_basis_repr_apply, ← map_neg, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide


-- @@ L83-91 verbatim
/-- The dual-right metric is antisymmetric `{εR' | β β' = - εR' | β' β}ᵀ`. -/
lemma dualRightMetric_antisymm : {εR' | α α' = - (εR' | α' α)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply]
  rw [dualRightMetric_eq_ofRat, ofRat_basis_repr_apply, ← map_neg, ofRat_basis_repr_apply]
  congr 1
  revert b
  decide


-- @@ L93-97 verbatim
/-!

## Contractions with each other

-/


-- @@ L99-103 verbatim
/-- The contraction of the covariant metric with the contravariant metric is the unit
`{η' | μ ρ ⊗ η | ρ ν = δ' | μ ν}ᵀ`.
-/
lemma coMetric_contr_contrMetric : {η' | μ ρ ⊗ η | ρ ν = δ' | μ ν}ᵀ := by
  exact contrT_metricTensor_metricTensor_eq_dual_unit


-- @@ L105-109 verbatim
/-- The contraction of the contravariant metric with the covariant metric is the unit
`{η | μ ρ ⊗ η' | ρ ν = δ | μ ν}ᵀ`.
-/
lemma contrMetric_contr_coMetric : {η | μ ρ ⊗ η' | ρ ν = δ | μ ν}ᵀ := by
  exact contrT_metricTensor_metricTensor_eq_dual_unit


-- @@ L111-115 verbatim
/-- The contraction of the left metric with the dual-left metric is the unit
`{εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`.
-/
lemma leftMetric_contr_dualLeftMetric : {εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ := by
  exact contrT_metricTensor_metricTensor_eq_dual_unit


-- @@ L117-121 verbatim
/-- The contraction of the right metric with the dual-right metric is the unit
`{εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`.
-/
lemma rightMetric_contr_dualRightMetric : {εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ := by
  exact contrT_metricTensor_metricTensor_eq_dual_unit


-- @@ L123-127 verbatim
/-- The contraction of the dual-left metric with the left metric is the unit
`{εL' | α β ⊗ εL | β γ = δL' | α γ}ᵀ`.
-/
lemma dualLeftMetric_contr_leftMetric : {εL' | α β ⊗ εL | β γ = δL' | α γ}ᵀ := by
  exact contrT_metricTensor_metricTensor_eq_dual_unit


-- @@ L129-133 verbatim
/-- The contraction of the dual-right metric with the right metric is the unit
`{εR' | α β ⊗ εR | β γ = δR' | α γ}ᵀ`.
-/
lemma dualRightMetric_contr_rightMetric : {εR' | α β ⊗ εR | β γ = δR' | α γ}ᵀ := by
  exact contrT_metricTensor_metricTensor_eq_dual_unit


-- @@ L135-192 verbatim
/-!

## Other relations

-/
/-
/-- The map to color one gets when multiplying left and right metrics. -/
def leftMetricMulRightMap := (Sum.elim ![Color.upL, Color.upL] ![Color.upR, Color.upR]) ∘
  finSumFinEquiv.symm

/-- Expansion of the product of `εL` and `εR` in terms of a basis. -/
lemma leftMetric_prod_rightMetric : {εL | α α' ⊗ εR | β β'}ᵀ.tensor
    = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    - basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    - basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [prod_tensor_eq_fst (leftMetric_expand_tree)]
  rw [prod_tensor_eq_snd (rightMetric_expand_tree)]
  rw [prod_add_both]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_tensor_eq <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_eq_one _ _ (by simp)]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| prod_basisVector_tree _ _]
  rw [← TensorTree.add_assoc]
  simp only [add_tensor, smul_tensor, tensorNode_tensor]
  change _ = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    +- basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    +- basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)
  congr 1
  congr 1
  congr 1
  all_goals
    congr
    funext x
    fin_cases x <;> rfl

/-- Expansion of the product of `εL` and `εR` in terms of a basis, as a tensor tree. -/
lemma leftMetric_prod_rightMetric_tree : {εL | α α' ⊗ εR | β β'}ᵀ.tensor
    = (TensorTree.add (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1))) <|
      TensorTree.add (TensorTree.smul (-1 : ℂ) (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)))) <|
      TensorTree.add (TensorTree.smul (-1 : ℂ) (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)))) <|
      (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)))).tensor := by
  rw [leftMetric_prod_rightMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, add_tensor, tensorNode_tensor,
    smul_tensor, neg_smul, one_smul]
  rfl
-/

-- @@ L193-193 verbatim
end complexLorentzTensor
