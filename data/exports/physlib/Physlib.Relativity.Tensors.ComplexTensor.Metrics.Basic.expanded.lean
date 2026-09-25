/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.OfRat

-- @@ L9-13 verbatim
/-!

## Metrics as complex Lorentz tensors

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Matrix

-- @@ L18-18 verbatim
open MatrixGroups

-- @@ L19-19 verbatim
open Complex

-- @@ L20-20 verbatim
open TensorProduct

-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace complexLorentzTensor

-- @@ L24-24 verbatim
open Fermion


-- @@ L26-30 verbatim
/-!

## Definitions.

-/


-- @@ L32-33 expanded
/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
abbrev coMetric : complexLorentzTensor.Tensor (vecCons .down ![.down]) :=
  complexLorentzTensor.metricTensor Color.down


-- @@ L35-36 expanded
/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
abbrev contrMetric : complexLorentzTensor.Tensor (vecCons .up ![.up]) :=
  complexLorentzTensor.metricTensor Color.up


-- @@ L38-39 expanded
/-- The metric `εᵃᵃ` as a complex Lorentz tensor. -/
abbrev leftMetric : complexLorentzTensor.Tensor (vecCons .upL ![.upL]) :=
  complexLorentzTensor.metricTensor Color.upL


-- @@ L41-42 expanded
/-- The metric `ε^{dot a}^{dot a}` as a complex Lorentz tensor. -/
abbrev rightMetric : complexLorentzTensor.Tensor (vecCons .upR ![.upR]) :=
  complexLorentzTensor.metricTensor Color.upR


-- @@ L44-45 expanded
/-- The metric `εₐₐ` as a complex Lorentz tensor. -/
abbrev dualLeftMetric : complexLorentzTensor.Tensor (vecCons .downL ![.downL]) :=
  complexLorentzTensor.metricTensor Color.downL


-- @@ L47-48 expanded
/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensor. -/
abbrev dualRightMetric : complexLorentzTensor.Tensor (vecCons .downR ![.downR]) :=
  complexLorentzTensor.metricTensor Color.downR


-- @@ L50-54 verbatim
/-!

## Notation

-/


-- @@ L56-57 verbatim
/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "η'" => coMetric


-- @@ L59-60 verbatim
/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "η" => contrMetric


-- @@ L62-63 verbatim
/-- The metric `εᵃᵃ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εL" => leftMetric


-- @@ L65-66 verbatim
/-- The metric `ε^{dot a}^{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR" => rightMetric


-- @@ L68-69 verbatim
/-- The metric `εₐₐ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εL'" => dualLeftMetric


-- @@ L71-72 verbatim
/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR'" => dualRightMetric


-- @@ L74-78 verbatim
/-!

## Other forms

-/

-- @@ L79-79 verbatim
open TensorSpecies

-- @@ L80-80 verbatim
open Tensor

-- @@ L81-85 verbatim
/-!

### fromConstPair

-/


-- @@ L87-90 verbatim
lemma coMetric_eq_fromConstPair : η' = fromConstPair (S := complexLorentzTensor)
    (c1 := .down) (c2 := .down) Lorentz.coMetric := by
  rw [Lorentz.coMetric]
  rfl


-- @@ L92-95 verbatim
lemma contrMetric_eq_fromConstPair : η = fromConstPair (S := complexLorentzTensor)
    (c1 := .up) (c2 := .up) Lorentz.contrMetric := by
  rw [Lorentz.contrMetric]
  rfl


-- @@ L97-97 verbatim
lemma leftMetric_eq_fromConstPair : εL = fromConstPair Fermion.leftMetric := rfl


-- @@ L99-99 verbatim
lemma rightMetric_eq_fromConstPair : εR = fromConstPair Fermion.rightMetric := rfl


-- @@ L101-101 verbatim
lemma dualLeftMetric_eq_fromConstPair : εL' = fromConstPair Fermion.dualLeftMetric := rfl


-- @@ L103-103 verbatim
lemma dualRightMetric_eq_fromConstPair : εR' = fromConstPair Fermion.dualRightMetric := rfl


-- @@ L105-109 verbatim
/-!

### fromPairT

-/


-- @@ L111-114 verbatim
lemma coMetric_eq_fromPairT : η' = fromPairT (Lorentz.coMetricVal) := by
  rw [coMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.coMetric_apply_one


-- @@ L116-119 verbatim
lemma contrMetric_eq_fromPairT : η = fromPairT (Lorentz.contrMetricVal) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.contrMetric_apply_one


-- @@ L121-124 verbatim
lemma leftMetric_eq_fromPairT : εL = fromPairT (Fermion.leftMetricVal) := by
  rw [leftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.leftMetric_apply_one


-- @@ L126-129 verbatim
lemma rightMetric_eq_fromPairT : εR = fromPairT (Fermion.rightMetricVal) := by
  rw [rightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.rightMetric_apply_one


-- @@ L131-134 verbatim
lemma dualLeftMetric_eq_fromPairT : εL' = fromPairT (Fermion.dualLeftMetricVal) := by
  rw [dualLeftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.dualLeftMetric_apply_one


-- @@ L136-139 verbatim
lemma dualRightMetric_eq_fromPairT : εR' = fromPairT (Fermion.dualRightMetricVal) := by
  rw [dualRightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.dualRightMetric_apply_one


-- @@ L141-145 verbatim
/-!

### complexCoBasis etc.

-/


-- @@ L147-154 verbatim
open Lorentz in
lemma coMetric_eq_complexCoBasis : η' =
    fromPairT (complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0))
    - fromPairT (complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0))
    - fromPairT (complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1))
    - fromPairT (complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2)) := by
  rw [coMetric_eq_fromPairT, coMetricVal_expand_tmul]
  simp


-- @@ L156-164 verbatim
open Lorentz in
lemma coMetric_eq_complexCoBasisFin4 : η' =
    fromPairT (complexCoBasisFin4 0 ⊗ₜ[ℂ] complexCoBasisFin4 0)
    - fromPairT (complexCoBasisFin4 1 ⊗ₜ[ℂ] complexCoBasisFin4 1)
    - fromPairT (complexCoBasisFin4 2 ⊗ₜ[ℂ] complexCoBasisFin4 2)
    - fromPairT (complexCoBasisFin4 3 ⊗ₜ[ℂ] complexCoBasisFin4 3) := by
  rw [coMetric_eq_complexCoBasis]
  simp [complexCoBasisFin4]
  rfl


-- @@ L166-173 verbatim
open Lorentz in
lemma contrMetric_eq_complexContrBasis : η =
    fromPairT (complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0))
    - fromPairT (complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0))
    - fromPairT (complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1))
    - fromPairT (complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2)) := by
  rw [contrMetric_eq_fromPairT, contrMetricVal_expand_tmul]
  simp


-- @@ L175-183 verbatim
open Lorentz in
lemma contrMetric_eq_complexContrBasisFin4 : η =
    fromPairT (complexContrBasisFin4 0 ⊗ₜ[ℂ] complexContrBasisFin4 0)
    - fromPairT (complexContrBasisFin4 1 ⊗ₜ[ℂ] complexContrBasisFin4 1)
    - fromPairT (complexContrBasisFin4 2 ⊗ₜ[ℂ] complexContrBasisFin4 2)
    - fromPairT (complexContrBasisFin4 3 ⊗ₜ[ℂ] complexContrBasisFin4 3) := by
  rw [contrMetric_eq_complexContrBasis]
  simp [complexContrBasisFin4]
  rfl


-- @@ L185-190 verbatim
open Fermion in
lemma leftMetric_eq_leftHandedWeyl_basis : εL =
    - fromPairT (LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1)
    + fromPairT (LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0) := by
  rw [leftMetric_eq_fromPairT, leftMetricVal_expand_tmul]
  simp


-- @@ L192-197 verbatim
open Fermion in
lemma dualLeftMetric_eq_dualLeftHandedWeyl_basis : εL' =
    fromPairT (DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1)
    - fromPairT (DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0) := by
  rw [dualLeftMetric_eq_fromPairT, dualLeftMetricVal_expand_tmul]
  simp


-- @@ L199-204 verbatim
open Fermion in
lemma rightMetric_eq_rightHandedWeyl_basis : εR =
    - fromPairT (RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1)
    + fromPairT (RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0) := by
  rw [rightMetric_eq_fromPairT, rightMetricVal_expand_tmul]
  simp


-- @@ L206-211 verbatim
open Fermion in
lemma dualRightMetric_eq_dualRightHandedWeyl_basis : εR' =
    fromPairT (DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1)
    - fromPairT (DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0) := by
  rw [dualRightMetric_eq_fromPairT, dualRightMetricVal_expand_tmul]
  simp


-- @@ L213-217 verbatim
/-!

### basis

-/


-- @@ L219-250 verbatim
open Lorentz in
lemma coMetric_eq_basis : η' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (0 : Fin 4) | 1 => (0 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (1 : Fin 4) | 1 => (1 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (2 : Fin 4) | 1 => (2 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (3 : Fin 4) | 1 => (3 : Fin 4))) := by
  rw [coMetric_eq_complexCoBasisFin4]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 2]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 2]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 1]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  rfl


-- @@ L252-283 verbatim
open Lorentz in
lemma contrMetric_eq_basis : η =
    (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (0 : Fin 4) | 1 => (0 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (1 : Fin 4) | 1 => (1 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (2 : Fin 4) | 1 => (2 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (3 : Fin 4) | 1 => (3 : Fin 4))) := by
  rw [contrMetric_eq_complexContrBasisFin4]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 2]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 2]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 1]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  rfl


-- @@ L285-302 verbatim
open Fermion in
lemma leftMetric_eq_basis : εL =
    - (Tensor.basis (S := complexLorentzTensor) ![Color.upL, Color.upL]
      (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    + (Tensor.basis (S := complexLorentzTensor)
      ![Color.upL, Color.upL] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [leftMetric_eq_leftHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .upL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upL _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1]
    change fromPairT ((complexLorentzTensor.basis .upL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upL _))
    rw [fromPairT_apply_basis_repr]
  rfl


-- @@ L304-321 verbatim
open Fermion in
lemma dualLeftMetric_eq_basis : εL' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.downL, Color.downL]
      (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    - (Tensor.basis (S := complexLorentzTensor)
      ![Color.downL, Color.downL] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [dualLeftMetric_eq_dualLeftHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .downL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downL _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1]
    change fromPairT ((complexLorentzTensor.basis .downL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downL _))
    rw [fromPairT_apply_basis_repr]
  rfl


-- @@ L323-340 verbatim
open Fermion in
lemma rightMetric_eq_basis : εR =
    - (Tensor.basis (S := complexLorentzTensor) ![Color.upR, Color.upR]
      (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    + (Tensor.basis (S := complexLorentzTensor)
      ![Color.upR, Color.upR] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [rightMetric_eq_rightHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .upR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upR _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1]
    change fromPairT ((complexLorentzTensor.basis .upR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upR _))
    rw [fromPairT_apply_basis_repr]
  rfl


-- @@ L342-359 verbatim
open Fermion in
lemma dualRightMetric_eq_basis : εR' =
    (Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.downR] (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    - (Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.downR] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [dualRightMetric_eq_dualRightHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .downR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downR _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1]
    change fromPairT ((complexLorentzTensor.basis .downR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downR _))
    rw [fromPairT_apply_basis_repr]
  rfl


-- @@ L361-365 verbatim
/-!

### ofRat

-/


-- @@ L367-376 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma coMetric_eq_ofRat : η' = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 4) ∧ f 1 = Fin.cast (by rfl) (0 : Fin 4) then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [coMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide


-- @@ L378-387 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma contrMetric_eq_ofRat : η = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 4) ∧ f 1 = Fin.cast (by rfl) (0 : Fin 4) then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [contrMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide


-- @@ L389-398 verbatim
lemma leftMetric_eq_ofRat : εL = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then - 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then
      1 else 0 := by
  rw [leftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide


-- @@ L400-409 verbatim
lemma dualLeftMetric_eq_ofRat : εL' = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then
      - 1 else 0 := by
  rw [dualLeftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub]
  congr
  with_unfolding_all decide


-- @@ L411-419 verbatim
lemma rightMetric_eq_ofRat : εR = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then - 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then 1 else 0 := by
  rw [rightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide


-- @@ L421-430 verbatim
lemma dualRightMetric_eq_ofRat : εR' = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then
      - 1 else 0 := by
  rw [dualRightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub]
  congr
  with_unfolding_all decide


-- @@ L432-436 verbatim
/-!

## Group actions

-/


-- @@ L438-438 verbatim
open TensorSpecies


-- @@ L440-442 verbatim
/-- The tensor `coMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_coMetric (g : SL(2,ℂ)) : g • η' = η' := by
  rw [metricTensor_invariant]


-- @@ L444-446 verbatim
/-- The tensor `contrMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_contrMetric (g : SL(2,ℂ)) : g • η = η := by
  rw [metricTensor_invariant]


-- @@ L448-450 verbatim
/-- The tensor `leftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_leftMetric (g : SL(2,ℂ)) : g • εL = εL := by
  rw [metricTensor_invariant]


-- @@ L452-454 verbatim
/-- The tensor `rightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_rightMetric (g : SL(2,ℂ)) : g • εR = εR := by
  rw [metricTensor_invariant]


-- @@ L456-458 verbatim
/-- The tensor `dualLeftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualLeftMetric (g : SL(2,ℂ)) : g • εL' = εL' := by
  rw [metricTensor_invariant]


-- @@ L460-462 verbatim
/-- The tensor `dualRightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualRightMetric (g : SL(2,ℂ)) : g • εR' = εR' := by
  rw [metricTensor_invariant]


-- @@ L464-464 verbatim
end complexLorentzTensor
