/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nikolai Kashcheev
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import Physlib.Relativity.Fermions.Weyl.Metric

-- @@ L10-14 verbatim
/-!

## Complex Lorentz tensors

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


-- @@ L23-23 verbatim
namespace complexLorentzTensor


-- @@ L25-40 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics. -/
inductive Color
  /-- The color associated with Left handed fermions. -/
  | upL : Color
  /-- The color associated with dual-Left handed fermions. -/
  | downL : Color
  /-- The color associated with Right handed fermions. -/
  | upR : Color
  /-- The color associated with dual-Right handed fermions. -/
  | downR : Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color
deriving Fintype


-- @@ L42-81 verbatim
/-- Color for complex Lorentz tensors is decidable. -/
instance : DecidableEq Color := fun x y =>
  match x, y with
  | Color.upL, Color.upL => isTrue rfl
  | Color.downL, Color.downL => isTrue rfl
  | Color.upR, Color.upR => isTrue rfl
  | Color.downR, Color.downR => isTrue rfl
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.upL, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.up => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.down => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.up => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.down => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.up => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.down => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.up => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.down => isFalse fun h => Color.noConfusion h
  | Color.up, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.up, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.up, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.up, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.down, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.down, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.down, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h


-- @@ L83-91 verbatim
/-- The dimensions of each of the different types of complex Lorentz vector space. -/
abbrev repDim (c : Color) : ℕ :=
  match c with
  | Color.upL => 2
  | Color.downL => 2
  | Color.upR => 2
  | Color.downR => 2
  | Color.up => 4
  | Color.down => 4


-- @@ L93-100 verbatim
/-- The modules associated with each of the different types of complex Lorentz vector space. -/
abbrev modules : Color → Type
  | Color.upL => Fermion.LeftHandedWeyl
  | Color.downL => Fermion.DualLeftHandedWeyl
  | Color.upR => Fermion.RightHandedWeyl
  | Color.downR => Fermion.DualRightHandedWeyl
  | Color.up => Lorentz.ContrℂModule
  | Color.down => Lorentz.CoℂModule


-- @@ L102-108 verbatim
instance modulesAddCommGroup : ∀ c, AddCommGroup (modules c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance


-- @@ L110-116 verbatim
noncomputable instance modulesModule : ∀ c, Module ℂ (modules c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance


-- @@ L118-118 verbatim
end complexLorentzTensor


-- @@ L120-120 verbatim
noncomputable section

-- @@ L121-225 verbatim
open complexLorentzTensor in
set_option maxHeartbeats 0 in
/-- The tensor structure for complex Lorentz tensors. -/
def complexLorentzTensor : TensorSpecies ℂ complexLorentzTensor.Color SL(2, ℂ)
    (fun c => match c with
      | Color.upL => Fermion.LeftHandedWeyl
      | Color.downL => Fermion.DualLeftHandedWeyl
      | Color.upR => Fermion.RightHandedWeyl
      | Color.downR => Fermion.DualRightHandedWeyl
      | Color.up => Lorentz.ContrℂModule
      | Color.down => Lorentz.CoℂModule)
    (fun c => Fin (repDim c))
    (fun c => match c with
      | Color.upL => Fermion.LeftHandedWeyl.rep
      | Color.downL => Fermion.DualLeftHandedWeyl.rep
      | Color.upR => Fermion.RightHandedWeyl.rep
      | Color.downR => Fermion.DualRightHandedWeyl.rep
      | Color.up => Lorentz.ContrℂModule.SL2CRep
      | Color.down => Lorentz.CoℂModule.SL2CRep)
    (fun c => match c with
    | Color.upL => Fermion.LeftHandedWeyl.basis
    | Color.downL => Fermion.DualLeftHandedWeyl.basis
    | Color.upR => Fermion.RightHandedWeyl.basis
    | Color.downR => Fermion.DualRightHandedWeyl.basis
    | Color.up => Lorentz.complexContrBasisFin4
    | Color.down => Lorentz.complexCoBasisFin4) where

  τ := fun c =>
    match c with
    | Color.upL => Color.downL
    | Color.downL => Color.upL
    | Color.upR => Color.downR
    | Color.downR => Color.upR
    | Color.up => Color.down
    | Color.down => Color.up
  τ_involution c := by
    match c with
    | Color.upL => rfl
    | Color.downL => rfl
    | Color.upR => rfl
    | Color.downR => rfl
    | Color.up => rfl
    | Color.down => rfl
  contr := fun c =>
    match c with
    | Color.upL => Fermion.leftDualContraction
    | Color.downL => Fermion.dualLeftContraction
    | Color.upR => Fermion.rightDualContraction
    | Color.downR => Fermion.dualRightContraction
    | Color.up => Lorentz.contrCoContraction
    | Color.down => Lorentz.coContrContraction
  metric := fun c =>
    match c with
    | Color.upL => Fermion.leftMetric
    | Color.downL => Fermion.dualLeftMetric
    | Color.upR => Fermion.rightMetric
    | Color.downR => Fermion.dualRightMetric
    | Color.up => Lorentz.contrMetric
    | Color.down => Lorentz.coMetric
  unit := fun c =>
    match c with
    | Color.upL => Fermion.dualLeftLeftUnit
    | Color.downL => Fermion.leftDualLeftUnit
    | Color.upR => Fermion.dualRightRightUnit
    | Color.downR => Fermion.rightDualRightUnit
    | Color.up => Lorentz.coContrUnit
    | Color.down => Lorentz.contrCoUnit
  contr_tmul_symm := fun c =>
    match c with
    | Color.upL => Fermion.leftDualContraction_tmul_symm
    | Color.downL => Fermion.dualLeftContraction_tmul_symm
    | Color.upR => Fermion.rightDualContraction_tmul_symm
    | Color.downR => Fermion.dualRightContraction_tmul_symm
    | Color.up => Lorentz.contrCoContraction_tmul_symm
    | Color.down => Lorentz.coContrContraction_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.upL => Fermion.contr_dualLeftLeftUnit
    | Color.downL => Fermion.contr_leftDualLeftUnit
    | Color.upR => Fermion.contr_dualRightRightUnit
    | Color.downR => Fermion.contr_rightDualRightUnit
    | Color.up => Lorentz.contr_coContrUnit
    | Color.down => Lorentz.contr_contrCoUnit
  unit_symm := fun c =>
    match c with
    | Color.upL => Fermion.dualLeftLeftUnit_symm
    | Color.downL => Fermion.leftDualLeftUnit_symm
    | Color.upR => Fermion.dualRightRightUnit_symm
    | Color.downR => Fermion.rightDualRightUnit_symm
    | Color.up => Lorentz.coContrUnit_symm
    | Color.down => Lorentz.contrCoUnit_symm
  contr_metric := fun c =>
    match c with
    | Color.upL => by
      simpa using Fermion.leftDualContraction_apply_metric
    | Color.downL => by
      simpa using Fermion.dualLeftContraction_apply_metric
    | Color.upR => by
      simpa using Fermion.rightDualContraction_apply_metric
    | Color.downR => by
      simpa using Fermion.dualRightContraction_apply_metric
    | Color.up => by
      simpa using Lorentz.contrCoContraction_apply_metric
    | Color.down => by
      simpa using Lorentz.coContrContraction_apply_metric


-- @@ L227-227 verbatim
namespace complexLorentzTensor


-- @@ L229-230 verbatim
/-- Complex Lorentz tensor. -/
syntax (name := complexLorentzTensorSyntax) "ℂT[" term,* "]" : term


-- @@ L232-240 verbatim
/-- The basis associated with each of the different types of complex Lorentz vector space. -/
abbrev basis (c : Color) : Module.Basis (Fin (repDim c)) ℂ (modules c) :=
  match c with
  | Color.upL => Fermion.LeftHandedWeyl.basis
  | Color.downL => Fermion.DualLeftHandedWeyl.basis
  | Color.upR => Fermion.RightHandedWeyl.basis
  | Color.downR => Fermion.DualRightHandedWeyl.basis
  | Color.up => Lorentz.complexContrBasisFin4
  | Color.down => Lorentz.complexCoBasisFin4


-- @@ L242-250 verbatim
/-- The reps associated with each of the different types of complex Lorentz vector space. -/
abbrev rep (c : Color) : Representation ℂ SL(2, ℂ) (modules c) :=
  match c with
  | Color.upL => Fermion.LeftHandedWeyl.rep
  | Color.downL => Fermion.DualLeftHandedWeyl.rep
  | Color.upR => Fermion.RightHandedWeyl.rep
  | Color.downR => Fermion.DualRightHandedWeyl.rep
  | Color.up => Lorentz.ContrℂModule.SL2CRep
  | Color.down => Lorentz.CoℂModule.SL2CRep


-- @@ L252-256 expanded
macro_rules
  | `(complexLorentzTensor.Tensor (vecCons $term:term ![$terms:term,*])) =>
    `(complexLorentzTensor.Tensor (vecCons $term ![$terms,*]))
  | `(complexLorentzTensor.Tensor (vecCons $term:term ![])) =>
    `(complexLorentzTensor.Tensor (vecCons $term ![]))
  | `(complexLorentzTensor.Tensor (vecEmpty)) => `(complexLorentzTensor.Tensor (vecEmpty))


-- @@ L258-259 verbatim
/-- Complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "ℂT(" c ")" => complexLorentzTensor.Tensor c


-- @@ L261-261 verbatim
open TensorSpecies Tensor


-- @@ L263-268 verbatim
lemma basisIdxCongr_eq_cast {c1 c2 : complexLorentzTensor.Color}
    (h : c1 = c2) (i : Fin (repDim c1)) :
    TensorSpecies.basisIdxCongr (basisIdx := fun c => Fin (repDim c)) h i =
      Fin.cast (by simp [h]) i := by
  subst h
  rfl


-- @@ L270-272 verbatim
lemma repDim_tau {c : complexLorentzTensor.Color} :
    repDim (complexLorentzTensor.τ c) = repDim c := by
  cases c <;> rfl


-- @@ L274-300 verbatim
lemma contrPCoeff_basis {n : ℕ} {c : Fin n → complexLorentzTensor.Color} (i j : Fin n)
    (hij : i ≠ j ∧ (complexLorentzTensor.τ (c i) = c j))
    (b : ComponentIdx (S := complexLorentzTensor) c) :
    Pure.contrPCoeff i j hij (Pure.basisVector c b) = if b i =
      Fin.cast (by simp [← hij.2, repDim_tau]) (b j)
    then 1 else 0 := by
  simp only [Pure.contrPCoeff, Pure.basisVector]
  generalize_proofs h1 h2
  generalize b i = b1 at *
  generalize b j = b2 at *
  generalize c i = ci at *
  generalize c j = cj at *
  subst h2
  cases ci
  all_goals simp only [complexLorentzTensor]
  · erw [Fermion.leftDualContraction_basis]
    exact if_congr Fin.ext_iff.symm rfl rfl
  · erw [Fermion.dualLeftContraction_basis]
    exact if_congr Fin.ext_iff.symm rfl rfl
  · erw [Fermion.rightDualContraction_basis]
    exact if_congr Fin.ext_iff.symm rfl rfl
  · erw [Fermion.dualRightContraction_basis]
    exact if_congr Fin.ext_iff.symm rfl rfl
  · erw [Lorentz.contrCoContraction_basis]
    exact if_congr Fin.ext_iff.symm rfl rfl
  · erw [Lorentz.coContrContraction_basis]
    exact if_congr Fin.ext_iff.symm rfl rfl


-- @@ L302-302 verbatim
end complexLorentzTensor

-- @@ L303-303 verbatim
end
