/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
module

public import LeanPool.ConnesRigidity.Construction.PaperActionInstances
public import LeanPool.ConnesRigidity.Foundation.GroupTheory.SpecialLinear.ElementaryGeneration
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.FinitePropertyT
import LeanPool.ConnesRigidity.Porting.CoreTransfer


-- @@ L15-17 verbatim
/-!
Property-(T) transfer for Zhou §4 on the concrete tensor-kernel groups.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Connes

-- @@ L22-22 verbatim
namespace PaperPropertyT


-- @@ L24-24 verbatim
open Construction

-- @@ L25-25 verbatim
open Construction.PaperKernel


-- @@ L27-27 verbatim
universe v


-- @@ L29-33 verbatim
/-- The elementary subgroup appearing in the cited EJZK theorem. Paper: §4. -/
noncomputable def elementaryGroup : CountableDiscreteGroup :=
  { Carrier := SpecialLinear.elementarySubgroup
    group := inferInstance
    countable := inferInstance }


-- @@ L35-40 verbatim
/-- Zhou Proposition 4.1(a) identifies the elementary group with `SL₃(R)`.
Paper: §4. -/
noncomputable def elementaryEquivSL3 :
    SpecialLinear.elementarySubgroup ≃* SpecialLinear.SL3 :=
  (MulEquiv.subgroupCongr SpecialLinear.elementarySubgroup_eq_top).trans
    Subgroup.topEquiv


-- @@ L42-45 verbatim
/-- The external EJZK property-(T) input used by Zhou §4. Paper: §4,
Proposition 4.1(b). -/
structure EJZKInput where
  propertyT : HasKazhdanPropertyT.{0, v} elementaryGroup


-- @@ L47-52 verbatim
/-- Transport the cited elementary-group theorem across Zhou Proposition 4.1(a).
Paper: §4. -/
theorem sl3_propertyT_from_EJZK (input : EJZKInput.{v}) :
    HasKazhdanPropertyT.{0, v} SpecialLinear.sl3Group := by
  exact (OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
    elementaryGroup SpecialLinear.sl3Group elementaryEquivSL3).mp input.propertyT


-- @@ L54-58 verbatim
/-- Inclusion of the SL₃ factor into the actual acting group. Paper: §4. -/
def sl3ToActingGroup : SpecialLinear.SL3 →* H where
  toFun l := (l, 1)
  map_one' := by rfl
  map_mul' l m := by simp


-- @@ L60-63 verbatim
/-- Pointwise form of the standard inclusion of the SL₃ factor. Paper: §4. -/
@[simp] theorem sl3ToActingGroup_apply (g : SpecialLinear.SL3) :
    sl3ToActingGroup g = (g, 1) :=
  rfl


-- @@ L65-69 verbatim
/-- The finite quotient in Zhou Proposition 4.8. Paper: §4. -/
noncomputable def finiteSymplecticGroup : CountableDiscreteGroup where
  Carrier := Q
  group := inferInstance
  countable := by infer_instance


-- @@ L71-74 verbatim
/-- Carrier of the SL₃ intermediate group associated to an action. Paper: §4. -/
abbrev lambdaCarrier (action : H →* MulAut (Multiplicative PaperKernel.D)) :=
  SemidirectProduct (Multiplicative PaperKernel.D) SpecialLinear.SL3
    (action.comp sl3ToActingGroup)


-- @@ L76-83 verbatim
/-- Countable wrapper for the SL₃ intermediate group of an action. Paper: §4. -/
noncomputable abbrev lambdaOf
    (action : H →* MulAut (Multiplicative PaperKernel.D)) :
    CountableDiscreteGroup :=
  { Carrier := lambdaCarrier action
    group := SemidirectProduct.instGroup
    countable := by
      exact SemidirectProduct.equivProd.injective.countable }


-- @@ L85-87 verbatim
/-- Zhou's first concrete SL₃ intermediate group. Paper: §4. -/
noncomputable abbrev lambdaOne : CountableDiscreteGroup :=
  lambdaOf PaperKernel.paperThetaOneHom


-- @@ L89-93 verbatim
/-- Zhou's second concrete SL₃ intermediate group. Paper: §4. -/
noncomputable abbrev lambdaTwo : CountableDiscreteGroup :=
  lambdaOf PaperKernel.paperThetaTwoHom

/- The finite quotient Property-(T) input is discharged by averaging. Paper: §4. -/

-- @@ L94-99 verbatim
theorem finiteSymplecticGroup_propertyT :
    HasKazhdanPropertyT.{0, v} finiteSymplecticGroup := by
  let _ : Fintype (finiteSymplecticGroup : Type) := by
    change Fintype Q
    infer_instance
  exact PropertyTTransfer.hasKazhdanPropertyT_of_fintype finiteSymplecticGroup


-- @@ L101-101 verbatim
end PaperPropertyT

-- @@ L102-102 verbatim
end Connes
