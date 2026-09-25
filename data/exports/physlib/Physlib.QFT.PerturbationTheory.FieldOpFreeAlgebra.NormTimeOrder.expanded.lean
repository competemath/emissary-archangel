/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FieldSpecification.TimeOrder
public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.Basic

-- @@ L10-14 verbatim
/-!

# Norm-time Ordering in the FieldOpFreeAlgebra

-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace FieldSpecification

-- @@ L19-19 verbatim
variable {𝓕 : FieldSpecification}

-- @@ L20-20 verbatim
open FieldStatistic


-- @@ L22-22 verbatim
namespace FieldOpFreeAlgebra


-- @@ L24-24 verbatim
noncomputable section

-- @@ L25-25 verbatim
open Module Physlib.List


-- @@ L27-31 verbatim
/-!

## Norm-time order

-/


-- @@ L33-36 verbatim
/-- The normal-time ordering on `FieldOpFreeAlgebra`. -/
def normTimeOrder : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)


-- @@ L38-39 verbatim
@[inherit_doc normTimeOrder]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓣𝓝ᶠ(" a ")" => normTimeOrder a


-- @@ L41-44 verbatim
lemma normTimeOrder_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    𝓣𝓝ᶠ(ofCrAnListF φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [normTimeOrder, Basis.constr_basis]


-- @@ L46-46 verbatim
end


-- @@ L48-48 verbatim
end FieldOpFreeAlgebra


-- @@ L50-50 verbatim
end FieldSpecification
