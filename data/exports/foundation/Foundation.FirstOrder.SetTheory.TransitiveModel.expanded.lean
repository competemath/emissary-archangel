module

public import Foundation.FirstOrder.SetTheory.Universe


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L8-8 verbatim
abbrev TransitiveModel.{u} := Set Universe.{u}


-- @@ L10-10 verbatim
namespace TransitiveModel


-- @@ L12-14 verbatim
variable {U : TransitiveModel}

lemma wellFounded : WellFounded (α := U) (· ∈ ·) := Universe.wellFounded.onFun (f := Subtype.val)


-- @@ L16-18 verbatim
@[elab_as_elim]
theorem ind {P : U → Prop} (ind : ∀ x, (∀ y ∈ x, P y) → P x) (x : U) : P x :=
  wellFounded.induction x ind


-- @@ L20-20 verbatim
noncomputable def model [Small U] : Universe := .mk U


-- @@ L22-22 verbatim
end TransitiveModel


-- @@ L24-24 verbatim
end FFL.FirstOrder.SetTheory
