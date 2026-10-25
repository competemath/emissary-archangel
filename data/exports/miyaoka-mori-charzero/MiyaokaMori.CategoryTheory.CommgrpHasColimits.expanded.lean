import MiyaokaMori.Prelude


-- @@ L3-9 verbatim
/-! # Colimits in the category of commutative groups

The category `CommGrpCat` of (multiplicatively written) commutative groups has all small colimits,
transported from the additive version along `CommGrpCat ≌ AddCommGrpCat`. This is what makes stalks
of `CommGrpCat`-valued sheaves (`TopCat.Presheaf.stalk` requires `HasColimits`) available, e.g. the
stalks of `𝒦^*/O^*` in the theory of Cartier divisors.
-/


-- @@ L11-11 verbatim
set_option autoImplicit false

-- @@ L12-12 verbatim
set_option maxHeartbeats 400000


-- @@ L14-14 verbatim
universe u v w u' v'


-- @@ L16-16 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L17-17 verbatim
open scoped AlgebraicGeometry


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-23 verbatim
/-- `CommGrpCat` has all small colimits (transported from `AddCommGrpCat`). -/
instance CommGrpCat.hasColimits : CategoryTheory.Limits.HasColimits CommGrpCat.{u} :=
  CategoryTheory.Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor


-- @@ L25-25 verbatim
end
