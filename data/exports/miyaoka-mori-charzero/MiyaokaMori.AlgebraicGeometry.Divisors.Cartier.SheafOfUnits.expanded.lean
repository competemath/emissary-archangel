import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnitsPostcompose


-- @@ L5-10 verbatim
/-! # Sheaves of units on a scheme

The sheaf of units `F^*: U ↦ Γ(F, U)^×` of a sheaf of rings is a sheaf of commutative groups. For the
structure sheaf this gives `O_X^*`, for the sheaf of rational functions `𝒦_X^*`; both enter the
sheaf-theoretic descriptions of Cartier divisors and of the Picard group.
-/


-- @@ L12-12 verbatim
set_option autoImplicit false

-- @@ L13-13 verbatim
set_option maxHeartbeats 400000


-- @@ L15-15 verbatim
universe u v w u' v'


-- @@ L17-17 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L18-18 verbatim
open scoped AlgebraicGeometry


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-25 verbatim
/-- The sheaf of units `O_X^*` of the structure sheaf. -/
noncomputable def AlgebraicGeometry.Scheme.unitsSheaf (X : AlgebraicGeometry.Scheme.{u}) :
    TopCat.Sheaf CommGrpCat.{u} X :=
  TopCat.Sheaf.units X.sheaf


-- @@ L27-30 verbatim
/-- The sheaf of units `𝒦_X^*` of the sheaf of rational functions. -/
noncomputable def AlgebraicGeometry.Scheme.rationalFunctionsUnitsSheaf
    (X : AlgebraicGeometry.Scheme.{u}) : TopCat.Sheaf CommGrpCat.{u} X :=
  TopCat.Sheaf.units X.rationalFunctionsSheaf


-- @@ L32-32 verbatim
end
