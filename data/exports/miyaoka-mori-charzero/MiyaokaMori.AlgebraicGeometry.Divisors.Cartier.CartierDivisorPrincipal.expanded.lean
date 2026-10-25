import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafAsCokernel
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnits
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme


-- @@ L11-15 verbatim
/-! # Principal Cartier divisors

The principal Cartier divisor `div(f)` of `f ∈ K(X)^×`: the image of `f` as a global section of
`𝒦^*/O^*` (`CartierDivisor.principal`). Source: Hartshorne II §6.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false

-- @@ L18-18 verbatim
set_option maxHeartbeats 400000


-- @@ L20-20 verbatim
universe u v w u' v'


-- @@ L22-22 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L23-23 verbatim
open scoped AlgebraicGeometry


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-34 verbatim
/-- The Cartier divisor of local equation data `CartierLocalData`, glued by
`CartierDivisor.ofLocalData` into a global section of `Γ(X, 𝒦^*/O^*)`. The transition condition of
`CartierLocalData` (`f_i / f_j` is a unit section on overlaps) implies the stalkwise unit condition,
so `ofLocalData` takes its gluing branch. -/

noncomputable def CartierDivisor.ofAuthorLocalData {k : Type*} [Field k] {X : Variety k}
    (D : AlgebraicGeometry.Intersection.CartierLocalData X.toScheme) : CartierDivisor X :=
  CartierDivisor.ofLocalData D.opens (fun i => Units.mk0 (D.equation i) (D.equation_ne_zero i))


-- @@ L36-41 verbatim
/-- The principal Cartier divisor `div(f)`: the local datum `principalCartierData f` (one chart, the
whole space, with equation `f`) glued by `CartierDivisor.ofAuthorLocalData`. -/

noncomputable def CartierDivisor.principal {k : Type*} [Field k] {X : Variety k}
    (f : X.toScheme.functionFieldˣ) : CartierDivisor X :=
  CartierDivisor.ofAuthorLocalData (AlgebraicGeometry.Intersection.principalCartierData f)


-- @@ L43-43 verbatim
end
