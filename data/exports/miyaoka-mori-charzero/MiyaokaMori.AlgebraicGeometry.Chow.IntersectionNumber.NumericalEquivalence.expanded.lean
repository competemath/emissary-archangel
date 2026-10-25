import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection


-- @@ L16-19 verbatim
/-! # Numerical equivalence of one-cycles

Numerical equivalence `≡` of one-cycles: two one-cycles are numerically equivalent when they have
the same intersection number with every line bundle. -/


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 400000


-- @@ L24-24 verbatim
universe u v w u' v'


-- @@ L26-26 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L27-27 verbatim
open scoped AlgebraicGeometry


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-33 expanded
/-- Numerical equivalence of one-cycles: the same intersection number with every line bundle. -/
def OneCycle.NumEquiv {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    (Z W : OneCycle X.toVariety) : Prop :=
  ∀ L : LineBundle X.toVariety, intersectionNumber _ L Z = intersectionNumber _ L W


-- @@ L35-37 verbatim
theorem OneCycle.numEquiv_equivalence {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} : Equivalence (@OneCycle.NumEquiv k _ _ X) :=
  ⟨fun _ _ => rfl, fun h L => (h L).symm, fun h h' L => (h L).trans (h' L)⟩


-- @@ L39-42 expanded
/--
Numerical equivalence of Cartier divisors: the same intersection number with every integral curve. -/
def NumEquivDivisor {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    (D E : CartierDivisor X.toVariety) : Prop :=
  ∀ Γ : IntegralCurve k X.toScheme,
    intersectionNumber _ D Γ.fundamentalClass = intersectionNumber _ E Γ.fundamentalClass


-- @@ L44-46 verbatim
theorem numEquivDivisor_equivalence {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} : Equivalence (@NumEquivDivisor k _ _ X) :=
  ⟨fun _ _ => rfl, fun h Γ => (h Γ).symm, fun h h' Γ => (h Γ).trans (h' Γ)⟩


-- @@ L48-48 verbatim
end
