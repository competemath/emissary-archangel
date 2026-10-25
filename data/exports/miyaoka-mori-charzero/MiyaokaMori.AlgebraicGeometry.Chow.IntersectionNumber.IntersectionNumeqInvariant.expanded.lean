import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.NumericalEquivalence


-- @@ L10-14 verbatim
/-! # Numerically equivalent one-cycles have the same intersection numbers

Numerically equivalent one-cycles have the same intersection number with every line bundle
(immediate from the definition). Used in §4 of the paper (the fibers of the ruled surface are
numerically equivalent). -/


-- @@ L16-16 verbatim
set_option autoImplicit false

-- @@ L17-17 verbatim
set_option maxHeartbeats 400000


-- @@ L19-19 verbatim
universe u v w u' v'


-- @@ L21-21 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L22-22 verbatim
open scoped AlgebraicGeometry


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-29 expanded
theorem inter_eq_of_numEquiv {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    (L : LineBundle X.toVariety) {Z W : OneCycle X.toVariety} (h : Z.NumEquiv W) :
    intersectionNumber _ L Z = intersectionNumber _ L W := by exact h L


-- @@ L31-31 verbatim
end
