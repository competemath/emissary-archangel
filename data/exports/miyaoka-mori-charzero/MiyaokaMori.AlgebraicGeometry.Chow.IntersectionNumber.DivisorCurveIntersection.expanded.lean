import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree


-- @@ L11-14 verbatim
/-! # Intersection number of a divisor with a one-cycle

The intersection number `D · Z ∈ ℤ` of a divisor with a one-cycle: take `D ∩ Z ∈ A_0(X)` and then
its degree (the number `-K_X · f_*[C]` of Theorem 1.1 of the paper). -/


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


-- @@ L26-34 verbatim
/-- The intersection number `D · Z := deg(D ∩ Z)` of a Cartier divisor with a one-cycle. -/
noncomputable def intersectionNumber {k : Type u} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (D : CartierDivisor X.toVariety)
    (Z : OneCycle X.toVariety) : ℤ :=
  ChowGroup.degree X (capDivisor D 0 Z)

/- Notation `D ⬝ Z` for the intersection number (`⬝` is U+2B1D). We do not use `·`: it is Lean's cdot
   notation, so `(D · Z)` would also parse as `fun x => D x Z` and report "Ambiguous notation in cdot
   function" inside parentheses. Left associative, precedence 70 (like `*`), right argument at 71. -/


-- @@ L36-36 verbatim
notation:70 D:70 " ⬝ " Z:71 => intersectionNumber _ D Z


-- @@ L38-38 verbatim
end
