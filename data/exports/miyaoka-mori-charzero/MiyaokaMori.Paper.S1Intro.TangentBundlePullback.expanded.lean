import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.TangentBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegreeDef
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme


-- @@ L13-18 verbatim
/-! # Pullback of the tangent bundle

The pullback `f^*T_X` of the tangent bundle along a morphism `f : C → X` from a smooth projective
curve (a vector bundle on `C`), and its degree `d = deg f^*T_X`, which appears in the hypothesis of
the main theorem (Theorem 1.1 of the paper, via the degree identity `-K_X · f_*[C] = deg f^*T_X`).
-/


-- @@ L20-20 verbatim
set_option autoImplicit false

-- @@ L21-21 verbatim
set_option maxHeartbeats 400000


-- @@ L23-23 verbatim
universe u v w u' v'


-- @@ L25-25 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L26-26 verbatim
open scoped AlgebraicGeometry


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-33 verbatim
/-- The pullback `f^*T_X` of the tangent bundle of `X` along `f : C → X`, as a vector bundle on `C`. -/
noncomputable def TangentBundle.pullback {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) : AlgebraicGeometry.VectorBundle C.toVariety :=
  AlgebraicGeometry.VectorBundle.pullback f (tangentBundle X)


-- @@ L35-39 verbatim
/-- The degree `deg f^*T_X` of the pulled-back tangent bundle. -/
noncomputable def TangentBundle.pullbackDegree {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) : ℤ :=
  VectorBundle.degree (TangentBundle.pullback f)


-- @@ L41-41 verbatim
end
