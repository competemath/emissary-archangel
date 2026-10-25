import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme


-- @@ L8-12 verbatim
/-! # Pullback of line bundles

The pullback `g^*L` of a line bundle along a morphism (the underlying vector bundle is
`VectorBundle.pullback`, still of rank 1); notation `g ^* L`. Pullback of modules: Stacks 01BG.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
set_option maxHeartbeats 400000


-- @@ L17-17 verbatim
universe u v w u' v'


-- @@ L19-19 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L20-20 verbatim
open scoped AlgebraicGeometry


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-27 verbatim
noncomputable def LineBundle.pullback {k : Type u} [Field k] {X Y : Variety k}
    (g : X.toScheme ⟶ Y.toScheme) (L : LineBundle Y) : LineBundle X where
  toVectorBundle := AlgebraicGeometry.VectorBundle.pullback g L.toVectorBundle
  rank_eq_one := L.rank_eq_one


-- @@ L29-29 verbatim
@[inherit_doc] infixr:80 " ^* " => LineBundle.pullback


-- @@ L31-31 verbatim
end
