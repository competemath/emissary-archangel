import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf


-- @@ L6-10 verbatim
/-! # Line bundles on a variety

Line bundles / invertible sheaves: vector bundles of rank 1; `LineBundle.toVectorBundle` is the forgetful
projection to vector bundles (e.g. `A = f^*O_X(1)`, `d_L = deg L`).
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


-- @@ L22-23 verbatim
structure LineBundle {k : Type u} [Field k] (X : Variety k) extends AlgebraicGeometry.VectorBundle X where
  rank_eq_one : toVectorBundle.rank = 1


-- @@ L25-30 verbatim
/-- Morphisms of line bundles = morphisms of the underlying modules; `L ≅ M` and the isomorphism classes
of `Pic` use this. -/

instance {k : Type u} [Field k] (X : Variety k) : CategoryTheory.Category.{u} (LineBundle X) :=
  inferInstanceAs (CategoryTheory.Category.{u}
    (CategoryTheory.InducedCategory X.carrier.Modules (fun L : LineBundle X => L.toModules)))


-- @@ L32-32 verbatim
end
