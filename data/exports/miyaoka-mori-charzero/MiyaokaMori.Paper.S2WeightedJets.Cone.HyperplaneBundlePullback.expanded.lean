import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegreeDef
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding


-- @@ L8-11 verbatim
/-! # The pullback of the hyperplane bundle

`A = f^*O_X(1)`, a line bundle on `C`, and its degree `a = deg A` (§2.1 of the paper).
-/


-- @@ L13-13 verbatim
set_option autoImplicit false

-- @@ L14-14 verbatim
set_option maxHeartbeats 400000


-- @@ L16-16 verbatim
universe u v w u' v'


-- @@ L18-18 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L19-19 verbatim
open scoped AlgebraicGeometry


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-28 verbatim
/-- The seed line bundle `A = f^*O_X(1) = f^*(e^*O_{ℙ^N}(1))` on `C`. -/
noncomputable def seedLineBundle {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (f : C ⟶ X) : C.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback f).obj (e.oX 1)


-- @@ L30-30 verbatim
end
