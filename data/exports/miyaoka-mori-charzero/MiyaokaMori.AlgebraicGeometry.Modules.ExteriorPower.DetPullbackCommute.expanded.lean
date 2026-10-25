import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleIsoOfModulesIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerPullbackIso


-- @@ L8-12 verbatim
/-! # The determinant commutes with pullback

`det(f^*E) ≅ f^*(det E)`; used in the degree identity `−K_X · f_*[C] = deg f^*T_X` of the paper. The
isomorphism is `AlgebraicGeometry.Scheme.Modules.moduleExteriorPullbackIso` (`ExteriorPowerPullbackIso`).
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


-- @@ L24-28 verbatim
/-- `det(f^*E) ≅ f^*(det E)` for a vector bundle `E`. -/
theorem AlgebraicGeometry.VectorBundle.det_pullback {k : Type*} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) (E : AlgebraicGeometry.VectorBundle Y) :
    Nonempty ((E.pullback f).det ≅ (E.det).pullback f) := by
  exact ⟨lineBundleIsoOfModulesIso (AlgebraicGeometry.Scheme.Modules.moduleExteriorPullbackIso f E.toModules E.rank).symm⟩


-- @@ L30-30 verbatim
end
