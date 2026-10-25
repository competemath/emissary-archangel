import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank


-- @@ L8-13 verbatim
/-! # The relative tangent sheaf of a smooth morphism is locally free

The relative tangent sheaf of a smooth morphism is locally free, with rank at each point equal to
the relative dimension (`Ω_{Z/C}` locally free implies that its dual is locally free of the same
rank). Used for `E = s^*T_{Z/C}` in §2.1 of the paper.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false

-- @@ L16-16 verbatim
set_option maxHeartbeats 400000


-- @@ L18-18 verbatim
universe u v w u' v'


-- @@ L20-20 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L21-21 verbatim
open scoped AlgebraicGeometry


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-34 verbatim
theorem AlgebraicGeometry.isLocallyFree_relativeTangent {Z C : AlgebraicGeometry.Scheme.{u}}
    (n : ℕ) (p : Z ⟶ C) [AlgebraicGeometry.SmoothOfRelativeDimension n p] :
    SheafOfModules.IsLocallyFree (AlgebraicGeometry.relativeTangent p) ∧
      ∀ z : Z, AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (AlgebraicGeometry.relativeTangent p) z = n := by
  have hsm : AlgebraicGeometry.Smooth p := AlgebraicGeometry.SmoothOfRelativeDimension.smooth n p
  have hft : (AlgebraicGeometry.Omega p).IsFiniteType := AlgebraicGeometry.Omega_isFiniteType p
  exact AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual (AlgebraicGeometry.Omega p) n
    (AlgebraicGeometry.isLocallyFree_omega_of_smooth p)
    (AlgebraicGeometry.rankAtStalk_omega_of_smoothOfRelativeDimension n p)


-- @@ L36-36 verbatim
end
