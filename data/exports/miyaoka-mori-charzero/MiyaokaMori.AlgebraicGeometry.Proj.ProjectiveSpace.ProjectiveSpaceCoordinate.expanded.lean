import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace


-- @@ L8-16 verbatim
/-! # Homogeneous coordinates of projective space

The homogeneous coordinates `x_i ∈ Γ(P^N, O(1))` of `P^N_k`; for a morphism `f : X → P^N` the
homogeneous coordinate sections of `f` are `f_ℓ = f^* x_ℓ` (§1 of the paper).

`projectiveSpaceCoordinate` is the only definition of the homogeneous coordinates; the section over
an arbitrary open `U` is the restriction of the global section,
`(projectiveSpaceTwist k N 1).presheaf.map (homOfLE le_top).op (projectiveSpaceCoordinate k N i)`.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option maxHeartbeats 400000


-- @@ L21-21 verbatim
universe u v w u' v'


-- @@ L23-23 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L24-24 verbatim
open scoped AlgebraicGeometry


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L30-36 verbatim
/-- The homogeneous coordinate `x_i ∈ Γ(P^N, O(1))`: the global section `X_i / 1` given by the
degree-one homogeneous element `X i`. -/
noncomputable def projectiveSpaceCoordinate (k : Type u) [Field k] (N : ℕ) (i : Fin (N + 1)) :
    ((projectiveSpaceTwist k N 1).val.obj (Opposite.op ⊤) : Type u) :=
  MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) ⊤


-- @@ L38-38 verbatim
end
