import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.Stacks01ne


-- @@ L12-18 verbatim
/-! # Homogeneous coordinate sections of a curve in projective space

For `f : C → X ⊂ P^N`, the homogeneous coordinate sections `f_0, …, f_N ∈ H^0(C, A)`
(`A = f^* O_X(1)`), and the property that they have no common zero, locally on `C`.

Source: §2 of the paper (Section 2), the coordinate sections `f_i = f^*(z_i|_X)`.
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


-- @@ L30-36 verbatim
def IsHomogeneousCoordinateTuple {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (f : C ⟶ X)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u)) : Prop :=
  ∃ h : ∀ c : C, ∃ i, ¬ IsZeroAt (coord i) c,
    projectivizationMorphism (k := k) (seedLineBundle e f) coord h = f ≫ e.emb


-- @@ L38-38 verbatim
end
