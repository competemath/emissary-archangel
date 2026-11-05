import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Affine


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
universe u


-- @@ L11-11 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial


-- @@ L13-13 verbatim
namespace AlgebraicGeometry


-- @@ L15-15 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L17-17 verbatim
namespace ProjSpace


-- @@ L19-19 verbatim
section StdCover


-- @@ L21-21 verbatim
variable (R : Type u) [CommRing R] (n : ℕ)


-- @@ L23-23 verbatim
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R


-- @@ L25-41 verbatim
def stdCover : Scheme.OrderedAffineCover.{u} (Proj 𝒜) where
  ι := ULift.{u} (Fin (n + 1))
  U j := AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  isAffineOpen j := AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j.down)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R j.down))
    one_pos
  iSup_eq_top := by
    have key : (⨆ j : ULift.{u} (Fin (n + 1)),
        AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down))
        = ⨆ j : Fin (n + 1), AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
      refine le_antisymm (iSup_le fun j => ?_) (iSup_le fun j => ?_)
      · exact le_iSup (fun j' : Fin (n + 1) => AlgebraicGeometry.Proj.basicOpen 𝒜 (X j')) j.down
      · exact le_iSup (fun j' : ULift.{u} (Fin (n + 1)) =>
          AlgebraicGeometry.Proj.basicOpen 𝒜 (X j'.down)) (ULift.up j)
    rw [key]
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜 _
      (irrelevant_le_span_X R n)


-- @@ L43-44 verbatim
theorem stdCover_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCover R n).U j = AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down) := rfl


-- @@ L46-46 verbatim
end StdCover


-- @@ L48-48 verbatim
section StdCoverPullback


-- @@ L50-50 verbatim
variable {A : Type u} [CommRing A] {n : ℕ}

-- @@ L51-52 verbatim
variable {W : Scheme.{u}}
  (ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]


-- @@ L54-59 verbatim
def stdCoverPullback : Scheme.OrderedAffineCover.{u} W :=
  let f := ι
  { ι := ULift.{u} (Fin (n + 1))
    U := fun j => f ⁻¹ᵁ ((stdCover A n).U j)
    isAffineOpen := fun j => ((stdCover A n).isAffineOpen j).preimage f
    iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top f (stdCover A n).iSup_eq_top }


-- @@ L61-62 verbatim
theorem stdCoverPullback_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCoverPullback ι).U j = ι ⁻¹ᵁ (stdCover A n).U j := rfl


-- @@ L64-64 verbatim
end StdCoverPullback


-- @@ L66-66 verbatim
end ProjSpace


-- @@ L68-68 verbatim
end AlgebraicGeometry


-- @@ L70-70 verbatim
end
