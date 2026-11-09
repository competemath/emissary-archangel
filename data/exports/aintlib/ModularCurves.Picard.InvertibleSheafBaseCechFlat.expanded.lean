import ModularCurves.ForMathlib.SchemeModuleBaseCechTrivialFlat
import ModularCurves.Picard.InvertibleSheafFiniteAffineCover


-- @@ L4-10 verbatim
/-!
# Flat Cech models for invertible sheaves

An invertible sheaf on a compact scheme admits a finite affine trivializing
cover.  For a separated flat family over an affine base, the associated
base-linear Cech complex is therefore termwise flat.
-/


-- @@ L12-12 verbatim
open CategoryTheory TopologicalSpace


-- @@ L14-14 verbatim
universe u


-- @@ L16-16 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-36 verbatim
/-- An invertible sheaf on a compact separated flat family over an affine base
admits a finite affine trivializing cover whose base-linear Cech complex is
termwise flat. -/
theorem IsInvertible.exists_finiteAffineBaseCech_flat
    {X S : Scheme.{u}} (π : X ⟶ S) [IsAffine S] [Flat π]
    [X.IsSeparated] [CompactSpace X] {M : X.Modules} (hM : IsInvertible M) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        (∀ i, Nonempty
          (M.restrict (U i).ι ≅ unitObj (U i).toScheme)) ∧
          ∀ n, Module.Flat Γ(S, (⊤ : S.Opens))
            ((baseCechComplex π M U).X n) := by
  obtain ⟨ι, hι, U, hU, hUaff, htriv⟩ :=
    hM.exists_finite_affine_trivializingCover
  exact ⟨ι, hι, U, hU, hUaff, htriv, fun n =>
    baseCechComplex_X_flat_of_trivializingCover
      π M U hUaff htriv n⟩


-- @@ L38-38 verbatim
end


-- @@ L40-40 verbatim
end AlgebraicGeometry.Scheme.Modules
