import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftData
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra


-- @@ L6-21 verbatim
/-! # Lift data for a projective bundle from an epimorphism

**Lift data for `P(E) = Proj_S Sym E` from an epimorphism `ψ : g^*E ↠ M`** (Stacks 01O9 / 01O4, the universal
property of the projective bundle in the form used by Stacks 07RM, Step 4): for `g : T ⟶ S`, `E` quasi-coherent on
`S`, `M` a line bundle on `T` and an epimorphism `ψ : g^*E ⟶ M`, the symmetric powers
`Ψ_m := symGradedPullbackDesc g ψ m : g^*(Sym^m E) ⟶ M^{⊗m}` form a `relativeProj.LiftData (Sym E) g M`:
* `map_one`, `map_mul` are `pullback_map_one_comp_symGradedPullbackDesc_zero` and
  `pullback_map_mul_comp_symGradedPullbackDesc` (`ProjectiveBundleUniversalPropertySymPowDesc.lean`);
* `generates`: `Ψ_1` is an epimorphism (`symGradedPullbackDesc_one_epi`): by
  `pullback_map_symPowπ_comp_symPowPullbackDesc` we have `g^*(π_1) ≫ Ψ_1 = pullbackMonoidalPow g E 1 ≫ (𝟙 ⊗ ψ)`,
  where `pullbackMonoidalPow g E 1 = pullbackTensorObjHom ≫ (pullbackUnitIso ▷ g^*E)` is an isomorphism
  (`pullbackTensorObjHom_isIso`) and `𝟙 ⊗ ψ` is an epimorphism (`epi_tensorHom_of_epi`); a right factor of an
  epimorphism is an epimorphism. The pullback functor is a left adjoint, so it preserves epimorphisms, which gives
  `generates` on the whole of `T` (`U = ⊤`, `m = 1`).

Used for the immersion of a quasi-projective scheme into a projective bundle (Stacks 07RM). -/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 400000


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L29-29 verbatim
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L35-35 verbatim
variable {X T : AlgebraicGeometry.Scheme.{u}}


-- @@ L37-60 verbatim
/-- `Sym^1` descent of an epimorphism is an epimorphism. -/
theorem symPowPullbackDesc_one_epi (g : T ⟶ X) (W : X.Modules) {M : T.Modules} [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj W ⟶ M) [CategoryTheory.Epi ψ] :
    CategoryTheory.Epi (symPowPullbackDesc g ψ 1) := by
  have h := pullback_map_symPowπ_comp_symPowPullbackDesc g W ψ 1
  have h1 : pullbackMonoidalPow g W 1 = pullbackTensorObjHom g (monoidalPow W 0) W ≫
      (pullbackMonoidalPow g W 0 ▷ (AlgebraicGeometry.Scheme.Modules.pullback g).obj W) := rfl
  have h2 : monoidalPowMap ψ 1 = (monoidalPowMap ψ 0 ⊗ₘ ψ) := rfl
  have hiso : IsIso (pullbackMonoidalPow g W 1) := by
    rw [h1]
    have h0 : IsIso (pullbackMonoidalPow g W 0) := by
      show IsIso (pullbackUnitIso g).hom
      exact (pullbackUnitIso g).isIso_hom
    exact IsIso.comp_isIso' (pullbackTensorObjHom_isIso g _ _)
      (MonoidalCategory.whiskerRight_isIso _ _)
  have hepi : CategoryTheory.Epi (monoidalPowMap ψ 1) := by
    rw [h2]
    have : CategoryTheory.Epi (monoidalPowMap ψ 0) := by
      show CategoryTheory.Epi (𝟙 _)
      infer_instance
    exact epi_tensorHom_of_epi _ _
  have : CategoryTheory.Epi (pullbackMonoidalPow g W 1 ≫ monoidalPowMap ψ 1) := epi_comp _ _
  rw [← h] at this
  exact epi_of_epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (W.symPowπ 1)) (symPowPullbackDesc g ψ 1)


-- @@ L62-71 verbatim
private theorem symGradedPullbackDesc_one_epi_aux (g : T ⟶ X) (W : X.Modules) (hq : W.IsQuasicoherent)
    {M : T.Modules} [M.IsLineBundle] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj W ⟶ M)
    [CategoryTheory.Epi ψ]
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (D : (AlgebraicGeometry.Scheme.Modules.pullback g).obj (S.part 1) ⟶ monoidalPow M 1)
    (hD : HEq D (symPowPullbackDesc g ψ 1)) : CategoryTheory.Epi D := by
  subst hS
  have hD' : D = symPowPullbackDesc g ψ 1 := eq_of_heq hD
  subst hD'
  exact symPowPullbackDesc_one_epi g W ψ


-- @@ L73-79 verbatim
/-- **`LiftData.generates` form**: for `W` quasi-coherent, `M` a line bundle and `ψ : g^*W ⟶ M` an epimorphism,
`Ψ_1 = symGradedPullbackDesc g ψ 1` is an epimorphism. -/
theorem symGradedPullbackDesc_one_epi (g : T ⟶ X) (W : X.Modules) [hq : W.IsQuasicoherent]
    {M : T.Modules} [M.IsLineBundle] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj W ⟶ M)
    [CategoryTheory.Epi ψ] : CategoryTheory.Epi (symGradedPullbackDesc g ψ 1) :=
  symGradedPullbackDesc_one_epi_aux g W hq ψ _
    (by delta symGradedAlgebra; exact dif_pos hq) _ (symGradedPullbackDesc_heq_of_isQuasicoherent g hq ψ 1)


-- @@ L81-81 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L83-98 verbatim
/-- **Lift data for `Proj_S (Sym E)` from an epimorphism `ψ : g^*E ↠ M`** (Stacks 01O9): `Ψ_m` are the symmetric
powers `symGradedPullbackDesc g ψ m`; `map_one`/`map_mul` are the computations of
`ProjectiveBundleUniversalPropertySymPowDesc.lean`, `generates` is `symGradedPullbackDesc_one_epi`. -/
def AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (E : X.Modules) [hq : E.IsQuasicoherent]
    (M : T.Modules) [M.IsLineBundle] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj E ⟶ M)
    (hψ : CategoryTheory.Epi ψ) :
    AlgebraicGeometry.Scheme.relativeProj.LiftData (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra E) g M where
  Ψ m := AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc g ψ m
  map_one := AlgebraicGeometry.Scheme.Modules.pullback_map_one_comp_symGradedPullbackDesc_zero g E hq ψ
  map_mul := AlgebraicGeometry.Scheme.Modules.pullback_map_mul_comp_symGradedPullbackDesc g E hq ψ
  generates := fun _ =>
    haveI := hψ
    haveI := AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc_one_epi g E ψ
    ⟨⊤, trivial, 1, Nat.one_pos,
      (AlgebraicGeometry.Scheme.Modules.pullback (⊤ : T.Opens).ι).map_epi _⟩


-- @@ L100-106 verbatim
@[simp]
theorem AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi_Ψ {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (E : X.Modules) [E.IsQuasicoherent]
    (M : T.Modules) [M.IsLineBundle] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj E ⟶ M)
    (hψ : CategoryTheory.Epi ψ) (m : ℕ) :
    (AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi g E M ψ hψ).Ψ m =
      AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc g ψ m := rfl


-- @@ L108-108 verbatim
end
