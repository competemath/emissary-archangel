/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.KTheory.ModuleResolution
import RiemannRoch.Chow.RegularLocalProjectiveDimension
import RiemannRoch.RelativeRiemannRoch.ProjectiveSpaceK0G0



-- @@ L12-33 verbatim
/-!
# The affine resolution theorem: `K₀(Spec R) ≅ G₀(Spec R)` for regular `R`

Main results:
* `SchemeKTheory.k0ToG0_bijective_spec_of_isRegularRing`. For `R` a regular ring with
  `ringKrullDim R ≤ d`, the comparison `K₀(Spec R) → G₀(Spec R)` is bijective. This discharges
  the base hypothesis of `SchemeProjectiveSpace.k0ToG0_bijective_of_base`.
* `SchemeProjectiveSpace.k0ToG0_bijective_of_isRegularRing`. `K₀(ℙⁿ_R) ≅ G₀(ℙⁿ_R)` over such
  a base, for `0 < n`.
* `ModuleResolution.k0ToG0_bijective_of_isRegularRing`. The module-level statement.

## Proof
1. `IsRegularRing.hasProjectiveDimensionLE` (Serre): every finite module has `pd ≤ d`.
2. `ModuleResolution.k0ToG0_bijective_of_hasProjectiveDimensionLE`: the module-level resolution
   theorem.
3. Transport along the affine tilde/global-sections dictionary. The ingredients are:
   * `gammaG` and `tildeG` are mutually inverse on `G₀`, via the unit `M ≅ Γ(M~)` and the
     counit `Γ(E)~ ≅ E` for quasicoherent `E`;
   * `tildeK : K₀(R) → K₀(Spec R)` is surjective, because a finite locally free sheaf has
     finite projective global sections (`projective_moduleSpecΓ_of_isFiniteLocallyFree`);
   * the square `k0ToG0 ∘ tildeK = tildeG ∘ k0ToG0` commutes.
-/


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
universe u


-- @@ L39-39 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SchemeKTheory

-- @@ L40-40 verbatim
open scoped ZeroObject


-- @@ L42-42 verbatim
namespace RegularAffineK0G0


-- @@ L44-44 verbatim
variable (R : Type u) [CommRing R]


-- @@ L46-46 verbatim
local notation "X" => Spec (CommRingCat.of R)


-- @@ L48-76 verbatim
/-- Global sections of a finite locally free sheaf on `Spec R` are a projective `R`-module. -/
theorem projective_moduleSpecΓ_of_isFiniteLocallyFree (E : (Spec (CommRingCat.of R)).Modules)
    (hE : IsFiniteLocallyFree _ E) :
    Module.Projective R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj E) := by
  obtain ⟨-, hproj⟩ := SchemeProjectiveSpace.sections_finite_projective_of_isFiniteLocallyFree E hE
    (U := ⊤) (isAffineOpen_top _)
  let e : Γ(Spec (CommRingCat.of R), ⊤) ≃+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  haveI : RingHomInvPair (e : Γ(Spec (CommRingCat.of R), ⊤) →+* R) (e.symm : R →+* _) :=
    RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : R →+* _) (e : Γ(Spec (CommRingCat.of R), ⊤) →+* R) :=
    RingHomInvPair.symm _ _
  let e₂ : Γ(E, ⊤) ≃ₛₗ[(e : Γ(Spec (CommRingCat.of R), ⊤) →+* R)]
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj E) :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change c • x = ((Spec (CommRingCat.of R)).presheaf.map (⊤ : (Spec (CommRingCat.of R)).Opens).leTop.op)
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (e c)) • x
        have h1 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv (e c) = c := by
          change ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv) c = c
          rw [Iso.hom_inv_id]; rfl
        have h2 : (⊤ : (Spec (CommRingCat.of R)).Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
        rw [h1, h2, op_id, CategoryTheory.Functor.map_id]
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Projective.of_equiv e₂



-- @@ L79-96 verbatim
/-- A homomorphism into a presented Grothendieck group hitting every generator is surjective. -/
theorem surjective_of_classOf {O : Type*} {Ex : O → O → O → Prop} {B : Type*} [AddCommGroup B]
    (φ : B →+ ExactGrothendieck.Group O Ex)
    (h : ∀ x, ∃ b, φ b = ExactGrothendieck.classOf O Ex x) : Function.Surjective φ := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
  induction z using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, by rw [map_add, hp, hq, map_add]⟩
  | single x n =>
      obtain ⟨b, hb⟩ := h x
      refine ⟨n • b, ?_⟩
      rw [map_zsmul, hb]
      change n • (QuotientAddGroup.mk' _ (Finsupp.single x 1)) = _
      rw [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]



-- @@ L99-102 verbatim
theorem finite_moduleSpecΓ (E : (Spec (CommRingCat.of R)).Modules) [E.IsFinitePresentation] :
    Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj E) := by
  haveI := moduleSpecΓ_isFinitePresentation E
  infer_instance


-- @@ L104-107 verbatim
theorem finite_moduleSpecΓ_of_isCoherentLike (E : (Spec (CommRingCat.of R)).Modules)
    (hE : IsCoherentLike X E) : Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj E) := by
  haveI : E.IsFinitePresentation := hE
  exact finite_moduleSpecΓ R E


-- @@ L109-110 verbatim
theorem tilde_isQuasicoherent (M : ModuleCat.{u} R) : ((tilde.functor (CommRingCat.of R)).obj M).IsQuasicoherent :=
  (inferInstance : (tilde (R := CommRingCat.of R) M).IsQuasicoherent)


-- @@ L112-114 verbatim
/-- The unit isomorphism `M ≅ Γ(M~)` as a linear equivalence. -/
def unitEquiv (M : ModuleCat.{u} R) : M ≃ₗ[R] ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj ((tilde.functor (CommRingCat.of R)).obj M)) :=
  ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M).toLinearEquiv


-- @@ L116-126 verbatim
/-- Global sections, `G₀(Spec R) → G₀(R)`. -/
def gammaG : G0 X →+ ModuleResolution.G0 R :=
  ExactGrothendieck.map
    (fun E => ⟨(moduleSpecΓFunctor (R := CommRingCat.of R)).obj E.1, finite_moduleSpecΓ_of_isCoherentLike R E.1 E.2⟩)
    (by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨f, g, zero, hS⟩
      haveI : A.IsFinitePresentation := hA
      haveI : B.IsFinitePresentation := hB
      haveI : C.IsFinitePresentation := hC
      have h := (moduleSpecΓ_map_shortExact_iff (ShortComplex.mk f g zero)).mpr hS
      exact ⟨_, _, _, h⟩)


-- @@ L128-128 verbatim
variable [IsNoetherianRing R]


-- @@ L130-136 verbatim
theorem tilde_isFinitePresentation (M : ModuleCat.{u} R) [Module.Finite R M] :
    ((tilde.functor (CommRingCat.of R)).obj M).IsFinitePresentation := by
  haveI := tilde_isQuasicoherent R M
  haveI : Module.FinitePresentation R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj ((tilde.functor (CommRingCat.of R)).obj M)) := by
    haveI := Module.finitePresentation_of_finite R M
    exact Module.FinitePresentation.of_equiv (unitEquiv R M)
  exact isFinitePresentation_of_moduleSpecΓ _


-- @@ L138-144 verbatim
omit [IsNoetherianRing R] in
theorem tilde_isFiniteLocallyFree (M : ModuleCat.{u} R) [Module.Finite R M]
    [Module.Projective R M] : IsFiniteLocallyFree X ((tilde.functor (CommRingCat.of R)).obj M) := by
  haveI := tilde_isQuasicoherent R M
  haveI : Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj ((tilde.functor (CommRingCat.of R)).obj M)) := Module.Finite.equiv (unitEquiv R M)
  haveI : Module.Projective R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj ((tilde.functor (CommRingCat.of R)).obj M)) := Module.Projective.of_equiv (unitEquiv R M)
  exact SchemeProjectiveSpace.isFiniteLocallyFree_of_globalSections_projective _


-- @@ L146-149 verbatim
theorem tilde_isFinitePresentation' (M : ModuleCat.{u} R) (hM : ModuleResolution.IsFG R M) :
    IsCoherentLike X ((tilde.functor (CommRingCat.of R)).obj M) := by
  haveI : Module.Finite R M := hM
  exact tilde_isFinitePresentation R M


-- @@ L151-156 verbatim
omit [IsNoetherianRing R] in
theorem tilde_isFiniteLocallyFree' (M : ModuleCat.{u} R) (hM : ModuleResolution.IsFGProj R M) :
    IsFiniteLocallyFree X ((tilde.functor (CommRingCat.of R)).obj M) := by
  haveI : Module.Finite R M := hM.1
  haveI : Module.Projective R M := hM.2
  exact tilde_isFiniteLocallyFree R M


-- @@ L158-164 verbatim
/-- The tilde construction, `G₀(R) → G₀(Spec R)`. -/
def tildeG : ModuleResolution.G0 R →+ G0 X :=
  ExactGrothendieck.map
    (fun M => ⟨(tilde.functor (CommRingCat.of R)).obj M.1, tilde_isFinitePresentation' R M.1 M.2⟩)
    (by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨f, g, zero, hS⟩
      exact ⟨_, _, _, tilde_map_shortExact (ShortComplex.mk f g zero) hS⟩)


-- @@ L166-172 verbatim
/-- The tilde construction, `K₀(R) → K₀(Spec R)`. -/
def tildeK : ModuleResolution.K0 R →+ K0 X :=
  ExactGrothendieck.map
    (fun M => ⟨(tilde.functor (CommRingCat.of R)).obj M.1, tilde_isFiniteLocallyFree' R M.1 M.2⟩)
    (by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨f, g, zero, hS⟩
      exact ⟨_, _, _, tilde_map_shortExact (ShortComplex.mk f g zero) hS⟩)


-- @@ L174-180 verbatim
theorem k0ToG0_comp_tildeK :
    (k0ToG0 X).comp (tildeK R) = (tildeG R).comp (ModuleResolution.k0ToG0 R) := by
  apply ExactGrothendieck.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, tildeK, tildeG, k0ToG0, ModuleResolution.k0ToG0,
    ExactGrothendieck.map_classOf]
  rfl


-- @@ L182-190 verbatim
theorem gammaG_comp_tildeG : (gammaG R).comp (tildeG R) = AddMonoidHom.id _ := by
  apply ExactGrothendieck.hom_ext
  rintro ⟨M, hM⟩
  simp only [AddMonoidHom.comp_apply, tildeG, gammaG, ExactGrothendieck.map_classOf,
    AddMonoidHom.id_apply]
  haveI : Module.Finite R M := hM
  exact (ExactGrothendieck.subcategoryClassOf_iso (ModuleCat.{u} R) (ModuleResolution.IsFG R)
    _ hM (show Module.Finite R (ModuleCat.of R PUnit.{u + 1}) from inferInstance)
    (ModuleCat.isZero_of_subsingleton _) ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M).symm)


-- @@ L192-204 verbatim
theorem tildeG_comp_gammaG : (tildeG R).comp (gammaG R) = AddMonoidHom.id _ := by
  apply ExactGrothendieck.hom_ext
  rintro ⟨E, hE⟩
  simp only [AddMonoidHom.comp_apply, tildeG, gammaG, ExactGrothendieck.map_classOf,
    AddMonoidHom.id_apply]
  haveI : E.IsFinitePresentation := hE
  exact ExactGrothendieck.subcategoryClassOf_iso _ (IsCoherentLike X) _ hE
    (show (0 : (Spec (CommRingCat.of R)).Modules).IsFinitePresentation from inferInstance)
    (isZero_zero _) (by
      haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) E) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) E
      let i := asIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) E)
      exact i)


-- @@ L206-219 verbatim
omit [IsNoetherianRing R] in
theorem tildeK_surjective : Function.Surjective (tildeK R) := by
  apply surjective_of_classOf
  rintro ⟨E, hE⟩
  haveI : E.IsFinitePresentation := hE.isFinitePresentation
  haveI := finite_moduleSpecΓ R E
  haveI := projective_moduleSpecΓ_of_isFiniteLocallyFree R E hE
  refine ⟨ExactGrothendieck.subcategoryClassOf _ (ModuleResolution.IsFGProj R) ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj E)
    ⟨inferInstance, inferInstance⟩, ?_⟩
  simp only [tildeK, ExactGrothendieck.subcategoryClassOf, ExactGrothendieck.map_classOf]
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) E) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) E
  let i := asIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) E)
  exact k0ClassOf_iso X _ hE i


-- @@ L221-238 verbatim
/-- **Affine resolution theorem, conditional form.** -/
theorem k0ToG0_bijective_of_hasProjectiveDimensionLE (d : ℕ)
    (hd : ∀ M : ModuleCat.{u} R, Module.Finite R M → HasProjectiveDimensionLE M d) :
    Function.Bijective (k0ToG0 X) := by
  have hφ := ModuleResolution.k0ToG0_bijective_of_hasProjectiveDimensionLE d hd
  have hT : Function.Bijective (tildeG R) :=
    ⟨Function.LeftInverse.injective (g := gammaG R) (DFunLike.congr_fun (gammaG_comp_tildeG R)),
     Function.RightInverse.surjective (g := gammaG R) (DFunLike.congr_fun (tildeG_comp_gammaG R))⟩
  have hc : ∀ y, k0ToG0 X (tildeK R y) = tildeG R (ModuleResolution.k0ToG0 R y) :=
    DFunLike.congr_fun (k0ToG0_comp_tildeK R)
  refine ⟨fun a b hab => ?_, fun z => ?_⟩
  · obtain ⟨a', rfl⟩ := tildeK_surjective R a
    obtain ⟨b', rfl⟩ := tildeK_surjective R b
    rw [hc, hc] at hab
    rw [hφ.1 (hT.1 hab)]
  · obtain ⟨w, rfl⟩ := hT.2 z
    obtain ⟨y, rfl⟩ := hφ.2 w
    exact ⟨tildeK R y, hc y⟩



-- @@ L241-241 verbatim
end RegularAffineK0G0


-- @@ L243-243 verbatim
section Regular


-- @@ L245-245 verbatim
variable (R : Type u) [CommRing R] [IsRegularRing R]


-- @@ L247-252 verbatim
/-- **Module-level resolution theorem for regular rings.** For a regular ring of finite Krull
dimension, `K₀(R) → G₀(R)` (projective vs. finitely generated modules) is bijective. -/
theorem ModuleResolution.k0ToG0_bijective_of_isRegularRing (d : ℕ) (hd : ringKrullDim R ≤ d) :
    Function.Bijective (ModuleResolution.k0ToG0 R) :=
  ModuleResolution.k0ToG0_bijective_of_hasProjectiveDimensionLE d
    fun M _ => IsRegularRing.hasProjectiveDimensionLE d hd M


-- @@ L254-259 verbatim
/-- **Affine resolution theorem.** For a regular ring `R` of finite Krull dimension,
`K₀(Spec R) → G₀(Spec R)` is bijective. -/
theorem SchemeKTheory.k0ToG0_bijective_spec_of_isRegularRing (d : ℕ) (hd : ringKrullDim R ≤ d) :
    Function.Bijective (k0ToG0 (Spec (CommRingCat.of R))) :=
  RegularAffineK0G0.k0ToG0_bijective_of_hasProjectiveDimensionLE R d
    fun M _ => IsRegularRing.hasProjectiveDimensionLE d hd M


-- @@ L261-266 verbatim
/-- **`K₀ ≅ G₀` on `ℙⁿ_R` over a regular base** of finite Krull dimension (`0 < n`). -/
theorem SchemeProjectiveSpace.k0ToG0_bijective_of_isRegularRing (d : ℕ)
    (hd : ringKrullDim R ≤ d) (n : ℕ) (hn : 0 < n) :
    Function.Bijective (k0ToG0 (SchemeProjectiveSpace.space R n)) :=
  SchemeProjectiveSpace.k0ToG0_bijective_of_base R n hn
    (SchemeKTheory.k0ToG0_bijective_spec_of_isRegularRing R d hd)


-- @@ L268-268 verbatim
end Regular

