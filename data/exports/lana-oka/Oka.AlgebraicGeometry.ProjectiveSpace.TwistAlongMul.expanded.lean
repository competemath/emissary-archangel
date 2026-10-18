/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Modules.QuasicoherentSections
import Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreMorphism


-- @@ L9-22 verbatim
/-!
# Multiplication by a power of a coordinate along a morphism to projective space

For a cocycle `d` on an open cover `U` of a scheme `X` and a global section `h = (hᵢ)` of the
line bundle `L_d` (`hᵢ = dᵢⱼ hⱼ`), multiplication by `h` is a morphism `F ⟶ F ⊗ L_d`
(`AlgebraicGeometry.Scheme.Modules.mulSection`). If `h_l = 1`, it is bijective on sections over
every open contained in `U_l` (`AlgebraicGeometry.Scheme.Modules.mulSection_app_bijective`).

For a morphism `j : Y' ⟶ ℙ(n; K)` and `m : ℕ`, the pullbacks along `j` of the sections
`(Xₗ / Xᵢ)ᵐ` form such a global section of the pullback of `O(m)`, giving multiplication by
`Xₗᵐ`, `G ⟶ G(m) = G ⊗ j^* O(m)` (`AlgebraicGeometry.ProjectiveSpace.mulXPowAlong`). It is
bijective on sections over opens contained in `j⁻¹ D₊(Xₗ)`
(`AlgebraicGeometry.ProjectiveSpace.mulXPowAlong_app_bijective`).
-/


-- @@ L24-24 verbatim
open CategoryTheory TopologicalSpace


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L30-30 verbatim
variable {X : Scheme.{u}}


-- @@ L32-39 verbatim
/-- An isomorphism of sheaves of modules is bijective on sections. -/
lemma bijective_app_of_iso {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    Function.Bijective (e.hom.app V) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app V, fun s ↦ ?_, fun s ↦ ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app]
    rfl


-- @@ L41-42 expanded
variable {ι : Type} {U : ι → X.Opens} (F : X.Modules) (c d : Cocycle U) (h : ∀ i, Γ(X, U i))
  (hh :
    ∀ i j,
      (TopCat.Presheaf.restrictOpen (h i) (U i ⊓ U j) (by order)) =
        d.g i j * (TopCat.Presheaf.restrictOpen (h j) (U i ⊓ U j) (by order)))


-- @@ L44-58 verbatim
/-- If `h_l = 1`, multiplication by `h` is bijective on sections over opens contained in
`U_l`. -/
lemma twistMulSection_app_bijective {l : ι} (hl : h l = 1) {V : X.Opens} (hV : V ≤ U l) :
    Function.Bijective ((twistMulSection F c d h hh).app V) := by
  have key : ∀ s, twistSectionsEquiv (c * d) l hV ((twistMulSection F c d h hh).app V s) =
      twistSectionsEquiv c l hV s := fun s ↦ by
    rw [twistSectionsEquiv_apply, twistSectionsEquiv_apply, twistComp_twistMulSection_app, hl,
      ores_one, one_smul]
  have e : ⇑((twistMulSection F c d h hh).app V) =
      (twistSectionsEquiv (c * d) l hV).symm ∘ twistSectionsEquiv c l hV := by
    funext s
    apply (twistSectionsEquiv (c * d) l hV).injective
    rw [Function.comp_apply, LinearEquiv.apply_symm_apply, key]
  rw [e]
  exact (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)


-- @@ L60-63 verbatim
/-- **Multiplication by a global section** `h = (hᵢ)` of `L_d`, `F ⟶ F ⊗ L_d`,
`t ↦ (hᵢ t)ᵢ`. -/
noncomputable def mulSection : F ⟶ twist F d :=
  toTwistOne F ≫ twistMulSection F 1 d h hh ≫ ((twistFunctorCongr (one_mul d)).app F).hom


-- @@ L65-73 verbatim
/-- If the `Uᵢ` cover `X` and `h_l = 1`, multiplication by `h` is bijective on sections over
opens contained in `U_l`. -/
lemma mulSection_app_bijective (hU : ⨆ i, U i = ⊤) {l : ι} (hl : h l = 1) {V : X.Opens}
    (hV : V ≤ U l) : Function.Bijective ((mulSection F d h hh).app V) := by
  have e : ⇑((mulSection F d h hh).app V) = ⇑(((twistFunctorCongr (one_mul d)).app F).hom.app V) ∘
      ⇑((twistMulSection F 1 d h hh).app V) ∘ ⇑((toTwistOne F).app V) := rfl
  rw [e]
  exact (bijective_app_of_iso _ V).comp
    ((twistMulSection_app_bijective F 1 d h hh hl hV).comp (toTwistOne_bijective hU V))


-- @@ L75-75 verbatim
variable {Y : Scheme.{u}} (φ : Y ⟶ X)


-- @@ L77-90 expanded
include hh in
/-- The pullback along `φ` of a global section of `L_d` is a global section of `L_{φ^♯ d}`. -/
lemma comap_mulSection_compat (i j : ι) :
    (TopCat.Presheaf.restrictOpen (φ.app (U i) (h i)) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) (by order)) =
      (d.comap φ).g i j *
        (TopCat.Presheaf.restrictOpen (φ.app (U j) (h j)) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) (by order)) :=
  by
  have e₁ :
    φ.app (U i ⊓ U j) (TopCat.Presheaf.restrictOpen (h i) (U i ⊓ U j) (by order)) =
      (TopCat.Presheaf.restrictOpen (φ.app (U i) (h i)) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) (by order)) :=
    app_ores φ inf_le_left (h i)
  have e₂ :
    φ.app (U i ⊓ U j) (TopCat.Presheaf.restrictOpen (h j) (U i ⊓ U j) (by order)) =
      (TopCat.Presheaf.restrictOpen (φ.app (U j) (h j)) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) (by order)) :=
    app_ores φ inf_le_right (h j)
  have e₃ : φ.app (U i ⊓ U j) (d.g i j) = (d.comap φ).g i j :=
    by
    rw [Cocycle.comap_g, Scheme.Hom.app_eq_appLE]
    rfl
  rw [← e₁, ← e₂, ← e₃, hh i j, map_mul]
  rfl


-- @@ L92-92 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L94-94 verbatim
namespace AlgebraicGeometry.ProjectiveSpace


-- @@ L96-96 verbatim
open Scheme.Modules


-- @@ L98-98 verbatim
variable {n : ℕ} {K : Type u} [CommRing K] {Y' : Scheme.{u}} (j : Y' ⟶ ℙ(n; K))


-- @@ L100-102 verbatim
/-- The preimages of the standard charts cover `Y'`. -/
lemma iSup_preimage_U : ⨆ i, j ⁻¹ᵁ U n K i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_U, Scheme.Hom.preimage_top]


-- @@ L104-108 expanded
/-- `(Xₗ / Xᵢ)ᵐ` on `Uᵢ = D₊(Xᵢ)`: a global section of `O(m)`. -/
lemma xDiv_pow_compat (m : ℕ) (l i i' : Fin (n + 1)) :
    (TopCat.Presheaf.restrictOpen (xDiv i l ^ m) (U n K i ⊓ U n K i') (by order)) =
      (cocycle n K ^ (m : ℤ)).g i i' *
        (TopCat.Presheaf.restrictOpen (xDiv i' l ^ m) (U n K i ⊓ U n K i') (by order)) :=
  by rw [ores_pow, ores_pow, zpow_natCast, Cocycle.pow_g, ← mul_pow, ← xDiv_compat]


-- @@ L110-116 verbatim
/-- **Multiplication by `Xₗᵐ` along `j`**, `G ⟶ G(m) = G ⊗ j^* O(m)`: on `j⁻¹ D₊(Xᵢ)` it is
multiplication by the pullback of `(Xₗ / Xᵢ)ᵐ`. -/
noncomputable def mulXPowAlong (G : Y'.Modules) (m : ℕ) (l : Fin (n + 1)) :
    G ⟶ twistAlong j G m :=
  mulSection G ((cocycle n K ^ (m : ℤ)).comap j) (fun i ↦ j.app (U n K i) (xDiv i l ^ m))
    (comap_mulSection_compat (cocycle n K ^ (m : ℤ)) (fun i ↦ xDiv i l ^ m)
      (xDiv_pow_compat m l) j)


-- @@ L118-123 verbatim
/-- Multiplication by `Xₗᵐ` along `j` is bijective on sections over opens contained in
`j⁻¹ D₊(Xₗ)`. -/
lemma mulXPowAlong_app_bijective (G : Y'.Modules) (m : ℕ) (l : Fin (n + 1)) {V : Y'.Opens}
    (hV : V ≤ j ⁻¹ᵁ U n K l) : Function.Bijective ((mulXPowAlong j G m l).app V) :=
  mulSection_app_bijective G _ _ _ (iSup_preimage_U j)
    (by simp only [xDiv_self, one_pow, map_one]) hV


-- @@ L125-125 verbatim
end AlgebraicGeometry.ProjectiveSpace
