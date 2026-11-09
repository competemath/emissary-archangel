import ModularCurves.GroupScheme.TranslationAction


-- @@ L3-15 verbatim
/-!
# The action shear and stability of the complement of `G`

Construction support for `[CHARTER-HOPF]` Wave C leaf `[HG-C3b]`
(`.mathlib-quality/decomposition-hopf-c3-cover.md`). The **action shear**
`actionShear : G ×_S E ≅ G ×_S E`, `(t, x) ↦ (t, x + ι t)`, is an automorphism of the square
(pure group-object algebra, inverse `(t, x) ↦ (t, x − ι t)`) that carries the projection leg to
the translation leg: `actionShear.hom ≫ actionProj = translationAction`. It repackages the
stability predicate for the `[HG-C3]` cover.

## Main definitions
* `FiniteLocallyFreeSubgroup.actionShear` — the shear automorphism of `G ×_S E`.
-/


-- @@ L17-17 verbatim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj


-- @@ L19-20 verbatim
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
namespace ModularCurves


-- @@ L26-26 verbatim
namespace EllipticCurve


-- @@ L28-28 verbatim
variable {S : Scheme.{u}} {E : EllipticCurve S}


-- @@ L30-30 verbatim
namespace FiniteLocallyFreeSubgroup


-- @@ L32-36 verbatim
/-- The **action shear** `(t, x) ↦ (t, x + ι t)` on `G ×_S E`, in hom form: identity on the
`G`-factor, translation on the `E`-factor. -/
noncomputable def actionShearHom (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ (Over.mk G.π) ⊗ E.asOver :=
  lift (fst (Over.mk G.π) E.asOver) G.translationAction


-- @@ L38-43 verbatim
/-- The inverse action shear `(t, x) ↦ (t, x − ι t)`. -/
noncomputable def actionUnshearHom (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ (Over.mk G.π) ⊗ E.asOver :=
  letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
  lift (fst (Over.mk G.π) E.asOver)
    ((fst (Over.mk G.π) E.asOver ≫ G.ιOver)⁻¹ * snd (Over.mk G.π) E.asOver)


-- @@ L45-48 verbatim
@[reassoc (attr := simp)]
theorem actionShearHom_fst (G : FiniteLocallyFreeSubgroup E) :
    G.actionShearHom ≫ fst (Over.mk G.π) E.asOver = fst (Over.mk G.π) E.asOver :=
  lift_fst _ _


-- @@ L50-53 verbatim
@[reassoc (attr := simp)]
theorem actionShearHom_snd (G : FiniteLocallyFreeSubgroup E) :
    G.actionShearHom ≫ snd (Over.mk G.π) E.asOver = G.translationAction :=
  lift_snd _ _


-- @@ L55-58 verbatim
@[reassoc (attr := simp)]
theorem actionUnshearHom_fst (G : FiniteLocallyFreeSubgroup E) :
    G.actionUnshearHom ≫ fst (Over.mk G.π) E.asOver = fst (Over.mk G.π) E.asOver :=
  lift_fst _ _


-- @@ L60-65 verbatim
@[reassoc (attr := simp)]
theorem actionUnshearHom_snd (G : FiniteLocallyFreeSubgroup E) :
    letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    G.actionUnshearHom ≫ snd (Over.mk G.π) E.asOver
      = (fst (Over.mk G.π) E.asOver ≫ G.ιOver)⁻¹ * snd (Over.mk G.π) E.asOver :=
  lift_snd _ _


-- @@ L67-85 verbatim
/-- **The action shear automorphism** of `G ×_S E`: `(t, x) ↦ (t, x + ι t)`, inverse the
unshear. The inverse laws are pure hom-group algebra (`translationAction_eq_mul`). -/
noncomputable def actionShear (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ≅ (Over.mk G.π) ⊗ E.asOver where
  hom := G.actionShearHom
  inv := G.actionUnshearHom
  hom_inv_id := by
    letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.id_comp, actionUnshearHom_fst, actionShearHom_fst]
    · rw [Category.assoc, Category.id_comp, actionUnshearHom_snd, MonObj.comp_mul,
        GrpObj.comp_inv, actionShearHom_fst_assoc, actionShearHom_snd, G.translationAction_eq_mul,
        inv_mul_cancel_left]
  inv_hom_id := by
    letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.id_comp, actionShearHom_fst, actionUnshearHom_fst]
    · rw [Category.assoc, Category.id_comp, actionShearHom_snd, G.translationAction_eq_mul,
        MonObj.comp_mul, actionUnshearHom_fst_assoc, actionUnshearHom_snd, mul_inv_cancel_left]


-- @@ L87-93 verbatim
/-- **The shear carries the projection leg to the translation leg**: the geometric content
`act = pr ∘ shear`, `(t,x) ↦ x + ι t`. -/
@[reassoc]
theorem actionShear_hom_comp_actionProj (G : FiniteLocallyFreeSubgroup E) :
    G.actionShear.hom ≫ G.actionProj = G.translationAction := by
  rw [actionShear, actionProj]
  exact G.actionShearHom_snd


-- @@ L95-95 verbatim
end FiniteLocallyFreeSubgroup


-- @@ L97-97 verbatim
end EllipticCurve


-- @@ L99-99 verbatim
end ModularCurves
