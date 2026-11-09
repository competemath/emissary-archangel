import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Topology.Sheaves.Flasque


-- @@ L4-10 verbatim
/-!
# Restriction of sheaves to an open subspace

This file supplies the restriction functor along an open embedding, its adjunction with
pushforward, and the exactness properties needed to restrict short exact sequences of sheaves of
abelian groups.
-/


-- @@ L12-15 verbatim
open CategoryTheory Limits Opposite TopologicalSpace Topology

-- v4.33 bump: neither the category instances nor the semireducible component types are
-- transparent enough for the `show`/`rfl`/`rw` steps below at `implicit` transparency.

-- @@ L16-16 verbatim
set_option backward.defeqAttrib.useBackward true

-- @@ L17-17 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L18-18 verbatim
set_option backward.isDefEq.respectTransparency.types false


-- @@ L20-20 verbatim
universe u v w


-- @@ L22-23 verbatim
variable (C : Type v) [Category.{w} C] {X Y : TopCat.{u}} {f : Y ⟶ X}
  (hf : IsOpenEmbedding f)


-- @@ L25-25 verbatim
namespace TopCat.Sheaf


-- @@ L27-30 verbatim
/-- Restriction of sheaves along an open embedding. -/
abbrev restrict : Sheaf C X ⥤ Sheaf C Y :=
  haveI := hf.functor_isContinuous
  hf.functor.sheafPushforwardContinuous C ..


-- @@ L32-35 verbatim
/-- Restriction along an open embedding is left adjoint to pushforward. -/
abbrev restrictPushforwardAdjunction : restrict C hf ⊣ pushforward C f :=
  haveI := hf.functor_isContinuous
  Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..


-- @@ L37-38 verbatim
instance restrict_isLeftAdjoint : (restrict C hf).IsLeftAdjoint :=
  (restrictPushforwardAdjunction C hf).isLeftAdjoint


-- @@ L40-40 verbatim
variable (F : Sheaf C X) (U V : Opens X)


-- @@ L42-43 verbatim
/-- The adjunction unit from a sheaf to the pushforward of its restriction to an open. -/
abbrev toRestrict := (restrictPushforwardAdjunction C U.isOpenEmbedding).unit


-- @@ L45-47 verbatim
lemma toRestrict_obj_obj_obj :
    ((restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').obj F).obj.obj (op V) =
      F.obj.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V))) := rfl


-- @@ L49-52 verbatim
lemma toRestrict_app_hom_app :
    ((toRestrict C U).app F).hom.app (op V) =
      F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by
  simp


-- @@ L54-68 verbatim
private lemma restrict_comp_sheafToPresheaf_preservesFiniteLimits
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    PreservesFiniteLimits
      (restrict AddCommGrpCat.{u} hf ⋙
        sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := by
  letI := hf.functor_isContinuous
  letI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        hf.functor.op) := inferInstance
  change PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft _ _ _).obj hf.functor.op)
  exact comp_preservesFiniteLimits _ _


-- @@ L70-74 verbatim
private lemma sheafToPresheaf_reflectsFiniteShape
    {Y : TopCat.{u}} (J : Type) [SmallCategory J] [FinCategory J] :
    ReflectsLimitsOfShape J
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := by
  infer_instance


-- @@ L76-90 verbatim
/-- Restriction of sheaves of abelian groups along an open embedding preserves finite limits. -/
instance restrict_preservesFiniteLimits
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    PreservesFiniteLimits (restrict AddCommGrpCat.{u} hf) := by
  letI := restrict_comp_sheafToPresheaf_preservesFiniteLimits hf
  constructor
  intro J _ _
  have hPreserve : PreservesLimitsOfShape J
      (restrict AddCommGrpCat.{u} hf ⋙
        sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := inferInstance
  have hReflect := sheafToPresheaf_reflectsFiniteShape (Y := Y) J
  exact @preservesLimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _
    (restrict AddCommGrpCat.{u} hf)
    (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    hPreserve hReflect


-- @@ L92-98 verbatim
/-- Restriction of sheaves of abelian groups is additive. -/
instance restrict_additive {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    (restrict AddCommGrpCat.{u} hf).Additive where
  map_add := by
    intros
    apply CategoryTheory.Sheaf.hom_ext
    rfl


-- @@ L100-106 verbatim
/-- Pushforward of sheaves of abelian groups is additive. -/
instance pushforward_additive {X Y : TopCat.{u}} (f : Y ⟶ X) :
    (pushforward AddCommGrpCat.{u} f).Additive where
  map_add := by
    intros
    apply CategoryTheory.Sheaf.hom_ext
    rfl


-- @@ L108-114 verbatim
/-- Restriction of a flasque sheaf to an open subspace is flasque. -/
theorem IsFlasque.of_restrict {X Y : TopCat.{u}} {f : Y ⟶ X}
    (F : Sheaf C X) [F.IsFlasque] (hf : IsOpenEmbedding f) :
    ((restrict C hf).obj F).IsFlasque where
  epi i := by
    change Epi (F.obj.map (hf.functor.op.map i))
    infer_instance


-- @@ L116-116 verbatim
end TopCat.Sheaf
