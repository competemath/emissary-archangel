import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.Topology.Sheaves.AddCommGrpCat


-- @@ L5-12 verbatim
/-!
# The additive sheaf underlying a scheme module

This is the narrow scheme-module bridge used by sheaf cohomology. It follows the API
proposed upstream in mathlib PR #36345: forget the module structure, then sheafify the
underlying additive presheaf. The resulting functor is additive, faithful, and preserves
finite limits and all colimits.
-/


-- @@ L14-14 verbatim
open CategoryTheory Limits TopologicalSpace


-- @@ L16-16 verbatim
universe u v u₁ u₂ u₃ v₁ v₂ v₃


-- @@ L18-34 verbatim
private theorem preservesColimitsOfShape_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    {J : Type u} [Category.{v} J] (F : C ⥤ E)
    [PreservesColimitsOfShape J ((reflector R) ⋙ F)] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  refine @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _
    (NatIso.hcomp (asIso (𝟙 K)) (asIso (reflectorAdjunction R).counit).symm).symm
      ⟨fun hc ↦ ⟨?_⟩⟩
  let hc₂ := colimit.isColimit (K ⋙ R)
  let ψ := IsColimit.uniqueUpToIso (isColimitOfPreserves (reflector R) hc₂) hc
  have φ := IsColimit.ofIsoColimit (isColimitOfPreserves (reflector R ⋙ F) hc₂)
    (Functor.mapCoconeMapCocone (H := reflector R) (H' := F)
      (colimit.cocone (K ⋙ R))).symm
  exact IsColimit.ofIsoColimit φ ((Cocone.functoriality _ F).mapIso ψ)


-- @@ L36-41 verbatim
private theorem preservesColimitsOfSize_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    (F : C ⥤ E) [PreservesColimitsOfSize.{v, u} ((reflector R) ⋙ F)]
    [HasColimitsOfSize.{v, u} D] : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape := preservesColimitsOfShape_of_reflector_comp R F


-- @@ L43-43 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L45-45 verbatim
variable {X : Scheme.{u}} (M : X.Modules)


-- @@ L47-51 verbatim
variable (X) in
/-- The additive sheaf underlying a scheme module. -/
@[simps!]
noncomputable def toSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat X :=
  SheafOfModules.toSheaf X.ringCatSheaf


-- @@ L53-54 verbatim
instance : (toSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive


-- @@ L56-57 verbatim
instance : PreservesFiniteLimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))


-- @@ L59-60 verbatim
instance : (toSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful


-- @@ L62-70 verbatim
instance : PreservesColimitsOfSize.{v, u} (toSheaf X) := by
  letI : Reflective (toPresheafOfModules X) :=
    { L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
      adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj) }
  have : PreservesColimitsOfSize.{v, u}
      (reflector (toPresheafOfModules X) ⋙ toSheaf X) :=
    comp_preservesColimits (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
  exact preservesColimitsOfSize_of_reflector_comp (toPresheafOfModules X) _


-- @@ L72-72 verbatim
instance : PreservesColimits (toSheaf X) where


-- @@ L74-75 verbatim
/-- The additive sheaf underlying a scheme module. -/
noncomputable abbrev sheaf : TopCat.Sheaf AddCommGrpCat X := (toSheaf X).obj M


-- @@ L77-80 verbatim
/-- The additive-sheaf morphism underlying a morphism of scheme modules. -/
noncomputable abbrev Hom.sheafHom {M N : X.Modules} (f : M ⟶ N) :
    M.sheaf ⟶ N.sheaf :=
  (toSheaf X).map f


-- @@ L82-82 verbatim
end AlgebraicGeometry.Scheme.Modules
