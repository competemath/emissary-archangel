import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf


-- @@ L4-10 verbatim
/-!
# Limits and restriction of scheme modules

Restriction of modules along an open immersion preserves limits. This is the common categorical
input for affine-local constructions on quasicoherent modules and for descent of invertible
sheaves.
-/


-- @@ L12-12 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L14-14 verbatim
universe u


-- @@ L16-16 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-34 verbatim
private theorem presheafPushforward_preservesLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) :
    PreservesLimits (PresheafOfModules.pushforward.{u} φ) := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  intro c hc
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X => ?_)⟩
  let E := PresheafOfModules.evaluation R (F.op.obj X) ⋙
    ModuleCat.restrictScalars (φ.app X).hom
  exact isLimitOfPreserves E hc


-- @@ L36-51 verbatim
private theorem sheafPushforward_preservesLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [Functor.IsContinuous F J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesLimits (SheafOfModules.pushforward.{u} φ) := by
  letI : PreservesLimits
      (SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.forget S) := by
    change PreservesLimits (SheafOfModules.forget R ⋙
      PresheafOfModules.pushforward φ.hom)
    letI : PreservesLimits (PresheafOfModules.pushforward φ.hom) :=
      presheafPushforward_preservesLimits φ.hom
    exact comp_preservesLimits _ _
  exact preservesLimits_of_reflects_of_preserves
    (SheafOfModules.pushforward φ) (SheafOfModules.forget S)


-- @@ L53-58 verbatim
/-- Restriction of scheme modules along an open immersion preserves all limits. -/
theorem restrictFunctor_preservesLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimits (restrictFunctor f) := by
  dsimp only [restrictFunctor]
  apply sheafPushforward_preservesLimits


-- @@ L60-60 verbatim
end


-- @@ L62-62 verbatim
end AlgebraicGeometry.Scheme.Modules
