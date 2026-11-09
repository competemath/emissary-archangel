import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward


-- @@ L3-8 verbatim
/-!
# Local isomorphisms and pushforward

This file proves that pushforward preserves a module morphism which is an isomorphism over the
inverse image of a target open.
-/


-- @@ L10-10 verbatim
universe u


-- @@ L12-12 verbatim
open CategoryTheory TopologicalSpace


-- @@ L14-14 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-60 verbatim
/-- If a morphism of modules is an isomorphism over the inverse image of an open, then its
pushforward is an isomorphism over that open. -/
theorem isIso_restrict_pushforward_map_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {M N : X.Modules} (α : M ⟶ N)
    [IsIso ((restrictFunctor (f ⁻¹ᵁ U).ι).map α)] :
    IsIso
      ((restrictFunctor U.ι).map
        ((pushforward f).map α)) := by
  let e :
      pushforward f ⋙ restrictFunctor U.ι ≅
        restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) :=
    restrictPushforwardIsoOfIsPullback f (f ∣_ U)
      (f ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict f U)
  haveI hRight :
      IsIso
        ((pushforward (f ∣_ U)).map
          ((restrictFunctor (f ⁻¹ᵁ U).ι).map α)) :=
    inferInstance
  haveI hConjugate :
      IsIso
        (e.hom.app M ≫
          ((pushforward (f ∣_ U)).map
            ((restrictFunctor (f ⁻¹ᵁ U).ι).map α))) :=
    IsIso.comp_isIso' (e.app M).isIso_hom hRight
  haveI hComposite :
      IsIso
        ((restrictFunctor U.ι).map
            ((pushforward f).map α) ≫
          e.hom.app N) := by
    change
      IsIso
        ((pushforward f ⋙ restrictFunctor U.ι).map α ≫
          e.hom.app N)
    rw [e.hom.naturality α]
    exact hConjugate
  exact
    @IsIso.of_isIso_comp_right _ _ _ _ _
      ((restrictFunctor U.ι).map
        ((pushforward f).map α))
      (e.hom.app N)
      (e.app N).isIso_hom
      hComposite


-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
end AlgebraicGeometry.Scheme.Modules
