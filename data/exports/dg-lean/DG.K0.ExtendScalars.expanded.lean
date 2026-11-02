import DG.Category.Derived.ExtendScalars
import DG.K0.DGRing


-- @@ L4-12 verbatim
/-!
# `K₀` of a morphism of dg rings on K-projective compact modules

For a morphism of dg rings `φ : B → A`, the map `K₀(φ) : K₀(B) → K₀(A)` (`DG.DGRing.K0.map`) is
induced by derived induction. On the class of a K-projective dg module `P` which is compact in
`D(B)`, it is the class of the extension of scalars `A ⊗_B P`
(`DG.DGRing.K0.map_mk_of_isKProjective`), which is compact in `D(A)`
(`DG.DGRingHom.isCompact_Q_extendScalars_obj`).
-/


-- @@ L14-14 verbatim
open CategoryTheory


-- @@ L16-16 verbatim
universe w₁ w₂ u


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace DG


-- @@ L22-25 expanded
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [HasDerivedCategory.{w₁, u} B] [HasDerivedCategory.{w₂, u} A] (φ : DGRingHom B A)
  {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P)
  (hc : IsCompact.{u} (DerivedCategory.Q.obj P))


-- @@ L27-27 verbatim
namespace DGRingHom


-- @@ L29-36 verbatim
include hc in
/-- The object of `D(SingleObj B)` corresponding to a compact object of `D(B)` is compact. -/
theorem isCompact_singleObjEquivalence_inverse_obj
    [CatModule.HasDerivedCategory.{u, u} (SingleObj B)] :
    IsCompact.{u} ((CatModule.DerivedCategory.singleObjEquivalence B).inverse.obj
      (DerivedCategory.Q.obj P)) :=
  (isCompact_functor_obj_iff (CatModule.DerivedCategory.singleObjEquivalence B) _).mp
    (hc.of_iso ((CatModule.DerivedCategory.singleObjEquivalence B).counitIso.app _))


-- @@ L38-48 verbatim
include hP hc in
/-- Extension of scalars of a K-projective dg module which is compact in `D(B)` is compact in
`D(A)`: it is its derived induction (`DG.DGRingHom.derivedInductionObjIso`). -/
theorem isCompact_Q_extendScalars_obj :
    IsCompact.{u} (DerivedCategory.Q.obj ((DGModuleCat.extendScalars.{u} φ).obj P)) := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  exact ((CatModule.DerivedCategory.isCompact_induction_obj φ.singleObjFunctor
    (isCompact_singleObjEquivalence_inverse_obj hc)).map_of_equivalence
      (CatModule.DerivedCategory.singleObjEquivalence A)).of_iso
    (φ.derivedInductionObjIso hP).symm


-- @@ L50-50 verbatim
end DGRingHom


-- @@ L52-52 verbatim
namespace DGRing.K0


-- @@ L54-75 verbatim
include hP in
/-- **`K₀(φ)` on K-projective modules**: for a K-projective dg `B`-module `P` compact in `D(B)`,
`K₀(φ) [P] = [A ⊗_B P]`. -/
theorem map_mk_of_isKProjective :
    map φ (DG.K0.mk (⟨DerivedCategory.Q.obj P, hc⟩ : PerfectDerivedCategory B)) =
      DG.K0.mk (⟨DerivedCategory.Q.obj ((DGModuleCat.extendScalars.{u} φ).obj P),
        φ.isCompact_Q_extendScalars_obj hP hc⟩ : PerfectDerivedCategory A) := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  let y : DGCategory.K0 (SingleObj B) :=
    DG.K0.mk (⟨_, DGRingHom.isCompact_singleObjEquivalence_inverse_obj hc⟩ :
      CatModule.PerfectDerivedCategory (SingleObj B))
  have h1 : (DG.K0.mk (⟨DerivedCategory.Q.obj P, hc⟩ : PerfectDerivedCategory B)) =
      singleObjEquiv B y := by
    rw [singleObjEquiv, DG.K0.compactMapEquiv_mk]
    exact DG.K0.mk_eq_of_iso_obj
      ((CatModule.DerivedCategory.singleObjEquivalence B).counitIso.app _).symm
  rw [h1]
  change singleObjEquiv A (DGCategory.K0.map φ.singleObjFunctor
    ((singleObjEquiv B).symm (singleObjEquiv B y))) = _
  rw [AddEquiv.symm_apply_apply, DGCategory.K0.map_mk, singleObjEquiv, DG.K0.compactMapEquiv_mk]
  exact DG.K0.mk_eq_of_iso_obj (φ.derivedInductionObjIso hP)


-- @@ L77-77 verbatim
end DGRing.K0


-- @@ L79-79 verbatim
end DG


-- @@ L81-81 verbatim
end
