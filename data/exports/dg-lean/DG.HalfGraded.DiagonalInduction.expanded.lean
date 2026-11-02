import DG.HalfGraded.DiagonalK0Map
import DG.HalfGraded.Hom
import DG.K0.DGRing


-- @@ L5-26 verbatim
/-!
# Derived induction along diagonal morphisms

A morphism of dg rings `φ : A → B` induces a morphism of the diagonal half-graded dg rings
`Hom.ofDGRingHom φ : ofDGRing A → ofDGRing B` (the same map). Its weight dg functor
`F_w : C_{H_A} ⥤ C_{H_B}` satisfies `incl_A ⋙ F_w = φ_s ⋙ incl_B`, where
`incl = scalarInclusion _ 0 : SingleObj _ ⥤ C_H` is the weight-zero inclusion and
`φ_s = φ.singleObjFunctor` (`Diagonal.scalarInclusion_comp_weightFunctor`).

The diagonal functor `ι = toDerived A`, transported along `D(SingleObj A) ≌ D(A)`, is derived
induction along `incl_A` (`Diagonal.toDerivedInductionIso`): both are left adjoint to restriction
along `incl_A`, which is weight-zero recovery (`Diagonal.recoveryDerivedIso`). Consequently, on
`K₀`, `ι` is `K₀(incl_A)` (`Diagonal.mapCompactK0_singleObjEquiv`), and by functoriality of `K₀`
for dg functors the map `K₀(F_w)` of the induced morphism satisfies
`K₀(F_w) ∘ ι_A = ι_B ∘ K₀(φ)` (`Diagonal.K0Map_ofDGRingHom_mapCompactK0`). Under
`Diagonal.K0LinearEquiv` it is therefore `id ⊗ K₀(φ)`
(`Diagonal.K0LinearEquiv_K0Map_ofDGRingHom`), and likewise on `SuperK0c`
(`Diagonal.superK0LinearEquiv_superK0cMap_ofDGRingHom`).

All dg modules and derived Hom groups are taken in the universe of the rings, as in
`DG.DGRing.K0.map`.
-/


-- @@ L28-28 verbatim
open CategoryTheory Limits LaurentPolynomial TensorProduct


-- @@ L30-30 verbatim
universe u u₁ u₂ v₁ v₂ w w₂


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace DG


-- @@ L36-36 verbatim
namespace HalfGradedDGRing.Hom


-- @@ L38-39 verbatim
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]


-- @@ L41-50 expanded
/-- The morphism of diagonal half-graded dg rings induced by a morphism of dg rings. -/
def ofDGRingHom (φ : DGRingHom A B) : Hom (ofDGRing A) (ofDGRing B)
    where
  toRingHom := φ.toRingHom
  map_mem' {p a}
    ha :=
    by
    refine
      Diagonal.induction_on (P := fun a => φ a ∈ Diagonal.grading B p) ha
        (by rw [map_zero]; exact zero_mem _) (fun n a ha hn => ?_)
        (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    rw [← hn]
    exact Diagonal.mem_grading (φ.map_mem ha)
  map_hd' a := φ.map_d a


-- @@ L52-52 expanded
@[simp]
theorem ofDGRingHom_apply (φ : DGRingHom A B) (a : A) : ofDGRingHom φ a = φ a :=
  rfl


-- @@ L54-54 verbatim
end HalfGradedDGRing.Hom


-- @@ L56-56 verbatim
namespace Diagonal


-- @@ L58-58 verbatim
set_option backward.isDefEq.respectTransparency false


-- @@ L60-60 verbatim
section Functor


-- @@ L62-63 expanded
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : DGRingHom A B)


-- @@ L65-77 verbatim
theorem regraded_scalarHom (a : A) :
    (HalfGradedDGRing.Hom.ofDGRingHom φ).regraded (scalarHom A 0 a).1 =
      (scalarHom B 0 (φ a)).1 := by
  induction a using DG.induction_on with
  | h_zero => rw [map_zero, map_zero, map_zero]; rfl
  | h_homogeneous a =>
    rename_i n
    rw [scalarHom_homogeneous A 0 n a a.2, scalarHom_homogeneous B 0 n (φ a) (φ.map_mem a.2),
      HalfGradedDGRing.Hom.regraded_place]
    rfl
  | h_add a b ha hb =>
    rw [map_add, map_add, WeightCategory.add_val, map_add, ha, hb, map_add,
      WeightCategory.add_val]


-- @@ L79-85 verbatim
/-- `incl_A ⋙ F_w = φ_s ⋙ incl_B`. -/
theorem scalarInclusion_comp_weightFunctor :
    scalarInclusion A 0 ⋙ (HalfGradedDGRing.Hom.ofDGRingHom φ).weightFunctor =
      φ.singleObjFunctor ⋙ scalarInclusion B 0 :=
  CategoryTheory.Functor.ext (fun _ => by rfl) fun _ _ a => by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact WeightCategory.hom_ext (regraded_scalarHom φ a)


-- @@ L87-87 verbatim
end Functor


-- @@ L89-89 verbatim
section Adjoint


-- @@ L91-93 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{u, u} A]
  [CatModule.HasDerivedCategory.{u, u} (SingleObj A)]
  [CatModule.HasDerivedCategory.{u, u} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]


-- @@ L95-114 verbatim
/-- Weight-zero derived recovery is restriction along `incl_A`, followed by
`D(SingleObj A) ≌ D(A)`. -/
def recoveryDerivedIso : recoveryDerived.{u, u, u} A 0 ≅
    CatModule.DerivedCategory.restrict (scalarInclusion A 0) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor := by
  letI : Localization.Lifting CatModule.DerivedCategory.Qh
      (CatModule.HomotopyCategory.quasiIso
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
      (recoveryHomotopy A 0 ⋙ DerivedCategory.Qh)
      (CatModule.DerivedCategory.restrict (scalarInclusion A 0) ⋙
        (CatModule.DerivedCategory.singleObjEquivalence A).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatModule.DerivedCategory.QhCompRestrictIso _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.QhCompToDGDerivedCategoryIso A) ≪≫
      (Functor.associator _ _ _).symm⟩
  exact Localization.liftNatIso CatModule.DerivedCategory.Qh
    (CatModule.HomotopyCategory.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
    (recoveryHomotopy A 0 ⋙ DerivedCategory.Qh) (recoveryHomotopy A 0 ⋙ DerivedCategory.Qh) _ _
    (Iso.refl _)


-- @@ L116-128 verbatim
/-- The diagonal functor, transported along `D(SingleObj A) ≌ D(A)`, is derived induction along
the weight-zero inclusion: both are left adjoint to restriction along it. -/
def toDerivedInductionIso :
    (CatModule.DerivedCategory.singleObjEquivalence A).functor ⋙ toDerived.{u, u, u} A ≅
      CatModule.DerivedCategory.induction (scalarInclusion A 0) := by
  let e := CatModule.DerivedCategory.singleObjEquivalence A
  let R : CatModule.DerivedCategory.restrict (scalarInclusion A 0) ≅
      recoveryDerived.{u, u, u} A 0 ⋙ e.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (recoveryDerivedIso A).symm _
  exact (e.toAdjunction.comp (diagonalDerivedAdjunction.{u, u, u} A)).leftAdjointUniq
    ((CatModule.DerivedCategory.inductionAdjunction (scalarInclusion A 0)).ofNatIsoRight R)


-- @@ L130-141 verbatim
/-- On `K₀`, the diagonal functor is `K₀(incl_A)`. -/
theorem mapCompactK0_singleObjEquiv (z : DGCategory.K0.{u, u} (SingleObj A)) :
    mapCompactK0.{u, u, u} A (DGRing.K0.singleObjEquiv A z) =
      DGCategory.K0.map.{u, u} (scalarInclusion A 0) z := by
  induction z using K0.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | mk X =>
    rw [DGRing.K0.singleObjEquiv, DG.K0.compactMapEquiv_mk, mapCompactK0_mk,
      DGCategory.K0.map_mk]
    exact K0.mk_eq_of_iso_obj ((toDerivedInductionIso A).app X.obj)
  | neg x hx => rw [map_neg, map_neg, hx, map_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]


-- @@ L143-143 verbatim
end Adjoint


-- @@ L145-145 verbatim
section K0


-- @@ L147-155 verbatim
theorem _root_.DG.DGCategory.K0.map_congr_functor {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
    [CatModule.HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
    [CatModule.HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]
    {F G : C ⥤ D} [F.Additive] [F.IsDGFunctor] [G.Additive] [G.IsDGFunctor] (h : F = G) :
    DGCategory.K0.map.{w₂, w} F = DGCategory.K0.map.{w₂, w} G := by
  subst h
  rfl


-- @@ L157-161 expanded
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{u, u} A]
  [CatModule.HasDerivedCategory.{u, u} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
  [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{u, u} B]
  [CatModule.HasDerivedCategory.{u, u} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]
  (φ : DGRingHom A B)


-- @@ L163-177 verbatim
/-- **`K₀(F_w) ∘ ι_A = ι_B ∘ K₀(φ)`** for the morphism of diagonal half-graded dg rings induced by
a morphism of dg rings `φ`. -/
theorem K0Map_ofDGRingHom_mapCompactK0 (y : BaseK0.{u, u} A) :
    (HalfGradedDGRing.Hom.ofDGRingHom φ).K0Map (mapCompactK0.{u, u, u} A y) =
      mapCompactK0.{u, u, u} B (DGRing.K0.map φ y) := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  obtain ⟨z, rfl⟩ := (DGRing.K0.singleObjEquiv A).surjective y
  change _ = mapCompactK0.{u, u, u} B (DGRing.K0.singleObjEquiv B
    (DGCategory.K0.map φ.singleObjFunctor ((DGRing.K0.singleObjEquiv A).symm
      (DGRing.K0.singleObjEquiv A z))))
  rw [AddEquiv.symm_apply_apply, mapCompactK0_singleObjEquiv, mapCompactK0_singleObjEquiv,
    HalfGradedDGRing.Hom.K0Map_apply, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
    ← DGCategory.K0.map_comp, ← DGCategory.K0.map_comp]
  exact congrArg (fun f => f z) (DGCategory.K0.map_congr_functor (scalarInclusion_comp_weightFunctor φ))


-- @@ L179-184 verbatim
/-- **Derived induction along a morphism of dg rings**: under `K0LinearEquiv`, the map on `K₀` of
the induced morphism of diagonal half-graded dg rings is `id ⊗ K₀(φ)`. -/
theorem K0LinearEquiv_K0Map_ofDGRingHom (x : DiagK0.{u, u} A) :
    K0LinearEquiv.{u, u, u} B ((HalfGradedDGRing.Hom.ofDGRingHom φ).K0Map x) =
      LinearMap.lTensor _ (DGRing.K0.map φ).toIntLinearMap (K0LinearEquiv.{u, u, u} A x) :=
  K0LinearEquiv_linearMap A B _ _ (K0Map_ofDGRingHom_mapCompactK0 φ) x


-- @@ L186-192 verbatim
/-- The same on the compact super Grothendieck groups. -/
theorem superK0LinearEquiv_superK0cMap_ofDGRingHom
    (s : HalfGradedDGRing.SuperK0c.{u, u} (HalfGradedDGRing.ofDGRing A)) :
    superK0LinearEquiv.{u, u, u} B
      (HalfGradedDGRing.superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom φ).K0Map s) =
      LinearMap.lTensor _ (DGRing.K0.map φ).toIntLinearMap (superK0LinearEquiv.{u, u, u} A s) :=
  superK0LinearEquiv_superK0cMap_linearMap A B _ _ (K0Map_ofDGRingHom_mapCompactK0 φ) s


-- @@ L194-194 verbatim
end K0


-- @@ L196-196 verbatim
end Diagonal


-- @@ L198-198 verbatim
end DG
