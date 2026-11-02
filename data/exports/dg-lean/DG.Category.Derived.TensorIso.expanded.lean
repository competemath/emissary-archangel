import DG.Category.Derived.TensorInduction
import DG.Category.Derived.InductionComp


-- @@ L4-23 verbatim
/-!
# Isomorphisms of dg bimodules and derived tensor products

An isomorphism `e : B ≅ B'` of dg `(D, C)`-bimodules (`DG.CatBimodule.Iso`: isomorphisms of the
left dg modules `B(-, Y) ≅ B'(-, Y)` compatible with the right actions) induces natural
isomorphisms of the Hom functors `HOM_D(B, -) ≅ HOM_D(B', -)` on dg modules and on homotopy
categories (`DG.CatBimodule.homFunctorIso`, `DG.CatModule.HomotopyCategory.homFunctorIso`), of the
derived Hom functors (`DG.CatModule.DerivedCategory.rhomIso`) and, by uniqueness of left
adjoints, of the derived tensor products `B ⊗^L_C - ≅ B' ⊗^L_C -`
(`DG.CatModule.DerivedCategory.derivedTensorIso`).

Consequences:
* if `B ≅ C(-, -)` (the diagonal bimodule `CatBimodule.ofFunctor (𝟭 C)`), then
  `B ⊗^L_C - ≅ 𝟭` (`DG.CatModule.DerivedCategory.derivedTensorIsoId`); for a dg ring `A`, a dg
  `(A, A)`-bimodule isomorphic to `A` gives `M ⊗^L_A - ≅ 𝟭 (D(A))`
  (`DG.CatModule.DerivedCategory.singleObjDerivedTensorIsoId`);
* derived induction along a quasi-isomorphism of dg rings, in particular along an isomorphism
  of dg rings, is an equivalence (`DG.DGRingHom.derivedInductionEquivalence`,
  `DG.DGRingHom.isQuasiIso_of_leftInverse_rightInverse`).
-/


-- @@ L25-25 verbatim
open CategoryTheory


-- @@ L27-27 verbatim
universe w₁ w₂ w₃ w₄ w v v₁ v₂ u₁ u₂


-- @@ L29-29 verbatim
set_option backward.isDefEq.respectTransparency false


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace DG



-- @@ L36-36 verbatim
namespace CatBimodule


-- @@ L38-39 verbatim
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]


-- @@ L41-48 verbatim
/-- An isomorphism of dg `(D, C)`-bimodules: isomorphisms of the left dg modules
`B(-, Y) ≅ B'(-, Y)` over `D` which are compatible with the right actions of `C`. -/
structure Iso (B B' : CatBimodule.{w} D C) where
  /-- The isomorphisms of the left dg modules. -/
  left : ∀ Y : C, B.left Y ≅ B'.left Y
  /-- Compatibility with the right actions. -/
  ract : ∀ {Y Y' : C} (g : Y ⟶ Y') (X : D) (x : B.obj X Y'),
    (left Y).hom.app X (B.ract g x) = B'.ract g ((left Y').hom.app X x)


-- @@ L50-50 verbatim
namespace Iso


-- @@ L52-52 verbatim
variable {B B' : CatBimodule.{w} D C} (e : Iso B B')


-- @@ L54-56 verbatim
theorem inv_hom_app (Y : C) (X : D) (x : B'.obj X Y) :
    (e.left Y).hom.app X ((e.left Y).inv.app X x) = x := by
  rw [← CatModule.comp_app, Iso.inv_hom_id, CatModule.id_app]


-- @@ L58-60 verbatim
theorem hom_inv_app (Y : C) (X : D) (x : B.obj X Y) :
    (e.left Y).inv.app X ((e.left Y).hom.app X x) = x := by
  rw [← CatModule.comp_app, Iso.hom_inv_id, CatModule.id_app]


-- @@ L62-66 verbatim
theorem ract_inv {Y Y' : C} (g : Y ⟶ Y') (X : D) (x : B'.obj X Y') :
    (e.left Y).inv.app X (B'.ract g x) = B.ract g ((e.left Y').inv.app X x) := by
  apply (show Function.Injective ((e.left Y).hom.app X) from
    Function.LeftInverse.injective (g := (e.left Y).inv.app X) (e.hom_inv_app Y X))
  rw [inv_hom_app, e.ract, inv_hom_app]


-- @@ L68-71 verbatim
/-- The inverse isomorphism. -/
def symm : Iso B' B where
  left Y := (e.left Y).symm
  ract g X x := e.ract_inv g X x


-- @@ L73-84 verbatim
variable [DGCategory C] in
theorem ractCochain_inv {Y Y' : C} {i : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i) (X : D)
    (x : B'.obj X Y') :
    (B.ractCochain f hf).app X ((e.left Y').inv.app X x) =
      (e.left Y).inv.app X ((B'.ractCochain f hf).app X x) := by
  induction x using DG.induction_on with
  | h_zero => simp
  | h_add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | h_homogeneous x =>
    rename_i j
    rw [ractCochain_app_of_mem hf ((e.left Y').inv.map_mem x.2), ractCochain_app_of_mem hf x.2,
      Units.smul_def, Units.smul_def, map_zsmul, ract_inv]


-- @@ L86-86 verbatim
end Iso


-- @@ L88-88 verbatim
/-! ### The Hom functors -/


-- @@ L90-90 verbatim
section HomIso


-- @@ L92-92 verbatim
variable {B B' : CatBimodule.{w} D C} (e : Iso B B') (N : CatModule.{w} D)


-- @@ L94-100 verbatim
omit [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] in
theorem precompCochain_ofHom_of {P P' : CatModule.{w} D} (φ : P' ⟶ P) (j : ℤ)
    (w' : CatModule.Cochain P N j) :
    CatModule.HOM.precompCochain (CatModule.Cochain.ofHom φ) (DirectSum.of (fun n => CatModule.Cochain P N n) j w') =
      DirectSum.of (fun n => CatModule.Cochain P' N n) j (w'.comp (CatModule.Cochain.ofHom φ) (zero_add j)) := by
  rw [CatModule.HOM.precompCochain_of, zero_mul, koszulSign_zero, one_smul]
  exact CatModule.HOM.of_congr (zero_add j) fun _ _ => rfl


-- @@ L102-125 verbatim
/-- Precomposition with an isomorphism of dg modules, as an additive equivalence of Hom
complexes. -/
def homIsoApp {P P' : CatModule.{w} D} (φ : P ≅ P') : CatModule.HOM P N ≃+ CatModule.HOM P' N where
  toFun := CatModule.HOM.precompCochain (CatModule.Cochain.ofHom φ.inv)
  invFun := CatModule.HOM.precompCochain (CatModule.Cochain.ofHom φ.hom)
  left_inv w := by
    induction w using DirectSum.induction_on with
    | zero => simp
    | of j w' =>
      rw [precompCochain_ofHom_of, precompCochain_ofHom_of]
      refine CatModule.HOM.of_congr rfl fun X x => ?_
      simp only [CatModule.Cochain.comp_apply, CatModule.Cochain.ofHom_apply]
      rw [← CatModule.comp_app, Iso.hom_inv_id, CatModule.id_app]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  right_inv w := by
    induction w using DirectSum.induction_on with
    | zero => simp
    | of j w' =>
      rw [precompCochain_ofHom_of, precompCochain_ofHom_of]
      refine CatModule.HOM.of_congr rfl fun X x => ?_
      simp only [CatModule.Cochain.comp_apply, CatModule.Cochain.ofHom_apply]
      rw [← CatModule.comp_app, Iso.inv_hom_id, CatModule.id_app]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  map_add' := map_add _


-- @@ L127-128 verbatim
theorem homIsoApp_apply {P P' : CatModule.{w} D} (φ : P ≅ P') (w : CatModule.HOM P N) :
    homIsoApp N φ w = CatModule.HOM.precompCochain (CatModule.Cochain.ofHom φ.inv) w := rfl


-- @@ L130-139 verbatim
theorem homIsoApp_mem_iff {P P' : CatModule.{w} D} (φ : P ≅ P') {n : ℤ} {w : CatModule.HOM P N} :
    homIsoApp N φ w ∈ grading n ↔ w ∈ grading n := by
  constructor
  · intro h
    have := CatModule.HOM.precompCochain_mem (N := N) (CatModule.Cochain.ofHom φ.hom) h
    rw [zero_add] at this
    exact (homIsoApp N φ).symm_apply_apply w ▸ this
  · intro h
    have := CatModule.HOM.precompCochain_mem (N := N) (CatModule.Cochain.ofHom φ.inv) h
    rwa [zero_add] at this


-- @@ L141-144 verbatim
theorem homIsoApp_d {P P' : CatModule.{w} D} (φ : P ≅ P') (w : CatModule.HOM P N) :
    homIsoApp N φ (d w) = d (homIsoApp N φ w) := by
  rw [homIsoApp_apply, homIsoApp_apply, CatModule.HOM.d_precompCochain, CatModule.δ_ofHom,
    CatModule.HOM.precompCochain_zero, zero_add, koszulSign_zero, one_smul]


-- @@ L146-146 verbatim
variable [DGCategory C]


-- @@ L148-166 verbatim
theorem homIsoApp_homAct {Y Y' : C} (f : Y ⟶ Y') (w : CatModule.HOM (B.left Y) N) :
    homIsoApp N (e.left Y') (B.homAct N f w) = B'.homAct N f (homIsoApp N (e.left Y) w) := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_add f g hf hg =>
    rw [map_add, AddMonoidHom.add_apply, map_add, hf, hg, map_add, AddMonoidHom.add_apply]
  | h_homogeneous f =>
    rename_i i
    rw [homAct_of_mem f.2, homAct_of_mem f.2]
    induction w using DirectSum.induction_on with
    | zero => simp
    | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]
    | of j w' =>
      rw [homIsoApp_apply, homIsoApp_apply, CatModule.HOM.precompCochain_of, Units.smul_def, map_zsmul,
        precompCochain_ofHom_of, precompCochain_ofHom_of, CatModule.HOM.precompCochain_of, Units.smul_def]
      congr 1
      refine CatModule.HOM.of_congr (by ring) fun X x => ?_
      simp only [CatModule.Cochain.comp_apply, CatModule.Cochain.ofHom_apply]
      rw [e.ractCochain_inv f.2 X x]


-- @@ L168-171 verbatim
/-- `HOM_D(B, N) ≅ HOM_D(B', N)`. -/
def homObjIso : B.homObj N ≅ B'.homObj N :=
  CatModule.isoMk (fun Y => homIsoApp N (e.left Y)) (homIsoApp_mem_iff N _)
    (fun w => homIsoApp_d N _ w) (fun f w => homIsoApp_homAct e N f w)


-- @@ L173-179 verbatim
/-- **`HOM_D(B, -) ≅ HOM_D(B', -)`** for an isomorphism of dg bimodules. -/
def homFunctorIso : B.homFunctor ≅ B'.homFunctor :=
  NatIso.ofComponents (fun N => homObjIso e N) fun {N N'} φ => CatModule.hom_ext fun Y w => by
    change CatModule.HOM.precompCochain (CatModule.Cochain.ofHom (e.left Y).inv)
        (CatModule.HOM.postcompCochain (CatModule.Cochain.ofHom φ) w) =
      CatModule.HOM.postcompCochain (CatModule.Cochain.ofHom φ) (CatModule.HOM.precompCochain (CatModule.Cochain.ofHom (e.left Y).inv) w)
    rw [CatModule.HOM.postcompCochain_precompCochain, mul_zero, koszulSign_zero, one_smul]


-- @@ L181-181 verbatim
end HomIso


-- @@ L183-183 verbatim
end CatBimodule


-- @@ L185-185 verbatim
namespace CatModule


-- @@ L187-189 verbatim
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]


-- @@ L191-191 verbatim
namespace HomotopyCategory


-- @@ L193-198 verbatim
/-- The Hom functors of isomorphic dg bimodules on homotopy categories are isomorphic. -/
def homFunctorIso {B B' : CatBimodule.{w} D C} (e : CatBimodule.Iso B B') :
    homFunctor B ≅ homFunctor B' :=
  CategoryTheory.Quotient.natIsoLift _
    (homFunctorFactors B ≪≫ Functor.isoWhiskerRight (CatBimodule.homFunctorIso e) _ ≪≫
      (homFunctorFactors B').symm)


-- @@ L200-200 verbatim
end HomotopyCategory


-- @@ L202-202 verbatim
namespace DerivedCategory


-- @@ L204-204 verbatim
section Rhom


-- @@ L206-208 verbatim
variable {B B' : CatBimodule.{w} D C} (e : CatBimodule.Iso B B')
  (hB : ∀ Y : C, IsKProjective (B.left Y)) (hB' : ∀ Y : C, IsKProjective (B'.left Y))
  [HasDerivedCategory.{w₁, max u₂ w} C] [HasDerivedCategory.{w₂, w} D]


-- @@ L210-214 verbatim
/-- **`RHOM_D(B, -) ≅ RHOM_D(B', -)`** for an isomorphism of dg bimodules. -/
def rhomIso : rhom.{w₁, w₂} B hB ≅ rhom B' hB' :=
  Localization.liftNatIso Qh (HomotopyCategory.quasiIso D)
    (HomotopyCategory.homFunctor B ⋙ Qh) (HomotopyCategory.homFunctor B' ⋙ Qh) _ _
    (Functor.isoWhiskerRight (HomotopyCategory.homFunctorIso e) Qh)


-- @@ L216-216 verbatim
end Rhom


-- @@ L218-218 verbatim
section Tensor


-- @@ L220-222 verbatim
variable {B B' : CatBimodule.{max u₁ u₂ v₁ w} D C} (e : CatBimodule.Iso B B')
  (hB : ∀ Y : C, IsKProjective (B.left Y)) (hB' : ∀ Y : C, IsKProjective (B'.left Y))
  [HasDerivedCategory.{w₁, max u₁ u₂ v₁ w} C] [HasDerivedCategory.{w₂, max u₁ u₂ v₁ w} D]


-- @@ L224-228 verbatim
/-- **`B ⊗^L_C - ≅ B' ⊗^L_C -`** for an isomorphism of dg bimodules (uniqueness of left
adjoints). -/
def derivedTensorIso : derivedTensor.{w₁, w₂} B hB ≅ derivedTensor.{w₁, w₂} B' hB' :=
  (derivedTensorAdjunction B hB).leftAdjointUniq
    ((derivedTensorAdjunction B' hB').ofNatIsoRight (rhomIso e hB hB').symm)


-- @@ L230-230 verbatim
end Tensor


-- @@ L232-232 verbatim
section Diagonal


-- @@ L234-235 verbatim
variable {C : Type u₁} [Category.{max u₁ v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] [HasDerivedCategory.{w₁, max u₁ v} C]


-- @@ L237-244 verbatim
/-- If a dg `(C, C)`-bimodule is isomorphic to the diagonal bimodule `C(-, -)`, its derived
tensor product is the identity. -/
def derivedTensorIsoId {B : CatBimodule.{max u₁ v} C C}
    (e : CatBimodule.Iso B (CatBimodule.ofFunctor (𝟭 C)))
    (hB : ∀ Y : C, IsKProjective (B.left Y)) :
    derivedTensor.{w₁, w₁} B hB ≅ 𝟭 _ :=
  derivedTensorIso e hB (CatBimodule.isKProjective_ofFunctor_left (𝟭 C)) ≪≫
    derivedTensorOfFunctorIso.{w₁, w₁, v} (𝟭 C) ≪≫ inductionIdIso C


-- @@ L246-246 verbatim
end Diagonal


-- @@ L248-248 verbatim
section SingleObj


-- @@ L250-251 verbatim
variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w₁, v} (SingleObj A)] [DG.HasDerivedCategory.{w₂, v} A]


-- @@ L253-261 verbatim
/-- **A dg `(A, A)`-bimodule `M` isomorphic to `A` gives `M ⊗^L_A - ≅ 𝟭 (D(A))`**, the derived
tensor product transported along `D(SingleObj A) ≌ D(A)`. -/
def singleObjDerivedTensorIsoId {M : CatBimodule.{v} (SingleObj A) (SingleObj A)}
    (e : CatBimodule.Iso M (CatBimodule.ofFunctor (𝟭 (SingleObj A))))
    (hM : ∀ Y, IsKProjective (M.left Y)) :
    (singleObjEquivalence A).inverse ⋙ derivedTensor.{w₁, w₁} M hM ⋙
        (singleObjEquivalence A).functor ≅ 𝟭 (DG.DerivedCategory A) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (derivedTensorIsoId e hM) _ ≪≫
    Functor.leftUnitor _) ≪≫ (singleObjEquivalence A).counitIso


-- @@ L263-263 verbatim
end SingleObj


-- @@ L265-265 verbatim
end DerivedCategory


-- @@ L267-267 verbatim
end CatModule


-- @@ L269-269 verbatim
namespace DGRingHom


-- @@ L271-272 verbatim
variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] {B : Type v} [Ring B]
  [DGAddCommGroup B] [DGRing B]


-- @@ L274-286 expanded
omit [DGRing A] [DGRing B] in
/-- A morphism of dg rings with a two-sided inverse is a quasi-isomorphism. -/
theorem isQuasiIso_of_leftInverse_rightInverse (φ : DGRingHom B A) (ψ : DGRingHom A B)
    (h₁ : ∀ b, ψ (φ b) = b) (h₂ : ∀ a, φ (ψ a) = a) : φ.IsQuasiIso :=
  by
  intro n
  have e₁ : ψ.comp φ = DGRingHom.id := DGRingHom.ext h₁
  have e₂ : φ.comp ψ = DGRingHom.id := DGRingHom.ext h₂
  refine
    ⟨Function.LeftInverse.injective (g := ψ.cohomologyMap n) fun x => ?_,
      Function.RightInverse.surjective (g := ψ.cohomologyMap n) fun x => ?_⟩
  ·
    rw [← AddMonoidHom.comp_apply, ← cohomologyMap_comp, e₁, cohomologyMap_id,
      AddMonoidHom.id_apply]
  ·
    rw [← AddMonoidHom.comp_apply, ← cohomologyMap_comp, e₂, cohomologyMap_id,
      AddMonoidHom.id_apply]


-- @@ L288-290 verbatim
variable [CatModule.HasDerivedCategory.{v, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]


-- @@ L292-299 expanded
/-- **Derived induction along a quasi-isomorphism of dg rings is an equivalence** (for instance
along an isomorphism of dg rings, `isQuasiIso_of_leftInverse_rightInverse`). -/
theorem derivedInduction_isEquivalence (φ : DGRingHom B A) (hφ : φ.IsQuasiIso) :
    (φ.derivedInduction.{v, w₂, w₃, w₄}).IsEquivalence :=
  by
  have :=
    CatModule.DerivedCategory.induction_isEquivalence.{v, w₂}
      (φ.isQuasiEquivalence_singleObjFunctor hφ)
  unfold derivedInduction
  infer_instance


-- @@ L301-306 expanded
/-- Derived induction along a quasi-isomorphism of dg rings, as an equivalence
`D(B) ≌ D(A)`. -/
def derivedInductionEquivalence (φ : DGRingHom B A) (hφ : φ.IsQuasiIso) :
    DG.DerivedCategory B ≌ DG.DerivedCategory A :=
  haveI := derivedInduction_isEquivalence φ hφ
  (φ.derivedInduction.{v, w₂, w₃, w₄}).asEquivalence


-- @@ L308-308 verbatim
end DGRingHom


-- @@ L310-310 verbatim
end DG
