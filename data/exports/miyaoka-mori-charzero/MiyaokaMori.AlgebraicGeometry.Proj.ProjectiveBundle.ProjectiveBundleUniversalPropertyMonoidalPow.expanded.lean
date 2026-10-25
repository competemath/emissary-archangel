import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra


-- @@ L5-27 verbatim
/-! # Tensor-power constructions and their multiplicativity

Companion of `ProjectiveBundleUniversalProperty.lean`: the multiplicativity lemmas needed by
`projBundle.localRingHomComponent_mul`.

## Contents

1. The three tensor-power constructions:
   * `Modules.monoidalPowMap g m : V^{⊗m} ⟶ W^{⊗m}` (functoriality of the tensor power);
   * `Modules.pullbackMonoidalPow f W m : f^*(W^{⊗m}) ⟶ (f^*W)^{⊗m}` (comparison, built from
     `pullbackTensorObjHom` = the oplax `δ` of `pullback f`, and `pullbackUnitIso`);
   * `Modules.unitPowCollapse X m : 𝟙^{⊗m} ⟶ 𝟙` (collapse of the unit power by left unitors).
2. Their compatibility with the concatenation isomorphisms `monoidalPowCat V m n : V^{⊗m} ⊗ V^{⊗n} ≅ V^{⊗(m+n)}`:
   * (a) `projBundle.pullbackMonoidalPow_monoidalPowCat`:
     `f^*(cat_W m n) ≫ pullbackMonoidalPow f W (m+n) = δ ≫ (pullbackMonoidalPow m ⊗ₘ pullbackMonoidalPow n) ≫ cat_{f^*W} m n`
     (induction on `n`; `n = 0` is the oplax right unitality of `f^*`, `n+1` is oplax associativity + `δ_natural_left`);
   * (b) `projBundle.monoidalPowCat_monoidalPowMap`: `(g^{⊗m} ⊗ₘ g^{⊗n}) ≫ cat_W = cat_V ≫ g^{⊗(m+n)}`
     (induction on `n`; `n = 0` is right unitor naturality, `n+1` associator-inverse naturality);
   * (c) `projBundle.unitPowCollapse_monoidalPowCat`: `cat_𝟙 m n ≫ collapse (m+n) = (collapse m ⊗ₘ collapse n) ≫ (λ_ 𝟙).hom`
     (induction on `n`; `n = 0` is `unitors_equal` + right unitor naturality, `n+1` is the triangle identity).

Source: Stacks 01LQ / 01M2 (maps out of a symmetric algebra are determined degreewise and are multiplicative on
the tensor-power presentation). -/


-- @@ L29-29 verbatim
set_option autoImplicit false

-- @@ L30-30 verbatim
set_option maxHeartbeats 400000


-- @@ L32-32 verbatim
universe u v w u' v'


-- @@ L34-34 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L35-35 verbatim
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-47 verbatim
/-- Functoriality of the tensor power: `g : V ⟶ W` induces `V^{⊗m} ⟶ W^{⊗m}` (levelwise `tensorHom`,
following the right-multiplication recursion of `monoidalPow`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.monoidalPowMap {X : AlgebraicGeometry.Scheme.{u}}
    {V W : X.Modules} (g : V ⟶ W) : (m : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.monoidalPow V m ⟶ AlgebraicGeometry.Scheme.Modules.monoidalPow W m)
  | 0 => CategoryTheory.CategoryStruct.id _
  | m + 1 => CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
      (AlgebraicGeometry.Scheme.Modules.monoidalPowMap g m) g


-- @@ L49-61 verbatim
/-- Comparison of pullback and tensor power: `f^*(W^{⊗m}) ⟶ (f^*W)^{⊗m}`. In degree `0` it is
`f^*O_Y ≅ O_X` (`pullbackUnitIso`); the inductive step uses `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B`
(`pullbackTensorObjHom`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (W : Y.Modules) : (m : ℕ) →
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.monoidalPow W m) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow ((AlgebraicGeometry.Scheme.Modules.pullback f).obj W) m)
  | 0 => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom
  | m + 1 => AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f
        (AlgebraicGeometry.Scheme.Modules.monoidalPow W m) W ≫
      CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow f W m) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj W)


-- @@ L63-73 verbatim
/-- `O^{⊗m} ⟶ O`: the tensor power of the unit object collapsed levelwise by left unitors. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.unitPowCollapse (X : AlgebraicGeometry.Scheme.{u}) : (m : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) m ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules)
  | 0 => CategoryTheory.CategoryStruct.id _
  | m + 1 => CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.unitPowCollapse X m)
        (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) ≫
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor
        (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules)).hom


-- @@ L75-78 verbatim
/-! ## Abstract monoidal lemmas

Stated for an arbitrary monoidal category / oplax monoidal functor and applied with `exact`, so that no rewriting
has to see through the recursive definitions `monoidalPow` / `monoidalPowCat`. -/


-- @@ L80-80 verbatim
namespace AlgebraicGeometry.Scheme.projBundle.MonoidalPowAux


-- @@ L82-82 verbatim
open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal


-- @@ L84-84 verbatim
variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]


-- @@ L86-92 verbatim
theorem cat_step {A A' B B' Q Q' V V' : C} (mm : A ⟶ A') (mn : B ⟶ B') (f : V ⟶ V')
    (c : A ⊗ B ⟶ Q) (c' : A' ⊗ B' ⟶ Q') (q : Q ⟶ Q') (ih : (mm ⊗ₘ mn) ≫ c' = c ≫ q) :
    (mm ⊗ₘ (mn ⊗ₘ f)) ≫ (α_ A' B' V').inv ≫ (c' ▷ V') =
      ((α_ A B V).inv ≫ (c ▷ V)) ≫ (q ⊗ₘ f) := by
  rw [MonoidalCategory.associator_inv_naturality_assoc, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, ih, Category.assoc,
    ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]


-- @@ L94-96 verbatim
theorem rightUnitor_comp_to_unit {P : C} (a : P ⟶ 𝟙_ C) :
    (ρ_ P).hom ≫ a = (a ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom := by
  rw [tensorHom_id, unitors_equal, rightUnitor_naturality]


-- @@ L98-101 verbatim
theorem unit_assoc_collapse :
    (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom =
      (𝟙_ C ◁ (λ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom := by
  monoidal


-- @@ L103-113 verbatim
theorem collapse_step {P Q R : C} (c : P ⊗ Q ⟶ R) (a : P ⟶ 𝟙_ C) (b : Q ⟶ 𝟙_ C) (r : R ⟶ 𝟙_ C)
    (ih : c ≫ r = (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom) :
    ((α_ P Q (𝟙_ C)).inv ≫ (c ▷ 𝟙_ C)) ≫ ((r ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom) =
      (a ⊗ₘ ((b ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom)) ≫ (λ_ (𝟙_ C)).hom := by
  have h2 : (a ⊗ₘ ((b ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom)) =
      (a ⊗ₘ (b ⊗ₘ 𝟙 (𝟙_ C))) ≫ (𝟙_ C ◁ (λ_ (𝟙_ C)).hom) := by
    rw [tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [h2]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, ih, comp_whiskerRight, Category.assoc,
    ← tensorHom_id (a ⊗ₘ b) (𝟙_ C), ← associator_inv_naturality_assoc, unit_assoc_collapse]


-- @@ L115-115 verbatim
variable {D : Type w} [Category.{v} D] [MonoidalCategory D]

-- @@ L116-116 verbatim
variable (F : C ⥤ D) [F.OplaxMonoidal]


-- @@ L118-126 verbatim
theorem map_rightUnitor_hom_eq (P : C) :
    F.map (ρ_ P).hom = δ F P (𝟙_ C) ≫ (F.obj P ◁ η F) ≫ (ρ_ (F.obj P)).hom := by
  calc F.map (ρ_ P).hom = F.map (ρ_ P).hom ≫ (ρ_ (F.obj P)).inv ≫ (ρ_ (F.obj P)).hom := by
        rw [Iso.inv_hom_id, Category.comp_id]
    _ = F.map (ρ_ P).hom ≫ (F.map (ρ_ P).inv ≫ δ F P (𝟙_ C) ≫ F.obj P ◁ η F) ≫
          (ρ_ (F.obj P)).hom := by rw [right_unitality]
    _ = δ F P (𝟙_ C) ≫ (F.obj P ◁ η F) ≫ (ρ_ (F.obj P)).hom := by
        rw [← Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp,
          Category.assoc]


-- @@ L128-132 verbatim
theorem map_rightUnitor_comp {P : C} {Q : D} (x : F.obj P ⟶ Q) :
    F.map (ρ_ P).hom ≫ x = δ F P (𝟙_ C) ≫ (x ⊗ₘ η F) ≫ (ρ_ Q).hom := by
  rw [map_rightUnitor_hom_eq, tensorHom_def']
  simp only [Category.assoc]
  rw [← rightUnitor_naturality]


-- @@ L134-146 verbatim
@[reassoc]
theorem map_associator_inv_δ (P Q V : C) :
    F.map (α_ P Q V).inv ≫ δ F (P ⊗ Q) V ≫ (δ F P Q ▷ F.obj V) =
      δ F P (Q ⊗ V) ≫ (F.obj P ◁ δ F Q V) ≫ (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by
  calc F.map (α_ P Q V).inv ≫ δ F (P ⊗ Q) V ≫ (δ F P Q ▷ F.obj V)
      = F.map (α_ P Q V).inv ≫ (δ F (P ⊗ Q) V ≫ (δ F P Q ▷ F.obj V) ≫
          (α_ (F.obj P) (F.obj Q) (F.obj V)).hom) ≫ (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = F.map (α_ P Q V).inv ≫ (F.map (α_ P Q V).hom ≫ δ F P (Q ⊗ V) ≫ F.obj P ◁ δ F Q V) ≫
          (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by rw [associativity]
    _ = δ F P (Q ⊗ V) ≫ (F.obj P ◁ δ F Q V) ≫ (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by
        rw [← Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp,
          Category.assoc]


-- @@ L148-159 verbatim
theorem map_cat_step {P Q R V : C} {A B E : D} (c : P ⊗ Q ⟶ R) (x : F.obj P ⟶ A) (y : F.obj Q ⟶ B)
    (r : F.obj R ⟶ E) (c' : A ⊗ B ⟶ E)
    (ih : F.map c ≫ r = δ F P Q ≫ (x ⊗ₘ y) ≫ c') :
    F.map ((α_ P Q V).inv ≫ (c ▷ V)) ≫ (δ F R V ≫ (r ▷ F.obj V)) =
      δ F P (Q ⊗ V) ≫ (x ⊗ₘ (δ F Q V ≫ (y ▷ F.obj V))) ≫ (α_ A B (F.obj V)).inv ≫ (c' ▷ F.obj V) := by
  have h2 : (x ⊗ₘ (δ F Q V ≫ (y ▷ F.obj V))) =
      (F.obj P ◁ δ F Q V) ≫ (x ⊗ₘ (y ⊗ₘ 𝟙 (F.obj V))) := by
    rw [tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [h2, F.map_comp]
  simp only [Category.assoc]
  rw [← δ_natural_left_assoc, ← comp_whiskerRight, ih, comp_whiskerRight, comp_whiskerRight,
    map_associator_inv_δ_assoc, associator_inv_naturality_assoc, tensorHom_id]


-- @@ L161-166 verbatim
/-- `F.map (f ⊗ₘ f') ≫ δ ≫ (a ⊗ₘ a') ≫ h = δ ≫ ((F.map f ≫ a) ⊗ₘ (F.map f' ≫ a')) ≫ h`. -/
theorem map_tensorHom_δ_comp {P P' Q Q' : C} {A A' E : D} (f : P ⟶ Q) (f' : P' ⟶ Q')
    (a : F.obj Q ⟶ A) (a' : F.obj Q' ⟶ A') (h : A ⊗ A' ⟶ E) :
    F.map (f ⊗ₘ f') ≫ δ F Q Q' ≫ (a ⊗ₘ a') ≫ h =
      δ F P P' ≫ ((F.map f ≫ a) ⊗ₘ (F.map f' ≫ a')) ≫ h := by
  rw [← δ_natural_assoc, ← tensorHom_comp_tensorHom_assoc]


-- @@ L168-168 verbatim
end AlgebraicGeometry.Scheme.projBundle.MonoidalPowAux


-- @@ L170-170 verbatim
/-! ## The three compatibilities in `X.Modules` -/


-- @@ L172-172 verbatim
namespace AlgebraicGeometry.Scheme.projBundle


-- @@ L174-174 verbatim
open CategoryTheory.MonoidalCategory MonoidalPowAux AlgebraicGeometry.Scheme.Modules


-- @@ L176-176 verbatim
variable {X T : AlgebraicGeometry.Scheme.{u}}


-- @@ L178-193 verbatim
/-- (b) `monoidalPowMap g` is multiplicative:
`(g^{⊗m} ⊗ₘ g^{⊗n}) ≫ cat_W m n = cat_V m n ≫ g^{⊗(m+n)}`. -/
@[reassoc]
theorem monoidalPowCat_monoidalPowMap {V W : X.Modules} (g : V ⟶ W) (m : ℕ) :
    ∀ n, (monoidalPowMap g m ⊗ₘ monoidalPowMap g n) ≫ (monoidalPowCat W m n).hom =
      (monoidalPowCat V m n).hom ≫ monoidalPowMap g (m + n)
  | 0 => by
    show (monoidalPowMap g m ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ (monoidalPow W m)).hom =
      (ρ_ (monoidalPow V m)).hom ≫ monoidalPowMap g m
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.rightUnitor_naturality]
  | n + 1 => by
    show (monoidalPowMap g m ⊗ₘ (monoidalPowMap g n ⊗ₘ g)) ≫
        ((α_ (monoidalPow W m) (monoidalPow W n) W).inv ≫ (monoidalPowCat W m n).hom ▷ W) =
      ((α_ (monoidalPow V m) (monoidalPow V n) V).inv ≫ (monoidalPowCat V m n).hom ▷ V) ≫
        (monoidalPowMap g (m + n) ⊗ₘ g)
    exact cat_step _ _ _ _ _ _ (monoidalPowCat_monoidalPowMap g m n)


-- @@ L195-210 verbatim
/-- (a) `pullbackMonoidalPow` is multiplicative:
`f^*(cat_W m n) ≫ pullbackMonoidalPow f W (m+n) = δ ≫ (pullbackMonoidalPow m ⊗ₘ pullbackMonoidalPow n) ≫ cat_{f^*W} m n`. -/
@[reassoc]
theorem pullbackMonoidalPow_monoidalPowCat (f : T ⟶ X) (W : X.Modules) (m : ℕ) : ∀ n : ℕ,
    (Modules.pullback f).map (monoidalPowCat W m n).hom ≫ pullbackMonoidalPow f W (m + n) =
      pullbackTensorObjHom f (monoidalPow W m) (monoidalPow W n) ≫
        (pullbackMonoidalPow f W m ⊗ₘ pullbackMonoidalPow f W n) ≫
        (monoidalPowCat ((Modules.pullback f).obj W) m n).hom
  | 0 => by
    have h := map_rightUnitor_comp (Modules.pullback f) (pullbackMonoidalPow f W m)
    rw [pullback_η] at h
    exact h
  | n + 1 =>
    map_cat_step (Modules.pullback f) (monoidalPowCat W m n).hom (pullbackMonoidalPow f W m)
      (pullbackMonoidalPow f W n) (pullbackMonoidalPow f W (m + n))
      (monoidalPowCat ((Modules.pullback f).obj W) m n).hom (pullbackMonoidalPow_monoidalPowCat f W m n)


-- @@ L212-222 verbatim
/-- (c) `unitPowCollapse` is multiplicative:
`cat_𝟙 m n ≫ collapse (m+n) = (collapse m ⊗ₘ collapse n) ≫ (λ_ 𝟙).hom`. -/
@[reassoc]
theorem unitPowCollapse_monoidalPowCat (X : AlgebraicGeometry.Scheme.{u}) (m : ℕ) : ∀ n : ℕ,
    (monoidalPowCat (𝟙_ X.Modules) m n).hom ≫ unitPowCollapse X (m + n) =
      (unitPowCollapse X m ⊗ₘ unitPowCollapse X n) ≫
        (λ_ (𝟙_ X.Modules)).hom
  | 0 => rightUnitor_comp_to_unit (unitPowCollapse X m)
  | n + 1 =>
    collapse_step (monoidalPowCat (𝟙_ X.Modules) m n).hom (unitPowCollapse X m) (unitPowCollapse X n)
      (unitPowCollapse X (m + n)) (unitPowCollapse_monoidalPowCat X m n)


-- @@ L224-224 verbatim
end AlgebraicGeometry.Scheme.projBundle


-- @@ L226-226 verbatim
end
