import StringDiagrams.Super.PiCat
import StringDiagrams.Super.PiTwoCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Bicategory.Strict.Basic


-- @@ L6-26 verbatim
/-!
# The strict Π-2-category `Π-ℭ𝔞𝔱`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, after
Definition 5.2: "the basic example of a strict Π-2-category is `Π-ℭ𝔞𝔱`: objects are
Π-categories, 1-morphisms are Π-functors, and 2-morphisms are Π-natural transformations",
with `π_A := Π_A` and `β`, `ξ` coming from Definition 1.6(i)–(ii).

* `PiCat.piNat F G`: the `R`-submodule of Π-natural transformations `F ⟶ G`
  (Definition 1.6(iii)) of the natural transformations between two Π-functors.
* `PiCat.instBicategory`: `PiCat R` (the category `Π-Cat` of `StringDiagrams.Super.PiCat`) is a
  bicategory with Π-natural transformations as 2-morphisms, horizontal composition by whiskering
  and identity coherence isomorphisms; its underlying category structure is that of `Π-Cat`.
  It is strict (`PiCat.instStrict`).
* The hom categories are `R`-linear, and whiskering is `R`-linear
  (`PiCat.instPreadditiveBicategory`, `PiCat.instLinearBicategory`).
* **Π-2-category structure** (`PiCat.instPiTwoCategory`, Definition 5.2(i)): `π_A = (Π_A, -1)`
  (the Π-functor `PiFunctor.pi`), `β_F` the given isomorphism of the Π-functor `F`, and
  `ξ_A` the given isomorphism of the Π-category `A`. The axioms are those of Definition 1.6:
  `β_F` is Π-natural and its compatibility with `ξ` is the Π-functor axiom (`PiFunctor.comm`).
-/


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace StringDiagrams


-- @@ L32-32 verbatim
open CategoryTheory Bicategory


-- @@ L34-34 verbatim
universe w v u


-- @@ L36-36 verbatim
variable {R : Type w} [CommRing R]


-- @@ L38-38 verbatim
namespace PiFunctor


-- @@ L40-41 verbatim
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [PiCategory R C]
  {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D] [PiCategory R D]


-- @@ L43-49 verbatim
/-- The inverse of a Π-natural isomorphism is Π-natural. -/
theorem IsPiNatural.inv {F G : C ⥤ D} {hF : PiFunctor R F} {hG : PiFunctor R G} {e : F ≅ G}
    (he : IsPiNatural R hF hG e.hom) : IsPiNatural R hG hF e.inv := fun X => by
  have h := he X
  rw [← cancel_epi ((PiCategory.pi (R := R)).map (e.hom.app X)), ← reassoc_of% h,
    ← Functor.map_comp_assoc]
  simp


-- @@ L51-51 verbatim
end PiFunctor


-- @@ L53-53 verbatim
namespace PiCat


-- @@ L55-55 verbatim
variable {A B E : PiCat.{w, v, u} R}


-- @@ L57-57 verbatim
/-! ## Π-natural transformations as 2-morphisms -/


-- @@ L59-78 verbatim
variable (F G : A ⟶ B) in
/-- The `R`-submodule of Π-natural transformations (Brundan–Ellis, Definition 1.6(iii)) among the
natural transformations between the underlying functors of two Π-functors. -/
def piNat : Submodule R (F.toFunctor ⟶ G.toFunctor) where
  carrier := {x | PiFunctor.IsPiNatural R F.piFunctor G.piFunctor x}
  add_mem' {x y} hx hy X := by
    change F.piFunctor.β.hom.app X ≫ (x + y).app _ = (PiCategory.pi (R := R)).map ((x + y).app X) ≫
      G.piFunctor.β.hom.app X
    rw [NatTrans.app_add, NatTrans.app_add, Preadditive.comp_add, Functor.map_add,
      Preadditive.add_comp, hx X, hy X]
  zero_mem' X := by
    change F.piFunctor.β.hom.app X ≫ (0 : F.toFunctor ⟶ G.toFunctor).app _ =
      (PiCategory.pi (R := R)).map ((0 : F.toFunctor ⟶ G.toFunctor).app X) ≫
        G.piFunctor.β.hom.app X
    simp
  smul_mem' r x hx X := by
    change F.piFunctor.β.hom.app X ≫ (r • x).app _ = (PiCategory.pi (R := R)).map ((r • x).app X) ≫
      G.piFunctor.β.hom.app X
    rw [NatTrans.app_smul, NatTrans.app_smul, Linear.comp_smul, Functor.map_smul,
      Linear.smul_comp, hx X]


-- @@ L80-88 verbatim
/-- The category of Π-functors `A → B` and Π-natural transformations (the morphism category
`Hom_{Π-ℭ𝔞𝔱}(A, B)`). -/
instance homCategory (A B : PiCat.{w, v, u} R) : Category (A ⟶ B) where
  Hom F G := piNat F G
  id F := ⟨𝟙 F.toFunctor, PiFunctor.isPiNatural_id _⟩
  comp x y := ⟨x.1 ≫ y.1, PiFunctor.IsPiNatural.comp x.2 y.2⟩
  id_comp x := Subtype.ext (Category.id_comp x.1)
  comp_id x := Subtype.ext (Category.comp_id x.1)
  assoc x y z := Subtype.ext (Category.assoc x.1 y.1 z.1)


-- @@ L90-90 verbatim
variable {F G H K : A ⟶ B}


-- @@ L92-94 verbatim
/-- The natural transformation underlying a 2-morphism of `Π-ℭ𝔞𝔱`. -/
abbrev Hom₂.natTrans (x : F ⟶ G) : F.toFunctor ⟶ G.toFunctor := Subtype.val (p := fun y =>
  y ∈ piNat F G) x


-- @@ L96-98 verbatim
theorem Hom₂.isPiNatural (x : F ⟶ G) :
    PiFunctor.IsPiNatural R F.piFunctor G.piFunctor (Hom₂.natTrans x) :=
  Subtype.property (p := fun y => y ∈ piNat F G) x


-- @@ L100-102 verbatim
/-- A 2-morphism of `Π-ℭ𝔞𝔱` from a Π-natural transformation. -/
abbrev hom₂Mk (x : F.toFunctor ⟶ G.toFunctor)
    (hx : PiFunctor.IsPiNatural R F.piFunctor G.piFunctor x) : F ⟶ G := ⟨x, hx⟩


-- @@ L104-106 verbatim
@[simp] theorem hom₂Mk_natTrans (x : F.toFunctor ⟶ G.toFunctor)
    (hx : PiFunctor.IsPiNatural R F.piFunctor G.piFunctor x) :
    Hom₂.natTrans (hom₂Mk x hx) = x := rfl


-- @@ L108-110 verbatim
@[ext] theorem hom₂_ext {x y : F ⟶ G} (h : ∀ X, (Hom₂.natTrans x).app X = (Hom₂.natTrans y).app X) :
    x = y :=
  Subtype.ext (NatTrans.ext (funext h))


-- @@ L112-112 verbatim
@[simp] theorem id₂_natTrans (F : A ⟶ B) : Hom₂.natTrans (𝟙 F) = 𝟙 F.toFunctor := rfl


-- @@ L114-115 verbatim
@[simp] theorem comp₂_natTrans (x : F ⟶ G) (y : G ⟶ H) :
    Hom₂.natTrans (x ≫ y) = Hom₂.natTrans x ≫ Hom₂.natTrans y := rfl


-- @@ L117-117 verbatim
instance (F G : A ⟶ B) : AddCommGroup (F ⟶ G) := inferInstanceAs (AddCommGroup (piNat F G))


-- @@ L119-119 verbatim
instance (F G : A ⟶ B) : Module R (F ⟶ G) := inferInstanceAs (Module R (piNat F G))


-- @@ L121-124 verbatim
instance (A B : PiCat.{w, v, u} R) : Preadditive (A ⟶ B) where
  homGroup F G := inferInstanceAs (AddCommGroup (piNat F G))
  add_comp _ _ _ x x' y := Subtype.ext (Preadditive.add_comp _ _ _ x.1 x'.1 y.1)
  comp_add _ _ _ x y y' := Subtype.ext (Preadditive.comp_add _ _ _ x.1 y.1 y'.1)


-- @@ L126-129 verbatim
instance (A B : PiCat.{w, v, u} R) : Linear R (A ⟶ B) where
  homModule F G := inferInstanceAs (Module R (piNat F G))
  smul_comp _ _ _ r x y := Subtype.ext (Linear.smul_comp _ _ _ r x.1 y.1)
  comp_smul _ _ _ x r y := Subtype.ext (Linear.comp_smul _ _ _ x.1 r y.1)


-- @@ L131-132 verbatim
@[simp] theorem add₂_natTrans (x y : F ⟶ G) :
    Hom₂.natTrans (x + y) = Hom₂.natTrans x + Hom₂.natTrans y := rfl


-- @@ L134-134 verbatim
@[simp] theorem neg₂_natTrans (x : F ⟶ G) : Hom₂.natTrans (-x) = -Hom₂.natTrans x := rfl


-- @@ L136-136 verbatim
@[simp] theorem zero₂_natTrans : Hom₂.natTrans (0 : F ⟶ G) = 0 := rfl


-- @@ L138-139 verbatim
@[simp] theorem smul₂_natTrans (r : R) (x : F ⟶ G) :
    Hom₂.natTrans (r • x) = r • Hom₂.natTrans x := rfl


-- @@ L141-148 verbatim
/-- A Π-natural isomorphism of Π-functors, as an isomorphism in `Hom_{Π-ℭ𝔞𝔱}(A, B)`. -/
@[simps]
def iso₂Mk (e : F.toFunctor ≅ G.toFunctor)
    (he : PiFunctor.IsPiNatural R F.piFunctor G.piFunctor e.hom) : F ≅ G where
  hom := hom₂Mk e.hom he
  inv := hom₂Mk e.inv he.inv
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id


-- @@ L150-150 verbatim
/-! ## The bicategory `Π-ℭ𝔞𝔱` -/


-- @@ L152-155 verbatim
/-- Whiskering on the left by a Π-functor. -/
def whiskerLeft₂ (F : A ⟶ B) {G H : B ⟶ E} (y : G ⟶ H) : F ≫ G ⟶ F ≫ H :=
  hom₂Mk (Functor.whiskerLeft F.toFunctor (Hom₂.natTrans y))
    (Associated.isPiNatural_whiskerLeft F.piFunctor (Hom₂.isPiNatural y))


-- @@ L157-160 verbatim
/-- Whiskering on the right by a Π-functor. -/
def whiskerRight₂ {F G : A ⟶ B} (x : F ⟶ G) (H : B ⟶ E) : F ≫ H ⟶ G ≫ H :=
  hom₂Mk (Functor.whiskerRight (Hom₂.natTrans x) H.toFunctor)
    (Associated.isPiNatural_whiskerRight H.piFunctor (Hom₂.isPiNatural x))


-- @@ L162-166 verbatim
theorem associator_isPiNatural {A B E E' : PiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E)
    (H : E ⟶ E') :
    PiFunctor.IsPiNatural R ((F ≫ G) ≫ H).piFunctor (F ≫ G ≫ H).piFunctor
      (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom := fun X => by
  simp [PiFunctor.comp]


-- @@ L168-171 verbatim
theorem leftUnitor_isPiNatural (F : A ⟶ B) :
    PiFunctor.IsPiNatural R (𝟙 A ≫ F).piFunctor F.piFunctor
      (Functor.leftUnitor F.toFunctor).hom := fun X => by
  simp [PiFunctor.comp, PiFunctor.id]


-- @@ L173-176 verbatim
theorem rightUnitor_isPiNatural (F : A ⟶ B) :
    PiFunctor.IsPiNatural R (F ≫ 𝟙 B).piFunctor F.piFunctor
      (Functor.rightUnitor F.toFunctor).hom := fun X => by
  simp [PiFunctor.comp, PiFunctor.id]


-- @@ L178-211 verbatim
/-- **Brundan–Ellis, after Definition 5.2.** The bicategory `Π-ℭ𝔞𝔱` of Π-categories, Π-functors
and Π-natural transformations. Its underlying category structure is that of the category
`Π-Cat` (`PiCat.instCategory`). -/
instance instBicategory : Bicategory.{max u v, max u v} (PiCat.{w, v, u} R) where
  toCategoryStruct := inferInstance
  homCategory A B := homCategory A B
  whiskerLeft F _ _ y := whiskerLeft₂ F y
  whiskerRight x H := whiskerRight₂ x H
  associator F G H := iso₂Mk (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
    (associator_isPiNatural F G H)
  leftUnitor F := iso₂Mk (Functor.leftUnitor F.toFunctor) (leftUnitor_isPiNatural F)
  rightUnitor F := iso₂Mk (Functor.rightUnitor F.toFunctor) (rightUnitor_isPiNatural F)
  whiskerLeft_id F G := hom₂_ext fun X => rfl
  whiskerLeft_comp F _ _ _ x y := hom₂_ext fun X => rfl
  id_whiskerLeft x := hom₂_ext fun X => by
    simp [whiskerLeft₂]
  comp_whiskerLeft F G _ _ x := hom₂_ext fun X => by
    simp [whiskerLeft₂]
  id_whiskerRight F G := hom₂_ext fun X => by
    simp [whiskerRight₂]
  comp_whiskerRight x y H := hom₂_ext fun X => by
    simp [whiskerRight₂]
  whiskerRight_id x := hom₂_ext fun X => by
    simp [whiskerRight₂]
  whiskerRight_comp x G H := hom₂_ext fun X => by
    simp [whiskerRight₂]
  whisker_assoc F _ _ y H := hom₂_ext fun X => by
    simp [whiskerLeft₂, whiskerRight₂]
  whisker_exchange x y := hom₂_ext fun X => by
    simp [whiskerLeft₂, whiskerRight₂]
  pentagon F G H K := hom₂_ext fun X => by
    simp [whiskerLeft₂, whiskerRight₂]
  triangle F G := hom₂_ext fun X => by
    simp [whiskerLeft₂, whiskerRight₂]


-- @@ L213-214 verbatim
@[simp] theorem whiskerLeft_natTrans_app (F : A ⟶ B) {G H : B ⟶ E} (y : G ⟶ H) (X : A) :
    (Hom₂.natTrans (F ◁ y)).app X = (Hom₂.natTrans y).app (F.toFunctor.obj X) := rfl


-- @@ L216-217 verbatim
@[simp] theorem whiskerRight_natTrans_app {F G : A ⟶ B} (x : F ⟶ G) (H : B ⟶ E) (X : A) :
    (Hom₂.natTrans (x ▷ H)).app X = H.toFunctor.map ((Hom₂.natTrans x).app X) := rfl


-- @@ L219-221 verbatim
@[simp] theorem associator_hom_natTrans_app {E' : PiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E)
    (H : E ⟶ E') (X : A) :
    (Hom₂.natTrans (Bicategory.associator F G H).hom).app X = 𝟙 _ := rfl


-- @@ L223-225 verbatim
@[simp] theorem associator_inv_natTrans_app {E' : PiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E)
    (H : E ⟶ E') (X : A) :
    (Hom₂.natTrans (Bicategory.associator F G H).inv).app X = 𝟙 _ := rfl


-- @@ L227-228 verbatim
@[simp] theorem leftUnitor_hom_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.leftUnitor F).hom).app X = 𝟙 _ := rfl


-- @@ L230-231 verbatim
@[simp] theorem leftUnitor_inv_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.leftUnitor F).inv).app X = 𝟙 _ := rfl


-- @@ L233-234 verbatim
@[simp] theorem rightUnitor_hom_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.rightUnitor F).hom).app X = 𝟙 _ := rfl


-- @@ L236-237 verbatim
@[simp] theorem rightUnitor_inv_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.rightUnitor F).inv).app X = 𝟙 _ := rfl


-- @@ L239-242 verbatim
theorem eqToHom_natTrans_app {F G : A ⟶ B} (h : F = G) (X : A) :
    (Hom₂.natTrans (eqToHom h)).app X = eqToHom (by rw [h]) := by
  subst h
  rfl


-- @@ L244-254 verbatim
/-- `Π-ℭ𝔞𝔱` is a strict bicategory. -/
instance instStrict : Bicategory.Strict (PiCat.{w, v, u} R) where
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc
  leftUnitor_eqToIso F := Iso.ext (hom₂_ext fun X => by
    rw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]; rfl)
  rightUnitor_eqToIso F := Iso.ext (hom₂_ext fun X => by
    rw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]; rfl)
  associator_eqToIso F G H := Iso.ext (hom₂_ext fun X => by
    rw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]; rfl)


-- @@ L256-256 verbatim
/-! ## The Π-2-category structure -/


-- @@ L258-261 verbatim
instance instPreadditiveBicategory : PreadditiveBicategory (PiCat.{w, v, u} R) where
  whiskerLeft_add _ _ _ _ _ := hom₂_ext fun _ => rfl
  add_whiskerRight x y H := hom₂_ext fun X => by
    simp


-- @@ L263-266 verbatim
instance instLinearBicategory : LinearBicategory R (PiCat.{w, v, u} R) where
  whiskerLeft_smul _ _ _ _ _ := hom₂_ext fun _ => rfl
  smul_whiskerRight r x H := hom₂_ext fun X => by
    simp


-- @@ L268-270 verbatim
variable (A) in
/-- The 1-morphism `π_A = (Π_A, β_Π = -1)` of `Π-ℭ𝔞𝔱`. -/
abbrev piHom : A ⟶ A := ⟨PiCategory.pi (R := R), PiFunctor.pi⟩


-- @@ L272-276 verbatim
/-- `β_F` is a Π-natural isomorphism `Π_B F ≅ F Π_A` (from `β_Π = -1`). -/
theorem β_isPiNatural (F : A ⟶ B) :
    PiFunctor.IsPiNatural R (F ≫ piHom B).piFunctor (piHom A ≫ F).piFunctor
      F.piFunctor.β.hom := fun X => by
  simp [PiFunctor.comp, PiFunctor.pi]


-- @@ L278-282 verbatim
/-- `ξ_A` is a Π-natural isomorphism `Π_A² ≅ 1_A` (from `ξ Π = Π ξ`). -/
theorem ξ_isPiNatural (A : PiCat.{w, v, u} R) :
    PiFunctor.IsPiNatural R (piHom A ≫ piHom A).piFunctor (𝟙 A : A ⟶ A).piFunctor
      (PiCategory.ξ (R := R) (C := A)).hom := fun X => by
  simp [PiFunctor.comp, PiFunctor.pi, PiFunctor.id, PiCategory.ξ_pi]


-- @@ L284-298 verbatim
/-- **Brundan–Ellis, after Definition 5.2.** `Π-ℭ𝔞𝔱` is a Π-2-category with `π_A = Π_A`,
`β_F` the isomorphism of the Π-functor `F` and `ξ_A` the isomorphism of the Π-category `A`. -/
instance instPiTwoCategory : PiTwoCategory R (PiCat.{w, v, u} R) where
  pi A := piHom A
  β F := iso₂Mk F.piFunctor.β (β_isPiNatural F)
  β_naturality x := hom₂_ext fun X => (Hom₂.isPiNatural x X)
  β_comp F G := hom₂_ext fun X => by
    simp [PiFunctor.comp]
  β_id A := hom₂_ext fun X => by
    simp [PiFunctor.id]
  β_pi A := hom₂_ext fun X => by
    simp [PiFunctor.pi]
  ξ A := iso₂Mk (PiCategory.ξ (R := R) (C := A)) (ξ_isPiNatural A)
  ξ_comm F := hom₂_ext fun X => by
    simpa using F.piFunctor.comm X


-- @@ L300-300 verbatim
@[simp] theorem pi_eq (A : PiCat.{w, v, u} R) : PiTwoCategory.pi (R := R) A = piHom A := rfl


-- @@ L302-303 verbatim
@[simp] theorem β_hom_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (PiTwoCategory.β (R := R) F).hom).app X = F.piFunctor.β.hom.app X := rfl


-- @@ L305-307 verbatim
@[simp] theorem ξ_hom_natTrans_app (A : PiCat.{w, v, u} R) (X : A) :
    (Hom₂.natTrans (PiTwoCategory.ξ (R := R) A).hom).app X =
      (PiCategory.ξ (R := R) (C := A)).hom.app X := rfl


-- @@ L309-311 verbatim
@[simp] theorem ξ_inv_natTrans_app (A : PiCat.{w, v, u} R) (X : A) :
    (Hom₂.natTrans (PiTwoCategory.ξ (R := R) A).inv).app X =
      (PiCategory.ξ (R := R) (C := A)).inv.app X := rfl


-- @@ L313-313 verbatim
end PiCat


-- @@ L315-315 verbatim
end StringDiagrams


-- @@ L317-317 verbatim
end
