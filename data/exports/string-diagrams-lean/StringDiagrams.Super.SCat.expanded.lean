import StringDiagrams.Super.FunctorCategory
import StringDiagrams.Super.Bicategory
import StringDiagrams.Super.Pi


-- @@ L5-35 verbatim
/-!
# The strict 2-supercategories `𝔖ℭ𝔞𝔱` and `Π-𝔖ℭ𝔞𝔱`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Section 2 (after Definition 2.1) and Section 3 (before Lemma 3.2).

`SCat R` is the type of (small, in fixed universes) supercategories over `R`: an `R`-linear
category with a supercategory structure (`StringDiagrams.Supercategory`). It is a strict
2-supercategory (in the unpacked form `TwoSupercategory` of Definition 2.2(i), with
`BicategoryStruct.Strict`, i.e. Definition 2.1):

* the morphism supercategories are the supercategories `ℋom(A, B)` of superfunctors and
  supernatural transformations (`Supercategory.Superfunctor R A B`, Example 1.2(iv));
* horizontal composition of 1-morphisms is composition of superfunctors (`G F := G ∘ F`, in
  diagrammatic order `F ≫ G`);
* horizontal composition of supernatural transformations is
  `(yx)_λ := y_{Hλ} ∘ G x_λ` (`Superfunctor.hcomp`), obtained from the whiskerings
  `Superfunctor.whiskerLeft` and `Superfunctor.whiskerRight`;
* the associator and unitors are identities, and the super interchange law is
  `Superfunctor.whisker_exchange`.

`PiSCat R` is the type of Π-supercategories (Definition 1.7). With superfunctors and
supernatural transformations it is the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱`; its Π-2-supercategory
structure (Definition 3.1) is in `StringDiagrams.Super.PiTwo`.

## Main definitions

* `SCat R`, with instances `BicategoryStruct (SCat R)`, `TwoSupercategory R (SCat R)` and
  `BicategoryStruct.Strict (SCat R)`.
* `PiSCat R`, with the same instances.
-/


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
namespace StringDiagrams


-- @@ L41-41 verbatim
open CategoryTheory Supercategory


-- @@ L43-43 verbatim
universe w v u


-- @@ L45-45 verbatim
variable (R : Type w) [CommRing R]


-- @@ L47-55 verbatim
/-- A supercategory over `R` (Brundan–Ellis, Definition 1.1(i)), bundled: an `R`-linear
category `carrier` with a supercategory structure. -/
structure SCat where
  /-- The objects. -/
  carrier : Type u
  [str : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear R carrier]
  [super : Supercategory R carrier]


-- @@ L57-57 verbatim
namespace SCat


-- @@ L59-59 verbatim
attribute [instance] str preadditive linear super


-- @@ L61-61 verbatim
variable {R}


-- @@ L63-63 verbatim
instance : CoeSort (SCat.{w, v, u} R) (Type u) := ⟨SCat.carrier⟩


-- @@ L65-69 verbatim
variable (R) in
/-- The bundled supercategory of a supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C] :
    SCat.{w, v, u} R :=
  ⟨C⟩


-- @@ L71-82 verbatim
/-- The horizontal composition data of `𝔖ℭ𝔞𝔱`: superfunctors, supernatural transformations,
their whiskerings, and identity coherence maps. -/
instance : BicategoryStruct.{max u v, max u v} (SCat.{w, v, u} R) where
  Hom A B := Superfunctor R A B
  id A := Superfunctor.id R A
  comp F G := F.comp G
  homCategory _ _ := inferInstance
  whiskerLeft F _ _ y := Superfunctor.whiskerLeft F y
  whiskerRight x G := Superfunctor.whiskerRight x G
  associator F G H := Iso.refl (F.comp (G.comp H))
  leftUnitor F := Iso.refl F
  rightUnitor F := Iso.refl F


-- @@ L84-85 verbatim
instance (A B : SCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (Superfunctor R A B))


-- @@ L87-88 verbatim
instance (A B : SCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (Superfunctor R A B))


-- @@ L90-91 verbatim
instance (A B : SCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (Superfunctor R A B))


-- @@ L93-93 verbatim
open BicategoryStruct


-- @@ L95-95 verbatim
theorem hom_def (A B : SCat.{w, v, u} R) : (A ⟶ B) = Superfunctor R A B := rfl


-- @@ L97-97 verbatim
theorem comp_def {A B C : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) : F ≫ G = F.comp G := rfl


-- @@ L99-99 verbatim
theorem id_def (A : SCat.{w, v, u} R) : 𝟙 A = Superfunctor.id R A := rfl


-- @@ L101-102 verbatim
theorem whiskerLeft_def {A B C : SCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) :
    F ◁ y = Superfunctor.whiskerLeft F y := rfl


-- @@ L104-105 verbatim
theorem whiskerRight_def {A B C : SCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) :
    x ▷ G = Superfunctor.whiskerRight x G := rfl


-- @@ L107-108 verbatim
@[simp] theorem associator_hom {A B C D : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl


-- @@ L110-111 verbatim
@[simp] theorem associator_inv {A B C D : SCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl


-- @@ L113-114 verbatim
@[simp] theorem leftUnitor_hom {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl


-- @@ L116-117 verbatim
@[simp] theorem leftUnitor_inv {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl


-- @@ L119-120 verbatim
@[simp] theorem rightUnitor_hom {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl


-- @@ L122-123 verbatim
@[simp] theorem rightUnitor_inv {A B : SCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl



-- @@ L126-126 verbatim
section App


-- @@ L128-128 verbatim
variable {A B C : SCat.{w, v, u} R}


-- @@ L130-132 verbatim
@[simp] theorem comp_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  Superfunctor.comp_app_zero x y X


-- @@ L134-136 verbatim
@[simp] theorem comp_app_one {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  Superfunctor.comp_app_one x y X


-- @@ L138-139 verbatim
theorem comp_app {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : A.carrier) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl


-- @@ L141-142 verbatim
@[simp] theorem id_app_zero (F : A ⟶ B) (X : A.carrier) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl


-- @@ L144-144 verbatim
@[simp] theorem id_app_one (F : A ⟶ B) (X : A.carrier) : (𝟙 F : F ⟶ F).app 1 X = 0 := rfl


-- @@ L146-147 verbatim
@[simp] theorem add_app {F G : A ⟶ B} (x y : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (x + y).app p X = x.app p X + y.app p X := rfl


-- @@ L149-150 verbatim
@[simp] theorem neg_app {F G : A ⟶ B} (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (-x).app p X = -x.app p X := rfl


-- @@ L152-153 verbatim
@[simp] theorem smul_app {F G : A ⟶ B} (r : R) (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (r • x).app p X = r • x.app p X := rfl


-- @@ L155-156 verbatim
@[simp] theorem zero_app {F G : A ⟶ B} (p : ZMod 2) (X : A.carrier) :
    (0 : F ⟶ G).app p X = 0 := rfl


-- @@ L158-159 verbatim
@[simp] theorem whiskerLeft_app (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) (p : ZMod 2)
    (X : A.carrier) : (F ◁ y).app p X = y.app p (F.obj X) := rfl


-- @@ L161-162 verbatim
@[simp] theorem whiskerRight_app {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) (p : ZMod 2)
    (X : A.carrier) : (x ▷ G).app p X = G.map (x.app p X) := rfl


-- @@ L164-165 verbatim
@[simp] theorem comp_obj (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    Superfunctor.obj (F ≫ G) X = G.obj (F.obj X) := rfl


-- @@ L167-168 verbatim
@[simp] theorem comp_map (F : A ⟶ B) (G : B ⟶ C) {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (F ≫ G) f = G.map (F.map f) := rfl


-- @@ L170-170 verbatim
@[simp] theorem id_obj (X : A.carrier) : Superfunctor.obj (𝟙 A) X = X := rfl


-- @@ L172-172 verbatim
@[simp] theorem id_map {X Y : A.carrier} (f : X ⟶ Y) : Superfunctor.map (𝟙 A) f = f := rfl


-- @@ L174-176 verbatim
theorem hom_ext {F G : A ⟶ B} {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  Superfunctor.hom_ext_parity h0 h1


-- @@ L178-178 verbatim
end App


-- @@ L180-217 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, Section 2.** Supercategories, superfunctors and supernatural
transformations form a 2-supercategory `𝔖ℭ𝔞𝔱`. -/
instance : TwoSupercategory R (SCat.{w, v, u} R) where
  whiskerLeft_id F G := Superfunctor.whiskerLeft_id F G
  whiskerLeft_comp F _ _ _ y z := Superfunctor.whiskerLeft_comp F y z
  id_whiskerLeft y := by
    rw [leftUnitor_hom, leftUnitor_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  comp_whiskerLeft F G _ _ y := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  id_whiskerRight F G := Superfunctor.id_whiskerRight F G
  comp_whiskerRight x z G := Superfunctor.comp_whiskerRight x z G
  whiskerRight_id x := by
    rw [rightUnitor_hom, rightUnitor_inv]; erw [Category.id_comp, Category.comp_id]
    exact Superfunctor.hom_ext fun _ _ => rfl
  whiskerRight_comp x G H := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  whisker_assoc F _ _ y H := by
    rw [associator_hom, associator_inv]; erw [Category.id_comp, Category.comp_id]; rfl
  pentagon F G H K := by
    simp only [associator_hom]; erw [Category.id_comp]
    change Superfunctor.whiskerRight (𝟙 (F.comp (G.comp H))) K ≫
      Superfunctor.whiskerLeft F (𝟙 (G.comp (H.comp K))) =
      Superfunctor.whiskerLeft F (𝟙 (G.comp (H.comp K)))
    rw [Superfunctor.id_whiskerRight, Superfunctor.whiskerLeft_id, Category.id_comp]
  triangle F G := by
    simp only [associator_hom, leftUnitor_hom, rightUnitor_hom]; erw [Category.id_comp]
    exact (Superfunctor.whiskerLeft_id F G).trans (Superfunctor.id_whiskerRight F G).symm
  whiskerLeft_add F _ _ y z := Superfunctor.whiskerLeft_add F y z
  add_whiskerRight x z G := Superfunctor.add_whiskerRight x z G
  whiskerLeft_smul F _ _ r y := Superfunctor.whiskerLeft_smul F r y
  smul_whiskerRight r x G := Superfunctor.smul_whiskerRight r x G
  whiskerLeft_mem F _ _ _ _ hy := Superfunctor.whiskerLeft_mem F hy
  whiskerRight_mem G hx := Superfunctor.whiskerRight_mem hx G
  super_interchange hx hy := Superfunctor.whisker_exchange hx hy
  associator_hom_mem _ _ _ := id_mem _
  leftUnitor_hom_mem _ := id_mem _
  rightUnitor_hom_mem _ := id_mem _


-- @@ L219-226 verbatim
/-- **Brundan–Ellis, Section 2.** `𝔖ℭ𝔞𝔱` is a strict 2-supercategory (Definition 2.1). -/
instance : BicategoryStruct.Strict (SCat.{w, v, u} R) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl


-- @@ L228-228 verbatim
end SCat


-- @@ L230-230 verbatim
/-! ## Π-supercategories -/


-- @@ L232-234 verbatim
/-- A Π-supercategory over `R` (Brundan–Ellis, Definition 1.7), bundled. -/
structure PiSCat extends SCat.{w, v, u} R where
  [pi : PiSupercategory R carrier]


-- @@ L236-236 verbatim
namespace PiSCat


-- @@ L238-238 verbatim
attribute [instance] pi


-- @@ L240-240 verbatim
variable {R}


-- @@ L242-242 verbatim
instance : CoeSort (PiSCat.{w, v, u} R) (Type u) := ⟨fun A => A.carrier⟩


-- @@ L244-248 verbatim
variable (R) in
/-- The bundled Π-supercategory of a Π-supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [PiSupercategory R C] : PiSCat.{w, v, u} R :=
  ⟨SCat.of R C⟩


-- @@ L250-250 verbatim
open BicategoryStruct


-- @@ L252-263 verbatim
/-- The data of the 2-supercategory `Π-𝔖ℭ𝔞𝔱` of Π-supercategories, superfunctors and
supernatural transformations: that of `𝔖ℭ𝔞𝔱` on the underlying supercategories. -/
instance : BicategoryStruct.{max u v, max u v} (PiSCat.{w, v, u} R) where
  Hom A B := A.toSCat ⟶ B.toSCat
  id A := 𝟙 A.toSCat
  comp F G := F ≫ G
  homCategory A B := inferInstanceAs (Category (A.toSCat ⟶ B.toSCat))
  whiskerLeft F _ _ y := F ◁ y
  whiskerRight x G := x ▷ G
  associator F G H := associator (B := SCat R) F G H
  leftUnitor F := leftUnitor (B := SCat R) F
  rightUnitor F := rightUnitor (B := SCat R) F


-- @@ L265-266 verbatim
instance (A B : PiSCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (A.toSCat ⟶ B.toSCat))


-- @@ L268-269 verbatim
instance (A B : PiSCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (A.toSCat ⟶ B.toSCat))


-- @@ L271-272 verbatim
instance (A B : PiSCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (A.toSCat ⟶ B.toSCat))


-- @@ L274-274 verbatim
theorem hom_def (A B : PiSCat.{w, v, u} R) : (A ⟶ B) = Superfunctor R A B := rfl


-- @@ L276-277 verbatim
theorem comp_def {A B C : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    F ≫ G = Superfunctor.comp F G := rfl


-- @@ L279-279 verbatim
theorem id_def (A : PiSCat.{w, v, u} R) : 𝟙 A = Superfunctor.id R A := rfl


-- @@ L281-282 verbatim
theorem whiskerLeft_def {A B C : PiSCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) :
    F ◁ y = Superfunctor.whiskerLeft F y := rfl


-- @@ L284-285 verbatim
theorem whiskerRight_def {A B C : PiSCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H)
    (G : B ⟶ C) : x ▷ G = Superfunctor.whiskerRight x G := rfl



-- @@ L288-288 verbatim
section App


-- @@ L290-290 verbatim
variable {A B C : PiSCat.{w, v, u} R}


-- @@ L292-294 verbatim
@[simp] theorem comp_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  Superfunctor.comp_app_zero x y X


-- @@ L296-298 verbatim
@[simp] theorem comp_app_one {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.carrier) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  Superfunctor.comp_app_one x y X


-- @@ L300-301 verbatim
theorem comp_app {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : A.carrier) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl


-- @@ L303-304 verbatim
@[simp] theorem id_app_zero (F : A ⟶ B) (X : A.carrier) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl


-- @@ L306-306 verbatim
@[simp] theorem id_app_one (F : A ⟶ B) (X : A.carrier) : (𝟙 F : F ⟶ F).app 1 X = 0 := rfl


-- @@ L308-309 verbatim
@[simp] theorem add_app {F G : A ⟶ B} (x y : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (x + y).app p X = x.app p X + y.app p X := rfl


-- @@ L311-312 verbatim
@[simp] theorem neg_app {F G : A ⟶ B} (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (-x).app p X = -x.app p X := rfl


-- @@ L314-315 verbatim
@[simp] theorem smul_app {F G : A ⟶ B} (r : R) (x : F ⟶ G) (p : ZMod 2) (X : A.carrier) :
    (r • x).app p X = r • x.app p X := rfl


-- @@ L317-318 verbatim
@[simp] theorem zero_app {F G : A ⟶ B} (p : ZMod 2) (X : A.carrier) :
    (0 : F ⟶ G).app p X = 0 := rfl


-- @@ L320-321 verbatim
@[simp] theorem whiskerLeft_app (F : A ⟶ B) {G K : B ⟶ C} (y : G ⟶ K) (p : ZMod 2)
    (X : A.carrier) : (F ◁ y).app p X = y.app p (F.obj X) := rfl


-- @@ L323-324 verbatim
@[simp] theorem whiskerRight_app {F H : A ⟶ B} (x : F ⟶ H) (G : B ⟶ C) (p : ZMod 2)
    (X : A.carrier) : (x ▷ G).app p X = G.map (x.app p X) := rfl


-- @@ L326-327 verbatim
@[simp] theorem comp_obj (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    Superfunctor.obj (F ≫ G) X = G.obj (F.obj X) := rfl


-- @@ L329-330 verbatim
@[simp] theorem comp_map (F : A ⟶ B) (G : B ⟶ C) {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (F ≫ G) f = G.map (F.map f) := rfl


-- @@ L332-332 verbatim
@[simp] theorem id_obj (X : A.carrier) : Superfunctor.obj (𝟙 A) X = X := rfl


-- @@ L334-334 verbatim
@[simp] theorem id_map {X Y : A.carrier} (f : X ⟶ Y) : Superfunctor.map (𝟙 A) f = f := rfl


-- @@ L336-338 verbatim
theorem hom_ext {F G : A ⟶ B} {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  Superfunctor.hom_ext_parity h0 h1


-- @@ L340-340 verbatim
end App


-- @@ L342-365 verbatim
/-- **Brundan–Ellis, Section 3.** Π-supercategories, superfunctors and supernatural
transformations form a 2-supercategory `Π-𝔖ℭ𝔞𝔱`. -/
instance : TwoSupercategory R (PiSCat.{w, v, u} R) where
  whiskerLeft_id F G := TwoSupercategory.whiskerLeft_id (R := R) (B := SCat R) F G
  whiskerLeft_comp F _ _ _ y z := TwoSupercategory.whiskerLeft_comp (R := R) (B := SCat R) F y z
  id_whiskerLeft y := TwoSupercategory.id_whiskerLeft (R := R) (B := SCat R) y
  comp_whiskerLeft F G _ _ y := TwoSupercategory.comp_whiskerLeft (R := R) (B := SCat R) F G y
  id_whiskerRight F G := TwoSupercategory.id_whiskerRight (R := R) (B := SCat R) F G
  comp_whiskerRight x z G := TwoSupercategory.comp_whiskerRight (R := R) (B := SCat R) x z G
  whiskerRight_id x := TwoSupercategory.whiskerRight_id (R := R) (B := SCat R) x
  whiskerRight_comp x G H := TwoSupercategory.whiskerRight_comp (R := R) (B := SCat R) x G H
  whisker_assoc F _ _ y H := TwoSupercategory.whisker_assoc (R := R) (B := SCat R) F y H
  pentagon F G H K := TwoSupercategory.pentagon (R := R) (B := SCat R) F G H K
  triangle F G := TwoSupercategory.triangle (R := R) (B := SCat R) F G
  whiskerLeft_add F _ _ y z := TwoSupercategory.whiskerLeft_add (R := R) (B := SCat R) F y z
  add_whiskerRight x z G := TwoSupercategory.add_whiskerRight (R := R) (B := SCat R) x z G
  whiskerLeft_smul F _ _ r y := TwoSupercategory.whiskerLeft_smul (B := SCat R) F r y
  smul_whiskerRight r x G := TwoSupercategory.smul_whiskerRight (B := SCat R) r x G
  whiskerLeft_mem F _ _ _ _ hy := TwoSupercategory.whiskerLeft_mem (B := SCat R) F hy
  whiskerRight_mem G hx := TwoSupercategory.whiskerRight_mem (B := SCat R) G hx
  super_interchange hx hy := TwoSupercategory.super_interchange (B := SCat R) hx hy
  associator_hom_mem F G H := TwoSupercategory.associator_hom_mem (B := SCat R) F G H
  leftUnitor_hom_mem F := TwoSupercategory.leftUnitor_hom_mem (B := SCat R) F
  rightUnitor_hom_mem F := TwoSupercategory.rightUnitor_hom_mem (B := SCat R) F


-- @@ L367-368 verbatim
@[simp] theorem associator_hom {A B C D : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl


-- @@ L370-371 verbatim
@[simp] theorem associator_inv {A B C D : PiSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl


-- @@ L373-374 verbatim
@[simp] theorem leftUnitor_hom {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl


-- @@ L376-377 verbatim
@[simp] theorem leftUnitor_inv {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl


-- @@ L379-380 verbatim
@[simp] theorem rightUnitor_hom {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl


-- @@ L382-383 verbatim
@[simp] theorem rightUnitor_inv {A B : PiSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl


-- @@ L385-392 verbatim
/-- `Π-𝔖ℭ𝔞𝔱` is a strict 2-supercategory. -/
instance : BicategoryStruct.Strict (PiSCat.{w, v, u} R) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl


-- @@ L394-394 verbatim
end PiSCat


-- @@ L396-396 verbatim
end StringDiagrams


-- @@ L398-398 verbatim
end
