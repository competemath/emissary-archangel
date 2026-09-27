/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import LeanPool.Circuitlib.Circuit.Category.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.Attr.Core


-- @@ L12-18 verbatim
/-! # Combinational circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Circuit


-- @@ L24-27 verbatim
/-- Category of combinational circuits. -/
structure CombinationalCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  /-- The number of wires of this object. -/
  obj : ℕ


-- @@ L29-29 verbatim
attribute [inline, simp] CombinationalCircuitCategory.obj


-- @@ L31-33 verbatim
@[simp]
instance : OfNat (CombinationalCircuitCategory V G) n where
  ofNat := .of V G n


-- @@ L35-35 verbatim
namespace CombinationalCircuitCategory


-- @@ L37-37 verbatim
universe u v


-- @@ L39-39 verbatim
variable {V : Type v} {G : Type u}


-- @@ L41-43 verbatim
/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : CombinationalCircuitCategory V G) :=
  { f : Wires V I.obj → Wires V O.obj // Monotone f }


-- @@ L45-47 verbatim
/-- The underlying identity wire-function. -/
@[inline, simp]
def idVal : Wires V n → Wires V n := fun x => x


-- @@ L49-50 verbatim
@[simp]
lemma id_monotone [Preorder V] : Monotone (idVal (V:=V) (n:=n)) := monotone_id


-- @@ L52-54 verbatim
/-- The identity morphism. -/
@[inline, simp]
def id [Preorder V] : CombinationalCircuitCategory.Hom V X X := ⟨idVal, id_monotone⟩


-- @@ L56-56 verbatim
open CategoryTheory


-- @@ L58-65 verbatim
@[inline, simp]
instance [Preorder V] : Category.{v} (CombinationalCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := by rfl
  comp_id _ := by rfl
  assoc _ _ _ := by rfl


-- @@ L67-71 verbatim
@[simp]
lemma id_coe_apply
    [Preorder V]
    (X : CombinationalCircuitCategory V G) (v : Wires V X.obj) :
    (𝟙 X : Hom V X X).val v = v := rfl


-- @@ L73-75 verbatim
/-- The wire-function that duplicates its single input wire. -/
@[inline, simp]
def fork (w : Wires V 1) : Wires V 2 := #v[w.get 0, w.get 0]


-- @@ L77-80 verbatim
@[simp]
lemma fork_monotone [Preorder V] : Monotone (fork (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> exact h 0


-- @@ L82-84 verbatim
/-- The wire-function that joins two input wires by taking their supremum. -/
@[inline, simp]
def join [SemilatticeSup V] (w : Wires V 2) : Wires V 1 := #v[w.get 0 ⊔ w.get 1]


-- @@ L86-89 verbatim
@[simp]
lemma join_monotone [SemilatticeSup V] : Monotone (join (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 := by omega
  subst this; exact sup_le_sup (h 0) (h 1)


-- @@ L91-94 verbatim
/-- The monoidal product of two objects, adding their wire counts. -/
@[inline, simp]
abbrev tensorObj (X Y : CombinationalCircuitCategory V G) : CombinationalCircuitCategory V G :=
  .of V G (X.obj + Y.obj)


-- @@ L96-106 verbatim
@[inline]
instance
    [SemilatticeSup V]
    [Gate V G]
    [Bot V] :
    CircuitCategory V G (CombinationalCircuitCategory V G) where
  gate g := ⟨Gate.gate g, Gate.gate_monotone g⟩
  stub := ⟨fun _ => #v[⊥], fun _ _ _ => le_refl _⟩
  drop := ⟨fun _ => #v[], fun _ _ _ => le_refl _⟩
  fork := ⟨fork, fork_monotone⟩
  join := ⟨join, join_monotone⟩


-- @@ L108-111 verbatim
lemma tensorHom_val_add
    {X₁ X₂ : CombinationalCircuitCategory V G} :
    min X₁.obj (X₁.obj + X₂.obj) = X₁.obj :=
  by simp


-- @@ L113-116 verbatim
lemma tensorHom_val_sub
    {X₁ X₂ : CombinationalCircuitCategory V G} :
    X₁.obj + X₂.obj - X₁.obj = X₂.obj :=
  by simp


-- @@ L118-118 verbatim
variable [SemilatticeSup V]


-- @@ L120-129 verbatim
/-- The underlying wire-function of the monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHomVal
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Wires V (X₁.obj + X₂.obj)) :
    Wires V (Y₁.obj + Y₂.obj) :=
  (f.val ((v.take X₁.obj).cast tensorHom_val_add)).append
    (g.val ((v.drop X₁.obj).cast tensorHom_val_sub))


-- @@ L131-136 verbatim
lemma tensorHom_eq
    {X₁ Y₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (f : X₁ ⟶ Y₁) :
    (f.val (Vector.ofFn fun i ↦ Vector.get a (Fin.castAdd X₂.obj i))).toArray.size = Y₁.obj :=
  (f.val (Vector.ofFn (fun i => a.get (i.castAdd _)))).size_toArray


-- @@ L138-147 verbatim
omit [SemilatticeSup V] in
lemma tensorHom_take
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.take X₁.obj).cast tensorHom_val_add =
    Vector.ofFn fun i => a.get (Fin.castAdd X₂.obj i) := by
  unfold Wires at a
  apply Wires.ext; intro i
  simp [Vector.get]
  rfl


-- @@ L149-158 verbatim
omit [SemilatticeSup V] in
lemma tensorHom_drop
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.drop X₁.obj).cast tensorHom_val_sub =
    Vector.ofFn fun i => a.get (Fin.natAdd X₁.obj i) := by
  unfold Wires at a
  apply Wires.ext; intro i
  simp [Vector.get]
  rfl


-- @@ L160-168 verbatim
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHomVal f g a).get (Fin.castAdd Y₂.obj j) =
    Vector.get (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i))) j := by
  simp only [tensorHomVal, Wires.get_append_left, tensorHom_take]


-- @@ L170-178 verbatim
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHomVal f g a).get (Fin.natAdd Y₁.obj j) =
    Vector.get (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i))) j := by
  simp only [tensorHomVal, Wires.get_append_right, tensorHom_drop]


-- @@ L180-193 verbatim
lemma tensorHom_get
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj))
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHomVal f g w).get i =
    if h : i.val < Y₁.obj
    then (f.val (Vector.ofFn fun k => w.get (Fin.castAdd X₂.obj k))).get ⟨i.val, h⟩
    else (g.val (Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k))).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tensorHom_eq_left, Fin.val_castAdd, dite_eq_left j.isLt]
  · simp only [tensorHom_eq_right, Fin.val_natAdd,
               dite_eq_right (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1; exact Fin.ext (by simp)


-- @@ L195-216 verbatim
@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHomVal f g) := fun a b h i =>
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left a j f g
      have rhs_eq := tensorHom_eq_left b j f g
      rw [lhs_eq, rhs_eq]
      exact f.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn]
        exact h (k.castAdd _)) j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right a j f g
      have rhs_eq := tensorHom_eq_right b j f g
      rw [lhs_eq, rhs_eq]
      exact g.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn]
        exact h (k.natAdd _)) j)
    i


-- @@ L218-225 verbatim
/-- The monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHomVal f g, tensorHom_monotone f g⟩


-- @@ L227-229 verbatim
/-- The underlying wire-function of the forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHomVal (h : n = m) : Wires V n → Wires V m := (·.cast h)


-- @@ L231-233 verbatim
@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (isoHomVal (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h.symm)


-- @@ L235-238 verbatim
/-- The forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHom (h : n = m) : { f : Wires V n → Wires V m // Monotone f } :=
  ⟨isoHomVal h, iso_hom_monotone h⟩


-- @@ L240-242 verbatim
/-- The underlying wire-function of the inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInvVal (h : n = m) : Wires V m → Wires V n := (·.cast h.symm)


-- @@ L244-245 verbatim
lemma iso_inv_monotone (h : n = m) : Monotone (isoInvVal (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h)


-- @@ L247-250 verbatim
/-- The inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInv (h : n = m) : { f : Wires V m → Wires V n // Monotone f } :=
  ⟨isoInvVal h, iso_inv_monotone h⟩


-- @@ L252-256 verbatim
@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    isoHom h ≫ isoInv h = 𝟙 (OfNat.ofNat n : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl


-- @@ L258-261 verbatim
lemma iso_inv_hom_id
    (h : n = m) :
    isoInv h ≫ isoHom h = 𝟙 (OfNat.ofNat m : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl


-- @@ L263-271 verbatim
/-- The isomorphism between objects with equal wire counts. -/
@[inline, simp]
def iso
    (h : n = m) :
    CombinationalCircuitCategory.of V G n ≅ CombinationalCircuitCategory.of V G m :=
  { hom := isoHom h
    inv := isoInv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }


-- @@ L273-285 verbatim
@[simp]
lemma whisker
    (X Y : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X) (𝟙 Y) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]


-- @@ L287-294 verbatim
/-- Left whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerLeft
    (X : CombinationalCircuitCategory V G)
    {Y₁ Y₂ : CombinationalCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)


-- @@ L296-302 verbatim
/-- Right whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : CombinationalCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)


-- @@ L304-320 verbatim
@[simp]
lemma tensorHom_def
    {W X Y Z : CombinationalCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext; funext v
  change tensorHomVal f g v = tensorHomVal id g (tensorHomVal f id v)
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j f g, tensorHom_eq_left _ j id g]
    simp only [id, idVal, Wires.get_ofFn]
    exact (tensorHom_eq_left v j f id).symm
  · rw [tensorHom_eq_right v j f g, tensorHom_eq_right _ j id g]
    simp only [id]
    exact congrArg (fun x => (g.val x).get j)
      (Wires.ext (fun k => by
        conv_rhs => rw [Wires.get_ofFn]
        exact (tensorHom_eq_right v k f (𝟙 _)).symm))


-- @@ L322-334 verbatim
@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X₁) (𝟙 X₂) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]


-- @@ L336-359 verbatim
@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal g₁ g₂ (tensorHomVal f₁ f₂ v) = tensorHomVal (f₁ ≫ g₁) (f₂ ≫ g₂) v
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ j g₁ g₂, tensorHom_eq_left v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₁.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_left v k f₁ f₂))
  · rw [tensorHom_eq_right _ j g₁ g₂, tensorHom_eq_right v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₂.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_right v k f₁ f₂))


-- @@ L361-363 verbatim
/-- The monoidal unit, the object with no wires. -/
@[inline, simp]
def tensorUnit : CombinationalCircuitCategory V G := .of V G 0


-- @@ L365-370 verbatim
omit [SemilatticeSup V] in
@[simp]
lemma associator_eq
    (X Y Z : CombinationalCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj


-- @@ L372-377 verbatim
/-- The associator isomorphism of the monoidal structure. -/
@[inline, simp]
def associator
    (X Y Z : CombinationalCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)


-- @@ L379-387 verbatim
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext; funext v; unfold Wires at v; apply Vector.ext; intro i hi
  simp [CategoryStruct.comp, Function.comp, Vector.append, Vector.cast]


-- @@ L389-401 verbatim
lemma pentagon
    (W X Y Z : CombinationalCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < W.obj + (X.obj + (Y.obj + Z.obj)) := i.isLt
  simp only [CategoryStruct.comp, Function.comp, associator, iso, isoHom, isoHomVal,
    tensorHomVal, CategoryStruct.id, id, idVal,
    Wires.get_append_vector, Wires.get_cast, Wires.get_cast_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;> exact congrArg v.get (Fin.ext (by simp <;> omega))


-- @@ L403-407 verbatim
omit [SemilatticeSup V] in
lemma leftUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj


-- @@ L409-413 verbatim
omit [SemilatticeSup V] in
lemma rightUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj


-- @@ L415-418 verbatim
/-- The left unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev leftUnitor (X : CombinationalCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)


-- @@ L420-423 verbatim
/-- The right unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev rightUnitor (X : CombinationalCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)


-- @@ L425-438 verbatim
lemma leftUnitor_naturality
    {X Y : CombinationalCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have harg : (Vector.ofFn fun k : Fin X.obj =>
      Vector.get v (Fin.natAdd (tensorUnit (V := V) (G := G)).obj k))
      = Vector.cast (leftUnitor_eq X) v := by
    apply Wires.ext; intro k
    simp only [Wires.get_ofFn, Wires.get_cast]
    exact congrArg v.get (Fin.ext (by simp))
  simp only [CategoryStruct.comp, Function.comp, leftUnitor, iso, isoHom, isoHomVal]
  rw [Wires.get_cast, tensorHom_get,
    dite_eq_right (show ¬ (i.val < (tensorUnit (V := V) (G := G)).obj) from by simp), harg]
  exact congrArg _ (Fin.ext (by simp))


-- @@ L440-452 verbatim
lemma rightUnitor_naturality
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have harg : (Vector.ofFn fun k : Fin X.obj =>
      Vector.get v (Fin.castAdd (tensorUnit (V := V) (G := G)).obj k))
      = Vector.cast (rightUnitor_eq X) v := by
    apply Wires.ext; intro k
    simp only [Wires.get_ofFn, Wires.get_cast]
    exact congrArg v.get (Fin.ext (by simp))
  simp only [CategoryStruct.comp, Function.comp, rightUnitor, iso, isoHom, isoHomVal]
  rw [Wires.get_cast, tensorHom_get, dite_eq_left (show i.val < Y.obj from i.isLt), harg]


-- @@ L454-454 verbatim
open MonoidalCategory


-- @@ L456-467 verbatim
lemma triangle
    (X Y : CombinationalCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, associator, leftUnitor, rightUnitor, iso,
    isoHom, isoHomVal, tensorHomVal,
    CategoryStruct.id, id, idVal,
    Wires.get_append_vector, Wires.get_cast, Wires.get_cast_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;> exact congrArg v.get (Fin.ext (by simp))


-- @@ L469-488 verbatim
@[inline, simp]
instance : MonoidalCategory.{v} (CombinationalCircuitCategory V G) where
  tensorObj
  tensorHom
  whiskerLeft
  whiskerRight
  tensorHom_def
  id_tensorHom_id
  tensorHom_comp_tensorHom
  whiskerLeft_id := whisker
  id_whiskerRight := whisker
  tensorUnit
  associator
  associator_naturality
  leftUnitor
  leftUnitor_naturality
  rightUnitor
  rightUnitor_naturality
  pentagon
  triangle


-- @@ L490-493 verbatim
@[simp]
lemma monoidal_tensorObj_obj
    (X Y : CombinationalCircuitCategory V G) :
    (X ⊗ Y).obj = X.obj + Y.obj := rfl


-- @@ L495-497 verbatim
@[simp]
lemma monoidal_tensorUnit_obj :
    (𝟙_ (CombinationalCircuitCategory V G)).obj = 0 := rfl


-- @@ L499-502 verbatim
@[simp]
lemma id_hom_apply
    (X : CombinationalCircuitCategory V G) (v : Wires V X.obj) :
    (CategoryStruct.id X : Hom V X X).val v = v := rfl


-- @@ L504-505 verbatim
omit [SemilatticeSup V] in
lemma sub_eq {X Y : CombinationalCircuitCategory V G} : X.obj + Y.obj - X.obj = Y.obj := by omega


-- @@ L507-511 verbatim
@[simp]
lemma associator_hom_apply
    (X Y Z : CombinationalCircuitCategory V G)
    (v : Wires V ((X ⊗ Y) ⊗ Z).obj) :
    (α_ X Y Z).hom.val v = v.cast (associator_eq X Y Z) := rfl


-- @@ L513-517 verbatim
@[simp]
lemma associator_inv_apply
    (X Y Z : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ (Y ⊗ Z)).obj) :
    (α_ X Y Z).inv.val v = v.cast (associator_eq X Y Z).symm := rfl


-- @@ L519-521 verbatim
lemma braiding_hom_eq
    {X Y : CombinationalCircuitCategory V G} :
    (X ⊗ Y).obj - X.obj + min X.obj (X ⊗ Y).obj = (Y ⊗ X).obj := by simp


-- @@ L523-529 verbatim
/-- The underlying wire-function of the braiding, swapping two blocks of wires. -/
@[inline, simp]
abbrev braidingHomVal
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ Y).obj) :
    Wires V (Y ⊗ X).obj :=
  ((v.drop X.obj).append (v.take X.obj)).cast braiding_hom_eq


-- @@ L531-535 verbatim
lemma braiding_hom_lt
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin Y.obj} :
    X.obj + ↑j < (X ⊗ Y).obj := by
  simp_all


-- @@ L537-542 verbatim
lemma braiding_hom_ge
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin X.obj} :
    ↑j < (X ⊗ Y).obj := by
  change j.val < X.obj + Y.obj
  omega


-- @@ L544-551 verbatim
@[simp]
lemma braiding_hom_monotone
    {X Y : CombinationalCircuitCategory V G} :
    Monotone (X.braidingHomVal Y) := fun a b hab i => by
  simp only [braidingHomVal, monoidal_tensorObj_obj, Wires.get_cast_vector,
    Wires.get_append_vector, Wires.get_take,
    Wires.get_drop]
  split_ifs <;> exact hab _


-- @@ L553-556 verbatim
/-- The braiding morphism, swapping two blocks of wires. -/
@[inline, simp]
def braidingHom (X Y : CombinationalCircuitCategory V G) : X ⊗ Y ⟶ Y ⊗ X :=
  ⟨braidingHomVal X Y, braiding_hom_monotone⟩


-- @@ L558-568 verbatim
lemma braiding_hom_inv_id
    {X Y : CombinationalCircuitCategory V G} :
    X.braidingHom Y ≫ Y.braidingHom X = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext; funext v
  apply Wires.ext; intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, braidingHom, braidingHomVal,
    monoidal_tensorObj_obj, id_coe_apply, Wires.get_cast_vector,
    Wires.get_append_vector, Wires.get_take, Wires.get_take_vector,
    Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;> exact congrArg v.get (Fin.ext (by simp <;> omega))


-- @@ L570-576 verbatim
/-- The braiding isomorphism of the symmetric monoidal structure. -/
@[inline, simp]
def braiding (X Y : CombinationalCircuitCategory V G) : X ⊗ Y ≅ Y ⊗ X :=
  { hom := braidingHom X Y
    inv := braidingHom Y X
    hom_inv_id := braiding_hom_inv_id
    inv_hom_id := braiding_hom_inv_id }


-- @@ L578-606 verbatim
lemma braiding_naturality_left
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y)
    (Z : CombinationalCircuitCategory V G) :
    f ▷ Z ≫ (Y.braiding Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Z.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrArg f.val (Wires.ext fun k => ?_)
               simp only [Wires.get_cast_vector,
                 Wires.get_append_vector,
                 Wires.get_take,
                 Wires.get_drop, Wires.get_drop_vector]
               split_ifs <;>
                 first
                   | (exfalso; omega)
                   | (exact congrArg v.get (Fin.ext (by simp)))))


-- @@ L608-626 verbatim
lemma braiding_eq
    {X Y Z : CombinationalCircuitCategory V G}
    {f : Y ⟶ Z}
    {v : Wires V (X ⊗ Y).obj}
    {j : Fin X.obj} :
    Vector.get ((X ◁ f ≫ (X.braiding Z).hom).val v) (Fin.natAdd Z.obj j) =
    Vector.get (((X.braiding Y).hom ≫ f ▷ X).val v) (Fin.natAdd Z.obj j) := by
  have hj : j.val < X.obj := j.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector,
    Fin.val_natAdd]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))


-- @@ L628-656 verbatim
lemma braiding_naturality_right
    (X : CombinationalCircuitCategory V G)
    {Y Z : CombinationalCircuitCategory V G}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (X.braiding Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Z.obj + X.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrArg f.val (Wires.ext fun k => ?_)
               simp only [Wires.get_cast_vector,
                 Wires.get_append_vector,
                 Wires.get_take, Wires.get_take_vector,
                 Wires.get_drop]
               split_ifs <;>
                 first
                   | (exfalso; omega)
                   | (exact congrArg v.get (Fin.ext (by simp)))))


-- @@ L658-662 verbatim
omit [SemilatticeSup V] in
lemma braiding_add
    {X Y : CombinationalCircuitCategory V G}
    (h : ↑i < Y.obj) :
    X.obj + ↑i < X.obj + Y.obj := by omega


-- @@ L664-670 verbatim
lemma braiding_sub
    {X Y : CombinationalCircuitCategory V G}
    {i : Fin (Y ⊗ X).obj} :
    ↑i - Y.obj < (X ⊗ Y).obj := by
  have : i.val < Y.obj + X.obj := i.isLt
  change i.val - Y.obj < X.obj + Y.obj
  omega


-- @@ L672-676 verbatim
omit [SemilatticeSup V] in
lemma braiding_get_ge
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin X.obj} :
    ¬Y.obj + ↑j < Y.obj := by omega


-- @@ L678-693 verbatim
lemma braiding_get
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ Y).obj)
    (i : Fin (Y ⊗ X).obj) :
    ((X.braiding Y).hom.val v).get i =
      if h : i.val < Y.obj
      then v.get ⟨X.obj + i.val, braiding_add h⟩
      else v.get ⟨i.val - Y.obj, braiding_sub⟩ := by
  have hi : i.val < Y.obj + X.obj := i.isLt
  simp only [braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_drop]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))


-- @@ L695-701 verbatim
lemma braiding_get_castAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin Y.obj) :
    ((braiding X Y).hom.val v).get (Fin.castAdd X.obj j) =
    v.get (Fin.natAdd X.obj j) := by
  simp only [braiding_get, Fin.val_castAdd, dite_eq_left j.isLt]
  exact congrArg v.get (Fin.ext (by simp))


-- @@ L703-709 verbatim
lemma braiding_get_natAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin X.obj) :
    ((braiding X Y).hom.val v).get (Fin.natAdd Y.obj j) =
    v.get (Fin.castAdd Y.obj j) := by
  simp only [braiding_get, braiding_get_ge, Fin.val_natAdd]
  exact congrArg v.get (Fin.ext (by simp))


-- @@ L711-727 verbatim
lemma hexagon_forward
    (X Y Z : CombinationalCircuitCategory V G) :
    (α_ X Y Z).hom ≫ (X.braiding (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (X.braiding Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (X.braiding Z).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Y.obj + (Z.obj + X.obj) := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    MonoidalCategoryStruct.associator, associator, iso, isoHom, isoHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj,
    CategoryStruct.id, id, idVal,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp <;> omega)))


-- @@ L729-745 verbatim
lemma hexagon_reverse
    (X Y Z : CombinationalCircuitCategory V G) :
    (α_ X Y Z).inv ≫ ((X ⊗ Y).braiding Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Z.obj + X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    MonoidalCategoryStruct.associator, associator, iso, isoInv, isoInvVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj,
    CategoryStruct.id, id, idVal,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp; omega)))


-- @@ L747-754 verbatim
lemma symmetry
    (X Y : CombinationalCircuitCategory V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp, braiding_get]
  have htXY : (X ⊗ Y).obj = X.obj + Y.obj := rfl
  split <;> split <;>
  exact congrArg v.get (Fin.ext (by simp only []; omega))


-- @@ L756-763 verbatim
@[inline, simp]
instance : SymmetricCategory (CombinationalCircuitCategory V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry


-- @@ L765-765 verbatim
end CombinationalCircuitCategory


-- @@ L767-767 verbatim
end Circuit
