/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Comonoid
public import PolyFun.PFunctor.Lens.Duoidal
public import Mathlib.CategoryTheory.Iso


-- @@ L12-31 verbatim
/-!
# Tensor products of polynomial comonoids

The duoidal interchange lens equips the tensor product of two comonoids in
`(Poly, ◃, y)` with a comonoid structure.  Its objects and outgoing arrows are
pairs, its counit combines the two component counits, and its comultiplication
composes each component independently.  This is the concrete construction in
Spivak–Niu, Proposition 8.77 in the current edition (Proposition 8.79 in the
earlier-edition notes).

The two input comonoids retain independent position and direction universes.
The counit uses `Lens.tensorUnitMap` to compare their independently instantiated
copies of the composition unit with the unit at the componentwise maximum.
Tensor products of retrofunctors are defined componentwise.

The common composition unit `y` is packaged as `Comonoid.unit`.  The tensor
left/right unitors and associator lift to `CategoryTheory.Iso`s of comonoids;
their forward and inverse retrofunctors use exactly the corresponding
polynomial-lens equivalences.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃


-- @@ L37-37 verbatim
namespace PFunctor

-- @@ L38-38 verbatim
namespace Comonoid


-- @@ L40-40 verbatim
/-! ## The composition-unit comonoid -/


-- @@ L42-53 expanded
/-- The composition unit `y` as a composition comonoid.  Its counit and
comultiplication are the canonical maps between universe-instantiated copies
of `y`; all of its arrows are the unique unit arrow. -/
@[reducible]
def unit : Comonoid.{uA, uB} where
  carrier := y
  counit := Lens.unitComparison
  comult := comp Lens.compUnitMap (Lens.unitComparison : Lens y.{uA, uB} y.{max uA uB, uB})
  counit_left := Lens.compUnitMap_counit_left
  counit_right := Lens.compUnitMap_counit_right
  coassoc := Lens.compUnitMap_coassoc.{uA, uB}


-- @@ L55-55 verbatim
@[simp] theorem unit_carrier : (unit.{uA, uB}).carrier = y := rfl


-- @@ L57-59 verbatim
/-- The counit of the composition-unit comonoid is the canonical comparison
between its two universe instantiations. -/
theorem unit_counit : (unit.{uA, uB}).counit = Lens.unitComparison := rfl


-- @@ L61-66 expanded
/-- The comultiplication of the composition-unit comonoid is the canonical
map `y ⇆ y ◃ y`, after comparing its source universe instantiation. -/
theorem unit_comult :
    (unit.{uA, uB}).comult =
      comp Lens.compUnitMap (Lens.unitComparison : Lens y.{uA, uB} y.{max uA uB, uB}) :=
  rfl


-- @@ L68-68 verbatim
/-! ## Tensor product -/


-- @@ L70-74 expanded
/-- The counit of the tensor product of two composition comonoids. -/
def tensorCounit (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens (C.carrier ⊗ D.carrier) y.{max (max uA₁ uA₂) (max uB₁ uB₂), max uB₁ uB₂} :=
  comp Lens.tensorUnitMap (tensorMap C.counit D.counit)


-- @@ L76-81 expanded
/-- The comultiplication of the tensor product of two composition comonoids. -/
def tensorComult (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens (C.carrier ⊗ D.carrier) ((C.carrier ⊗ D.carrier) ◃ (C.carrier ⊗ D.carrier)) :=
  comp (Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier) (tensorMap C.comult D.comult)


-- @@ L83-91 expanded
private theorem tensorCounit_left_factor (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    comp
        (comp Lens.Equiv.yComp.toLens
          (compMap (tensorCounit C D) (Lens.id (C.carrier ⊗ D.carrier))))
        (tensorComult C D) =
      (tensorMap
        (comp (comp Lens.Equiv.yComp.toLens (compMap C.counit (Lens.id C.carrier))) C.comult)
        (comp (comp Lens.Equiv.yComp.toLens (compMap D.counit (Lens.id D.carrier))) D.comult)) :=
  rfl


-- @@ L93-101 expanded
private theorem tensorCounit_right_factor (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    comp
        (comp Lens.Equiv.compY.toLens
          (compMap (Lens.id (C.carrier ⊗ D.carrier)) (tensorCounit C D)))
        (tensorComult C D) =
      (tensorMap
        (comp (comp Lens.Equiv.compY.toLens (compMap (Lens.id C.carrier) C.counit)) C.comult)
        (comp (comp Lens.Equiv.compY.toLens (compMap (Lens.id D.carrier) D.counit)) D.comult)) :=
  rfl


-- @@ L103-115 expanded
private theorem tensorComult_assoc_left_factor (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    comp
        (comp Lens.Equiv.compAssoc.toLens
          (compMap (tensorComult C D) (Lens.id (C.carrier ⊗ D.carrier))))
        (tensorComult C D) =
      comp
        (comp
          (compMap (Lens.id (C.carrier ⊗ D.carrier))
            (Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier))
          (Lens.duoidalLens C.carrier (C.carrier ◃ C.carrier) D.carrier (D.carrier ◃ D.carrier)))
        (tensorMap
          (comp (comp Lens.Equiv.compAssoc.toLens (compMap C.comult (Lens.id C.carrier))) C.comult)
          (comp (comp Lens.Equiv.compAssoc.toLens (compMap D.comult (Lens.id D.carrier)))
            D.comult)) :=
  rfl


-- @@ L117-126 expanded
private theorem tensorComult_assoc_right_factor (C : Comonoid.{uA₁, uB₁})
    (D : Comonoid.{uA₂, uB₂}) :
    comp (compMap (Lens.id (C.carrier ⊗ D.carrier)) (tensorComult C D)) (tensorComult C D) =
      comp
        (comp
          (compMap (Lens.id (C.carrier ⊗ D.carrier))
            (Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier))
          (Lens.duoidalLens C.carrier (C.carrier ◃ C.carrier) D.carrier (D.carrier ◃ D.carrier)))
        (tensorMap (comp (compMap (Lens.id C.carrier) C.comult) C.comult)
          (comp (compMap (Lens.id D.carrier) D.comult) D.comult)) :=
  rfl


-- @@ L128-145 verbatim
/-- The tensor product of two comonoids in `(Poly, ◃, y)`.  The construction
is heterogeneous in both input universe pairs and lands at their componentwise
maximum. -/
@[reducible]
def tensor (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Comonoid.{max uA₁ uA₂, max uB₁ uB₂} where
  carrier := C.carrier ⊗ D.carrier
  counit := tensorCounit C D
  comult := tensorComult C D
  counit_left := by
    rw [tensorCounit_left_factor, C.counit_left, D.counit_left,
      Lens.tensorMap_id]
  counit_right := by
    rw [tensorCounit_right_factor, C.counit_right, D.counit_right,
      Lens.tensorMap_id]
  coassoc := by
    rw [tensorComult_assoc_left_factor, C.coassoc, D.coassoc]
    exact (tensorComult_assoc_right_factor C D).symm


-- @@ L147-148 verbatim
@[simp] theorem tensor_carrier (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).carrier = C.carrier ⊗ D.carrier := rfl


-- @@ L150-153 verbatim
/-- The tensor-product counit is the componentwise counit followed by the
canonical comparison of tensor units. -/
theorem tensor_counit (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).counit = tensorCounit C D := rfl


-- @@ L155-158 verbatim
/-- The tensor-product comultiplication is componentwise comultiplication
followed by duoidal interchange. -/
theorem tensor_comult (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).comult = tensorComult C D := rfl


-- @@ L160-160 verbatim
/-! ## Tensor coherence isomorphisms -/


-- @@ L162-175 verbatim
/-- The left tensor unitor, lifted from polynomial lenses to composition
comonoids.  Both directions preserve identities and composition. -/
def tensorUnitLeftIso (C : Comonoid.{uA, uB}) :
    CategoryTheory.Iso (tensor (unit.{uA, uB}) C) C where
  hom := {
    toLens := (Lens.Equiv.yTensor (P := C.carrier)).toLens
    map_counit := rfl
    map_comult := rfl }
  inv := {
    toLens := (Lens.Equiv.yTensor (P := C.carrier)).invLens
    map_counit := rfl
    map_comult := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl


-- @@ L177-179 verbatim
@[simp] theorem tensorUnitLeftIso_hom_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitLeftIso C).hom.toLens =
      (Lens.Equiv.yTensor (P := C.carrier)).toLens := rfl


-- @@ L181-183 verbatim
@[simp] theorem tensorUnitLeftIso_inv_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitLeftIso C).inv.toLens =
      (Lens.Equiv.yTensor (P := C.carrier)).invLens := rfl


-- @@ L185-198 verbatim
/-- The right tensor unitor, lifted from polynomial lenses to composition
comonoids.  Both directions preserve identities and composition. -/
def tensorUnitRightIso (C : Comonoid.{uA, uB}) :
    CategoryTheory.Iso (tensor C (unit.{uA, uB})) C where
  hom := {
    toLens := (Lens.Equiv.tensorY (P := C.carrier)).toLens
    map_counit := rfl
    map_comult := rfl }
  inv := {
    toLens := (Lens.Equiv.tensorY (P := C.carrier)).invLens
    map_counit := rfl
    map_comult := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl


-- @@ L200-202 verbatim
@[simp] theorem tensorUnitRightIso_hom_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitRightIso C).hom.toLens =
      (Lens.Equiv.tensorY (P := C.carrier)).toLens := rfl


-- @@ L204-206 verbatim
@[simp] theorem tensorUnitRightIso_inv_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitRightIso C).inv.toLens =
      (Lens.Equiv.tensorY (P := C.carrier)).invLens := rfl


-- @@ L208-226 verbatim
/-- The tensor associator, lifted from polynomial lenses to composition
comonoids.  The three input universe pairs remain independent. -/
def tensorAssocIso
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    CategoryTheory.Iso (tensor (tensor C D) E)
      (tensor C (tensor D E)) where
  hom := {
    toLens := (Lens.Equiv.tensorAssoc
      (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens
    map_counit := rfl
    map_comult := rfl }
  inv := {
    toLens := (Lens.Equiv.tensorAssoc
      (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens
    map_counit := rfl
    map_comult := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl


-- @@ L228-233 verbatim
@[simp] theorem tensorAssocIso_hom_toLens
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (tensorAssocIso C D E).hom.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens := rfl


-- @@ L235-240 verbatim
@[simp] theorem tensorAssocIso_inv_toLens
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (tensorAssocIso C D E).inv.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens := rfl


-- @@ L242-242 verbatim
/-! ## Tensor products of retrofunctors -/


-- @@ L244-244 verbatim
namespace Hom


-- @@ L246-259 expanded
/-- The componentwise tensor product of two retrofunctors. -/
def tensor {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}} (f : Hom C₁ D₁)
    (g : Hom C₂ D₂) : Hom (Comonoid.tensor C₁ C₂) (Comonoid.tensor D₁ D₂)
    where
  toLens := tensorMap f.toLens g.toLens
  map_counit :=
    by
    change
      comp Lens.tensorUnitMap (comp (tensorMap D₁.counit D₂.counit) (tensorMap f.toLens g.toLens)) =
        _
    rw [← Lens.tensorMap_comp, f.map_counit, g.map_counit]
    rfl
  map_comult :=
    by
    change
      comp (Lens.duoidalLens D₁.carrier D₁.carrier D₂.carrier D₂.carrier)
          (comp (tensorMap D₁.comult D₂.comult) (tensorMap f.toLens g.toLens)) =
        _
    rw [← Lens.tensorMap_comp, f.map_comult, g.map_comult]
    rfl


-- @@ L261-262 expanded
@[simp]
theorem tensor_toLens {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}} (f : Hom C₁ D₁)
    (g : Hom C₂ D₂) : (tensor f g).toLens = tensorMap f.toLens g.toLens :=
  rfl


-- @@ L264-266 verbatim
@[simp] theorem tensor_id (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    tensor (Hom.id C) (Hom.id D) = Hom.id (Comonoid.tensor C D) :=
  Hom.ext _ _ Lens.tensorMap_id


-- @@ L268-271 verbatim
theorem tensor_comp {C₁ D₁ E₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ E₂ : Comonoid.{uA₂, uB₂}}
    (f₁ : Hom C₁ D₁) (g₁ : Hom D₁ E₁) (f₂ : Hom C₂ D₂) (g₂ : Hom D₂ E₂) :
    tensor (f₁.comp g₁) (f₂.comp g₂) = (tensor f₁ f₂).comp (tensor g₁ g₂) :=
  Hom.ext _ _ (Lens.tensorMap_comp f₁.toLens f₂.toLens g₁.toLens g₂.toLens)


-- @@ L273-273 verbatim
end Hom

-- @@ L274-274 verbatim
end Comonoid

-- @@ L275-275 verbatim
end PFunctor
