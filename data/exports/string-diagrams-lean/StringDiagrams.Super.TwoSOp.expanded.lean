import StringDiagrams.Super.TwoSOpWhisker


-- @@ L3-11 verbatim
/-!
# The 2-super-opposite: data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 3.4: for
a 2-supercategory `𝔄`, the 2-supercategory `𝔄^{sop}` has the objects and 1-morphisms of `𝔄` and
hom supercategories `ℋom_𝔄(λ, μ)^{sop}`; horizontal composition and whiskering are those of `𝔄`.
The associator and unitors of `𝔄^{sop}` are the `sop` of the inverses of those of `𝔄` (`TwoSOp`,
`TwoSOp.bicategoryStruct`).
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
namespace StringDiagrams

-- @@ L15-15 verbatim
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

-- @@ L16-16 verbatim
universe r u v w


-- @@ L18-20 verbatim
/-- Same objects, with Koszul super-opposite hom categories. -/
structure TwoSOp (R : Type r) (B : Type u) where
  unop : B


-- @@ L22-22 verbatim
namespace TwoSOp

-- @@ L23-25 verbatim
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]


-- @@ L27-37 verbatim
instance bicategoryStruct : BicategoryStruct (TwoSOp R B) where
  Hom a b := SOp R (a.unop ⟶ b.unop)
  id a := ⟨𝟙 a.unop⟩
  comp f g := ⟨(SOp.unop f) ≫ g.unop⟩
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := SOp.mk' ((SOp.unop f) ◁ SOp.unsop η)
  whiskerRight η h := SOp.mk' (SOp.unsop η ▷ h.unop)
  associator f g h := SOp.evenIso (associator (SOp.unop f) g.unop h.unop)
    (associator_hom_mem _ _ _)
  leftUnitor f := SOp.evenIso (leftUnitor (SOp.unop f)) (leftUnitor_hom_mem _)
  rightUnitor f := SOp.evenIso (rightUnitor (SOp.unop f)) (rightUnitor_hom_mem _)


-- @@ L39-39 verbatim
instance (a b : TwoSOp R B) : Preadditive (a ⟶ b) := SOp.preadditive

-- @@ L40-40 verbatim
instance (a b : TwoSOp R B) : Linear R (a ⟶ b) := SOp.linear

-- @@ L41-41 verbatim
instance (a b : TwoSOp R B) : Supercategory R (a ⟶ b) := SOp.supercategory


-- @@ L43-45 verbatim
@[simp] theorem unsop_comp₂ {a b : TwoSOp R B} {f g h : a ⟶ b}
    (η : f ⟶ g) (θ : g ⟶ h) :
    SOp.unsop (η ≫ θ) = SOp.compC (R := R) (SOp.unsop η) (SOp.unsop θ) := rfl


-- @@ L47-47 verbatim
@[simp] theorem id_unop (a : TwoSOp R B) : SOp.unop (𝟙 a : a ⟶ a) = 𝟙 a.unop := rfl

-- @@ L48-49 verbatim
@[simp] theorem comp_unop {a b c : TwoSOp R B} (f : a ⟶ b) (g : b ⟶ c) :
    SOp.unop (f ≫ g) = SOp.unop f ≫ SOp.unop g := rfl

-- @@ L50-51 verbatim
@[simp] theorem unsop_whiskerLeft {a b c : TwoSOp R B} (f : a ⟶ b)
    {g h : b ⟶ c} (η : g ⟶ h) : SOp.unsop (f ◁ η) = SOp.unop f ◁ SOp.unsop η := rfl

-- @@ L52-53 verbatim
@[simp] theorem unsop_whiskerRight {a b c : TwoSOp R B} {f g : a ⟶ b}
    (η : f ⟶ g) (h : b ⟶ c) : SOp.unsop (η ▷ h) = SOp.unsop η ▷ SOp.unop h := rfl

-- @@ L54-57 verbatim
@[simp] theorem unsop_associator_hom {a b c d : TwoSOp R B}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    SOp.unsop (associator f g h).hom =
      (associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).inv := rfl

-- @@ L58-61 verbatim
@[simp] theorem unsop_associator_inv {a b c d : TwoSOp R B}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    SOp.unsop (associator f g h).inv =
      (associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).hom := rfl

-- @@ L62-63 verbatim
@[simp] theorem unsop_leftUnitor_hom {a b : TwoSOp R B} (f : a ⟶ b) :
    SOp.unsop (leftUnitor f).hom = (leftUnitor (SOp.unop f)).inv := rfl

-- @@ L64-65 verbatim
@[simp] theorem unsop_leftUnitor_inv {a b : TwoSOp R B} (f : a ⟶ b) :
    SOp.unsop (leftUnitor f).inv = (leftUnitor (SOp.unop f)).hom := rfl

-- @@ L66-67 verbatim
@[simp] theorem unsop_rightUnitor_hom {a b : TwoSOp R B} (f : a ⟶ b) :
    SOp.unsop (rightUnitor f).hom = (rightUnitor (SOp.unop f)).inv := rfl

-- @@ L68-69 verbatim
@[simp] theorem unsop_rightUnitor_inv {a b : TwoSOp R B} (f : a ⟶ b) :
    SOp.unsop (rightUnitor f).inv = (rightUnitor (SOp.unop f)).hom := rfl

-- @@ L70-70 verbatim
end TwoSOp

-- @@ L71-71 verbatim
end StringDiagrams
