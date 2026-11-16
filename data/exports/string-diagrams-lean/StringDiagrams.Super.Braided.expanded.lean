import StringDiagrams.Super.Monoidal


-- @@ L3-15 verbatim
/-!
# Braided monoidal supercategories

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, remark after
Definition 2.3, state that the Drinfeld center of a 2-supercategory is a braided monoidal
supercategory, but omit the definition of such a structure. This module supplies the standard
definition, as an extension beyond the text of the paper: a *braided monoidal supercategory* is
a monoidal supercategory with even isomorphisms `c_{X,Y} : X ⊗ Y ≅ Y ⊗ X`, natural in each
variable separately, satisfying the two hexagon axioms (the axioms of Mathlib's
`BraidedCategory`, plus evenness). Naturality in each variable is sign-free; for the paper's
tensor product `f ⊗ g = (1 ⊗ g)(f ⊗ 1)` of homogeneous morphisms it becomes the sign rule
`c ∘ (f ⊗ g) = (-1)^{|f||g|} (g ⊗ f) ∘ c` (`BraidedMonoidalSupercategory.braiding_naturality`).
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace StringDiagrams


-- @@ L21-21 verbatim
open CategoryTheory MonoidalCategory Supercategory


-- @@ L23-23 verbatim
universe w w₁ w₂


-- @@ L25-26 verbatim
variable (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]


-- @@ L28-46 verbatim
/-- A braided monoidal supercategory: a monoidal supercategory with even braiding isomorphisms
`c_{X,Y} : X ⊗ Y ≅ Y ⊗ X`, natural in each variable, satisfying the hexagon axioms. This
notion is not defined in Brundan–Ellis (see the module documentation). -/
class BraidedMonoidalSupercategory where
  /-- The braiding `c_{X,Y} : X ⊗ Y ≅ Y ⊗ X`. -/
  braiding (X Y : C) : X ⊗ Y ≅ Y ⊗ X
  braiding_hom_mem (X Y : C) : (braiding X Y).hom ∈ parity (R := R) (X ⊗ Y) (Y ⊗ X) 0
  braiding_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X
  braiding_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f
  /-- The first hexagon axiom. -/
  hexagon_forward (X Y Z : C) :
    (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding X Z).hom
  /-- The second hexagon axiom. -/
  hexagon_reverse (X Y Z : C) :
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (braiding Y Z).hom ≫ (α_ X Z Y).inv ≫ (braiding X Z).hom ▷ Y


-- @@ L48-48 verbatim
namespace BraidedMonoidalSupercategory


-- @@ L50-50 verbatim
variable {R C} [BraidedMonoidalSupercategory R C]


-- @@ L52-52 verbatim
attribute [reassoc] braiding_naturality_right braiding_naturality_left


-- @@ L54-62 verbatim
/-- Naturality of the braiding for the paper's tensor product `f ⊗ g = (1 ⊗ g)(f ⊗ 1)` of
homogeneous morphisms: `c ∘ (f ⊗ g) = (-1)^{|f||g|} (g ⊗ f) ∘ c`. -/
theorem braiding_naturality {X X' Y Y' : C} {p q : ZMod 2} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : f ∈ parity (R := R) X X' p) (hg : g ∈ parity (R := R) Y Y' q) :
    MonoidalSupercategory.superTensorHom f g ≫ (braiding (R := R) X' Y').hom =
      koszulSign p q • ((braiding (R := R) X Y).hom ≫ MonoidalSupercategory.superTensorHom g f) := by
  simp only [MonoidalSupercategory.superTensorHom, Category.assoc]
  rw [braiding_naturality_left, braiding_naturality_right_assoc,
    MonoidalSupercategory.super_interchange hg hf, koszulSign_comm, Linear.comp_smul]


-- @@ L64-64 verbatim
end BraidedMonoidalSupercategory


-- @@ L66-66 verbatim
end StringDiagrams


-- @@ L68-68 verbatim
end
