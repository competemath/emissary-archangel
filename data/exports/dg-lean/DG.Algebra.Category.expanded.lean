import Mathlib.CategoryTheory.Category.Basic
import DG.Algebra.Hom


-- @@ L4-12 verbatim
/-!
# The category of dg algebras

`DG.DGAlgCat.{w, u} R` is the category of dg `R`-algebras with carriers in `Type u`, for a
commutative ring `R : Type w`: objects are bundled types with `Ring`, `Algebra R`,
`DGAddCommGroup`, `DGRing` and `DGAlgebra R` instances, and morphisms are morphisms of dg
`R`-algebras (`DG.DGAlgHom`, `A →ᵈᵍₐ[R] B`), wrapped in a one-field structure as in Mathlib's
`AlgebraCat`.
-/


-- @@ L14-14 verbatim
open CategoryTheory


-- @@ L16-16 verbatim
universe w u


-- @@ L18-18 verbatim
namespace DG


-- @@ L20-28 verbatim
/-- The category of dg `R`-algebras with carriers in `Type u`. -/
structure DGAlgCat (R : Type w) [CommRing R] where
  /-- The underlying type. -/
  carrier : Type u
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]
  [isDGAddCommGroup : DGAddCommGroup carrier]
  [isDGRing : DGRing carrier]
  [isDGAlgebra : DGAlgebra R carrier]


-- @@ L30-31 verbatim
attribute [instance] DGAlgCat.isRing DGAlgCat.isAlgebra DGAlgCat.isDGAddCommGroup
  DGAlgCat.isDGRing DGAlgCat.isDGAlgebra


-- @@ L33-33 verbatim
namespace DGAlgCat


-- @@ L35-35 verbatim
variable (R : Type w) [CommRing R]


-- @@ L37-38 verbatim
instance : CoeSort (DGAlgCat.{w, u} R) (Type u) :=
  ⟨DGAlgCat.carrier⟩


-- @@ L40-40 verbatim
attribute [coe] DGAlgCat.carrier


-- @@ L42-45 verbatim
/-- The object of `DGAlgCat R` associated to a dg `R`-algebra. -/
abbrev of (A : Type u) [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] :
    DGAlgCat.{w, u} R :=
  ⟨A⟩


-- @@ L47-52 expanded
variable {R} in
/-- The type of morphisms in `DGAlgCat R`: morphisms of dg `R`-algebras. -/
@[ext]
structure Hom (A B : DGAlgCat.{w, u} R) where
  /-- The underlying morphism of dg algebras. -/
  hom : DGAlgHom R A B


-- @@ L54-58 verbatim
/-- The category of dg `R`-algebras. -/
instance category : Category.{u} (DGAlgCat.{w, u} R) where
  Hom A B := Hom A B
  id _ := ⟨DGAlgHom.id⟩
  comp f g := ⟨g.hom.comp f.hom⟩


-- @@ L60-60 verbatim
variable {R}


-- @@ L62-66 expanded
/-- A morphism of dg algebras as a morphism in `DGAlgCat R`. -/
abbrev ofHom {A B : Type u} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
    [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B] (f : DGAlgHom R A B) :
    of R A ⟶ of R B :=
  ⟨f⟩


-- @@ L68-69 verbatim
@[simp]
theorem hom_id (A : DGAlgCat.{w, u} R) : Hom.hom (𝟙 A) = DGAlgHom.id := rfl


-- @@ L71-73 verbatim
@[simp]
theorem hom_comp {A B C : DGAlgCat.{w, u} R} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl


-- @@ L75-77 verbatim
@[ext]
theorem hom_ext {A B : DGAlgCat.{w, u} R} {f g : A ⟶ B} (h : ∀ a, f.hom a = g.hom a) : f = g :=
  Hom.ext (DGAlgHom.ext h)


-- @@ L79-79 verbatim
end DGAlgCat


-- @@ L81-81 verbatim
end DG
