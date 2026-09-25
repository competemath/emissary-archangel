import Seymour.Basic.Basic


-- @@ L3-7 verbatim
/-!
# Matrix is a signing of another matrix

This file describes when a matrix is a signing of another matrix.
-/


-- @@ L9-9 verbatim
variable {X Y R : Type*} [LinearOrderedRing R] {n : ℕ}


-- @@ L11-14 verbatim
/-- `LinearOrderedRing`-valued matrix `A` is a signing of `U` (matrix of the same size but different type) iff `A` has
    the same entries as `U` on respective positions up to signs. -/
def Matrix.IsSigningOf (A : Matrix X Y R) (U : Matrix X Y (ZMod n)) : Prop :=
  ∀ i : X, ∀ j : Y, |A i j| = (U i j).val


-- @@ L16-19 verbatim
lemma Matrix.IsSigningOf.submatrix {X' Y' : Type*} {A : Matrix X Y R} {U : Matrix X Y (ZMod n)}
    (hAU : A.IsSigningOf U) (f : X' → X) (g : Y' → Y) :
    (A.submatrix f g).IsSigningOf (U.submatrix f g) :=
  fun i : X' => fun j : Y' => hAU (f i) (g j)


-- @@ L21-24 verbatim
lemma Matrix.IsSigningOf.reindex {X' Y' : Type*} {A : Matrix X Y R} {U : Matrix X Y (ZMod n)}
    (hAU : A.IsSigningOf U) (f : X ≃ X') (g : Y ≃ Y') :
    (A.reindex f g).IsSigningOf (U.reindex f g) :=
  hAU.submatrix f.symm g.symm
