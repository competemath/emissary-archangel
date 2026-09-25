import Seymour.Matrix.Basic


-- @@ L3-7 verbatim
/-!
# Partial Unimodularity

This file is about matrices that are totally unimodular up to certain size of the square submatrix.
-/


-- @@ L9-9 verbatim
variable {X Y R : Type*} [CommRing R]


-- @@ L11-14 verbatim
/-- Matrix `A` satisfies TUness for submatrices up to `k`×`k` size, i.e.,
    the determinant of every `k`×`k` submatrix of `A` (not necessarily injective) is `1`, `0`, or `-1`. -/
def Matrix.IsPartiallyUnimodular (A : Matrix X Y R) (k : ℕ) : Prop :=
  ∀ f : Fin k → X, ∀ g : Fin k → Y, (A.submatrix f g).det ∈ SignType.cast.range


-- @@ L16-23 verbatim
/-- Matrix is totally unimodular iff it is partially unimodular for all sizes.
    One might argue that this should be the definition of total unimodularity, rather than a lemma.
    They would be wrong, however, because
    (1) total unimodularity is a part of the trusted code whereäs partial unimodularity is used only in auxiliary constructions
    (2) total unimodularity is defined in Mathlib whereäs partial unimodularity is defined in our project only. -/
lemma Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ∀ k : ℕ, A.IsPartiallyUnimodular k :=
  A.isTotallyUnimodular_iff
