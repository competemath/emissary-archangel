module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Star.Pi


-- @@ L6-6 verbatim
open scoped ComplexConjugate Indicator


-- @@ L8-8 verbatim
public section


-- @@ L10-10 verbatim
namespace Set

-- @@ L11-11 verbatim
variable {α R : Type*} [CommSemiring R] [StarRing R]


-- @@ L13-14 expanded
@[simp]
lemma conj_indicator_one_apply (s : Set α) (a : α) :
    conj ((Set.indicator s fun _ ↦ (1 : R)) a) = (Set.indicator s fun _ ↦ (1 : _)) a := by
  classical simp [indicator_apply]


-- @@ L16-16 expanded
@[simp]
lemma conj_indicator_one (s : Set α) :
    conj (Set.indicator s fun _ ↦ (1 : R)) = Set.indicator s fun _ ↦ (1 : _) := by ext; simp


-- @@ L18-18 verbatim
end Set
