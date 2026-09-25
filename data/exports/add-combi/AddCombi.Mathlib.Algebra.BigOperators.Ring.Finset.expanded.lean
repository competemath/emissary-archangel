module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.BigOperators.Ring.Finset


-- @@ L6-6 verbatim
open scoped Indicator


-- @@ L8-8 verbatim
public section


-- @@ L10-10 verbatim
namespace Finset

-- @@ L11-11 verbatim
variable {α R : Type*} [Fintype α] [Semiring R]


-- @@ L13-14 expanded
@[simp]
lemma sum_indicator_one (s : Finset α) : ∑ x, (Set.indicator (s : Set α) fun _ ↦ (1 : R)) x = #s :=
  by classical simp [Set.indicator_apply]


-- @@ L16-17 expanded
lemma card_eq_sum_indicator_one (s : Finset α) :
    #s = ∑ x, (Set.indicator (s : Set α) fun _ ↦ (1 : _)) x :=
  (sum_indicator_one _).symm


-- @@ L19-19 verbatim
end Finset
