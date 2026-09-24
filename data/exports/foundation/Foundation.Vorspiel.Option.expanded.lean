module

public import Mathlib.Data.Option.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace Option


-- @@ L9-9 verbatim
variable {α : Type u}


-- @@ L11-13 verbatim
inductive IsSubsetOf : Option α → Option α → Prop
| none : IsSubsetOf none o
| some (a : α) : IsSubsetOf (some a) (some a)


-- @@ L15-15 verbatim
instance : HasSubset (Option α) := ⟨IsSubsetOf⟩


-- @@ L17-17 verbatim
@[simp] lemma none_subset (o : Option α) : none ⊆ o := IsSubsetOf.none


-- @@ L19-19 verbatim
@[simp] lemma some_subset_some_self (a : α) : some a ⊆ some a := IsSubsetOf.some a


-- @@ L21-24 verbatim
@[simp] lemma subset_none_iff (o : Option α) : o ⊆ none ↔ o = none := by
  cases o
  · simp
  · simp only [reduceCtorEq, iff_false]; rintro ⟨⟩


-- @@ L26-30 verbatim
@[simp] lemma some_subset_some {a b : α} :
    some a ⊆ some b ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact IsSubsetOf.some a


-- @@ L32-37 verbatim
lemma subset_iff (o₁ o₂ : Option α) : o₁ ⊆ o₂ ↔ ∀ a, a ∈ o₁ → a ∈ o₂ := by
  cases o₁
  · simp
  · cases o₂
    · simp
    · simp; grind


-- @@ L39-39 verbatim
end Option
