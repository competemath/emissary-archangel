import Mathlib.Data.Fintype.BigOperators


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Exact finite counting when a specified set of coordinates is fixed. -/


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical


-- @@ L10-10 verbatim
namespace Paper320


-- @@ L12-12 verbatim
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]


-- @@ L14-29 verbatim
def fixedCoordinatesEquiv (s : Finset α) (v : α → β) :
    {f : α → β // ∀ i ∈ s, f i = v i} ≃ ({i : α // i ∉ s} → β) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : i ∈ s then v i else f ⟨i,h⟩, by
    intro i hi
    simp only [dite_eq_left hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp only [dite_eq_left hi]
      exact (f.property i hi).symm
    · simp only [dite_eq_right hi]
  right_inv f := by
    funext i
    simp only [dite_eq_right i.property]


-- @@ L31-37 verbatim
theorem card_fixedCoordinates (s : Finset α) (v : α → β)
    [DecidablePred (fun f : α → β => ∀ i ∈ s, f i = v i)] :
    (Finset.univ.filter fun f : α → β => ∀ i ∈ s, f i = v i).card =
      Fintype.card β ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fixedCoordinatesEquiv s v), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe]


-- @@ L39-39 verbatim
end Paper320


-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
