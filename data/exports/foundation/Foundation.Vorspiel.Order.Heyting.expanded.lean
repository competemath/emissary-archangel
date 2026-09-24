module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteBooleanAlgebra


-- @@ L6-6 verbatim
public section


-- @@ L8-8 verbatim
section frame


-- @@ L10-10 verbatim
variable {α : Type*} [Order.Frame α]


-- @@ L12-13 verbatim
theorem compl_iSup' {a : ι → α} : (⨆ i, a i)ᶜ = ⨅ i, (a i)ᶜ := by
  simpa using iSup_himp_eq (f := a) (a := ⊥)


-- @@ L15-15 verbatim
end frame


-- @@ L17-17 verbatim
section HeytingAlgebra


-- @@ L19-19 verbatim
variable {α : Type*} [HeytingAlgebra α]


-- @@ L21-29 verbatim
@[simp, grind .]
lemma himp_himp_inf_himp_inf_le (a b c : α) : (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := calc
  (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a = (a ⇨ b ⇨ c) ⊓ b ⊓ a := by simp only [inf_assoc, himp_inf_self]
  _                         = (a ⇨ b ⇨ c) ⊓ a ⊓ b := by simp only [inf_assoc, inf_comm a b]
  _                         ≤ (b ⇨ c) ⊓ b         := by simp only [himp_inf_self a (b ⇨ c), le_inf_iff]
                                                        constructor
                                                        · simp only [inf_assoc, inf_le_left]
                                                        · exact inf_le_right
  _                         ≤ c                   := by simp


-- @@ L31-40 verbatim
@[simp, grind .]
lemma himp_inf_himp_inf_sup_le (a b c : α) : (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c := by
  have ha : a ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have hb : b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, inf_comm (a ⇨ c) (b ⇨ c), ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have : a ⊔ b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := sup_le_iff.mpr ⟨ha, hb⟩
  simpa only [GeneralizedHeytingAlgebra.le_himp_iff, inf_comm (a ⊔ b)] using this


-- @@ L42-42 verbatim
end HeytingAlgebra


-- @@ L44-44 verbatim
namespace CompleteBooleanAlgebra


-- @@ L46-46 verbatim
variable {α : Type*} [CompleteBooleanAlgebra α]




-- @@ L50-50 verbatim
end CompleteBooleanAlgebra
