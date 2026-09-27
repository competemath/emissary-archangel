/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Formula


-- @@ L10-10 verbatim
/-! # Subformulas -/


-- @@ L12-12 verbatim
@[expose] public section




-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal


-- @@ L19-24 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.subformulas [DecidableEq α] : Formula α → FormulaFinset α
  | .atom a => {(.atom a)}
  | ⊥ => {⊥}
  | Arrow.arrow φ ψ => insert (Arrow.arrow φ ψ) (φ.subformulas ∪ ψ.subformulas)
  | Box.box φ => insert (Box.box φ) φ.subformulas


-- @@ L26-26 verbatim
namespace Formula

-- @@ L27-27 verbatim
namespace subformulas


-- @@ L29-29 verbatim
variable [DecidableEq α]


-- @@ L31-32 verbatim
@[simp] lemma mem_self {φ : Formula α} :
    φ ∈ φ.subformulas := by induction φ <;> { simp [subformulas]; try tauto; }


-- @@ L34-34 verbatim
variable {φ ψ χ : Formula α}


-- @@ L36-52 expanded
lemma mem_imp (h : (Arrow.arrow ψ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | hfalsum =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | hatom _ =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | himp φ₁ φ₂ ihp₁
    ihp₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h ⊢
    rcases h with h_eq | h₁ | h₂
    · simp_all
    · simp_all
    · simp_all
  | hbox _ ihp =>
    simp only [subformulas, Finset.mem_insert] at h ⊢
    simp_all


-- @@ L54-54 expanded
lemma mem_imp₁ (h : (Arrow.arrow ψ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas :=
  mem_imp h |>.1


-- @@ L56-56 expanded
lemma mem_imp₂ (h : (Arrow.arrow ψ χ) ∈ φ.subformulas) : χ ∈ φ.subformulas :=
  mem_imp h |>.2


-- @@ L58-78 expanded
lemma mem_box (h : Box.box ψ ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | hfalsum =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | hatom _ =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | himp _ _ ihp₁
    ihp₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h ⊢
    rcases h with h_eq | h₁ | h₂
    · cases h_eq
    · exact Or.inr (Or.inl (ihp₁ h₁))
    · exact Or.inr (Or.inr (ihp₂ h₂))
  | hbox _ ihp =>
    simp only [subformulas, Finset.mem_insert] at h ⊢
    rcases h with h_eq | h_sub
    · simp_all
    ·
      exact
        Or.inr
          (ihp h_sub)
            -- TODO: add tactic like `subformulas`.


-- @@ L79-82 verbatim
attribute [aesop safe 5 forward]
  mem_imp₁
  mem_imp₂
  mem_box


-- @@ L84-130 verbatim
@[simp]
lemma complexity_lower (h : ψ ∈ φ.subformulas) : ψ.complexity ≤ φ.complexity  := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h
    rcases h with h_eq | h₁ | h₂
    · simp_all
    · have h_le := ihp₁ h₁
      change ψ.complexity ≤ max φ₁.complexity φ₂.complexity + 1
      exact le_trans h_le (le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
    · have h_le := ihp₂ h₂
      change ψ.complexity ≤ max φ₁.complexity φ₂.complexity + 1
      exact le_trans h_le (le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
  | hbox φ ihp =>
    simp only [subformulas, Finset.mem_insert] at h
    rcases h with h_eq | h₁
    · simp_all
    · have h_le := ihp h₁
      change ψ.complexity ≤ φ.complexity + 1
      exact le_trans h_le (Nat.le_succ _)
  | hatom =>
    simp only [subformulas, Finset.mem_singleton] at h
    simp_all
  | hfalsum =>
    simp only [subformulas, Finset.mem_singleton] at h
    simp_all

/-
@[simp]
lemma degree_lower (h : ψ ∈ φ.subformulas) : ψ.degree ≤ φ.degree := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp_all [subformulas];
    rcases h with rfl | h₁ | h₂;
    · simp_all [Formula.degree];
    · have := ihp₁ h₁; simp [Formula.degree]; omega;
    · have := ihp₂ h₂; simp [Formula.degree]; omega;
  | hbox φ ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    · subst_vars; simp [Formula.degree];
    · have := ihp h₁; simp [Formula.degree]; omega;
  | hatom =>
    simp_all [subformulae];
    rcases h with rfl | rfl <;> simp [Formula.degree];
  | hfalsum => simp_all [subformulae, Formula.degree];
-/


-- @@ L132-132 verbatim
end subformulas

-- @@ L133-133 verbatim
end Formula



-- @@ L136-139 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Modal.FormulaSet.SubformulaClosed (P : FormulaSet α) where
  imp_closed : ∀ {φ ψ}, Arrow.arrow φ ψ ∈ P → φ ∈ P ∧ ψ ∈ P
  box_closed : ∀ {φ}, Box.box φ ∈ P → φ ∈ P


-- @@ L141-141 verbatim
namespace FormulaSet

-- @@ L142-142 verbatim
namespace SubformulaClosed


-- @@ L144-144 verbatim
variable {φ : Formula α} {P : FormulaSet α} [hP : P.SubformulaClosed]


-- @@ L146-146 expanded
lemma mem_imp₁ (h : Arrow.arrow φ ψ ∈ P) : φ ∈ P :=
  hP.imp_closed h |>.1


-- @@ L147-147 expanded
lemma mem_imp₂ (h : Arrow.arrow φ ψ ∈ P) : ψ ∈ P :=
  hP.imp_closed h |>.2


-- @@ L148-148 expanded
lemma mem_box (h : Box.box φ ∈ P) : φ ∈ P :=
  hP.box_closed h


-- @@ L150-157 verbatim
instance {φ : Formula α} [DecidableEq α] :
    FormulaSet.SubformulaClosed (SetLike.coe (φ.subformulas)) where
  box_closed := by
    intro φ hφ;
    exact Formula.subformulas.mem_box hφ;
  imp_closed := by
    intro φ ψ hφ;
    exact Formula.subformulas.mem_imp hφ;


-- @@ L159-159 verbatim
end SubformulaClosed

-- @@ L160-160 verbatim
end FormulaSet


-- @@ L162-162 verbatim
end Modal

-- @@ L163-163 verbatim
end LO
