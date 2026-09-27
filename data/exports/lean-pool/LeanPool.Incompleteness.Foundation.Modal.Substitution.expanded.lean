/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Formula


-- @@ L10-10 verbatim
/-! # Substitution -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal


-- @@ L18-19 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Substitution (α) := α → (Formula α)


-- @@ L21-22 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Substitution.id {α} : Substitution α := fun a => .atom a


-- @@ L24-24 verbatim
namespace Formula


-- @@ L26-26 verbatim
variable {φ ψ : Formula α} {s : Substitution α}


-- @@ L28-33 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def subst (s : Substitution α) : Formula α → Formula α
  | atom a => (s a)
  | ⊥ => ⊥
  | Box.box φ => Box.box (φ.subst s)
  | Arrow.arrow φ ψ => Arrow.arrow (φ.subst s) (ψ.subst s)


-- @@ L35-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 φ "⟦" s "⟧" => Formula.subst s φ


-- @@ L38-38 expanded
@[simp]
lemma subst_atom {a} : Formula.subst s (.atom a) = s a :=
  rfl


-- @@ L40-40 expanded
@[simp]
lemma subst_bot : Formula.subst s ⊥ = ⊥ :=
  rfl


-- @@ L42-42 expanded
@[simp]
lemma subst_imp :
    Formula.subst s (Arrow.arrow φ ψ) = Arrow.arrow (Formula.subst s φ) (Formula.subst s ψ) :=
  rfl


-- @@ L44-44 expanded
@[simp]
lemma subst_neg : Formula.subst s (Tilde.tilde φ) = Tilde.tilde (Formula.subst s φ) :=
  rfl


-- @@ L46-46 expanded
@[simp]
lemma subst_and :
    Formula.subst s (Wedge.wedge φ ψ) = Wedge.wedge (Formula.subst s φ) (Formula.subst s ψ) :=
  rfl


-- @@ L48-48 expanded
@[simp]
lemma subst_or : Formula.subst s (Vee.vee φ ψ) = Vee.vee (Formula.subst s φ) (Formula.subst s ψ) :=
  rfl


-- @@ L50-50 expanded
@[simp]
lemma subst_iff :
    Formula.subst s (LogicalConnective.iff φ ψ) =
      (LogicalConnective.iff (Formula.subst s φ) (Formula.subst s ψ)) :=
  rfl


-- @@ L52-52 expanded
@[simp]
lemma subst_box : Formula.subst s (Box.box φ) = Box.box (Formula.subst s φ) :=
  rfl


-- @@ L54-57 expanded
@[simp]
lemma subst_multibox : Formula.subst s (multibox n φ) = multibox n (Formula.subst s φ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]


-- @@ L59-59 expanded
@[simp]
lemma subst_dia : Formula.subst s (Dia.dia φ) = Dia.dia (Formula.subst s φ) :=
  rfl


-- @@ L61-64 expanded
@[simp]
lemma subst_multidia : Formula.subst s (multidia n φ) = multidia n (Formula.subst s φ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]


-- @@ L66-66 verbatim
end Formula



-- @@ L69-70 expanded
@[simp]
lemma subst_id {φ : Formula α} : Formula.subst .id φ = φ := by
  induction φ using Formula.rec' <;> simp_all;


-- @@ L72-74 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := fun a =>
  Formula.subst s₂ (s₁ a)


-- @@ L75-76 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:80 " ∘ " => Substitution.comp


-- @@ L78-80 expanded
@[simp]
lemma subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} :
    Formula.subst (s₁ ∘ s₂) φ = Formula.subst s₂ (Formula.subst s₁ φ) := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];


-- @@ L82-84 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, Formula.subst s φ ∈ S)


-- @@ L87-87 verbatim
end Modal

-- @@ L88-88 verbatim
end LO
