/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Formula
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # Substitution -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace IntProp


-- @@ L19-20 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Substitution (α) := α → (Formula α)


-- @@ L22-23 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Substitution.id {α} : Substitution α := fun a => .atom a


-- @@ L25-25 verbatim
namespace Formula


-- @@ L27-27 verbatim
variable {φ ψ : Formula α} {s : Substitution α}


-- @@ L29-35 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def subst (s : Substitution α) : Formula α → Formula α
  | atom a => (s a)
  | ⊥ => ⊥
  | Wedge.wedge φ ψ => Wedge.wedge (φ.subst s) (ψ.subst s)
  | Vee.vee φ ψ => Vee.vee (φ.subst s) (ψ.subst s)
  | Arrow.arrow φ ψ => Arrow.arrow (φ.subst s) (ψ.subst s)


-- @@ L37-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 φ "⟦" s "⟧" => Formula.subst s φ


-- @@ L40-40 expanded
@[simp]
lemma subst_atom {a} : Formula.subst s (.atom a) = s a :=
  rfl


-- @@ L42-42 expanded
@[simp]
lemma subst_bot : Formula.subst s ⊥ = ⊥ :=
  rfl


-- @@ L44-44 expanded
@[simp]
lemma subst_top : Formula.subst s ⊤ = ⊤ :=
  rfl


-- @@ L46-46 expanded
@[simp]
lemma subst_imp :
    Formula.subst s (Arrow.arrow φ ψ) = Arrow.arrow (Formula.subst s φ) (Formula.subst s ψ) :=
  rfl


-- @@ L48-48 expanded
@[simp]
lemma subst_neg : Formula.subst s (Tilde.tilde φ) = Tilde.tilde (Formula.subst s φ) :=
  rfl


-- @@ L50-50 expanded
@[simp]
lemma subst_and :
    Formula.subst s (Wedge.wedge φ ψ) = Wedge.wedge (Formula.subst s φ) (Formula.subst s ψ) :=
  rfl


-- @@ L52-52 expanded
@[simp]
lemma subst_or : Formula.subst s (Vee.vee φ ψ) = Vee.vee (Formula.subst s φ) (Formula.subst s ψ) :=
  rfl


-- @@ L54-54 expanded
@[simp]
lemma subst_iff :
    Formula.subst s (LogicalConnective.iff φ ψ) =
      (LogicalConnective.iff (Formula.subst s φ) (Formula.subst s ψ)) :=
  rfl


-- @@ L56-56 verbatim
end Formula



-- @@ L59-60 expanded
@[simp]
lemma subst_id {φ : Formula α} : Formula.subst .id φ = φ := by
  induction φ using Formula.rec' <;> simp_all;


-- @@ L62-64 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.IntProp.Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := fun a =>
  Formula.subst s₂ (s₁ a)


-- @@ L65-66 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:80 " ∘ " => Substitution.comp


-- @@ L68-70 expanded
@[simp]
lemma subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} :
    Formula.subst (s₁ ∘ s₂) φ = Formula.subst s₂ (Formula.subst s₁ φ) := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];


-- @@ L72-74 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, Formula.subst s φ ∈ S)


-- @@ L77-77 verbatim
end IntProp

-- @@ L78-78 verbatim
end LO
