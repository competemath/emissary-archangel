/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Substitution
public import LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental


-- @@ L12-12 verbatim
/-! # Basic -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Modal


-- @@ L20-20 verbatim
open Entailment


-- @@ L22-22 verbatim
variable {α : Type*}


-- @@ L24-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Hilbert (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  axioms : Set (Formula α)


-- @@ L29-29 verbatim
namespace Hilbert


-- @@ L31-31 verbatim
variable {H H₁ H₂ : Hilbert α}


-- @@ L33-35 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev axiomInstances (H : Hilbert α) : Set (Formula α) :=
  {Formula.subst s φ | (φ ∈ H.axioms) (s : Substitution α)}


-- @@ L37-42 verbatim
lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  · assumption;
  · use Substitution.id;
    simp;


-- @@ L44-46 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms := by aesop



-- @@ L49-56 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive Deduction (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ} : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ} : Deduction H (Arrow.arrow φ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ} : Deduction H φ → Deduction H (Box.box φ)
  | imply₁ φ ψ : Deduction H <| Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ : Deduction H <| Axioms.Imply₂ φ ψ χ
  | ec φ ψ : Deduction H <| Axioms.ElimContra φ ψ


-- @@ L58-58 verbatim
namespace Deduction


-- @@ L60-60 verbatim
instance : Entailment (Formula α) (Hilbert α) := ⟨Deduction⟩


-- @@ L62-66 verbatim
instance : Entailment.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elimContra := ec


-- @@ L68-68 verbatim
instance : Entailment.Classical H where


-- @@ L70-70 verbatim
instance : Entailment.HasDiaDuality H := inferInstance


-- @@ L72-72 verbatim
instance : Entailment.Necessitation H := ⟨nec⟩


-- @@ L74-74 expanded
lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : Provable H φ :=
  ⟨maxm h⟩


-- @@ L76-76 verbatim
end Deduction



-- @@ L79-79 verbatim
open Deduction


-- @@ L81-81 verbatim
namespace Deduction


-- @@ L83-99 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def rec! {motive : (φ : Formula α) → Provable H φ → Sort*}
    (maxm : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
    (mdp :
      ∀ {φ ψ},
        {hpq : Provable H (Arrow.arrow φ ψ)} →
          {hp : Provable H φ} → motive (Arrow.arrow φ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
    (nec : ∀ {φ}, {hp : Provable H φ} → (ihp : motive φ hp) → motive (Box.box φ) (nec! hp))
    (imply₁ : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) <| ⟨imply₁ φ ψ⟩)
    (imply₂ : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) <| ⟨imply₂ φ ψ χ⟩)
    (ec : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) <| ⟨ec φ ψ⟩) :
    ∀ {φ}, (d : Provable H φ) → motive φ d := by intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact nec (ih ⟨hp⟩)
  | _ => aesop;


-- @@ L101-116 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma subst! {φ} (s) (h : Provable H φ) : Provable H (Formula.subst s φ) := by
  induction h using Deduction.rec! with
  | imply₁ => simp;
  | imply₂ => simp;
  | ec => simp;
  | mdp ihφψ ihφ => exact mdp ihφψ ihφ;
  | nec ihφ => exact nec! ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h; apply maxm!; use ψ; constructor; · assumption;
    · use s' ∘ s; exact subst_comp;


-- @@ L118-118 verbatim
end Deduction



-- @@ L121-122 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev theorems (H : Hilbert α) := Entailment.theory H


-- @@ L124-136 expanded
lemma of_subset (hs : H₁.axioms ⊆ H₂.axioms) : Provable H₁ φ → Provable H₂ φ := by intro h;
  induction h using Deduction.rec! with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h; apply maxm!; use ψ; constructor; · exact hs h;
    · use s;
  | mdp ih₁ ih₂ => exact mdp! ih₁ ih₂;
  | nec ih => exact nec! ih;
  | _ => simp;


-- @@ L138-147 expanded
lemma weakerThan_of_dominate_axiomInstances
    (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axiomInstances → Provable H₂ φ) : WeakerThan H₁ H₂ := by
  apply Entailment.weakerThan_iff.mpr; intro φ h;
  induction h using Deduction.rec! with
  | maxm h => apply hMaxm h;
  | mdp ih₁ ih₂ => exact mdp! ih₁ ih₂;
  | nec ih => exact nec! ih;
  | _ => simp;


-- @@ L149-154 expanded
lemma weakerThan_of_dominate_axioms (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → Provable H₂ φ) :
    WeakerThan H₁ H₂ := by apply weakerThan_of_dominate_axiomInstances; rintro φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
  apply subst!; apply hMaxm hψ;


-- @@ L156-156 verbatim
end Hilbert


-- @@ L158-158 verbatim
end Modal

-- @@ L159-159 verbatim
end LO
