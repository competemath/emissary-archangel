/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.MaximalConsistentSet
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic
import LeanPool.Incompleteness.Foundation.Modal.Entailment.K
import Mathlib.Tactic.TautoSet


-- @@ L13-13 verbatim
/-! # Completeness -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Modal


-- @@ L21-21 verbatim
open Entailment

-- @@ L22-22 verbatim
open Formula

-- @@ L23-23 verbatim
open Kripke

-- @@ L24-24 verbatim
open MaximalConsistentSet


-- @@ L26-26 verbatim
variable {S} [Entailment (Formula ℕ) S]

-- @@ L27-27 verbatim
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]


-- @@ L29-29 verbatim
namespace Kripke


-- @@ L31-34 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Kripke.Frame
    where
  World := MaximalConsistentSet 𝓢
  Rel X Y := Set.prebox X.1 ⊆ Y.1


-- @@ L36-36 verbatim
namespace canonicalFrame


-- @@ L38-38 verbatim
variable {Ω₁ Ω₂ : (canonicalFrame 𝓢).World}


-- @@ L40-40 expanded
@[simp]
lemma rel_def_box : Frame.Rel' Ω₁ Ω₂ ↔ ∀ {φ}, Box.box φ ∈ Ω₁ → φ ∈ Ω₂ := by simp [Frame.Rel'];
  aesop;


-- @@ L42-92 expanded
lemma multirel_def_multibox : Frame.RelItr' n Ω₁ Ω₂ ↔ ∀ {φ}, multibox n φ ∈ Ω₁.1 → φ ∈ Ω₂.1 := by
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    simp_all only [Rel.iterate.iff_zero, Function.iterate_zero, id_eq]; constructor;
    · intro h; tauto_set;
    · intro h; apply intro_equality; tauto_set;
  | succ n ih =>
    constructor;
    · intro h φ hp; obtain ⟨⟨Ω₃, _⟩, R₁₃, R₃₂⟩ := h;
      apply
        ih.mp R₃₂ <|
          rel_def_box.mp R₁₃ (by simp only [Function.iterate_succ_apply'] at hp; exact hp);
    · intro h;
      obtain ⟨Ω, hΩ⟩ :=
        lindenbaum (𝓢 := 𝓢) (T := (Set.prebox Ω₁.1 ∪ Set.multidia n Ω₂.1)) <|
          by
          apply FormulaSet.intro_union_consistent; rintro Γ Δ ⟨hΓ, hΔ⟩ hC;
          replace hΓ : ∀ φ ∈ Γ, Box.box φ ∈ Ω₁ := fun φ hpp => hΓ φ hpp;
          have dΓconj : Provable 𝓢 Ω₁.1 (Box.box (List.conj₂ Γ)) :=
            membership_iff.mp <| iff_mem_box_conj.mpr hΓ;
          have hΔ₂ : ∀ φ ∈ List.premultidia n Δ, φ ∈ Ω₂ := by intro φ hp;
            exact Set.iff_mem_multidia.mp <| hΔ (multidia n φ) (by simpa using hp);
          have hΔconj : List.conj₂ (List.premultidia n Δ) ∈ Ω₂ := iff_mem_conj.mpr hΔ₂;
          have : List.conj₂ (List.premultidia n Δ) ∉ Ω₂ := by
            {
            have d₁ : Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) (Arrow.arrow (List.conj₂ Δ) ⊥)) :=
              and_imply_iff_imply_imply'!.mp hC;
            have :
              Provable 𝓢
                (Arrow.arrow (List.conj₂ (List.multidia n (List.premultidia n Δ)))
                  (List.conj₂ Δ)) :=
              by apply conjconj_subset!; intro ψ hq; obtain ⟨χ, _, _⟩ := hΔ ψ hq; subst_vars; simpa;
            have :
              Provable 𝓢
                (Arrow.arrow (multidia n (List.conj₂ (List.premultidia n Δ))) (List.conj₂ Δ)) :=
              imp_trans''! iff_conjmultidia_multidiaconj! <| this;
            have :
              Provable 𝓢
                (Arrow.arrow
                  (Tilde.tilde (multibox n (Tilde.tilde (List.conj₂ (List.premultidia n Δ)))))
                  (List.conj₂ Δ)) :=
              imp_trans''! (and₂'! multidia_duality!) this;
            have :
              Provable 𝓢
                (Arrow.arrow (Tilde.tilde (List.conj₂ Δ))
                  (multibox n (Tilde.tilde (List.conj₂ (List.premultidia n Δ))))) :=
              contra₂'! this;
            have :
              Provable 𝓢
                (Arrow.arrow (Arrow.arrow (List.conj₂ Δ) ⊥)
                  (multibox n (Tilde.tilde (List.conj₂ (List.premultidia n Δ))))) :=
              imp_trans''! (and₂'! negEquiv!) this;
            have :
              Provable 𝓢
                (Arrow.arrow (List.conj₂ Γ)
                  (multibox n (Tilde.tilde (List.conj₂ (List.premultidia n Δ))))) :=
              imp_trans''! d₁ this;
            have :
              Provable 𝓢
                (Arrow.arrow (Box.box (List.conj₂ Γ))
                  (multibox (n + 1) (Tilde.tilde (List.conj₂ (List.premultidia n Δ))))) :=
              by simpa using imply_box_distribute'! this;
            exact iff_mem_neg.mp <| h <| membership_iff.mpr <| mdp (Context.of! this) dΓconj;
          }
          contradiction;
      use Ω; constructor; · simp_all
      · apply ih.mpr; apply multibox_multidia.mpr; intro φ hp; apply hΩ; simp_all;


-- @@ L94-97 expanded
lemma multirel_def_multibox' :
    Frame.RelItr' n Ω₁ Ω₂ ↔ ∀ {φ}, φ ∈ (Set.premultibox n Ω₁.1) → φ ∈ Ω₂.1 :=
  by
  constructor; · intro h φ hp; exact multirel_def_multibox.mp h hp;
  · intro h; apply multirel_def_multibox.mpr; assumption;


-- @@ L99-100 expanded
lemma multirel_def_multidia : Frame.RelItr' n Ω₁ Ω₂ ↔ ∀ {φ}, (φ ∈ Ω₂.1 → multidia n φ ∈ Ω₁.1) :=
  Iff.trans multirel_def_multibox multibox_multidia


-- @@ L102-106 expanded
lemma rel_def_dia : Frame.Rel' Ω₁ Ω₂ ↔ ∀ {φ}, φ ∈ Ω₂.1 → Dia.dia φ ∈ Ω₁.1 :=
  by
  rw [rel_def_box]
  have h := multibox_multidia (n := 1) (Ω₁ := Ω₁) (Ω₂ := Ω₂)
  simp only [Function.iterate_one] at h
  exact h


-- @@ L108-108 verbatim
end canonicalFrame



-- @@ L111-114 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Model where
  toFrame := canonicalFrame 𝓢
  Val Ω a := (atom a) ∈ Ω.1


-- @@ L116-118 verbatim
@[reducible]
instance : Semantics (Formula ℕ) (canonicalModel 𝓢).World :=
  Formula.Kripke.Satisfies.semantics (M := canonicalModel 𝓢)



-- @@ L121-121 verbatim
section «lp_section_1»


-- @@ L123-123 verbatim
variable {φ ψ : Formula ℕ}


-- @@ L125-152 expanded
lemma truthlemma : ∀ {Ω : (canonicalModel 𝓢).World}, Realize Ω φ ↔ (φ ∈ Ω.1) := by
  induction φ using Formula.rec' with
  | hatom => simp_all [Semantics.Realize, Kripke.Satisfies];
  | hfalsum => simp only [Semantics.Realize, Satisfies, false_iff]; exact not_mem_falsum;
  | hbox φ ih =>
    intro Ω; constructor;
    · intro h; apply iff_mem_box.mpr; intro Ω' hΩ'; apply ih.mp; exact h Ω' hΩ';
    · intro h Ω' hΩ'; apply ih.mpr; exact canonicalFrame.rel_def_box.mp hΩ' h;
  | himp φ ψ ihp ihq =>
    intro Ω; constructor;
    · intro h; apply iff_mem_imp.mpr; intro hp; replace hp := ihp.mpr hp; exact ihq.mp <| h hp;
    · intro h; have := iff_mem_imp.mp h; intro hp; replace hp := ihp.mp hp; exact ihq.mpr <| this hp


-- @@ L155-175 expanded
lemma iff_valid_on_canonicalModel_deducible : Realize (canonicalModel 𝓢) φ ↔ Provable 𝓢 φ :=
  by
  constructor;
  · contrapose; intro h;
    have : FormulaSet.Consistent 𝓢 ({Tilde.tilde φ}) := by apply FormulaSet.def_consistent.mpr;
      intro Γ hΓ; by_contra hC;
      have : Provable 𝓢 φ := dne'! <| negEquiv'!.mpr <| replace_imply_left_conj! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this; apply ValidOnModel.not_of_exists_world; use Ω;
    exact truthlemma.not.mpr <| iff_mem_neg.mp (by tauto_set);
  · intro h Ω; suffices φ ∈ Ω.1 by exact truthlemma.mpr this;
    by_contra hC; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := FormulaSet.iff_insert_inconsistent.mp <| (Ω.maximal' hC);
    have : Provable 𝓢 Γ ⊥ :=
      FiniteContext.provable_iff.mpr <| mdp (and_imply_iff_imply_imply'!.mp hΓ₂) h;
    have : Unprovable 𝓢 Γ ⊥ := FormulaSet.def_consistent.mp (Ω.consistent) _ hΓ₁; contradiction;


-- @@ L177-177 verbatim
end «lp_section_1»


-- @@ L179-181 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] (C : FrameClass) : Prop where
  canonical : (Kripke.canonicalFrame 𝓢) ∈ C


-- @@ L183-192 verbatim
instance [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  intro φ hφ
  by_contra h
  exact
    (ValidOnFrameClass.not_of_exists_model (by
      use (canonicalModel 𝓢)
      constructor
      · exact Canonical.canonical
      · exact iff_valid_on_canonicalModel_deducible.not.mpr h)) hφ
⟩


-- @@ L194-194 verbatim
end Kripke


-- @@ L196-196 verbatim
end Modal

-- @@ L197-197 verbatim
end LO
