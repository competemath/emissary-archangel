/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.ComplementClosedConsistentFinset
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
import LeanPool.Incompleteness.Foundation.Modal.Entailment.GL
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Soundness


-- @@ L14-14 verbatim
/-! # Completeness -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace Modal

-- @@ L21-21 verbatim
namespace Hilbert

-- @@ L22-22 verbatim
namespace GL

-- @@ L23-23 verbatim
namespace Kripke


-- @@ L25-25 verbatim
open _root_.LO.Modal.Kripke

-- @@ L26-26 verbatim
open Entailment

-- @@ L27-27 verbatim
open Formula

-- @@ L28-28 verbatim
open Entailment Entailment.FiniteContext

-- @@ L29-29 verbatim
open Formula.Kripke

-- @@ L30-30 verbatim
open ComplementClosedConsistentFinset


-- @@ L32-32 verbatim
variable {φ ψ : Formula ℕ}


-- @@ L34-39 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.FiniteFrame
    where
  World := ComplementClosedConsistentFinset Hilbert.GL φ.subformulas
  Rel X
    Y :=
    (∀ ψ ∈ Set.prebox φ.subformulas, Box.box ψ ∈ X → (ψ ∈ Y ∧ Box.box ψ ∈ Y)) ∧
      (∃ χ ∈ Set.prebox φ.subformulas, Box.box χ ∉ X ∧ Box.box χ ∈ Y)


-- @@ L41-41 verbatim
namespace miniCanonicalFrame


-- @@ L43-45 verbatim
lemma is_irreflexive : Std.Irrefl (miniCanonicalFrame φ).Rel := by
  constructor
  simp_all


-- @@ L47-53 verbatim
lemma is_transitive : IsTrans (miniCanonicalFrame φ).World (miniCanonicalFrame φ).Rel := by
  constructor
  rintro X Y Z ⟨RXY, ⟨χ, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  · simp_all
  · use χ;
    simp_all


-- @@ L55-55 verbatim
end miniCanonicalFrame



-- @@ L58-61 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X



-- @@ L64-84 expanded
lemma truthlemma_lemma1 {X : ComplementClosedConsistentFinset Hilbert.GL φ.subformulas}
    (hq : Box.box ψ ∈ φ.subformulas) :
    ((X.1.prebox ∪ X.1.prebox.modalBox) ∪ {Box.box ψ, -ψ}) ⊆ complementary φ.subformulas :=
  by
  intro χ hr;
  replace hr : χ = Box.box ψ ∨ χ = -ψ ∨ Box.box χ ∈ X ∨ (∃ a, Box.box a ∈ X ∧ Box.box a = χ) := by
    simp at hr; tauto;
  rcases hr with (rfl | rfl | hp | ⟨χ, hr, rfl⟩); · apply Finset.mem_union.mpr; tauto;
  · apply Finset.mem_union.mpr; right; apply Finset.mem_image.mpr; use ψ; constructor;
    · exact subformulas.mem_box hq;
    · tauto;
  · have := X.closed.subset hp;
    have := FormulaFinset.complementary_mem_box (by apply subformulas.mem_imp₁) this;
    apply Finset.mem_union.mpr; left; exact subformulas.mem_box this;
  · exact X.closed.subset hr;


-- @@ L87-134 expanded
lemma truthlemma_lemma2 {X : ComplementClosedConsistentFinset Hilbert.GL φ.subformulas}
    (hq₁ : Box.box ψ ∈ φ.subformulas) (hq₂ : Box.box ψ ∉ X) :
    FormulaFinset.Consistent Hilbert.GL ((X.1.prebox ∪ X.1.prebox.modalBox) ∪ {Box.box ψ, -ψ}) :=
  by
  apply FormulaFinset.intro_union_consistent; rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;
  replace hΓ₂ : ∀ χ ∈ Γ₂, χ = Box.box ψ ∨ χ = -ψ := by simp_all
  by_contra hC;
  have : Provable _ Γ₁ (Arrow.arrow (List.conj₂ Γ₂) ⊥) :=
    provable_iff.mpr <| and_imply_iff_imply_imply'!.mp hC;
  have : Provable _ Γ₁ (Arrow.arrow (Wedge.wedge (Box.box ψ) (-ψ)) ⊥) :=
    imp_trans''!
      (by
        suffices Provable Hilbert.GL Γ₁ (Arrow.arrow (List.conj₂ [Box.box ψ, -ψ]) (List.conj₂ Γ₂))
          by simp_all
        apply conjconj_subset!; simpa using hΓ₂; )
      this;
  have : Provable _ Γ₁ (Arrow.arrow (Box.box ψ) (Arrow.arrow (-ψ) ⊥)) :=
    and_imply_iff_imply_imply'!.mp this;
  have : Provable Hilbert.GL Γ₁ (Arrow.arrow (Box.box ψ) ψ) :=
    by
    rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
    · rw [hp] at this; exact imp_trans''! this dne!;
    · exact this;
  have : Provable _ (List.box Γ₁) (Box.box (Arrow.arrow (Box.box ψ) ψ)) := contextual_nec! this;
  have : Provable _ (List.box Γ₁) (Box.box ψ) := mdp axiomL! this;
  have : Provable _ (Arrow.arrow (List.conj₂ (List.box Γ₁)) (Box.box ψ)) := provable_iff.mp this;
  have :
    Provable _
      (Arrow.arrow (List.conj₂ (List.box (X.1.prebox ∪ X.1.prebox.modalBox |>.toList)))
        (Box.box ψ)) :=
    imp_trans''! (conjconj_subset! (by simp_all)) this;
  have : Provable _ (Arrow.arrow (List.conj₂ (List.box (X.1.prebox.toList))) (Box.box ψ)) :=
    imp_trans''!
      (conjconj_provable!
        (by
          suffices
            ∀ χ,
              (Box.box χ ∈ X ∨ ∃ χ', Box.box χ' ∈ X ∧ Box.box χ' = χ) →
                Provable Hilbert.GL (List.multibox 1 (Finset.premultibox 1 X).toList) (Box.box χ)
            by simpa;
          rintro χ (hχ | ⟨χ, hχ, rfl⟩); · apply FiniteContext.by_axm!; simpa;
          · apply axiomFour'!; apply FiniteContext.by_axm!; simpa; ))
      this;
  have : Provable Hilbert.GL X (Box.box ψ) :=
    by
    apply Context.provable_iff.mpr; use List.box X.1.prebox.toList; constructor; · simp;
    · assumption;
  have : Box.box ψ ∈ X := membership_iff hq₁ |>.mpr this; contradiction;


-- @@ L136-189 verbatim
lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    constructor;
    · contrapose;
      intro h;
      apply Satisfies.imp_def.not.mpr;
      push Not;
      constructor;
      · apply ihq (subformulas.mem_imp₁ q_sub) |>.mpr;
        exact iff_not_mem_imp q_sub (subformulas.mem_imp₁ q_sub) (subformulas.mem_imp₂ q_sub)
          |>.mp h |>.1;
      · apply ihr (subformulas.mem_imp₂ q_sub) |>.not.mpr;
        have :=
          iff_not_mem_imp q_sub (subformulas.mem_imp₁ q_sub) (subformulas.mem_imp₂ q_sub)
            |>.mp h |>.2;
        exact iff_mem_compl (subformulas.mem_imp₂ q_sub) |>.not.mpr (by simpa using this);
    · contrapose;
      intro h;
      replace h := Satisfies.imp_def.not.mp h; push Not at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq : ψ ∈ X := ihq (subformulas.mem_imp₁ q_sub) |>.mp hq;
      replace hr : χ ∉ X := ihr (subformulas.mem_imp₂ q_sub) |>.not.mp hr;
      apply iff_not_mem_imp q_sub (subformulas.mem_imp₁ q_sub) (subformulas.mem_imp₂ q_sub) |>.mpr;
      constructor;
      · assumption;
      · simpa using iff_mem_compl (subformulas.mem_imp₂ q_sub) |>.not.mp (by simpa using hr);
  | hbox ψ ih =>
    constructor;
    · contrapose;
      intro h;
      obtain ⟨Y, hY₁⟩ :=
        lindenbaum (Ψ := φ.subformulas) (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
      simp only [Finset.union_subset_iff] at hY₁;
      apply Satisfies.box_def.not.mpr;
      push Not;
      use Y;
      constructor;
      · constructor;
        · aesop;
        · aesop;
      · apply ih ?_ |>.not.mpr;
        · apply iff_mem_compl (subformulas.mem_box q_sub) |>.not.mpr;
          push Not;
          apply hY₁.2;
          simp;
        · exact subformulas.mem_box q_sub;
    · intro h Y RXY;
      apply ih (subformulas.mem_box q_sub) |>.mpr;
      refine RXY.1 ψ ?_ h |>.1;
      assumption;


-- @@ L191-217 expanded
instance finiteComplete : Complete Hilbert.GL Kripke.TransitiveIrreflexiveFiniteFrameClass :=
  ⟨by
    intro φ; contrapose; intro h; apply ValidOnFiniteFrameClass.not_of_exists_frame;
    use (miniCanonicalFrame φ); constructor;
    · exact ⟨miniCanonicalFrame.is_transitive, miniCanonicalFrame.is_irreflexive⟩;
    · apply ValidOnFrame.not_of_exists_model_world;
      obtain ⟨X, hX₁⟩ :=
        lindenbaum (Φ := {-φ}) (Ψ := φ.subformulas)
          (by
            simp only [FormulaFinset.complementary, Finset.singleton_subset_iff, Finset.mem_union,
              Finset.mem_image];
            right; use φ; constructor <;> simp; )
          (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
      use (miniCanonicalModel φ), X; constructor; · tauto;
      · apply truthlemma (by simp) |>.not.mpr;
        exact iff_mem_compl (by simp) |>.not.mpr <| by push Not; apply hX₁; tauto; ⟩


-- @@ L219-219 verbatim
end Kripke

-- @@ L220-220 verbatim
end GL

-- @@ L221-221 verbatim
end Hilbert

-- @@ L222-222 verbatim
end Modal

-- @@ L223-223 verbatim
end LO
