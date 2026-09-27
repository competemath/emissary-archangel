/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.ComplementClosedConsistentFinset
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomGrz
import LeanPool.Incompleteness.Foundation.Modal.Entailment.Grz
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Grz.Soundness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KT


-- @@ L15-15 verbatim
/-! # Completeness -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Modal


-- @@ L23-23 verbatim
namespace Formula


-- @@ L25-25 verbatim
variable {α : Type u} [DecidableEq α]

-- @@ L26-26 verbatim
variable {φ ψ : Formula ℕ}


-- @@ L28-30 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable abbrev subformulasGrz (φ : Formula α) :=
  φ.subformulas ∪ (φ.subformulas.prebox.image (fun ψ => Box.box (Arrow.arrow ψ (Box.box ψ))))


-- @@ L32-32 verbatim
namespace subformulasGrz


-- @@ L34-35 verbatim
@[simp 1100]
lemma mem_self : φ ∈ φ.subformulasGrz := by simp [subformulasGrz, subformulas.mem_self]


-- @@ L37-39 expanded
lemma mem_boximpbox (h : ψ ∈ φ.subformulas.prebox) :
    Box.box (Arrow.arrow ψ (Box.box ψ)) ∈ φ.subformulasGrz := by simp_all [subformulasGrz];


-- @@ L41-41 verbatim
lemma mem_origin (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by simp_all [subformulasGrz];


-- @@ L43-45 expanded
lemma mem_imp (h : (Arrow.arrow ψ χ) ∈ φ.subformulasGrz) :
    ψ ∈ φ.subformulasGrz ∧ χ ∈ φ.subformulasGrz := by simp_all [subformulasGrz]; aesop;


-- @@ L47-47 expanded
lemma mem_imp₁ (h : (Arrow.arrow ψ χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz :=
  mem_imp h |>.1


-- @@ L49-49 expanded
lemma mem_imp₂ (h : (Arrow.arrow ψ χ) ∈ φ.subformulasGrz) : χ ∈ φ.subformulasGrz :=
  mem_imp h |>.2


-- @@ L51-56 verbatim
macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_origin <| by assumption
    | apply mem_imp₁ <| by assumption
    | apply mem_imp₂ <| by assumption
  )


-- @@ L58-59 verbatim
lemma mem_left (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by
  simp_all




-- @@ L63-63 verbatim
end subformulasGrz


-- @@ L65-65 verbatim
end Formula




-- @@ L69-69 verbatim
namespace Hilbert

-- @@ L70-70 verbatim
namespace Grz

-- @@ L71-71 verbatim
namespace Kripke


-- @@ L73-73 verbatim
open Formula

-- @@ L74-74 verbatim
open Formula.Kripke

-- @@ L75-75 verbatim
open Entailment

-- @@ L76-76 verbatim
open Entailment.Context

-- @@ L77-77 verbatim
open ComplementClosedConsistentFinset


-- @@ L79-79 verbatim
variable {φ ψ : Formula ℕ}


-- @@ L81-86 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.FiniteFrame
    where
  World := ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)
  Rel X
    Y :=
    (∀ ψ ∈ Set.prebox (φ.subformulasGrz), Box.box ψ ∈ X → Box.box ψ ∈ Y) ∧
      ((∀ ψ ∈ Set.prebox (φ.subformulasGrz), Box.box ψ ∈ Y → Box.box ψ ∈ X) → X = Y)


-- @@ L88-88 verbatim
namespace miniCanonicalFrame


-- @@ L90-91 verbatim
lemma reflexive : Std.Refl (miniCanonicalFrame φ).Rel :=
  ⟨fun _ => by simp⟩


-- @@ L93-99 verbatim
lemma transitive : IsTrans (miniCanonicalFrame φ).World (miniCanonicalFrame φ).Rel := by
  constructor
  rintro X Y Z ⟨RXY₁, RXY₂⟩ ⟨RYZ₁, RYZ₂⟩;
  constructor;
  · simp_all
  · intro h;
    simp_all


-- @@ L101-104 verbatim
lemma antisymm : Std.Antisymm (miniCanonicalFrame φ).Rel := by
  constructor
  rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
  exact h₁ h₂;


-- @@ L106-106 verbatim
end miniCanonicalFrame



-- @@ L109-112 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X



-- @@ L115-135 expanded
lemma truthlemma_lemma1 {X : ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)}
    (hq : Box.box ψ ∈ φ.subformulas) :
    ((X.1.prebox.modalBox) ∪ {Box.box (Arrow.arrow ψ (Box.box ψ)), -ψ}) ⊆
      complementary (φ.subformulasGrz) :=
  by
  simp only [FormulaFinset.complementary]; intro χ hr;
  replace hr :
    χ = Box.box (Arrow.arrow ψ (Box.box ψ)) ∨ χ = -ψ ∨ (∃ a, Box.box a ∈ X ∧ Box.box a = χ) := by
    simp at hr; tauto;
  apply Finset.mem_union.mpr; rcases hr with (rfl | rfl | ⟨χ, hr, rfl⟩); · simp_all
  · right;
    simp only [Finset.mem_image, Finset.mem_union, Finset.eq_prebox_premultibox_one,
      Finset.mem_preimage, Function.iterate_one];
    use ψ; constructor; · left; exact subformulas.mem_box hq;
    · rfl;
  · have := X.closed.subset hr; left;
    exact FormulaFinset.complementary_mem_box subformulasGrz.mem_imp₁ this;


-- @@ L137-191 expanded
lemma truthlemma_lemma2 {X : ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)}
    (hq₁ : Box.box ψ ∈ φ.subformulas) (hq₂ : Box.box ψ ∉ X) :
    FormulaFinset.Consistent (Hilbert.Grz)
      ((X.1.prebox.modalBox) ∪ {Box.box (Arrow.arrow ψ (Box.box ψ)), -ψ}) :=
  by
  apply FormulaFinset.intro_union_consistent; rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;
  replace hΓ₂ : ∀ χ ∈ Γ₂, χ = Box.box (Arrow.arrow ψ (Box.box ψ)) ∨ χ = -ψ := by simp_all
  by_contra hC;
  have : Provable (Hilbert.Grz) Γ₁ (Arrow.arrow (List.conj₂ Γ₂) ⊥) :=
    and_imply_iff_imply_imply'!.mp hC;
  have :
    Provable (Hilbert.Grz) Γ₁
      (Arrow.arrow (Wedge.wedge (Box.box (Arrow.arrow ψ (Box.box ψ))) (-ψ)) ⊥) :=
    imp_trans''!
      (by
        suffices
          Provable (Hilbert.Grz) Γ₁
            (Arrow.arrow (List.conj₂ [Box.box (Arrow.arrow ψ (Box.box ψ)), -ψ]) (List.conj₂ Γ₂))
          by simp_all
        apply conjconj_subset!; simpa using hΓ₂; )
      this;
  have :
    Provable (Hilbert.Grz) Γ₁
      (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ))) (Arrow.arrow (-ψ) ⊥)) :=
    and_imply_iff_imply_imply'!.mp this;
  have : Provable (Hilbert.Grz) Γ₁ (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ))) ψ) :=
    by
    rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
    · rw [hp] at this; exact imp_trans''! this dne!;
    · exact this;
  have :
    Provable (Hilbert.Grz) (List.box Γ₁)
      (Box.box (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ))) ψ)) :=
    contextual_nec! this;
  have : Provable (Hilbert.Grz) (List.box Γ₁) ψ := mdp axiomGrz! this;
  have : Provable (Hilbert.Grz) (Arrow.arrow (List.conj₂ (List.box (List.box Γ₁))) (Box.box ψ)) :=
    contextual_nec! this;
  have : Provable (Hilbert.Grz) (Arrow.arrow (Box.box (Box.box (List.conj₂ Γ₁))) (Box.box ψ)) :=
    imp_trans''! (imp_trans''! (distribute_multibox_conj! (n := 2)) <| conjconj_subset! (by simp))
      this;
  have : Provable (Hilbert.Grz) (Arrow.arrow (Box.box (List.conj₂ Γ₁)) (Box.box ψ)) :=
    imp_trans''! axiomFour! this;
  have : Provable (Hilbert.Grz) (Arrow.arrow (List.conj₂ (List.box Γ₁)) (Box.box ψ)) :=
    imp_trans''! collect_box_conj! this;
  have :
    Provable (Hilbert.Grz)
      (Arrow.arrow (List.conj₂ (List.box (X.1.prebox.modalBox |>.toList))) (Box.box ψ)) :=
    imp_trans''! (conjconj_subset! (by simp_all)) this;
  have :
    Provable (Hilbert.Grz) (Arrow.arrow (List.conj₂ (List.box (X.1.prebox.toList))) (Box.box ψ)) :=
    imp_trans''!
      (conjconj_provable!
        (by intro ψ hq;
          simp only [Finset.eq_prebox_premultibox_one, Finset.eq_box_multibox_one,
            List.eq_box_multibox_one, Finset.mem_toList, Finset.toList_toFinset, Finset.mem_image,
            Finset.mem_preimage, Function.iterate_one, exists_exists_and_eq_and] at hq;
          obtain ⟨χ, hr, rfl⟩ := hq; apply axiomFour'!; apply FiniteContext.by_axm!; simpa; ))
      this;
  have : Provable (Hilbert.Grz) X (Box.box ψ) :=
    by
    apply Context.provable_iff.mpr; use List.box X.1.prebox.toList; constructor; · simp;
    · assumption;
  have : Box.box ψ ∈ X := membership_iff (by trivial) |>.mpr this; contradiction;
  -- TODO: syntactical proof


-- @@ L192-202 expanded
lemma truthlemma_lemma3 :
    Provable (Hilbert.Grz)
      (Arrow.arrow (Wedge.wedge φ (Box.box (Arrow.arrow φ (Box.box φ)))) (Box.box φ)) :=
  by apply KT_weakerThan_Grz.pbl; by_contra hC;
  have := (not_imp_not.mpr <| Hilbert.KT.Kripke.complete |>.complete) hC;
  simp only [ValidOnFrameClass.models_iff] at this;
  obtain ⟨F, F_refl, hF⟩ := ValidOnFrameClass.exists_frame_of_not this;
  simp only [Semantics.Realize, ValidOnFrame, ValidOnModel, Satisfies,
    LogicalConnective.Prop.arrow_eq, imp_false, not_forall, not_exists, not_not] at hF;
  obtain ⟨V, x, ⟨⟨h₁, h₂⟩, ⟨y, ⟨Rxy, h₃⟩⟩⟩⟩ := hF; have := h₂ x (F_refl.refl x); simp_all


-- @@ L204-301 expanded
lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
    Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    have := subformulas.mem_imp₁ q_sub; have := subformulas.mem_imp₂ q_sub; constructor;
    · contrapose; intro h; apply Satisfies.not_imp.mpr; apply Satisfies.and_def.mpr; constructor;
      · apply ihq (subformulas.mem_imp₁ q_sub) |>.mpr;
        exact
          iff_not_mem_imp (hsub_qr := subformulasGrz.mem_origin q_sub) (hsub_q :=
                subformulasGrz.mem_left (by assumption)) (hsub_r :=
                subformulasGrz.mem_left (by assumption)) |>.mp
              h |>.1;
      · apply ihr (subformulas.mem_imp₂ q_sub) |>.not.mpr;
        have :=
          iff_not_mem_imp (hsub_qr := subformulasGrz.mem_origin q_sub) (hsub_q :=
                subformulasGrz.mem_left (by assumption)) (hsub_r :=
                subformulasGrz.mem_left (by assumption)) |>.mp
              h |>.2;
        exact
          iff_mem_compl (subformulasGrz.mem_left (by assumption)) |>.not.mpr (by simpa using this);
    · contrapose; intro h; replace h := Satisfies.and_def.mp <| Satisfies.not_imp.mp h;
      obtain ⟨hq, hr⟩ := h; replace hq := ihq (by assumption) |>.mp hq;
      replace hr := ihr (by assumption) |>.not.mp hr;
      apply
        iff_not_mem_imp (hsub_qr := subformulasGrz.mem_origin q_sub) (hsub_q :=
            subformulasGrz.mem_left (by assumption)) (hsub_r :=
            subformulasGrz.mem_left (by assumption)) |>.mpr;
      constructor; · assumption;
      ·
        simpa using
          iff_mem_compl (subformulasGrz.mem_left (by assumption)) |>.not.mp (by assumption);
  | hbox ψ ih =>
    have := subformulas.mem_box q_sub; constructor;
    · contrapose; by_cases w : ψ ∈ X;
      · intro h;
        obtain ⟨Y, hY⟩ :=
          lindenbaum (𝓢 := Hilbert.Grz) (Ψ := φ.subformulasGrz) (truthlemma_lemma1 q_sub)
            (truthlemma_lemma2 q_sub h);
        simp only [Finset.union_subset_iff] at hY; simp only [Satisfies]; push Not; use Y;
        constructor;
        · constructor; · intro χ _ hr₂; apply hY.1; simpa;
          · apply imp_iff_not_or (b := X = Y) |>.mpr; left; push Not;
            use (Arrow.arrow ψ (Box.box ψ)); refine ⟨?_, ?_, ?_⟩; · simp_all;
            · apply hY.2; simp;
            · by_contra hC;
              have : Provable Hilbert.Grz (↑X) ψ :=
                membership_iff (subformulasGrz.mem_left (by assumption)) |>.mp w;
              have : Provable (Hilbert.Grz) (↑X) (Box.box (Arrow.arrow ψ (Box.box ψ))) :=
                membership_iff (subformulasGrz.mem_boximpbox (by simp_all)) |>.mp hC;
              have :
                Provable (Hilbert.Grz) (↑X)
                  (Arrow.arrow (Wedge.wedge ψ (Box.box (Arrow.arrow ψ (Box.box ψ)))) (Box.box ψ)) :=
                Context.of! <| truthlemma_lemma3;
              have : Provable (Hilbert.Grz) (↑X) (Box.box ψ) :=
                mdp this (and₃'! (by assumption) (by assumption));
              have : Box.box ψ ∈ X :=
                membership_iff (subformulasGrz.mem_origin (by assumption)) |>.mpr this;
              contradiction;
        · apply ih (by aesop) |>.not.mpr;
          apply iff_mem_compl (subformulasGrz.mem_origin (by aesop)) |>.not.mpr; push Not;
          apply hY.2; simp;
      · intro _; simp only [Satisfies]; push Not; use X; constructor;
        · exact miniCanonicalFrame.reflexive.refl X;
        · exact ih (by aesop) |>.not.mpr w;
    · intro h Y RXY; apply ih (subformulas.mem_box q_sub) |>.mpr;
      have : Provable (Hilbert.Grz) (↑Y) (Arrow.arrow (Box.box ψ) ψ) := Context.of! <| axiomT!;
      have : Provable (Hilbert.Grz) (↑Y) ψ :=
        mdp this
          (membership_iff (by apply subformulasGrz.mem_left; assumption) |>.mp
            (RXY.1 ψ (by apply subformulasGrz.mem_left; tauto) h));
      exact
        membership_iff (by apply subformulasGrz.mem_left; exact subformulas.mem_box q_sub) |>.mpr
          this;


-- @@ L303-328 expanded
instance complete :
    Complete (Hilbert.Grz) (Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass) :=
  ⟨by
    intro φ; contrapose; intro h; apply ValidOnFiniteFrameClass.not_of_exists_frame;
    use (miniCanonicalFrame φ); constructor;
    ·
      refine
        ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm⟩;
    · apply ValidOnFiniteFrame.not_of_exists_valuation_world;
      obtain ⟨X, hX₁⟩ :=
        lindenbaum (𝓢 := Hilbert.Grz) (Φ := {-φ}) (Ψ := φ.subformulasGrz)
          (by simp only [Finset.singleton_subset_iff]; apply FormulaFinset.complementary_comp;
            exact subformulasGrz.mem_self)
          (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
      use (miniCanonicalModel φ).Val, X; apply truthlemma (by simp) |>.not.mpr;
      exact iff_mem_compl (by simp) |>.not.mpr <| by push Not; apply hX₁; tauto; ⟩


-- @@ L330-330 verbatim
end Kripke

-- @@ L331-331 verbatim
end Grz

-- @@ L332-332 verbatim
end Hilbert


-- @@ L334-334 verbatim
end Modal

-- @@ L335-335 verbatim
end LO
