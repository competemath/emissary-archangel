/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Geach
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Entailment.K
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness


-- @@ L13-13 verbatim
/-! # Geach -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Modal


-- @@ L21-21 verbatim
open Formula.Kripke


-- @@ L23-23 verbatim
namespace Kripke


-- @@ L25-28 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev MultiGeacheanConfluentFrameClass (G : Set Geachean.Taple) :
    FrameClass :=
  { F | (MultiGeachean G) F.Rel }


-- @@ L30-34 verbatim
instance : (MultiGeacheanConfluentFrameClass G).IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }


-- @@ L36-66 expanded
instance _root_.LO.Modal.Kripke.MultiGeacheanFrameClass.isDefinedByGeachAxioms (G) :
    (MultiGeacheanConfluentFrameClass G).DefinedBy (G.image (fun t => Axioms.Geach t (.atom 0))) :=
  by
  unfold MultiGeacheanConfluentFrameClass MultiGeachean Axioms.Geach; constructor; intro F;
  constructor;
  · rintro hF φ ⟨g, ⟨hg, rfl⟩⟩ V x h; obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
    apply Satisfies.multibox_def.mpr; intro z Rxz; apply Satisfies.multidia_def.mpr;
    obtain ⟨u, Ryu, Rzu⟩ := hF g hg ⟨Rxy, Rxz⟩; use u; constructor; · assumption;
    · exact (Satisfies.multibox_def.mp hbp) Ryu;
  · rintro h g hg x y z ⟨Rxy, Rxz⟩; let V : Kripke.Valuation F := fun v _ => Frame.RelItr' g.m y v;
    have : Satisfies ⟨F, V⟩ x (multidia g.i (multibox g.m (.atom 0))) :=
      by
      apply Satisfies.multidia_def.mpr; use y; constructor; · assumption;
      · apply Satisfies.multibox_def.mpr; aesop;
    have : Satisfies ⟨F, V⟩ x (multibox g.j (multidia g.n (Formula.atom 0))) :=
      h (Axioms.Geach g (.atom 0)) (by tauto) V x this;
    have : Satisfies ⟨F, V⟩ z (multidia g.n (Formula.atom 0)) := Satisfies.multibox_def.mp this Rxz;
    obtain ⟨u, Rzu, Ryu⟩ := Satisfies.multidia_def.mp this; exact ⟨u, Ryu, Rzu⟩;


-- @@ L68-70 verbatim
instance _root_.LO.Modal.Kripke.MultiGeacheanFrameClass.isDefinedByGeachHilbertAxioms (ts)
  : (MultiGeacheanConfluentFrameClass ts).DefinedBy (Hilbert.Geach ts).axioms :=
  FrameClass.definedBy_with_axiomK (MultiGeacheanFrameClass.isDefinedByGeachAxioms ts)



-- @@ L73-73 verbatim
section «lp_section_1»


-- @@ L75-75 verbatim
variable {F : Frame}


-- @@ L77-81 expanded
lemma reflexive_of_validate_AxiomT (h : Realize F (Axioms.T (.atom 0))) : Std.Refl F.Rel :=
  by
  have : ValidOnFrame F (Axioms.T (.atom 0)) → Std.Refl F.Rel := by
    simpa [Axioms.Geach, MultiGeachean, ← Geachean.reflexive_def] using
      MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 0, 1, 0⟩} |>.defines F |>.mpr;
  exact this h;


-- @@ L83-88 expanded
lemma transitive_of_validate_AxiomFour (h : Realize F (Axioms.Four (.atom 0))) :
    IsTrans F.World F.Rel :=
  by
  have : ValidOnFrame F (Axioms.Four (.atom 0)) → IsTrans F.World F.Rel := by
    simpa [Axioms.Geach, MultiGeachean, ← Geachean.transitive_def] using
      MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 2, 1, 0⟩} |>.defines F |>.mpr;
  exact this h;


-- @@ L90-90 verbatim
end «lp_section_1»


-- @@ L92-92 verbatim
end Kripke




-- @@ L96-96 verbatim
namespace Kripke


-- @@ L98-98 verbatim
variable {S} [Entailment (Formula ℕ) S]

-- @@ L99-99 verbatim
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]


-- @@ L101-101 verbatim
open Entailment

-- @@ L102-102 verbatim
open FormulaSet

-- @@ L103-103 verbatim
open canonicalFrame

-- @@ L104-104 verbatim
open MaximalConsistentSet


-- @@ L106-140 expanded
lemma _root_.LO.Modal.Kripke.canonicalFrame.multigeachean_of_provable_geach
    (hG :
      ∀ g ∈ G,
        ∀ φ,
          Provable 𝓢
            (Arrow.arrow (multidia g.i (multibox g.m φ)) (multibox g.j (multidia g.n φ)))) :
    MultiGeachean G (canonicalFrame 𝓢).Rel :=
  by
  intro t ht; rintro X Y Z ⟨RXY, RXZ⟩;
  have ⟨U, hU⟩ :=
    lindenbaum (𝓢 := 𝓢) (T := Set.premultibox t.m Y.1 ∪ Set.premultibox t.n Z.1) <|
      by
      apply intro_union_consistent; rintro Γ Δ ⟨hΓ, hΔ⟩ hC;
      replace hΓ : ∀ φ ∈ Γ, multibox t.m φ ∈ Y := fun φ hpp => hΓ φ hpp;
      have hΓconj : multibox t.m (List.conj₂ Γ) ∈ Y := iff_mem_multibox_conj.mpr hΓ;
      replace hΔ : ∀ φ ∈ Δ, multibox t.n φ ∈ Z := fun φ hpp => hΔ φ hpp;
      have hZ₁ : multibox t.n (List.conj₂ Δ) ∈ Z := iff_mem_multibox_conj.mpr hΔ;
      have : multibox t.j (multidia t.n (List.conj₂ Γ)) ∈ X :=
        MaximalConsistentSet.mdp (membership_iff.mpr <| Context.of! (hG t ht _))
          (multirel_def_multidia.mp RXY hΓconj)
      have hZ₂ : multidia t.n (List.conj₂ Γ) ∈ Z := multirel_def_multibox.mp RXZ this;
      have :
        Provable 𝓢
          (Arrow.arrow (Wedge.wedge (multibox t.n (List.conj₂ Δ)) (multidia t.n (List.conj₂ Γ)))
            ⊥) :=
        by { apply and_imply_iff_imply_imply'!.mpr;
        exact
          imp_trans''!
            (show
              Provable _
                (Arrow.arrow (multibox t.n (List.conj₂ Δ))
                  (multibox t.n (Tilde.tilde (List.conj₂ Γ))))
              by
              exact
                imply_multibox_distribute'! <|
                  contra₁'! <| imp_trans''! (and_imply_iff_imply_imply'!.mp hC) (and₂'! negEquiv!))
            (show
              Provable _
                (Arrow.arrow (multibox t.n (Tilde.tilde (List.conj₂ Γ)))
                  (Arrow.arrow (multidia t.n (List.conj₂ Γ)) ⊥))
              by exact imp_trans''! (contra₁'! <| and₁'! <| multidia_duality!) (and₁'! negEquiv!));
      }
      have :
        Unprovable 𝓢
          (Arrow.arrow (Wedge.wedge (multibox t.n (List.conj₂ Δ)) (multidia t.n (List.conj₂ Γ)))
            ⊥) :=
        (def_consistent.mp (Z.consistent)) (Γ :=
            [multibox t.n (List.conj₂ Δ), multidia t.n (List.conj₂ Γ)]) <|
          by
          suffices multibox t.n (List.conj₂ Δ) ∈ ↑Z ∧ multidia t.n (List.conj₂ Γ) ∈ ↑Z by simpa;
          constructor <;> assumption;
      contradiction;
  use U; simp only [Set.union_subset_iff] at hU; constructor;
  · apply multirel_def_multibox.mpr; apply hU.1;
  · apply multirel_def_multibox.mpr; apply hU.2;


-- @@ L142-142 verbatim
end Kripke



-- @@ L145-145 verbatim
namespace Hilbert

-- @@ L146-146 verbatim
namespace Geach


-- @@ L148-148 verbatim
open Kripke


-- @@ L150-152 verbatim
instance _root_.LO.Modal.Hilbert.Geach.Kripke.sound :
    Sound (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) :=
  inferInstance


-- @@ L154-156 verbatim
instance _root_.LO.Modal.Hilbert.Geach.Kripke.Consistent :
    Entailment.Consistent (Hilbert.Geach G) :=
  Kripke.Hilbert.consistent_of_FrameClass (Kripke.MultiGeacheanConfluentFrameClass G)


-- @@ L158-171 verbatim
instance _root_.LO.Modal.Hilbert.Geach.Kripke.Canonical :
    Canonical (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) :=
  ⟨by
  apply canonicalFrame.multigeachean_of_provable_geach;
  intro t ht φ;
  apply Hilbert.Deduction.maxm!;
  unfold Hilbert.axiomInstances;
  use Axioms.Geach t (.atom 0);
  constructor;
  · simp only [];
    right;
    aesop;
  · use (fun _ => φ); simp;
⟩


-- @@ L173-175 verbatim
instance _root_.LO.Modal.Hilbert.Geach.Kripke.Complete :
    Complete (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) :=
  inferInstance


-- @@ L177-177 verbatim
end Geach

-- @@ L178-178 verbatim
end Hilbert



-- @@ L181-181 verbatim
end Modal

-- @@ L182-182 verbatim
end LO
