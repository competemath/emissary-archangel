/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomDot3
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness


-- @@ L15-15 verbatim
/-! # S4Dot3 -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Modal


-- @@ L23-23 verbatim
open Kripke

-- @@ L24-24 verbatim
open Geachean


-- @@ L26-28 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveConnectedFrameClass : FrameClass :=
  { F | Std.Refl F ∧ IsTrans F.World F.Rel ∧ Connected F }


-- @@ L30-38 verbatim
instance _root_.LO.Modal.Kripke.ReflexiveTransitiveConnectedFrameClass.DefinedByS4Dot3Axioms
  : FrameClass.DefinedBy Kripke.ReflexiveTransitiveConnectedFrameClass Hilbert.S4Dot3.axioms := by
  rw [
    (show ReflexiveTransitiveConnectedFrameClass =
      ReflexiveTransitiveFrameClass ∩ ConnectedFrameClass by aesop),
    (show Hilbert.S4Dot3.axioms = Hilbert.S4.axioms ∪ {Axioms.Dot3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.ReflexiveTransitiveFrameClass (Hilbert.S4.axioms)
    ConnectedFrameClass {Axioms.Dot3 (.atom 0) (.atom 1)};


-- @@ L40-47 verbatim
instance : Kripke.ReflexiveTransitiveConnectedFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  constructor
  · exact ⟨fun _ => trivial⟩
  · constructor
    · exact ⟨fun _ _ _ _ _ => trivial⟩
    · intro _ _ _ _
      exact Or.inl trivial



-- @@ L50-50 verbatim
namespace Hilbert

-- @@ L51-51 verbatim
namespace S4Dot3


-- @@ L53-55 verbatim
instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.sound :
    Sound (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass :=
  inferInstance


-- @@ L57-59 verbatim
instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.consistent :
    Entailment.Consistent (Hilbert.S4Dot3) :=
  Kripke.Hilbert.consistent_of_FrameClass Kripke.ReflexiveTransitiveConnectedFrameClass



-- @@ L62-101 expanded
open Kripke MaximalConsistentSet in
instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.canonical :
    Canonical (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass :=
  by
  have hS4 :=
    canonicalFrame.multigeachean_of_provable_geach (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩}) (𝓢 :=
      Hilbert.S4Dot3) (by simp);
  constructor; refine ⟨?_, ?_, ?_⟩;
  · simpa [reflexive_def, Geachean] using @hS4 (⟨0, 0, 1, 0⟩) <| by tauto;
  · simpa [transitive_def, Geachean] using @hS4 ⟨0, 2, 1, 0⟩ <| by tauto;
  · intro X Y Z ⟨hXY, hXZ⟩; by_contra hC; push Not at hC; have ⟨hnYZ, hnZY⟩ := hC; clear hC;
    simp only [Set.not_subset] at hnYZ hnZY; obtain ⟨φ, hpY, hpZ⟩ := hnYZ;
    replace hpY : Box.box φ ∈ Y := hpY; obtain ⟨ψ, hqZ, hqY⟩ := hnZY;
    replace hqZ : Box.box ψ ∈ Z := hqZ;
    have hpqX : Box.box (Arrow.arrow (Box.box φ) ψ) ∉ X :=
      by
      apply iff_mem_box.not.mpr; push Not; use Y; constructor; · assumption;
      · apply iff_mem_imp.not.mpr; aesop;
    have hqpX : Box.box (Arrow.arrow (Box.box ψ) φ) ∉ X :=
      by
      apply iff_mem_box.not.mpr; push Not; use Z; constructor; · assumption;
      · apply iff_mem_imp.not.mpr; aesop;
    have :
      (Vee.vee (Box.box (Arrow.arrow (Box.box φ) ψ)) (Box.box (Arrow.arrow (Box.box ψ) φ))) ∉ X :=
      by apply iff_mem_or.not.mpr; push Not; exact ⟨hpqX, hqpX⟩;
    have :
      Vee.vee (Box.box (Arrow.arrow (Box.box φ) ψ)) (Box.box (Arrow.arrow (Box.box ψ) φ)) ∈ X :=
      membership_iff.mpr Entailment.axiomDot3!
    contradiction;


-- @@ L103-105 verbatim
instance _root_.LO.Modal.Hilbert.S4Dot3.Kripke.complete :
    Complete (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass :=
  inferInstance


-- @@ L107-107 verbatim
end S4Dot3

-- @@ L108-108 verbatim
end Hilbert



-- @@ L111-111 verbatim
end Modal

-- @@ L112-112 verbatim
end LO
