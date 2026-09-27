/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic


-- @@ L10-10 verbatim
/-! # AxiomDot3 -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal


-- @@ L18-18 verbatim
open Formula.Kripke


-- @@ L20-20 verbatim
namespace Kripke


-- @@ L22-22 verbatim
variable {F : Kripke.Frame}


-- @@ L24-36 expanded
lemma connected_of_validate_dot3 (hCon : Connected F) :
    Realize F (Axioms.Dot3 (.atom 0) (.atom 1)) :=
  by
  rintro V x; apply Satisfies.or_def.mpr;
  suffices
    (∀ y, Frame.Rel' x y → (∀ z, Frame.Rel' y z → V z 0) → V y 1) ∨
      (∀ y, Frame.Rel' x y → (∀ z, Frame.Rel' y z → V z 1) → V y 0)
    by simpa [Semantics.Realize, Satisfies];
  by_contra hC; push Not at hC; obtain ⟨⟨y, Rxy, hp, hnq⟩, ⟨z, Rxz, hq, hnp⟩⟩ := hC;
  cases hCon ⟨Rxy, Rxz⟩ with
  | inl Ryz => have := hp z Ryz; contradiction;
  | inr Rzy => have := hq y Rzy; contradiction;


-- @@ L38-47 expanded
lemma validate_dot3_of_connected : Realize F (Axioms.Dot3 (.atom 0) (.atom 1)) → Connected F :=
  by
  contrapose; intro hCon; obtain ⟨x, y, Rxy, z, Ryz, nRyz, nRzy⟩ := by simpa [Connected] using hCon;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use
    (fun w a =>
      match a with
      | 0 => Frame.Rel' y w
      | 1 => Frame.Rel' z w
      | _ => False),
    x;
  suffices
    ∃ y',
      Frame.Rel' x y' ∧
        (∀ z', Frame.Rel' y' z' → Frame.Rel' y z') ∧
          ¬Frame.Rel' z y' ∧
            (∃ z', Frame.Rel' x z' ∧ (∀ y, Frame.Rel' z' y → Frame.Rel' z y) ∧ ¬Frame.Rel' y z')
    by simpa [Semantics.Realize, Satisfies];
  refine ⟨y, Rxy, by tauto, nRzy, z, Ryz, by tauto, nRyz⟩;


-- @@ L49-50 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ConnectedFrameClass : FrameClass := { F | Connected F }


-- @@ L52-59 verbatim
instance _root_.LO.Modal.Kripke.ConnectedFrameClass.DefinedByDot3 :
    ConnectedFrameClass.DefinedBy {Axioms.Dot3 (.atom 0) (.atom 1)} :=
  ⟨by
  intro F;
  constructor;
  · simpa using connected_of_validate_dot3;
  · simpa using validate_dot3_of_connected;
⟩


-- @@ L61-61 verbatim
end Kripke


-- @@ L63-63 verbatim
end Modal

-- @@ L64-64 verbatim
end LO
