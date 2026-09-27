/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Basic
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame


-- @@ L11-11 verbatim
/-! # Soundness -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal


-- @@ L19-19 verbatim
open Kripke

-- @@ L20-20 verbatim
open Formula

-- @@ L21-21 verbatim
open Formula.Kripke


-- @@ L23-23 verbatim
namespace Kripke

-- @@ L24-24 verbatim
namespace Hilbert


-- @@ L26-26 verbatim
variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}



-- @@ L29-29 verbatim
section «lp_section_1»


-- @@ L31-31 verbatim
variable {C : Kripke.FrameClass}


-- @@ L33-45 expanded
lemma soundness_of_FrameClass_definedBy_axiomInstances [defined : C.DefinedBy H.axiomInstances] :
    Provable H φ → Realize C φ := by intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h => obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h; apply defined.defines F |>.mp hF (Formula.subst s ψ);
    exact ⟨ψ, by assumption, s, rfl⟩;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;


-- @@ L47-57 verbatim
instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  · rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst <| defs.defines F |>.mp hF ψ hψ;
  · intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    exact ⟨φ, by assumption, .id, by simp⟩;
⟩


-- @@ L59-61 verbatim
instance [C.DefinedBy H.axioms] :
    Sound H C :=
  ⟨fun {_} => soundness_of_FrameClass_definedBy_axiomInstances⟩


-- @@ L63-67 expanded
lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : Unprovable H ⊥ :=
  by apply not_imp_not.mpr sound.sound; apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty; exact ⟨F, hF, by simp⟩;


-- @@ L69-72 verbatim
lemma consistent_of_FrameClass (C : Kripke.FrameClass) [C.IsNonempty] [Sound H C] :
    Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);


-- @@ L74-74 verbatim
end «lp_section_1»



-- @@ L77-77 verbatim
section «lp_section_2»


-- @@ L79-79 verbatim
variable {C : Kripke.FiniteFrameClass}


-- @@ L81-94 expanded
lemma soundness_of_FiniteFrameClass_definedBy_axiomInstances
    [defined : C.DefinedBy H.axiomInstances] : Provable H φ → Realize C φ := by
  rintro hφ _ ⟨F, ⟨hF, rfl⟩⟩;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h => obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h; apply defined.defines F |>.mp hF (Formula.subst s ψ);
    exact ⟨ψ, by assumption, s, rfl⟩;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;


-- @@ L96-106 verbatim
instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  · rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst <| defs.defines F |>.mp hF ψ hψ;
  · intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    exact ⟨φ, by assumption, .id, by simp⟩;
⟩


-- @@ L108-110 verbatim
instance [C.DefinedBy H.axioms] :
    Sound H C :=
  ⟨fun {_} => soundness_of_FiniteFrameClass_definedBy_axiomInstances⟩


-- @@ L112-116 expanded
lemma consistent_of_FiniteFrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] :
    Unprovable H ⊥ := by apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame; obtain ⟨F, hF⟩ := nonempty;
  exact ⟨F.toFrame, ⟨F, hF, rfl⟩, by simp⟩;


-- @@ L118-121 verbatim
lemma consistent_of_FiniteFrameClass (C : Kripke.FiniteFrameClass) [C.IsNonempty] [Sound H C] :
    Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FiniteFrameClass_aux (C := C);


-- @@ L123-123 verbatim
end «lp_section_2»



-- @@ L126-126 verbatim
end Hilbert

-- @@ L127-127 verbatim
end Kripke


-- @@ L129-129 verbatim
end Modal

-- @@ L130-130 verbatim
end LO
