/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.Basic
public import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Basic


-- @@ L11-11 verbatim
/-! # Soundness -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace IntProp


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


-- @@ L33-49 expanded
lemma soundness_of_FrameClass_definedBy_axiomInstances [defined : C.DefinedBy H.axiomInstances] :
    Provable H φ → Realize C φ := by intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
  | verum => apply ValidOnFrame.top;
  | implyS => apply ValidOnFrame.imply₁;
  | implyK => apply ValidOnFrame.imply₂;
  | andElimL => apply ValidOnFrame.andElim₁;
  | andElimR => apply ValidOnFrame.andElim₂;
  | andIntro => apply ValidOnFrame.andInst₃;
  | orIntroL => apply ValidOnFrame.orInst₁;
  | orIntroR => apply ValidOnFrame.orInst₂;
  | orElim => apply ValidOnFrame.orElim;
  | mdp => exact ValidOnFrame.mdp (by assumption) (by assumption);
  | maxm hi => obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := hi;
    exact defined.defines F |>.mp hF (Formula.subst s ψ) ⟨ψ, h, s, rfl⟩


-- @@ L51-62 verbatim
instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  · rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst <| defs.defines F |>.mp hF ψ hψ;
  · intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    refine ⟨φ, hφ, .id, ?_⟩;
    simp;
⟩


-- @@ L64-65 verbatim
instance [C.DefinedBy H.axioms] : Sound H C :=
  ⟨fun {_} => soundness_of_FrameClass_definedBy_axiomInstances⟩


-- @@ L67-71 expanded
lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : Unprovable H ⊥ :=
  by apply not_imp_not.mpr sound.sound; apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty; exact ⟨F, hF, by simp⟩


-- @@ L73-76 verbatim
lemma consistent_of_FrameClass (C : Kripke.FrameClass) [C.IsNonempty] [Sound H C] :
    Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);


-- @@ L78-78 verbatim
end «lp_section_1»


-- @@ L80-80 verbatim
end Hilbert

-- @@ L81-81 verbatim
end Kripke


-- @@ L83-83 verbatim
end IntProp

-- @@ L84-84 verbatim
end LO
