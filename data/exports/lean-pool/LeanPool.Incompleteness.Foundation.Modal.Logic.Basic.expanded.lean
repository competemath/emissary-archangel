/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.K
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness


-- @@ L15-15 verbatim
/-! # Basic -/


-- @@ L17-17 verbatim
@[expose] public section




-- @@ L21-21 verbatim
namespace LO

-- @@ L22-22 verbatim
namespace Modal


-- @@ L24-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Logic := Set (Modal.Formula ℕ)


-- @@ L27-28 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Hilbert.logic (H : Hilbert ℕ) : Logic :=
  {φ | Provable H φ}


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Logic.K : Logic := Hilbert.K.logic



-- @@ L34-34 verbatim
namespace Logic


-- @@ L36-38 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Unnecessitation (L : Logic) where
  unnec_closed {φ} : Box.box φ ∈ L → φ ∈ L


-- @@ L40-42 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class ModalDisjunctive (L : Logic) where
  modal_disjunctive_closed {φ ψ} : Vee.vee (Box.box φ) (Box.box ψ) ∈ L → φ ∈ L ∨ ψ ∈ L


-- @@ L44-48 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class QuasiNormal (L : Logic) where
  subset_K : Logic.K ⊆ L
  mdp_closed {φ ψ} : Arrow.arrow φ ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, Formula.subst s φ ∈ L


-- @@ L50-52 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Normal (L : Logic) extends L.QuasiNormal where
  nec_closed {φ} : φ ∈ L → Box.box φ ∈ L


-- @@ L54-56 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Sublogic (L₁ L₂ : Logic) where
  subset : L₁ ⊆ L₂


-- @@ L58-60 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class ProperSublogic (L₁ L₂ : Logic) : Prop where
  ssubset : L₁ ⊂ L₂


-- @@ L62-62 verbatim
end Logic


-- @@ L64-64 verbatim
namespace Hilbert


-- @@ L66-66 verbatim
open Entailment


-- @@ L68-68 verbatim
variable {H : Hilbert ℕ}


-- @@ L70-87 expanded
instance normal [H.HasK] : (H.logic).Normal
    where
  subset_K := by intro φ hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h => rcases (by simpa using h) with ⟨s, rfl⟩; simp;
    | mdp ihφψ ihφ => exact mdp! ihφψ ihφ;
    | nec ih => exact nec! ih;
    | _ => simp;
  mdp_closed := by intro φ ψ hφψ hφ; exact mdp hφψ hφ;
  subst_closed := by intro φ hφ s; exact Hilbert.Deduction.subst! s hφ;
  nec_closed := by intro φ hφ; exact Entailment.nec! hφ;


-- @@ L89-89 verbatim
instance [Entailment.Unnecessitation H] : H.logic.Unnecessitation := ⟨fun {_} h => unnec! h⟩


-- @@ L91-92 verbatim
instance [Entailment.ModalDisjunctive H] : H.logic.ModalDisjunctive :=
  ⟨fun {_ _} h => modal_disjunctive h⟩


-- @@ L94-94 verbatim
instance : (Logic.K).Normal := Hilbert.normal


-- @@ L96-96 verbatim
end Hilbert



-- @@ L99-99 verbatim
section «lp_section_1»


-- @@ L101-101 verbatim
open Kripke


-- @@ L103-104 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FrameClass.logic (C : FrameClass) : Logic :=
  {φ | Realize C φ}


-- @@ L106-107 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FiniteFrameClass.logic (C : FiniteFrameClass) : Logic :=
  {φ | Realize C φ}


-- @@ L109-116 verbatim
lemma _root_.LO.Modal.Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic
  {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  · exact sound.sound;
  · exact complete.complete;


-- @@ L118-125 verbatim
lemma _root_.LO.Modal.Logic.eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic
  {H : Hilbert ℕ} {C : FiniteFrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  · exact sound.sound;
  · exact complete.complete;


-- @@ L127-128 verbatim
lemma _root_.LO.Modal.Logic.K.eq_AllKripkeFrameClass_Logic : Logic.K = AllFrameClass.logic :=
  Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic


-- @@ L130-132 verbatim
lemma _root_.LO.Modal.Logic.K.eq_AllKripkeFiniteFrameClass_Logic :
    Logic.K = AllFiniteFrameClass.logic :=
  Logic.eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic


-- @@ L134-134 verbatim
end «lp_section_1»



-- @@ L137-137 verbatim
end Modal

-- @@ L138-138 verbatim
end LO
