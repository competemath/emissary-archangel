/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.IntProp


-- @@ L12-12 verbatim
/-! # Basic -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Modal


-- @@ L20-20 verbatim
variable {α} [DecidableEq α]


-- @@ L22-22 verbatim
namespace Formula


-- @@ L24-29 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def TrivTranslation : Formula α → Formula α
  | .atom a => atom a
  | Box.box φ => φ.TrivTranslation
  | ⊥ => ⊥
  | Arrow.arrow φ ψ => Arrow.arrow (φ.TrivTranslation) (ψ.TrivTranslation)


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᵀ" => TrivTranslation


-- @@ L33-33 verbatim
namespace TrivTranslation


-- @@ L35-35 expanded
@[simp]
lemma degree_zero : (TrivTranslation φ).degree = 0 := by
  induction φ <;> simp [TrivTranslation, degree, *];


-- @@ L37-42 expanded
@[simp]
lemma back :
    Formula.toModalFormula (Formula.toPropFormula (TrivTranslation φ)) = TrivTranslation φ := by
  induction φ using rec' with
  | himp => simp [TrivTranslation, toPropFormula, *];
  | hbox => simp [TrivTranslation, *];
  | _ => rfl;


-- @@ L44-44 verbatim
end TrivTranslation



-- @@ L47-52 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | Box.box _ => ⊤
  | ⊥ => ⊥
  | Arrow.arrow φ ψ => Arrow.arrow (φ.VerTranslation) (ψ.VerTranslation)


-- @@ L53-54 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ⱽ" => VerTranslation


-- @@ L56-56 verbatim
namespace VerTranslation


-- @@ L58-62 expanded
@[simp]
lemma degree_zero : (VerTranslation φ).degree = 0 := by
  induction φ using rec' with
  | himp => simp [VerTranslation, *];
  | _ => rfl;


-- @@ L64-67 expanded
@[simp]
lemma back : Formula.toModalFormula (Formula.toPropFormula (VerTranslation φ)) = VerTranslation φ :=
  by
  induction φ using rec' with
  | himp => simp [VerTranslation, toPropFormula, *];
  | _ => rfl;


-- @@ L69-69 verbatim
end VerTranslation


-- @@ L71-71 verbatim
end Formula


-- @@ L73-73 verbatim
open Entailment

-- @@ L74-74 verbatim
open Formula (TrivTranslation VerTranslation)


-- @@ L76-76 verbatim
namespace Hilbert


-- @@ L78-89 expanded
lemma provable_of_classical_provable {mH : Modal.Hilbert ℕ} {φ : IntProp.Formula ℕ} :
    (Provable (IntProp.Hilbert.Cl) φ) → (Provable mH (Formula.toModalFormula φ)) := by intro h;
  induction h using IntProp.Hilbert.Deduction.rec! with
  | maxm ih =>
    rcases (by simpa using ih) with (⟨_, rfl⟩ | ⟨_, rfl⟩); · exact efq!;
    · exact lem!;
  | mdp ihφψ ihφ => exact mdp ihφψ ihφ;
  | _ => dsimp [IntProp.Formula.toModalFormula]; simp;


-- @@ L91-91 verbatim
namespace Triv



-- @@ L94-101 expanded
lemma iff_trivTranslated : Provable (Hilbert.Triv) (LogicalConnective.iff φ (TrivTranslation φ)) :=
  by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    apply iff_intro!; · exact imp_trans''! axiomT! (and₁'! ih)
    · exact imp_trans''! (and₂'! ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!


-- @@ L103-119 expanded
protected theorem classical_reducible :
    Provable Hilbert.Triv φ ↔
      Provable (IntProp.Hilbert.Cl) (Formula.toPropFormula (TrivTranslation φ)) :=
  by
  constructor;
  · intro h;
    induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩ <;>
        simp [TrivTranslation, Formula.toPropFormula];
    | mdp ih₁ ih₂ => dsimp [TrivTranslation] at ih₁ ih₂; exact mdp ih₁ ih₂;
    | nec ih => exact ih;
    | _ => simp [TrivTranslation, Formula.toPropFormula];
  · intro h;
    have d₁ : Provable Hilbert.Triv (Arrow.arrow (TrivTranslation φ) φ) :=
      and₂'! iff_trivTranslated;
    have d₂ : Provable Hilbert.Triv (TrivTranslation φ) := by
      simpa only [TrivTranslation.back] using provable_of_classical_provable h;
    exact mdp d₁ d₂;


-- @@ L121-121 verbatim
end Triv



-- @@ L124-124 verbatim
namespace Ver


-- @@ L126-133 expanded
lemma iff_verTranslated : Provable (Hilbert.Ver) (LogicalConnective.iff φ (VerTranslation φ)) := by
  induction φ using Formula.rec' with
  | hbox =>
    apply iff_intro!; · exact imply₁'! verum!
    · exact imply₁'! (by simp)
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!


-- @@ L135-149 expanded
protected lemma classical_reducible :
    Provable (Hilbert.Ver) φ ↔
      Provable (IntProp.Hilbert.Cl) (Formula.toPropFormula (VerTranslation φ)) :=
  by
  constructor;
  · intro h;
    induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩ <;>
        simp [VerTranslation, Formula.toPropFormula];
    | mdp ih₁ ih₂ => dsimp [VerTranslation] at ih₁ ih₂; exact mdp ih₁ ih₂;
    | _ => simp [VerTranslation, Formula.toPropFormula];
  · intro h;
    have d₁ : Provable Hilbert.Ver (Arrow.arrow (VerTranslation φ) φ) := and₂'! iff_verTranslated;
    have d₂ : Provable Hilbert.Ver (VerTranslation φ) := by
      simpa using provable_of_classical_provable h;
    exact mdp d₁ d₂;


-- @@ L151-151 verbatim
end Ver



-- @@ L154-154 verbatim
end Hilbert


-- @@ L156-156 verbatim
end Modal

-- @@ L157-157 verbatim
end LO
