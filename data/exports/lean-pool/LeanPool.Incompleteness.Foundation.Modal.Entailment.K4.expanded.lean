/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Entailment.K


-- @@ L10-10 verbatim
/-! # K4 -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Entailment


-- @@ L18-18 verbatim
open FiniteContext


-- @@ L20-20 verbatim
variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]

-- @@ L21-21 verbatim
variable {𝓢 : S} [Entailment.K4 𝓢]


-- @@ L23-24 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxdotBox : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (Box.box φ)) :=
  impTrans'' distributeBoxAnd and₁


-- @@ L25-28 expanded
omit [DecidableEq F] in
@[simp]
lemma imply_boxboxdot_box : Provable 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (Box.box φ)) := by
  classical exact ⟨implyBoxBoxdotBox⟩


-- @@ L30-32 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxBoxdot : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box (boxdot φ))) :=
  impTrans'' (implyRightAnd (impId _) axiomFour) collectBoxAnd


-- @@ L33-36 expanded
omit [DecidableEq F] in
@[simp]
lemma imply_box_boxboxdot! : Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box (boxdot φ))) := by
  classical exact ⟨implyBoxBoxBoxdot⟩


-- @@ L38-39 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxBoxdot' (h : Entailment.Prf 𝓢 (Box.box φ)) : Entailment.Prf 𝓢 (Box.box (boxdot φ)) :=
  mdp implyBoxBoxBoxdot h


-- @@ L40-44 expanded
omit [DecidableEq F] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma implyBoxBoxBoxdot'! (h : Provable 𝓢 (Box.box φ)) : Provable 𝓢 (Box.box (boxdot φ)) := by
  classical exact ⟨implyBoxBoxBoxdot' h.some⟩


-- @@ L46-47 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffBoxBoxBoxdot : Entailment.Prf 𝓢 (LogicalConnective.iff (Box.box φ) (Box.box (boxdot φ))) :=
  iffIntro implyBoxBoxBoxdot implyBoxBoxdotBox


-- @@ L48-51 expanded
omit [DecidableEq F] in
@[simp]
lemma iff_box_boxboxdot! : Provable 𝓢 (LogicalConnective.iff (Box.box φ) (Box.box (boxdot φ))) := by
  classical exact ⟨iffBoxBoxBoxdot⟩


-- @@ L53-55 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffBoxBoxdotBox : Entailment.Prf 𝓢 (LogicalConnective.iff (Box.box φ) (boxdot (Box.box φ))) :=
  iffIntro (impTrans'' (implyRightAnd (impId _) axiomFour) (impId _)) and₁


-- @@ L56-59 expanded
omit [DecidableEq F] in
@[simp]
lemma iff_box_boxdotbox! : Provable 𝓢 (LogicalConnective.iff (Box.box φ) (boxdot (Box.box φ))) := by
  classical exact ⟨iffBoxBoxdotBox⟩


-- @@ L61-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffBoxdotBoxdotBoxdot :
    Entailment.Prf 𝓢 (LogicalConnective.iff (boxdot φ) (boxdot (boxdot φ))) :=
  iffIntro (implyRightAnd (impId _) (impTrans'' boxdotBox (and₁' iffBoxBoxBoxdot))) and₁


-- @@ L64-67 expanded
omit [DecidableEq F] in
@[simp]
lemma iff_boxdot_boxdotboxdot : Provable 𝓢 (LogicalConnective.iff (boxdot φ) (boxdot (boxdot φ))) :=
  by classical exact ⟨iffBoxdotBoxdotBoxdot⟩


-- @@ L69-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomFour : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (boxdot (boxdot φ))) :=
  and₁' iffBoxdotBoxdotBoxdot


-- @@ L71-74 expanded
omit [DecidableEq F] in
@[simp]
lemma boxdot_axiomFour! : Provable 𝓢 (Arrow.arrow (boxdot φ) (boxdot (boxdot φ))) := by
  classical exact ⟨boxdotAxiomFour⟩


-- @@ L76-76 verbatim
end Entailment

-- @@ L77-77 verbatim
end LO
