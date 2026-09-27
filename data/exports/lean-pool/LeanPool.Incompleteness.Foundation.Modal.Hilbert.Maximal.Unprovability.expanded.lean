/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Maximal.Basic
import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Hilbert.Cl.Classical


-- @@ L11-11 verbatim
/-! # Unprovability -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal


-- @@ L19-19 verbatim
open Entailment


-- @@ L21-21 verbatim
open IntProp


-- @@ L23-23 verbatim
open Hilbert

-- @@ L24-24 verbatim
open Hilbert.Deduction

-- @@ L25-25 verbatim
open Formula


-- @@ L27-27 verbatim
namespace Hilbert



-- @@ L30-30 verbatim
namespace Triv


-- @@ L32-36 expanded
lemma unprovable_AxiomL : Unprovable Hilbert.Triv (Axioms.L (.atom a)) := by
  apply Hilbert.Triv.classical_reducible.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation; use (fun _ => False);
  simp [TrivTranslation, toPropFormula];


-- @@ L38-38 verbatim
end Triv



-- @@ L41-41 verbatim
namespace Ver


-- @@ L43-47 expanded
lemma unprovable_AxiomP : Unprovable (Hilbert.Ver) Axioms.P := by
  apply Hilbert.Ver.classical_reducible.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies]; simp_all


-- @@ L49-49 verbatim
end Ver



-- @@ L52-52 verbatim
namespace K4


-- @@ L54-57 expanded
lemma provable_Cl_trivTranslated :
    Provable (Hilbert.K4) φ → Provable (Hilbert.Cl) (Formula.toPropFormula (TrivTranslation φ)) :=
  by intro h; apply Hilbert.Triv.classical_reducible.mp;
  exact Entailment.weakerThan_iff.mp K4_weakerThan_Triv h;


-- @@ L59-63 expanded
lemma unprovable_AxiomL : Unprovable Hilbert.K4 (Axioms.L (.atom a)) := by
  apply not_imp_not.mpr provable_Cl_trivTranslated;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation; use (fun _ => False);
  simp [TrivTranslation, toPropFormula];


-- @@ L65-65 verbatim
end K4



-- @@ L68-68 verbatim
namespace GL


-- @@ L70-79 expanded
lemma provable_CL_verTranslated :
    Provable (Hilbert.GL) φ → Provable (Hilbert.Cl) (Formula.toPropFormula (VerTranslation φ)) := by
  intro h;
  induction h using Deduction.rec! with
  | maxm a =>
    rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩ <;> simp [VerTranslation, toPropFormula];
  | mdp ih₁ ih₂ => dsimp [VerTranslation] at ih₁ ih₂; exact mdp ih₁ ih₂;
  | _ => simp [VerTranslation, toPropFormula];


-- @@ L81-85 expanded
lemma unprovable_AxiomT : Unprovable (Hilbert.GL) (Axioms.T (.atom a)) := by
  apply not_imp_not.mpr provable_CL_verTranslated;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation; use (fun _ => False);
  simp [VerTranslation, toPropFormula];


-- @@ L87-90 verbatim
instance : Entailment.Consistent (Hilbert.GL) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT;


-- @@ L92-92 verbatim
end GL


-- @@ L94-99 expanded
theorem not_S4_weakerThan_GL : ¬WeakerThan (Hilbert.S4) (Hilbert.GL) :=
  by
  apply Entailment.not_weakerThan_iff.mpr; existsi (Axioms.T (atom 0)); constructor;
  · exact axiomT!;
  · exact GL.unprovable_AxiomT;


-- @@ L101-101 verbatim
end Hilbert



-- @@ L104-104 verbatim
end Modal

-- @@ L105-105 verbatim
end LO
