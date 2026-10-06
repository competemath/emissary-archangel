/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat


-- @@ L8-29 verbatim
/-!
# HORN-SAT: definition

The problem HORN-SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT:
a CNF structure is a yes-instance iff every clause contains at most one
positive literal (`DescriptiveComplexity.AtMostOnePositive`) *and* the CNF is
satisfiable (`DescriptiveComplexity.HornSatisfiable`, bundled as
`DescriptiveComplexity.HORNSAT`).

Folding the Horn condition into the yes-instances rather than into the
vocabulary is the same choice as for 3SAT and its width bound
(`DescriptiveComplexity.WidthAtMostThree`): it keeps HORN-SAT a decision problem on
arbitrary `Language.sat`-structures, so that it lives in the same catalog and
composes with the same reductions.

Horn formulas are the tractable case of propositional satisfiability – a
satisfiable Horn formula has a *least* model, computed by unit propagation in
linear time ([Dowling & Gallier 1984][dowling1984linear]) – and HORN-SAT is the
canonical complete problem for polynomial time. The corresponding hardness
statement, machine-free and one level below the Cook–Levin discharge, is in
`DescriptiveComplexity.Problems.HornSat.Hardness`.
-/


-- @@ L31-31 verbatim
namespace DescriptiveComplexity


-- @@ L33-33 verbatim
open FirstOrder


-- @@ L35-35 verbatim
open Language Structure


-- @@ L37-37 verbatim
section HornSat


-- @@ L39-39 verbatim
variable (A : Type) [Language.sat.Structure A]


-- @@ L41-45 verbatim
/-- Every clause of a `Language.sat`-structure has at most one positive
literal: any two variables occurring positively in the same clause coincide. -/
def AtMostOnePositive : Prop :=
  ∀ c x y : A, RelMap satIsClause ![c] → RelMap satPosIn ![c, x] →
    RelMap satPosIn ![c, y] → x = y


-- @@ L47-50 verbatim
/-- A `Language.sat`-structure is a yes-instance of HORN-SAT if every clause
has at most one positive literal and the CNF is satisfiable. -/
def HornSatisfiable : Prop :=
  AtMostOnePositive A ∧ Satisfiable A


-- @@ L52-52 verbatim
end HornSat


-- @@ L54-54 verbatim
/-! ### Isomorphism-invariance and the bundled problem -/


-- @@ L56-56 verbatim
section Iso


-- @@ L58-58 verbatim
variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]


-- @@ L60-67 verbatim
private theorem atMostOnePositive_of_iso (e : A ≃[Language.sat] B)
    (h : AtMostOnePositive A) : AtMostOnePositive B := by
  intro c x y hc hx hy
  have hx' := (relMap_equiv₂ e satPosIn (e.symm c) (e.symm x)).mpr (by simpa using hx)
  have hy' := (relMap_equiv₂ e satPosIn (e.symm c) (e.symm y)).mpr (by simpa using hy)
  have := h (e.symm c) (e.symm x) (e.symm y)
    ((relMap_equiv₁ e.symm satIsClause c).mp hc) hx' hy'
  simpa using congrArg e this


-- @@ L69-73 verbatim
/-- Horn satisfiability is isomorphism-invariant. -/
theorem hornSatisfiable_iso (e : A ≃[Language.sat] B) :
    HornSatisfiable A ↔ HornSatisfiable B :=
  and_congr ⟨atMostOnePositive_of_iso e, atMostOnePositive_of_iso e.symm⟩
    (satisfiable_iso e)


-- @@ L75-75 verbatim
end Iso


-- @@ L77-81 verbatim
/-- HORN-SAT, as a problem on `Language.sat`-structures: the same vocabulary as
SAT, with the Horn condition folded into the yes-instances. -/
def HORNSAT : DecisionProblem Language.sat where
  Holds := fun A inst => @HornSatisfiable A inst
  iso_invariant := fun e => hornSatisfiable_iso e


-- @@ L83-83 verbatim
end DescriptiveComplexity
