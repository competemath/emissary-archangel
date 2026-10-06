/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.HornSat.Unsat
import DescriptiveComplexity.FixedPointOrderTransfer
import DescriptiveComplexity.Counting
import DescriptiveComplexity.Vocabulary
import Mathlib.Algebra.BigOperators.Finprod


-- @@ L12-34 verbatim
/-!
# The number written by unit propagation: definition

The function counterpart of HORN-SAT (`DescriptiveComplexity.HORNSAT`): some
variables of a Horn formula are marked as *outputs* and compared by
significance, and the problem is to compute the number whose binary digits say
which of them unit propagation forces to be true
(`DescriptiveComplexity.Forced`), i.e., which are true in the least model.

* The vocabulary is the one of CNF instances (`FirstOrder.Language.sat`) with
  two more symbols (`FirstOrder.Language.digitOrder`): `out` marks the output
  variables and `below` compares them.
* `DescriptiveComplexity.hornNumber`: a forced output variable contributes
  `2 ^ r`, where `r` is the number of output variables strictly below it, when
  `below` linearly orders the output variables
  (`DescriptiveComplexity.VarOrder`). An instance that is not a satisfiable
  Horn formula, or whose `below` is not such an order, writes `0`.

This is the problem through which the number written by a machine
(`DescriptiveComplexity.DTMNumber`) is shown hard for FP: the least fixed
point of a system of rules is the least model of a Horn formula, and the
unit-propagation machine leaves that model on its tape.
-/


-- @@ L36-36 verbatim
namespace FirstOrder


-- @@ L38-38 verbatim
namespace Language


-- @@ L40-46 verbatim
/-- The symbols reading a number off a set of marked elements. -/
fo_language digitOrder with dgo where
  /-- `out x`: the element `x` holds one digit. -/
  out : 1
  /-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
  below : 2


-- @@ L48-49 verbatim
/-- The relational language of Horn formulas writing a number. -/
abbrev satOut : Language.{0, 0} := Language.sat.sum Language.digitOrder


-- @@ L51-51 verbatim
end Language


-- @@ L53-53 verbatim
end FirstOrder


-- @@ L55-55 verbatim
namespace DescriptiveComplexity


-- @@ L57-57 verbatim
open FirstOrder


-- @@ L59-59 verbatim
open Language Structure


-- @@ L61-62 verbatim
/-- “Is an output variable”. -/
abbrev hnOut : Language.satOut.Relations 1 := Sum.inr dgoOut


-- @@ L64-65 verbatim
/-- The comparison of the output variables. -/
abbrev hnBelow : Language.satOut.Relations 2 := Sum.inr dgoBelow


-- @@ L67-70 verbatim
/-- A Horn formula writing a number is a CNF instance. -/
instance satOutStructure (A : Type) [Language.satOut.Structure A] :
    Language.sat.Structure A :=
  (LHom.sumInl : Language.sat →ᴸ Language.satOut).reduct A


-- @@ L72-72 verbatim
/-! ### The propagation closure is isomorphism-invariant -/


-- @@ L74-74 verbatim
section ForcedIso


-- @@ L76-76 verbatim
variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]


-- @@ L78-91 verbatim
theorem forcedIn_map (e : A ≃[Language.sat] B) :
    ∀ (n : ℕ) (x : A), ForcedIn n x → ForcedIn n (e x) := by
  intro n
  induction n with
  | zero => exact fun _ h => h.elim
  | succ n ih =>
    rintro x ⟨c, hc, hp, hneg⟩
    refine ⟨e c, (relMap_equiv₁ e satIsClause c).mp hc, (relMap_equiv₂ e satPosIn c x).mp hp,
      fun y hy => ?_⟩
    have hy' : RelMap satNegIn ![c, e.symm y] := by
      refine (relMap_equiv₂ e satNegIn c (e.symm y)).mpr ?_
      rwa [show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y]
    have := ih (e.symm y) (hneg _ hy')
    rwa [show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y] at this


-- @@ L93-100 verbatim
theorem forced_equiv (e : A ≃[Language.sat] B) (x : A) : Forced (e x) ↔ Forced x := by
  constructor
  · rintro ⟨n, hn⟩
    have := forcedIn_map e.symm n (e x) hn
    rw [show (e.symm (e x) : A) = x from e.toEquiv.symm_apply_apply x] at this
    exact ⟨n, this⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, forcedIn_map e n x hn⟩


-- @@ L102-102 verbatim
end ForcedIso


-- @@ L104-104 verbatim
/-! ### The number -/


-- @@ L106-106 verbatim
section Semantics


-- @@ L108-108 verbatim
variable {A : Type} [Language.satOut.Structure A]


-- @@ L110-112 verbatim
/-- The output variable `x` is forced. -/
def ForcedDigit (x : A) : Prop :=
  RelMap hnOut ![x] ∧ Forced x


-- @@ L114-116 verbatim
/-- `y` is an output variable strictly below `x`. -/
def LowerVar (x y : A) : Prop :=
  RelMap hnOut ![y] ∧ y ≠ x ∧ RelMap hnBelow ![y, x]


-- @@ L118-121 verbatim
/-- The rank of a variable among the outputs: the number of output variables
strictly below it. -/
noncomputable def varRank (x : A) : ℕ :=
  Nat.card {y : A // LowerVar x y}


-- @@ L123-133 verbatim
variable (A) in
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output variables. -/
def VarOrder : Prop :=
  (∀ p : A, RelMap hnOut ![p] → RelMap hnBelow ![p, p]) ∧
    (∀ p q r : A, RelMap hnOut ![p] → RelMap hnOut ![q] → RelMap hnOut ![r] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, r] → RelMap hnBelow ![p, r]) ∧
    (∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] ∨ RelMap hnBelow ![q, p]


-- @@ L135-143 verbatim
variable (A) in
open Classical in
/-- **The number written by unit propagation**: each forced output variable
contributes two to the power of its rank among the outputs. Instances that are
not satisfiable Horn formulas, or whose outputs are not linearly ordered,
write `0`. -/
noncomputable def hornNumber : ℕ :=
  if HornSatisfiable A ∧ VarOrder A then ∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0
  else 0


-- @@ L145-145 verbatim
end Semantics


-- @@ L147-147 verbatim
section Iso


-- @@ L149-149 verbatim
variable {A B : Type} [Language.satOut.Structure A] [Language.satOut.Structure B]


-- @@ L151-153 verbatim
theorem forcedDigit_equiv (e : A ≃[Language.satOut] B) (x : A) :
    ForcedDigit (e x) ↔ ForcedDigit x :=
  and_congr (relMap_equiv₁ e hnOut x).symm (forced_equiv (reductSumInlEquiv e) x)


-- @@ L155-158 verbatim
theorem lowerVar_equiv (e : A ≃[Language.satOut] B) (x y : A) :
    LowerVar (e x) (e y) ↔ LowerVar x y :=
  and_congr (relMap_equiv₁ e hnOut y).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e hnBelow y x).symm)


-- @@ L160-161 verbatim
theorem varRank_equiv (e : A ≃[Language.satOut] B) (x : A) : varRank (e x) = varRank x :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun y => (lowerVar_equiv e x y).symm)).symm


-- @@ L163-191 verbatim
theorem varOrder_equiv (e : A ≃[Language.satOut] B) : VarOrder A ↔ VarOrder B := by
  have h1 : ∀ p, (RelMap hnOut ![e p] : Prop) ↔ RelMap hnOut ![p] :=
    fun p => (relMap_equiv₁ e hnOut p).symm
  have h2 : ∀ p q, (RelMap hnBelow ![e p, e q] : Prop) ↔ RelMap hnBelow ![p, q] :=
    fun p q => (relMap_equiv₂ e hnBelow p q).symm
  constructor
  · rintro ⟨hr, ht, ha, hl⟩
    refine ⟨fun p hp => ?_, fun p q r hp hq hr' hpq hqr => ?_, fun p q hp hq hpq hqp => ?_,
      fun p q hp hq => ?_⟩
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      exact (h2 p p).mpr (hr p ((h1 p).mp hp))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      obtain ⟨r, rfl⟩ := e.toEquiv.surjective r
      exact (h2 p r).mpr (ht p q r ((h1 p).mp hp) ((h1 q).mp hq) ((h1 r).mp hr')
        ((h2 p q).mp hpq) ((h2 q r).mp hqr))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      exact congrArg e (ha p q ((h1 p).mp hp) ((h1 q).mp hq) ((h2 p q).mp hpq) ((h2 q p).mp hqp))
    · obtain ⟨p, rfl⟩ := e.toEquiv.surjective p
      obtain ⟨q, rfl⟩ := e.toEquiv.surjective q
      exact (hl p q ((h1 p).mp hp) ((h1 q).mp hq)).imp (h2 p q).mpr (h2 q p).mpr
  · rintro ⟨hr, ht, ha, hl⟩
    exact ⟨fun p hp => (h2 p p).mp (hr _ ((h1 p).mpr hp)),
      fun p q r hp hq hr' hpq hqr => (h2 p r).mp (ht _ _ _ ((h1 p).mpr hp) ((h1 q).mpr hq)
        ((h1 r).mpr hr') ((h2 p q).mpr hpq) ((h2 q r).mpr hqr)),
      fun p q hp hq hpq hqp => e.toEquiv.injective
        (ha _ _ ((h1 p).mpr hp) ((h1 q).mpr hq) ((h2 p q).mpr hpq) ((h2 q p).mpr hqp)),
      fun p q hp hq => (hl _ _ ((h1 p).mpr hp) ((h1 q).mpr hq)).imp (h2 p q).mp (h2 q p).mp⟩


-- @@ L193-203 verbatim
/-- The number written is isomorphism-invariant. -/
theorem hornNumber_iso (e : A ≃[Language.satOut] B) : hornNumber A = hornNumber B := by
  classical
  have hsum : (∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0) =
      ∑ᶠ x : B, if ForcedDigit x then 2 ^ varRank x else 0 := by
    rw [← finsum_comp_equiv e.toEquiv]
    refine finsum_congr fun x => ?_
    change _ = if ForcedDigit (e x) then 2 ^ varRank (e x) else 0
    rw [varRank_equiv e x, if_congr (forcedDigit_equiv e x) rfl rfl]
  rw [hornNumber, hornNumber, hsum]
  exact if_congr (and_congr (hornSatisfiable_iso (reductSumInlEquiv e)) (varOrder_equiv e)) rfl rfl


-- @@ L205-205 verbatim
end Iso


-- @@ L207-212 verbatim
/-- **The number written by unit propagation**, as a counting problem on
`Language.satOut`-structures: the function counterpart of
`DescriptiveComplexity.HORNSAT`. -/
noncomputable def HornNumber : CountingProblem Language.satOut where
  Count := fun A inst => @hornNumber A inst
  iso_invariant := fun e => hornNumber_iso e


-- @@ L214-214 verbatim
end DescriptiveComplexity
