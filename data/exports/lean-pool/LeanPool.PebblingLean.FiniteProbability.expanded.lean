/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset


-- @@ L20-26 verbatim
/-!
# Elementary finite probability

This file avoids measure-theory overhead for the upper-bound proof.  All random
objects used there are uniform on finite types, so probability and expectation
are just normalized finite sums.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace PebblingLean


-- @@ L32-32 verbatim
namespace FiniteProbability


-- @@ L34-34 verbatim
variable {Ω ι : Type*}


-- @@ L36-39 verbatim
/-- Uniform probability of an event on a finite sample space, as a rational
number. -/
noncomputable def uniformProbability [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℚ :=
  ((Finset.univ.filter P).card : ℚ) / (Fintype.card Ω : ℚ)


-- @@ L41-44 verbatim
/-- Uniform expectation of a natural-valued random variable on a finite sample
space, as a rational number. -/
noncomputable def uniformExpectation [Fintype Ω] (X : Ω → ℕ) : ℚ :=
  (∑ ω : Ω, (X ω : ℚ)) / (Fintype.card Ω : ℚ)


-- @@ L46-62 verbatim
theorem exists_not_of_uniformProbability_lt_one [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (hprob : uniformProbability P < 1) :
    ∃ ω : Ω, ¬ P ω := by
  classical
  by_contra hnone
  have hall : ∀ ω : Ω, P ω := by
    simp_all
  have hfilter :
      (Finset.univ.filter P).card = Fintype.card Ω := by
    simp_all
  have hcard_ne : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hprob_eq : uniformProbability P = 1 := by
    unfold uniformProbability
    simp_all
  linarith


-- @@ L64-91 verbatim
/-- Union bound for finite uniform probabilities. -/
theorem uniformProbability_exists_le_sum [Fintype Ω] [Nonempty Ω]
    [Fintype ι] (P : ι → Ω → Prop)
    [∀ i, DecidablePred (P i)]
    [DecidablePred fun ω => ∃ i : ι, P i ω] :
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω) ≤
      ∑ i : ι, uniformProbability (P i) := by
  classical
  let bad : Finset Ω := Finset.univ.filter fun ω : Ω => ∃ i : ι, P i ω
  let badAt : ι → Finset Ω := fun i => Finset.univ.filter fun ω : Ω => P i ω
  have hsubset : bad ⊆ Finset.univ.biUnion badAt := by
    intro ω hω
    have hex : ∃ i : ι, P i ω := by
      simpa [bad] using hω
    rcases hex with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [badAt, hi]⟩
  have hcard :
      bad.card ≤ ∑ i : ι, (badAt i).card := by
    exact (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hden_nonneg : 0 ≤ (Fintype.card Ω : ℚ) := by positivity
  calc
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω)
        = (bad.card : ℚ) / (Fintype.card Ω : ℚ) := by
          rfl
    _ ≤ ((∑ i : ι, (badAt i).card : ℕ) : ℚ) / (Fintype.card Ω : ℚ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden_nonneg
    _ = ∑ i : ι, uniformProbability (P i) := by
          simp [uniformProbability, badAt, Finset.sum_div]


-- @@ L93-93 verbatim
end FiniteProbability


-- @@ L95-95 verbatim
end PebblingLean
