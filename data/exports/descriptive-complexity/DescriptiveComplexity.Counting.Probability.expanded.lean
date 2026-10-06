/-
Copyright (c) 2025 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


-- @@ L19-45 verbatim
/-!
# Independent Boolean variables: probabilities, and weighted counts

The concrete side of probabilistic query evaluation, with no logic in it: a
finite set `X` of independent Boolean variables – the uncertain facts of a
tuple-independent database – each true with its own rational probability.

The first part is taken from the library
[provenance-lean](https://github.com/PierreSenellart/provenance-lean)
(`Provenance.Probability`), where it underlies the probabilistic semantics of
ProvSQL: `DescriptiveComplexity.ProbAssignment`, the probability
`DescriptiveComplexity.ProbAssignment.valProb` of a valuation (a possible
world), the fact that these form a distribution
(`DescriptiveComplexity.ProbAssignment.sum_valProb_eq_one`), and the
probability `DescriptiveComplexity.ProbAssignment.funcProb` of an event.

The second part is what the counting side needs. A probability `a / (a + c)`
is a pair of natural **weights**, `a` for “true” and `c` for “false”
(`DescriptiveComplexity.ProbAssignment.ofWeights`). The **weighted count** of
an event (`DescriptiveComplexity.weightedCount`) is the sum, over the
valuations in it, of the product of the weights each variable takes. Then

`Pr(f) = weightedCount f / weightedCount ⊤`

(`DescriptiveComplexity.ProbAssignment.funcProb_ofWeights`): a probability is
a ratio of two weighted counts, and those are natural numbers.
-/


-- @@ L47-47 verbatim
namespace DescriptiveComplexity


-- @@ L49-49 verbatim
variable {X : Type} [Fintype X] [DecidableEq X]


-- @@ L51-59 verbatim
/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1


-- @@ L61-61 verbatim
namespace ProbAssignment


-- @@ L63-63 verbatim
variable (P : ProbAssignment X)


-- @@ L65-68 verbatim
/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x


-- @@ L70-78 verbatim
omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is non-negative. -/
private lemma valProb_factor_nonneg (v : X → Bool) (x : X) :
    0 ≤ (if v x then P.prob x else 1 - P.prob x) := by
  by_cases hv : v x
  · simpa [hv] using P.prob_nonneg x
  · simp [hv]
    have := P.prob_le_one x
    linarith


-- @@ L80-88 verbatim
omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is at most `1`. -/
private lemma valProb_factor_le_one (v : X → Bool) (x : X) :
    (if v x then P.prob x else 1 - P.prob x) ≤ 1 := by
  by_cases hv : v x
  · simpa [hv] using P.prob_le_one x
  · simp [hv]
    have := P.prob_nonneg x
    linarith


-- @@ L90-92 verbatim
omit [DecidableEq X] in
theorem valProb_nonneg (v : X → Bool) : 0 ≤ P.valProb v :=
  Finset.prod_nonneg (fun x _ => P.valProb_factor_nonneg v x)


-- @@ L94-102 verbatim
omit [DecidableEq X] in
theorem valProb_le_one (v : X → Bool) : P.valProb v ≤ 1 := by
  unfold valProb
  calc ∏ x, (if v x then P.prob x else 1 - P.prob x)
      ≤ ∏ _x : X, (1 : ℚ) :=
        Finset.prod_le_prod₀
          (fun x _ => P.valProb_factor_nonneg v x)
          (fun x _ => P.valProb_factor_le_one v x)
    _ = 1 := by simp


-- @@ L104-113 verbatim
omit [Fintype X] [DecidableEq X] in
/-- For any `x : X`, `Pr(x) + (1 - Pr(x)) = 1`: summing the two cases of the
factor at `x` over `Bool` gives `1`. -/
private lemma sum_factor_at (x : X) :
    ∑ b : Bool, (if b then P.prob x else 1 - P.prob x) = 1 := by
  -- Bool's univ is {false, true}; enumerate explicitly.
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
      Finset.sum_singleton]
  simp


-- @@ L115-126 verbatim
/-- The valuations form a probability distribution: `∑ v, Pr(v) = 1`. -/
theorem sum_valProb_eq_one : ∑ v : X → Bool, P.valProb v = 1 := by
  -- Reduce ∑_v ∏_x f(x, v x) to ∏_x ∑_b f(x, b) via Fintype.prod_sum, then
  -- close via `sum_factor_at`.
  have hps :
      (∏ x : X, ∑ b : Bool, (if b then P.prob x else 1 - P.prob x))
        = ∑ v : X → Bool, ∏ x : X, (if v x then P.prob x else 1 - P.prob x) :=
    Fintype.prod_sum (fun (x : X) (b : Bool) => if b then P.prob x else 1 - P.prob x)
  unfold valProb
  rw [← hps]
  simp_rw [P.sum_factor_at]
  simp



-- @@ L129-132 verbatim
/-- Probability of an event, a Boolean function of the valuation:
`Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : (X → Bool) → Bool) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0


-- @@ L134-140 verbatim
theorem funcProb_nonneg (f : (X → Bool) → Bool) : 0 ≤ P.funcProb f := by
  unfold funcProb
  apply Finset.sum_nonneg
  intro v _
  by_cases hv : f v
  · simpa [hv] using P.valProb_nonneg v
  · simp [hv]


-- @@ L142-150 verbatim
/-- `Pr(f) ≤ ∑_v Pr(v) = 1`. -/
theorem funcProb_le_one (f : (X → Bool) → Bool) : P.funcProb f ≤ 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : f v
  · simp [hv]
  · simpa [hv] using P.valProb_nonneg v

-- @@ L151-151 verbatim
end ProbAssignment


-- @@ L153-153 verbatim
/-! ### Weights -/


-- @@ L155-155 verbatim
section Weights


-- @@ L157-157 verbatim
variable (a c : X → ℕ)


-- @@ L159-162 verbatim
/-- The weight of a valuation: the product, over the variables, of the weight
`a` of those it makes true and the weight `c` of those it makes false. -/
def valWeight (v : X → Bool) : ℕ :=
  ∏ x, if v x then a x else c x


-- @@ L164-167 verbatim
/-- The **weighted count** of an event: the sum of the weights of the
valuations in it. -/
def weightedCount (f : (X → Bool) → Bool) : ℕ :=
  ∑ v : X → Bool, if f v then valWeight a c v else 0


-- @@ L169-179 verbatim
/-- The weighted count of the sure event is the product of the total weights
of the variables. -/
theorem weightedCount_true :
    weightedCount a c (fun _ => true) = ∏ x, (a x + c x) := by
  have hps : (∏ x : X, ∑ b : Bool, (if b then a x else c x)) =
      ∑ v : X → Bool, ∏ x : X, (if v x then a x else c x) :=
    Fintype.prod_sum fun (x : X) (b : Bool) => if b then a x else c x
  simp only [weightedCount, valWeight, ite_true]
  rw [← hps]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp


-- @@ L181-191 verbatim
/-- The probability assignment of a family of weights: the variable `x` is
true with probability `a x / (a x + c x)`. -/
def ProbAssignment.ofWeights (h : ∀ x, 0 < a x + c x) : ProbAssignment X where
  prob x := (a x : ℚ) / ((a x : ℚ) + c x)
  prob_nonneg x := div_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _))
  prob_le_one x := by
    have hpos : (0 : ℚ) < (a x : ℚ) + c x := by exact_mod_cast h x
    rw [div_le_one hpos]
    have : (0 : ℚ) ≤ c x := Nat.cast_nonneg _
    linarith


-- @@ L193-193 verbatim
variable {a c} (h : ∀ x, 0 < a x + c x)


-- @@ L195-209 verbatim
omit [DecidableEq X] in
/-- The probability of a valuation is its weight, over the product of the
total weights. -/
theorem ProbAssignment.valProb_ofWeights (v : X → Bool) :
    (ProbAssignment.ofWeights a c h).valProb v =
      (valWeight a c v : ℚ) / ((∏ x, (a x + c x) : ℕ) : ℚ) := by
  simp only [ProbAssignment.valProb, valWeight, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  have hpos : (0 : ℚ) < (a x : ℚ) + c x := by exact_mod_cast h x
  by_cases hv : v x
  · simp [hv, ProbAssignment.ofWeights]
  · simp only [hv, Bool.false_eq_true, ite_false, ProbAssignment.ofWeights, Nat.cast_add]
    field_simp
    ring


-- @@ L211-224 verbatim
/-- **A probability is a ratio of two weighted counts**: the probability of an
event is its weighted count, divided by the weighted count of the sure
event. -/
theorem ProbAssignment.funcProb_ofWeights (f : (X → Bool) → Bool) :
    (ProbAssignment.ofWeights a c h).funcProb f =
      (weightedCount a c f : ℚ) / (weightedCount a c fun _ => true) := by
  rw [weightedCount_true]
  simp only [ProbAssignment.funcProb, weightedCount, Nat.cast_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hf : f v
  · simp only [hf, ite_true]
    exact ProbAssignment.valProb_ofWeights h v
  · simp [hf]


-- @@ L226-226 verbatim
end Weights


-- @@ L228-228 verbatim
end DescriptiveComplexity
