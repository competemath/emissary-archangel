/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import LeanPool.ChannelCapacity.NonDegeneracy


-- @@ L11-15 verbatim
/-!
# ChannelCapacity.Counterexample

A finite counterexample showing that row separation does not imply injective prior pushforward.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open MeasureTheory

-- @@ L20-20 verbatim
open ProbabilityTheory

-- @@ L21-21 verbatim
open scoped ENNReal NNReal


-- @@ L23-23 verbatim
namespace ChannelCapacity.Counterexample


-- @@ L25-28 verbatim
/-- The probability measure induced by a probability mass function. -/
noncomputable def asProbabilityMeasure {α : Type*} [MeasurableSpace α] (p : PMF α) :
    ProbabilityMeasure α :=
  ⟨p.toMeasure, by infer_instance⟩


-- @@ L30-45 verbatim
/-- The uniform probability measure supported on the three points `a`, `b`, and `c`. -/
noncomputable def uniformTriple {α : Type*} [MeasurableSpace α] (a b c : α) :
    ProbabilityMeasure α :=
  ProbabilityMeasure.convexCombination
    (MeasureTheory.diracProba a)
    (ProbabilityMeasure.convexCombination
      (MeasureTheory.diracProba b)
      (MeasureTheory.diracProba c)
      (1 / 2)
      (by
        have h : (1 : ℝ) / 2 ≤ 1 := by norm_num
        exact_mod_cast h))
    (1 / 3)
    (by
      have h : (1 : ℝ) / 3 ≤ 1 := by norm_num
      exact_mod_cast h)


-- @@ L47-51 verbatim
private lemma permutationWeightSum :
    (1 / 2 : ℝ≥0∞) + 1 / 3 + 1 / 6 = 1 := by
  have h : ((1 / 2 : ℝ≥0) + 1 / 3 + 1 / 6 : ℝ≥0) = 1 := by
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)


-- @@ L53-61 verbatim
private lemma prior₁_case0 :
    (1 / 3 : ℝ≥0∞) * (1 / 2) + (1 - 1 / 3) * ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 3)) =
      1 / 3 := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 2) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 3)) : ℝ≥0) = 1 / 3 := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)


-- @@ L63-71 verbatim
private lemma prior₁_case1 :
    (1 / 3 : ℝ≥0∞) * (1 / 3) + (1 - 1 / 3) * ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 6)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 3) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 6)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)


-- @@ L73-81 verbatim
private lemma prior₁_case2 :
    (1 / 3 : ℝ≥0∞) * (1 / 6) + (1 - 1 / 3) * ((1 / 2) * (1 / 3) + (1 / 2) * (1 / 2)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 6) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 3) + (1 / 2) * (1 / 2)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)


-- @@ L83-91 verbatim
private lemma prior₂_case1 :
    (1 / 3 : ℝ≥0∞) * (1 / 6) + (1 - 1 / 3) * ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 6) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)


-- @@ L93-101 verbatim
private lemma prior₂_case2 :
    (1 / 3 : ℝ≥0∞) * (1 / 3) + (1 - 1 / 3) * ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 2)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 3) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 2)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)


-- @@ L103-135 verbatim
/-- The six rows of the channel, one for each permutation of the values `1/2, 1/3, 1/6`,
as probability mass functions on `Fin 3`. -/
noncomputable def rowPMF : Fin 6 → PMF (Fin 3)
  | 0 => PMF.ofFintype (fun
      | 0 => (1 / 2 : ℝ≥0∞)
      | 1 => (1 / 3 : ℝ≥0∞)
      | _ => (1 / 6 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_assoc] using permutationWeightSum)
  | 1 => PMF.ofFintype (fun
      | 0 => (1 / 2 : ℝ≥0∞)
      | 1 => (1 / 6 : ℝ≥0∞)
      | _ => (1 / 3 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 2 => PMF.ofFintype (fun
      | 0 => (1 / 3 : ℝ≥0∞)
      | 1 => (1 / 2 : ℝ≥0∞)
      | _ => (1 / 6 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 3 => PMF.ofFintype (fun
      | 0 => (1 / 6 : ℝ≥0∞)
      | 1 => (1 / 2 : ℝ≥0∞)
      | _ => (1 / 3 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 4 => PMF.ofFintype (fun
      | 0 => (1 / 3 : ℝ≥0∞)
      | 1 => (1 / 6 : ℝ≥0∞)
      | _ => (1 / 2 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | _ => PMF.ofFintype (fun
      | 0 => (1 / 6 : ℝ≥0∞)
      | 1 => (1 / 3 : ℝ≥0∞)
      | _ => (1 / 2 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)


-- @@ L137-139 verbatim
/-- The six channel rows as probability measures on `Fin 3`. -/
noncomputable def permutationRows : Fin 6 → ProbabilityMeasure (Fin 3) :=
  fun i => asProbabilityMeasure (rowPMF i)


-- @@ L141-144 verbatim
@[simp]
lemma permutationRows_apply_singleton (i : Fin 6) (y : Fin 3) :
    (permutationRows i).toMeasure {y} = rowPMF i y := by
  simp [permutationRows, asProbabilityMeasure]


-- @@ L146-148 verbatim
/-- The Markov kernel `Fin 6 → Fin 3` whose rows are the six permutation rows. -/
noncomputable def permutationKernel : Kernel (Fin 6) (Fin 3) :=
  Kernel.ofFunOfCountable fun i => (permutationRows i).toMeasure


-- @@ L150-153 verbatim
@[simp]
lemma permutationKernel_apply (i : Fin 6) :
    permutationKernel i = (rowPMF i).toMeasure := by
  rfl


-- @@ L155-157 verbatim
lemma permutationKernel_apply_singleton (i : Fin 6) (y : Fin 3) :
    permutationKernel i {y} = rowPMF i y := by
  simp [permutationKernel_apply]


-- @@ L159-164 verbatim
noncomputable instance permutationKernel_isMarkov :
    IsMarkovKernel permutationKernel := by
  constructor
  intro i
  change IsProbabilityMeasure ((rowPMF i).toMeasure)
  infer_instance


-- @@ L166-174 verbatim
/-- Pushing a point mass through `permutationKernel` returns the corresponding row.

This restates `ChannelCapacity.Kernel.priorPushforward_dirac` with the row written as
`permutationRows i` rather than as an anonymous `Subtype` constructor: the latter is not
type-correct at `implicit` transparency, so `rw` refuses to see through it below. -/
private lemma priorPushforward_diracProba (i : Fin 6) :
    ChannelCapacity.Kernel.priorPushforward permutationKernel (MeasureTheory.diracProba i) =
      permutationRows i :=
  ChannelCapacity.Kernel.priorPushforward_dirac permutationKernel i


-- @@ L176-178 verbatim
/-- The first prior: uniform on the inputs `{0, 3, 4}`. -/
noncomputable def prior₁ : ProbabilityMeasure (Fin 6) :=
  uniformTriple 0 3 4


-- @@ L180-182 verbatim
/-- The second prior: uniform on the inputs `{1, 2, 5}`. -/
noncomputable def prior₂ : ProbabilityMeasure (Fin 6) :=
  uniformTriple 1 2 5


-- @@ L184-186 verbatim
/-- The uniform distribution on the output alphabet `Fin 3`. -/
noncomputable def uniformOutput : ProbabilityMeasure (Fin 3) :=
  uniformTriple 0 1 2


-- @@ L188-207 verbatim
/-- The rational values of each channel row, matching `rowPMF` entrywise. -/
def rowCode : Fin 6 → Fin 3 → Rat
  | 0, 0 => 1 / 2
  | 0, 1 => 1 / 3
  | 0, _ => 1 / 6
  | 1, 0 => 1 / 2
  | 1, 1 => 1 / 6
  | 1, _ => 1 / 3
  | 2, 0 => 1 / 3
  | 2, 1 => 1 / 2
  | 2, _ => 1 / 6
  | 3, 0 => 1 / 6
  | 3, 1 => 1 / 2
  | 3, _ => 1 / 3
  | 4, 0 => 1 / 3
  | 4, 1 => 1 / 6
  | 4, _ => 1 / 2
  | _, 0 => 1 / 6
  | _, 1 => 1 / 3
  | _, _ => 1 / 2


-- @@ L209-216 verbatim
lemma rowCode_injective : Function.Injective rowCode := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | (exfalso; simp [rowCode] at h0 h1)


-- @@ L218-223 verbatim
/-- The rational weight vector of `prior₁`: mass `1/3` on each of `0, 3, 4`. -/
def prior₁Code : Fin 6 → Rat
  | 0 => 1 / 3
  | 3 => 1 / 3
  | 4 => 1 / 3
  | _ => 0


-- @@ L225-230 verbatim
/-- The rational weight vector of `prior₂`: mass `1/3` on each of `1, 2, 5`. -/
def prior₂Code : Fin 6 → Rat
  | 1 => 1 / 3
  | 2 => 1 / 3
  | 5 => 1 / 3
  | _ => 0


-- @@ L232-234 verbatim
/-- The output weight vector obtained by pushing an input weight vector `w` through `rowCode`. -/
def outputCode (w : Fin 6 → Rat) : Fin 3 → Rat :=
  fun y => ∑ x, w x * rowCode x y


-- @@ L236-247 verbatim
lemma priorCode_counterexample :
    prior₁Code ≠ prior₂Code ∧ outputCode prior₁Code = outputCode prior₂Code := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    revert h0
    simp only [prior₁Code, prior₂Code]
    norm_num
  · funext y
    fin_cases y
    all_goals simp [outputCode, Fin.sum_univ_six, prior₁Code, prior₂Code, rowCode]
    all_goals norm_num


-- @@ L249-253 verbatim
lemma prior_ne : prior₁ ≠ prior₂ := by
  intro h
  have h0 := congrArg (fun p : ProbabilityMeasure (Fin 6) => p.toMeasure {0}) h
  simp [prior₁, prior₂, uniformTriple, ProbabilityMeasure.convexCombination_toMeasure,
    Measure.add_apply, Measure.smul_apply] at h0


-- @@ L255-279 verbatim
lemma pushforward_prior₁ :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₁ = uniformOutput := by
  change ChannelCapacity.Kernel.priorPushforward permutationKernel (uniformTriple 0 3 4) =
    uniformOutput
  rw [uniformTriple, ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    priorPushforward_diracProba]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro y
  have hs : MeasurableSet ({y} : Set (Fin 3)) := MeasurableSet.singleton y
  rw [uniformOutput, uniformTriple]
  repeat rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  fin_cases y
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case0
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case1
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case2


-- @@ L281-305 verbatim
lemma pushforward_prior₂ :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₂ = uniformOutput := by
  change ChannelCapacity.Kernel.priorPushforward permutationKernel (uniformTriple 1 2 5) =
    uniformOutput
  rw [uniformTriple, ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    priorPushforward_diracProba]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro y
  have hs : MeasurableSet ({y} : Set (Fin 3)) := MeasurableSet.singleton y
  rw [uniformOutput, uniformTriple]
  repeat rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  fin_cases y
  · simp [rowPMF, add_comm]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case0
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₂_case1
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₂_case2


-- @@ L307-310 verbatim
theorem permutationKernel_not_injectivePriorPushforward :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel := by
  intro h
  exact prior_ne (h (pushforward_prior₁.trans pushforward_prior₂.symm))


-- @@ L312-319 verbatim
lemma rowPMF_injective : Function.Injective rowPMF := by
  intro i j hij
  have h0 := congrArg (fun p : PMF (Fin 3) => p 0) hij
  have h1 := congrArg (fun p : PMF (Fin 3) => p 1) hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; simp [rowPMF, PMF.ofFintype_apply] at h0 h1)


-- @@ L321-325 verbatim
example : ChannelCapacity.Kernel.RowSeparating permutationKernel := by
  intro i j hij hEq
  have hmeas : (rowPMF i).toMeasure = (rowPMF j).toMeasure := by
    simpa using hEq
  exact hij (rowPMF_injective (PMF.toMeasure_injective hmeas))


-- @@ L327-329 verbatim
example :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel :=
  permutationKernel_not_injectivePriorPushforward


-- @@ L331-334 verbatim
example :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₁ =
      ChannelCapacity.Kernel.priorPushforward permutationKernel prior₂ := by
  rw [pushforward_prior₁, pushforward_prior₂]


-- @@ L336-336 verbatim
namespace Toy


-- @@ L338-339 verbatim
/-- The identity kernel on `Fin 3`, used as a positive control with injective pushforward. -/
noncomputable def identityKernel : Kernel (Fin 3) (Fin 3) := Kernel.id


-- @@ L341-343 verbatim
noncomputable instance : IsMarkovKernel identityKernel := by
  dsimp [identityKernel]
  infer_instance


-- @@ L345-346 verbatim
example : ChannelCapacity.Kernel.InjectivePriorPushforward identityKernel :=
  ChannelCapacity.Kernel.id_injectivePriorPushforward


-- @@ L348-348 verbatim
end Toy


-- @@ L350-350 verbatim
end ChannelCapacity.Counterexample
