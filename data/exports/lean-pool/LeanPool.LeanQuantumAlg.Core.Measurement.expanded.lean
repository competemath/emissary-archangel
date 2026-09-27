/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Core.Gate
public import LeanPool.LeanQuantumAlg.Util.FinPow


-- @@ L12-25 verbatim
/-!
# Computational-basis measurement

Born rule for the computational-basis PVM `{|x><x|}` [dW19,
qcnotes.tex:406]: measuring a state vector `psi` yields outcome `x` with
probability `|psi x|^2`. For a `1 + n`-qubit register we also provide the
marginal probability of observing the first qubit, given by the projective
measurement `{|b><b| ⊗ I}` whose outcome probability is the squared norm of the
projected block [dW19, qcnotes.tex:433].

The raw `StateVector` definitions are available for algebraic intermediate
states. The `PureState` wrappers automatically form probability distributions,
because normalization is part of `PureState`.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
namespace QuantumAlg


-- @@ L31-31 verbatim
namespace StateVector


-- @@ L33-33 verbatim
section


-- @@ L35-35 verbatim
variable {n : ℕ}


-- @@ L37-40 verbatim
/-- Born rule [dW19, qcnotes.tex:406]: the probability of observing outcome `x`
when measuring `psi` in the computational basis. -/
noncomputable def probOutcome (psi : StateVector n) (x : Fin (2 ^ n)) : ℝ :=
  ‖psi x‖ ^ 2


-- @@ L42-44 verbatim
theorem probOutcome_nonneg (psi : StateVector n) (x : Fin (2 ^ n)) :
    0 ≤ probOutcome psi x :=
  sq_nonneg _


-- @@ L46-51 verbatim
/-- The Born-rule weights sum to the squared norm. -/
theorem sum_probOutcome (psi : StateVector n) :
    ∑ x, probOutcome psi x = ‖psi‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖psi i‖)]
  rfl


-- @@ L53-59 verbatim
@[simp]
theorem probOutcome_ket (x y : Fin (2 ^ n)) :
    probOutcome (PureState.ket x : StateVector n) y = if y = x then 1 else 0 := by
  rw [probOutcome, PureState.ket_apply]
  by_cases h : y = x
  · simp_all
  · simp_all


-- @@ L61-64 verbatim
/-- Probability that measuring qubit 0 of a `1 + n`-qubit raw state vector
yields `b`, leaving the other qubits unobserved. -/
noncomputable def probQubit0 (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) : ℝ :=
  ∑ y : Fin (2 ^ n), ‖psi (prodEquiv (b, y))‖ ^ 2


-- @@ L66-68 verbatim
theorem probQubit0_nonneg (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 psi b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _


-- @@ L70-76 verbatim
/-- Scaling a raw state vector scales the marginal probability by the squared
scalar norm. -/
theorem probQubit0_smul (c : ℂ) (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) :
    probQubit0 (c • psi) b = ‖c‖ ^ 2 * probQubit0 psi b := by
  rw [probQubit0, probQubit0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow]


-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
end StateVector


-- @@ L82-82 verbatim
namespace PureState


-- @@ L84-84 verbatim
noncomputable section


-- @@ L86-86 verbatim
variable {n : ℕ}


-- @@ L88-90 verbatim
/-- Born-rule probability for a pure state. -/
def probOutcome (psi : PureState n) (x : Fin (2 ^ n)) : ℝ :=
  StateVector.probOutcome (psi : StateVector n) x


-- @@ L92-94 verbatim
theorem probOutcome_nonneg (psi : PureState n) (x : Fin (2 ^ n)) :
    0 ≤ probOutcome psi x :=
  StateVector.probOutcome_nonneg (psi : StateVector n) x


-- @@ L96-100 verbatim
/-- Pure-state outcome probabilities form a probability distribution. -/
theorem sum_probOutcome (psi : PureState n) :
    ∑ x, probOutcome psi x = 1 := by
  change ∑ x, StateVector.probOutcome (psi : StateVector n) x = 1
  rw [StateVector.sum_probOutcome, psi.norm_eq_one, one_pow]


-- @@ L102-105 verbatim
/-- Compatibility name for the pure-state probability distribution theorem. -/
theorem sum_probOutcome_eq_one (psi : PureState n) :
    ∑ x, probOutcome psi x = 1 :=
  sum_probOutcome psi


-- @@ L107-110 verbatim
@[simp]
theorem probOutcome_ket (x y : Fin (2 ^ n)) :
    probOutcome (ket x) y = if y = x then 1 else 0 :=
  StateVector.probOutcome_ket x y


-- @@ L112-116 verbatim
/-- Expectation value `<psi|O|psi>` of an observable `O`, represented as a real
number via the real part. Hermiticity is a property of the observable, not part
of the raw `HilbertOperator` type. -/
def expVal (psi : PureState n) (O : HilbertOperator n) : ℝ :=
  (inner ℂ (psi : StateVector n) (HilbertOperator.applyVec O (psi : StateVector n))).re


-- @@ L118-121 verbatim
/-- Probability that measuring qubit 0 of a `1 + n`-qubit pure state yields
`b`, leaving the other qubits unobserved. -/
def probQubit0 (psi : PureState (1 + n)) (b : Fin (2 ^ 1)) : ℝ :=
  StateVector.probQubit0 (psi : StateVector (1 + n)) b


-- @@ L123-125 verbatim
theorem probQubit0_nonneg (psi : PureState (1 + n)) (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 psi b :=
  StateVector.probQubit0_nonneg (psi : StateVector (1 + n)) b


-- @@ L127-131 verbatim
/-- Compatibility name for raw-vector marginal scaling. -/
theorem probQubit0_smul (c : ℂ) (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) :
    StateVector.probQubit0 (c • psi) b
      = ‖c‖ ^ 2 * StateVector.probQubit0 psi b :=
  StateVector.probQubit0_smul c psi b


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end PureState


-- @@ L137-137 verbatim
end QuantumAlg
