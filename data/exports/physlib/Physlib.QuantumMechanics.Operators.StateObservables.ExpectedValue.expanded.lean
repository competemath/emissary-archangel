/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded

-- @@ L9-28 verbatim
/-!
# Expectation values and centered vectors

For a partial linear map `T` on a complex inner product space and `ψ ∈ T.domain`, this file
defines the expectation value and the centered vector `Tψ - ⟨T⟩_ψ ψ`.

## Main definitions

- `LinearPMap.expectedValue`: the real part of `⟪ψ, Tψ⟫_ℂ`.
- `LinearPMap.centered`: the centered vector `Tψ - ⟨T⟩ψ`.

## Main statements

- `LinearPMap.expectedValue_eq_inner`: for symmetric `T`, the complex inner product is real and
  equals the real expectation value coerced to `ℂ`.

## References

* B. C. Hall, Quantum Theory for Mathematicians, Chapter 12. [ref: hall2013quantum]
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace LinearPMap


-- @@ L34-34 verbatim
open InnerProductSpace


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


-- @@ L40-43 verbatim
private lemma conj_inner_apply_self_eq_of_isSymmetric (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : T.domain) :
    (starRingEnd ℂ) ⟪(ψ : H), T ψ⟫_ℂ = ⟪(ψ : H), T ψ⟫_ℂ := by
  simpa [inner_conj_symm] using hT ψ ψ


-- @@ L45-50 verbatim
/-- Expectation value `re ⟪ψ, Tψ⟫_ℂ` for `ψ ∈ T.domain`.

For symmetric `T`, this agrees with `⟪ψ, Tψ⟫_ℂ` after coercion from `ℝ`;
see `expectedValue_eq_inner`. -/
def expectedValue (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  (⟪(ψ : H), T ψ⟫_ℂ).re


-- @@ L52-55 verbatim
/-- The expectation value, unfolded as a real part. -/
lemma expectedValue_eq_re_inner (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    expectedValue T ψ = (⟪(ψ : H), T ψ⟫_ℂ).re :=
  rfl


-- @@ L57-63 verbatim
/-- If `T` is symmetric, `⟪ψ, Tψ⟫_ℂ` is the expectation value, coerced to `ℂ`. -/
lemma expectedValue_eq_inner (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric) (ψ : T.domain) :
    ⟪(ψ : H), T ψ⟫_ℂ = (expectedValue T ψ : ℂ) := by
  have h_re : ((⟪(ψ : H), T ψ⟫_ℂ).re : ℂ) = ⟪(ψ : H), T ψ⟫_ℂ :=
    Complex.conj_eq_iff_re.mp
      (by simpa using conj_inner_apply_self_eq_of_isSymmetric T hT ψ)
  simpa [expectedValue] using h_re.symm


-- @@ L65-68 verbatim
/-- Reverse orientation of `LinearPMap.expectedValue_eq_inner`. -/
lemma inner_eq_expectedValue (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric) (ψ : T.domain) :
    (expectedValue T ψ : ℂ) = ⟪(ψ : H), T ψ⟫_ℂ :=
  (expectedValue_eq_inner T hT ψ).symm


-- @@ L70-72 verbatim
/-- The centered vector `Tψ - ⟨T⟩_ψ ψ`. -/
def centered (T : H →ₗ.[ℂ] H) (ψ : T.domain) : H :=
  T ψ - (expectedValue T ψ : ℂ) • (ψ : H)


-- @@ L74-77 verbatim
/-- The centered vector, unfolded to its raw expression. -/
lemma centered_eq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    centered T ψ = T ψ - (expectedValue T ψ : ℂ) • (ψ : H) :=
  rfl


-- @@ L79-82 verbatim
/-- A centered vector vanishes exactly when `Tψ = ⟨T⟩_ψ ψ`. -/
lemma centered_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    centered T ψ = 0 ↔ T ψ = (expectedValue T ψ : ℂ) • (ψ : H) := by
  rw [centered_eq, sub_eq_zero]


-- @@ L84-89 verbatim
/-- For a unit vector and symmetric `T`, the centered vector is orthogonal to the state. -/
lemma inner_state_centered_eq_zero (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    ⟪(ψ : H), centered T ψ⟫_ℂ = 0 := by
  rw [centered_eq, inner_sub_right, inner_smul_right, expectedValue_eq_inner T hT ψ]
  simp [hψ_norm, inner_self_eq_norm_sq_to_K]


-- @@ L91-100 verbatim
/-- The conjugate orientation of `LinearPMap.inner_state_centered_eq_zero`. -/
lemma inner_centered_state_eq_zero (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    ⟪centered T ψ, (ψ : H)⟫_ℂ = 0 := by
  rw [centered_eq, inner_sub_left, inner_smul_left]
  have hμ := expectedValue_eq_inner T hT ψ
  have hμ' : ⟪T ψ, (ψ : H)⟫_ℂ = (expectedValue T ψ : ℂ) := by
    simpa [inner_conj_symm] using congrArg star hμ
  rw [hμ']
  simp [hψ_norm, inner_self_eq_norm_sq_to_K]


-- @@ L102-102 verbatim
end

-- @@ L103-103 verbatim
end LinearPMap
