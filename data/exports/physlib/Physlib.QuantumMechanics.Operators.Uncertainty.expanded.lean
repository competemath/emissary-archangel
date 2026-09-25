/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.QuantumMechanics.Operators.Covariance

-- @@ L9-51 verbatim
/-!

# Uncertainty bounds for partial linear maps

## i. Overview

In this module we prove abstract Robertson and Robertson–Schrödinger uncertainty bounds for
symmetric partial linear maps on a complex inner product space. The statements are independent of
any concrete position or momentum operator.

The centered-commutator results use only the domain assumptions needed to form the centered
vectors. The raw-commutator results add the second-order domain hypotheses required to apply `A`
to `Bψ` and `B` to `Aψ`.

## ii. Key results

- `inner_im_of_commutator_eq` : an anti-Hermitian commutator identity fixes the imaginary part of
  an inner product.
- `centeredCommutatorExpectation` : the scalar commutator of the centered vectors.
- `rawCommutatorExpectation` : the expectation of the raw commutator on a state.
- `inner_centered_commutator_of_raw_commutator` : a raw commutator expectation gives the centered
  commutator expectation.
- `state_uncertainty_squared_of_centered_commutator` : the Robertson squared bound from a centered
  commutator identity.
- `state_uncertainty_squared_with_covariance_of_centered_commutator` : the strengthened
  Robertson–Schrödinger bound.
- `state_uncertainty_of_centered_commutator` : the standard-deviation form of the bound.
- `state_uncertainty_squared_of_raw_commutator`,
  `state_uncertainty_squared_with_covariance_of_raw_commutator`, and
  `state_uncertainty_of_raw_commutator` : variants using a raw commutator expectation.

## iii. Table of contents

- A. Inner product lemmas
- B. Centered commutator bounds
- C. Raw commutator bounds

## iv. References

* H. P. Robertson, The Uncertainty Principle (1929). [ref: robertson1929uncertainty]
* E. Schrodinger, Zum Heisenbergschen Unscharfeprinzip (1930). [ref: schrodinger1930heisenberg]
* B. C. Hall, Quantum Theory for Mathematicians, Chapter 12. [ref: hall2013quantum]
-/


-- @@ L53-53 verbatim
@[expose] public section


-- @@ L55-55 verbatim
namespace LinearPMap


-- @@ L57-57 verbatim
open InnerProductSpace


-- @@ L59-59 verbatim
noncomputable section


-- @@ L61-61 verbatim
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


-- @@ L63-67 verbatim
/-!

## A. Inner product lemmas

-/


-- @@ L69-78 verbatim
lemma inner_im_of_commutator_eq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    (⟪u, v⟫_ℂ).im = c / 2 := by
  have h_conj_im : (⟪v, u⟫_ℂ).im = -(⟪u, v⟫_ℂ).im := by
    rw [(inner_conj_symm (𝕜 := ℂ) v u).symm, Complex.conj_im]
  have h_im := congrArg Complex.im h_comm
  rw [Complex.sub_im] at h_im
  simp at h_im
  rw [h_conj_im] at h_im
  linarith


-- @@ L80-84 verbatim
lemma inner_norm_sq_eq_re_sq_add_commutator_half_sq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 = (⟪u, v⟫_ℂ).re ^ 2 + (c / 2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, inner_im_of_commutator_eq h_comm]
  ring


-- @@ L86-107 verbatim
lemma sub_expectation_commutator_eq_raw
    (ψ a b : H) (μa μb : ℝ)
    (hμa_right : ⟪ψ, a⟫_ℂ = (μa : ℂ)) (hμa_left : ⟪a, ψ⟫_ℂ = (μa : ℂ))
    (hμb_right : ⟪ψ, b⟫_ℂ = (μb : ℂ)) (hμb_left : ⟪b, ψ⟫_ℂ = (μb : ℂ)) (hψ_norm : ‖ψ‖ = 1) :
    ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ =
      ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
  calc
    ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ =
          (⟪a, b⟫_ℂ - (μb : ℂ) * ⟪a, ψ⟫_ℂ - star (μa : ℂ) * ⟪ψ, b⟫_ℂ +
            star (μa : ℂ) * (μb : ℂ) * ⟪ψ, ψ⟫_ℂ) -
          (⟪b, a⟫_ℂ - (μa : ℂ) * ⟪b, ψ⟫_ℂ - star (μb : ℂ) * ⟪ψ, a⟫_ℂ +
            star (μb : ℂ) * (μa : ℂ) * ⟪ψ, ψ⟫_ℂ) := by
              simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
              simp [mul_comm, mul_assoc]
              ring_nf
    _ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
          rw [hμa_right, hμa_left, hμb_right, hμb_left, inner_self_eq_norm_sq_to_K,
            hψ_norm]
          simp only [Complex.star_def, Complex.conj_ofReal, pow_two, mul_assoc, mul_comm]
          ring_nf


-- @@ L109-129 verbatim
lemma raw_commutator_eq_of_symmetric
    (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : A.domain) (hψB : (ψ : H) ∈ B.domain)
    (hBA : A ψ ∈ B.domain) (hAB : B ⟨ψ, hψB⟩ ∈ A.domain)
    {c : ℝ}
    (h_raw : ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ψ, hBA⟩⟫_ℂ = Complex.I * c) :
    ⟪A ψ, B ⟨ψ, hψB⟩⟫_ℂ - ⟪B ⟨ψ, hψB⟩, A ψ⟫_ℂ = Complex.I * c := by
  have ha_pairing :
      ⟪A ψ, B ⟨ψ, hψB⟩⟫_ℂ = ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩⟫_ℂ := by
    exact hA ψ ⟨B ⟨ψ, hψB⟩, hAB⟩
  have hb_pairing :
      ⟪B ⟨ψ, hψB⟩, A ψ⟫_ℂ = ⟪(ψ : H), B ⟨A ψ, hBA⟩⟫_ℂ := by
    exact hB ⟨ψ, hψB⟩ ⟨A ψ, hBA⟩
  calc
    ⟪A ψ, B ⟨ψ, hψB⟩⟫_ℂ - ⟪B ⟨ψ, hψB⟩, A ψ⟫_ℂ =
      ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩⟫_ℂ -
        ⟪(ψ : H), B ⟨A ψ, hBA⟩⟫_ℂ := by
          rw [ha_pairing, hb_pairing]
    _ = ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ψ, hBA⟩⟫_ℂ := by
          rw [inner_sub_right]
    _ = Complex.I * c := h_raw


-- @@ L131-135 verbatim
/-- The scalar commutator of the centered vectors of `A` and `B` in the state `ψ`. -/
def centeredCommutatorExpectation (A B : H →ₗ.[ℂ] H)
    (ψ : A.domain) (hψB : (ψ : H) ∈ B.domain) : ℂ :=
  ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ -
    ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ


-- @@ L137-142 verbatim
/-- The expectation of the raw commutator `[A, B]` in the state `ψ`, with explicit second-order
domain witnesses. -/
def rawCommutatorExpectation (A B : H →ₗ.[ℂ] H)
    (ψ : A.domain) (hψB : (ψ : H) ∈ B.domain)
    (hBA : A ψ ∈ B.domain) (hAB : B ⟨ψ, hψB⟩ ∈ A.domain) : ℂ :=
  ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ψ, hBA⟩⟫_ℂ


-- @@ L144-155 verbatim
lemma commutator_half_sq_le_mul_norm_sq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    (|c| / 2) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
  suffices (|c| / 2) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 by exact this
  have h_sq : |c / 2| ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    have h_bound : |c / 2| ≤ ‖u‖ * ‖v‖ := by
      have h_im : |(⟪u, v⟫_ℂ).im| ≤ ‖u‖ * ‖v‖ :=
        le_trans (Complex.abs_im_le_norm ⟪u, v⟫_ℂ) (norm_inner_le_norm u v)
      rwa [inner_im_of_commutator_eq h_comm] at h_im
    have h_nonneg : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg u) (norm_nonneg v)
    nlinarith [abs_nonneg (c / 2), h_bound, h_nonneg]
  simpa [abs_div] using h_sq


-- @@ L157-163 verbatim
private lemma sqrt_mul_le_of_sq_le {x y z : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hxy : z ^ 2 ≤ x * y) :
    z ≤ Real.sqrt x * Real.sqrt y := by
  suffices z ≤ Real.sqrt x * Real.sqrt y by exact this
  have hs : Real.sqrt (z ^ 2) ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt hxy
  rw [Real.sqrt_sq hz, Real.sqrt_mul hx] at hs
  simpa [mul_comm] using hs


-- @@ L165-169 verbatim
/-!

## B. Centered commutator bounds

-/


-- @@ L171-171 verbatim
section CenteredBounds


-- @@ L173-173 verbatim
variable (A B : H →ₗ.[ℂ] H)

-- @@ L174-174 verbatim
variable (ψ : A.domain)

-- @@ L175-175 verbatim
variable (hψB : (ψ : H) ∈ B.domain)

-- @@ L176-176 verbatim
variable {c : ℝ}

-- @@ L177-177 verbatim
variable (h_centered : centeredCommutatorExpectation A B ψ hψB = Complex.I * c)


-- @@ L179-179 verbatim
include h_centered


-- @@ L181-188 verbatim
/-- A centered commutator identity implies the squared Robertson uncertainty bound. -/
lemma state_uncertainty_squared_of_centered_commutator :
    (|c| / 2) ^ 2 ≤ variance A ψ * variance B ⟨ψ, hψB⟩ := by
  rw [variance_eq_centered_norm_sq, variance_eq_centered_norm_sq]
  rw [show ‖centered A ψ‖ ^ 2 * ‖centered B ⟨ψ, hψB⟩‖ ^ 2 =
    (‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖) ^ 2 by ring]
  exact commutator_half_sq_le_mul_norm_sq (by simpa [centeredCommutatorExpectation] using
    h_centered)


-- @@ L190-210 verbatim
/-- A centered commutator identity implies the Robertson–Schrödinger uncertainty bound. -/
lemma state_uncertainty_squared_with_covariance_of_centered_commutator :
    (covariance A B ψ hψB) ^ 2 + (c / 2) ^ 2 ≤
      variance A ψ * variance B ⟨ψ, hψB⟩ := by
  rw [variance_eq_centered_norm_sq, variance_eq_centered_norm_sq]
  rw [show ‖centered A ψ‖ ^ 2 * ‖centered B ⟨ψ, hψB⟩‖ ^ 2 =
    (‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖) ^ 2 by ring]
  calc
    (covariance A B ψ hψB) ^ 2 + (c / 2) ^ 2 =
        ‖⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ‖ ^ 2 := by
          rw [inner_norm_sq_eq_re_sq_add_commutator_half_sq
            (by simpa [centeredCommutatorExpectation] using h_centered)]
          rfl
    _ ≤ (‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖) ^ 2 := by
        have h_bound :=
          norm_inner_le_norm (𝕜 := ℂ) (centered A ψ) (centered B ⟨ψ, hψB⟩)
        have h_inner_nonneg : 0 ≤ ‖⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ‖ :=
          norm_nonneg _
        have h_mul_nonneg : 0 ≤ ‖centered A ψ‖ * ‖centered B ⟨ψ, hψB⟩‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith


-- @@ L212-217 verbatim
/-- A centered commutator identity implies the standard uncertainty bound. -/
lemma state_uncertainty_of_centered_commutator :
    |c| / 2 ≤ standardDeviation A ψ * standardDeviation B ⟨ψ, hψB⟩ := by
  have h_sq := state_uncertainty_squared_of_centered_commutator A B ψ hψB h_centered
  refine sqrt_mul_le_of_sq_le (variance_nonneg A ψ) (by positivity) ?_
  simpa [standardDeviation] using h_sq


-- @@ L219-219 verbatim
end CenteredBounds


-- @@ L221-225 verbatim
/-!

## C. Raw commutator bounds

-/


-- @@ L227-227 verbatim
section RawBounds


-- @@ L229-229 verbatim
variable (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)

-- @@ L230-230 verbatim
variable (ψ : A.domain)

-- @@ L231-231 verbatim
variable (hψB : (ψ : H) ∈ B.domain)

-- @@ L232-232 verbatim
variable (hψ_norm : ‖(ψ : H)‖ = 1)

-- @@ L233-233 verbatim
variable (hBA : A ψ ∈ B.domain)

-- @@ L234-234 verbatim
variable (hAB : B ⟨ψ, hψB⟩ ∈ A.domain)

-- @@ L235-235 verbatim
variable {c : ℝ}

-- @@ L236-236 verbatim
variable (h_raw : rawCommutatorExpectation A B ψ hψB hBA hAB = Complex.I * c)


-- @@ L238-238 verbatim
include hA hB hψ_norm hBA hAB h_raw


-- @@ L240-273 verbatim
/-- A raw commutator expectation determines the centered commutator expectation. -/
lemma inner_centered_commutator_of_raw_commutator :
    centeredCommutatorExpectation A B ψ hψB = Complex.I * c := by
  let a : H := A ψ
  let b : H := B ⟨ψ, hψB⟩
  let μa : ℝ := expectedValue A ψ
  let μb : ℝ := expectedValue B ⟨ψ, hψB⟩
  have hμa_right : ⟪(ψ : H), a⟫_ℂ = (μa : ℂ) := by
    simpa [a, μa] using expectedValue_eq_inner A hA ψ
  have hμa_left : ⟪a, (ψ : H)⟫_ℂ = (μa : ℂ) := by
    have h_symm : ⟪a, (ψ : H)⟫_ℂ = ⟪(ψ : H), a⟫_ℂ := by
      simpa [a] using hA ψ ψ
    simpa [h_symm] using hμa_right
  have hμb_right : ⟪(ψ : H), b⟫_ℂ = (μb : ℂ) := by
    simpa [b, μb] using expectedValue_eq_inner B hB ⟨ψ, hψB⟩
  have hμb_left : ⟪b, (ψ : H)⟫_ℂ = (μb : ℂ) := by
    have h_symm : ⟪b, (ψ : H)⟫_ℂ = ⟪(ψ : H), b⟫_ℂ := by
      simpa [b] using hB ⟨ψ, hψB⟩ ⟨ψ, hψB⟩
    simpa [h_symm] using hμb_right
  calc
    centeredCommutatorExpectation A B ψ hψB =
      ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ -
        ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ := by
          rfl
    _ =
      ⟪a - (μa : ℂ) • (ψ : H), b - (μb : ℂ) • (ψ : H)⟫_ℂ -
        ⟪b - (μb : ℂ) • (ψ : H), a - (μa : ℂ) • (ψ : H)⟫_ℂ := by
          rfl
    _ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ :=
      sub_expectation_commutator_eq_raw (ψ : H) a b μa μb
        hμa_right hμa_left hμb_right hμb_left hψ_norm
    _ = Complex.I * c :=
      raw_commutator_eq_of_symmetric A B hA hB ψ hψB hBA hAB
        (by simpa [rawCommutatorExpectation] using h_raw)


-- @@ L275-279 verbatim
/-- A raw commutator expectation implies the squared Robertson uncertainty bound. -/
lemma state_uncertainty_squared_of_raw_commutator :
    (|c| / 2) ^ 2 ≤ variance A ψ * variance B ⟨ψ, hψB⟩ :=
  state_uncertainty_squared_of_centered_commutator A B ψ hψB
    (inner_centered_commutator_of_raw_commutator A B hA hB ψ hψB hψ_norm hBA hAB h_raw)


-- @@ L281-286 verbatim
/-- A raw commutator expectation implies the squared uncertainty bound with covariance term. -/
lemma state_uncertainty_squared_with_covariance_of_raw_commutator :
    (covariance A B ψ hψB) ^ 2 + (c / 2) ^ 2 ≤
      variance A ψ * variance B ⟨ψ, hψB⟩ :=
  state_uncertainty_squared_with_covariance_of_centered_commutator A B ψ hψB
    (inner_centered_commutator_of_raw_commutator A B hA hB ψ hψB hψ_norm hBA hAB h_raw)


-- @@ L288-292 verbatim
/-- A raw commutator expectation implies the standard uncertainty bound. -/
lemma state_uncertainty_of_raw_commutator :
    |c| / 2 ≤ standardDeviation A ψ * standardDeviation B ⟨ψ, hψB⟩ :=
  state_uncertainty_of_centered_commutator A B ψ hψB
    (inner_centered_commutator_of_raw_commutator A B hA hB ψ hψB hψ_norm hBA hAB h_raw)


-- @@ L294-294 verbatim
end RawBounds


-- @@ L296-296 verbatim
end

-- @@ L297-297 verbatim
end LinearPMap
