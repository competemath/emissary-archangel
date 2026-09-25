module

public import APAP.Prereqs.FourierTransform.Discrete

import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L7-9 verbatim
/-!
# Large spectrum of a function
-/


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
open Finset Fintype

-- @@ L14-14 verbatim
open scoped ComplexConjugate NNReal


-- @@ L16-17 verbatim
variable {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] {f : G → ℂ} {η : ℝ}
  {ψ : AddChar G ℂ} {Δ : Finset (AddChar G ℂ)} {m : ℕ}


-- @@ L19-21 expanded
/-- The `η`-large spectrum of a function. -/
noncomputable def largeSpec (f : G → ℂ) (η : ℝ) : Finset (AddChar G ℂ) :=
  {ψ | η * dLpNorm 1 f ≤ ‖dft f ψ‖}


-- @@ L23-23 expanded
@[simp]
lemma mem_largeSpec : ψ ∈ largeSpec f η ↔ η * dLpNorm 1 f ≤ ‖dft f ψ‖ := by simp [largeSpec]


-- @@ L25-26 verbatim
lemma largeSpec_anti (f : G → ℂ) : Antitone (largeSpec f) := fun η ν h ψ ↦ by
  simp_rw [mem_largeSpec]; exact (mul_le_mul_of_nonneg_right h (by positivity)).trans


-- @@ L28-28 verbatim
@[simp] lemma largeSpec_zero_left (η : ℝ) : largeSpec (0 : G → ℂ) η = univ := by simp [largeSpec]

-- @@ L29-29 verbatim
@[simp] lemma largeSpec_zero_right (f : G → ℂ) : largeSpec f 0 = univ := by simp [largeSpec]
