/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.Basic


-- @@ L10-14 verbatim
/-!

## Properties of light like vectors

-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
noncomputable section

-- @@ L19-19 verbatim
namespace Lorentz

-- @@ L20-20 verbatim
open realLorentzTensor

-- @@ L21-21 verbatim
open InnerProductSpace


-- @@ L23-23 verbatim
namespace Vector


-- @@ L25-30 verbatim
lemma lightLike_iff_norm_sq_zero {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.lightLike ↔ ⟪p, p⟫ₘ = 0 := by
  simp only [causalCharacter]
  split_ifs with h h2 <;> simp_all

  -- Zero vector has zero Minkowski norm squared

-- @@ L31-34 verbatim
@[simp]
lemma causalCharacter_zero {d : ℕ} : causalCharacter (0 : Vector d) =
    CausalCharacter.lightLike := by
  simp [causalCharacter]


-- @@ L36-39 verbatim
/-- Causally preceding is reflexive -/
@[simp]
lemma causallyPrecedes_refl {d : ℕ} (p : Vector d) : causallyPrecedes p p := by
  simp [causallyPrecedes, pastLightConeBoundary]


-- @@ L41-50 verbatim
/-- For two lightlike vectors with equal time components, their spatial parts
    have equal Euclidean norms -/
lemma lightlike_eq_spatial_norm_of_eq_time {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_time : timeComponent v = timeComponent w) :
    ⟪spatialPart v, spatialPart v⟫_ℝ = ⟪spatialPart w, spatialPart w⟫_ℝ := by
  rw [lightLike_iff_norm_sq_zero, minkowskiProduct_toCoord] at hv hw
  rw [show v (Sum.inl 0) = w (Sum.inl 0) from h_time] at hv
  simp only [PiLp.inner_apply, spatialPart, RCLike.inner_apply, conj_trivial]
  linarith


-- @@ L52-65 verbatim
set_option linter.unusedVariables false in
/-- If two lightlike vectors have parallel spatial components, their temporal components
must also be proportional, which implies the entire vectors are proportional -/
-- `unusedArguments` (newly flagged under v4.32.0): the lightlike hypotheses are
-- part of the intended interface but not needed by the current proof.
@[nolint unusedArguments]
lemma lightlike_spatial_parallel_implies_proportional {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_spatial_parallel : ∃ (r : ℝ), v = r • w) :
    ∃ (r : ℝ), |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [hr]
  simp [abs_mul]


-- @@ L67-67 verbatim
end Vector


-- @@ L69-69 verbatim
end Lorentz
