/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.FlavorPhysics.CKMMatrix.Basic
public import Mathlib.Analysis.Complex.Basic

-- @@ L10-20 verbatim
/-!
# Invariants of the CKM Matrix

The CKM matrix is only defined up to an equivalence.

This file defines some invariants of the CKM matrix, which are well-defined with respect to
this equivalence.

Of note, this file defines the complex jarlskog invariant.

-/


-- @@ L22-22 verbatim
@[expose] public section

-- @@ L23-23 verbatim
open Matrix Complex

-- @@ L24-24 verbatim
open ComplexConjugate

-- @@ L25-25 verbatim
open CKMMatrix


-- @@ L27-27 verbatim
noncomputable section

-- @@ L28-28 verbatim
namespace Invariant


-- @@ L30-32 expanded
/-- The complex jarlskog invariant for a CKM matrix. -/
def jarlskogℂCKM (V : CKMMatrix) : ℂ :=
  V.1 0 1 * V.1 1 2 * conj (V.1 0 2) * conj (V.1 1 1)


-- @@ L34-42 verbatim
/-- The complex jarlskog invariant is equal for equivalent CKM matrices. -/
lemma jarlskogℂCKM_equiv (V U : CKMMatrix) (h : V ≈ U) :
    jarlskogℂCKM V = jarlskogℂCKM U := by
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  change V = phaseShiftApply U a b c e f g at h
  rw [h]
  simp only [jarlskogℂCKM, phaseShiftApply.ub, phaseShiftApply.us, phaseShiftApply.cb,
    phaseShiftApply.cs, exp_add, _root_.map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg, exp_neg]
  field_simp [Complex.exp_ne_zero]


-- @@ L44-47 verbatim
/-- The complex jarlskog invariant for an equivalence class of CKM matrices. -/
@[simp]
def jarlskogℂ : Quotient CKMMatrixSetoid → ℂ :=
  Quotient.lift jarlskogℂCKM jarlskogℂCKM_equiv


-- @@ L49-53 verbatim
/-- An invariant for CKM matrices corresponding to the square of the absolute values
  of the `us`, `ub` and `cb` elements multiplied together divided by `(VudAbs V ^ 2 + VusAbs V ^2)`.
-/
def VusVubVcdSq (V : Quotient CKMMatrixSetoid) : ℝ :=
    VusAbs V ^ 2 * VubAbs V ^ 2 * VcbAbs V ^2 / (VudAbs V ^ 2 + VusAbs V ^2)


-- @@ L55-58 verbatim
/-- An invariant for CKM matrices. The argument of this invariant is `δ₁₃` in the
standard parameterization. -/
def mulExpδ₁₃ (V : Quotient CKMMatrixSetoid) : ℂ :=
  jarlskogℂ V + VusVubVcdSq V


-- @@ L60-60 verbatim
end Invariant

-- @@ L61-61 verbatim
end
