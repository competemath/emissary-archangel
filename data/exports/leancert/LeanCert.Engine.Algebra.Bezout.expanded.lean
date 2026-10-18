/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.QPoly
import Mathlib.FieldTheory.Separable


-- @@ L9-19 verbatim
/-!
# Executable Bézout certificates for polynomial simplicity

An untrusted CAS supplies exact cofactors `A`, `B`, and a nonzero scalar `c`
such that `A * P + B * P' = c`. The executable checker compares trimmed
`QPoly` coefficient arrays. Its soundness theorem transports the equality to
Mathlib polynomials and proves separability.

Keeping an arbitrary nonzero scalar lets certificate generators clear
denominators and emit compact integer-valued coefficients.
-/


-- @@ L21-21 verbatim
namespace LeanCert.Engine


-- @@ L23-28 verbatim
/-- Untrusted cofactors for the identity `A * P + B * P' = c`. -/
structure BezoutCert where
  A : QPoly
  B : QPoly
  c : ℚ
  deriving DecidableEq, Repr, Inhabited


-- @@ L30-32 verbatim
/-- The executable left side of a Bézout derivative certificate. -/
def bezoutLhs (P : QPoly) (cert : BezoutCert) : QPoly :=
  (cert.A.mul P).add (cert.B.mul P.derivative)


-- @@ L34-37 verbatim
/-- Check a nonzero constant Bézout identity using exact rational arrays. -/
def bezoutCheck (P : QPoly) (cert : BezoutCert) : Bool :=
  decide (cert.c ≠ 0) &&
    decide ((bezoutLhs P cert).trim = (QPoly.constant cert.c).trim)


-- @@ L39-48 verbatim
/-- A successful executable check implies the corresponding Mathlib
polynomial identity. -/
theorem bezoutCheck_identity (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    cert.A.toPoly * P.toPoly + cert.B.toPoly * P.toPoly.derivative =
      Polynomial.C cert.c := by
  simp only [bezoutCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hpoly := congrArg QPoly.toPoly h.2
  simpa only [QPoly.toPoly_trim, bezoutLhs, QPoly.toPoly_add, QPoly.toPoly_mul,
    QPoly.toPoly_derivative, QPoly.toPoly_constant] using hpoly


-- @@ L50-64 verbatim
/-- Golden theorem: a successful Bézout derivative check certifies that the
semantic polynomial is separable. -/
theorem bezoutCheck_sound (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) : P.toPoly.Separable := by
  have hid := bezoutCheck_identity P cert h
  simp only [bezoutCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Polynomial.separable_def']
  refine ⟨Polynomial.C cert.c⁻¹ * cert.A.toPoly,
    Polynomial.C cert.c⁻¹ * cert.B.toPoly, ?_⟩
  calc
    _ = Polynomial.C cert.c⁻¹ *
        (cert.A.toPoly * P.toPoly + cert.B.toPoly * P.toPoly.derivative) := by ring
    _ = Polynomial.C cert.c⁻¹ * Polynomial.C cert.c := by
      rw [hid]
    _ = 1 := by simp [← map_mul, h.1]


-- @@ L66-66 verbatim
end LeanCert.Engine
