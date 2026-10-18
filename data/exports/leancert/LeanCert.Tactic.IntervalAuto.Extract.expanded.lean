/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Meta.Numeral


-- @@ L10-15 verbatim
/-!
# Rational Extraction Utilities

Utilities for extracting rational numbers from Lean expressions representing
real number literals or coercions.
-/


-- @@ L17-17 verbatim
open Lean Meta


-- @@ L19-19 verbatim
namespace LeanCert.Tactic.Auto


-- @@ L21-21 verbatim
open LeanCert.Core


-- @@ L23-25 verbatim
/-- Try to extract a rational value from a normalized real-number expression. -/
def extractRatFromReal (e : Lean.Expr) : MetaM (Option ℚ) := do
  LeanCert.Meta.Numeral.toRealRatNormalized? e


-- @@ L27-38 verbatim
/-- Build an IntervalRat expression from two rational expressions and their Lean representations -/
def mkIntervalRat (loExpr hiExpr : Lean.Expr) (lo hi : ℚ) : MetaM Lean.Expr := do
  if lo > hi then
    throwError "Cannot create interval: lo ({lo}) > hi ({hi})"
  -- Build ⟨lo, hi, proof⟩
  -- The proof is `lo ≤ hi` which we can close with `by norm_num` or `by decide`
  let proofType ← mkAppM ``LE.le #[loExpr, hiExpr]

  -- Create the proof using decide (works for concrete rationals)
  let proof ← mkDecideProof proofType

  mkAppM ``IntervalRat.mk #[loExpr, hiExpr, proof]


-- @@ L40-42 verbatim
/-- Try to convert an expression directly to a rational (if it IS a rational constant) -/
def toRat? (e : Lean.Expr) : MetaM (Option ℚ) :=
  LeanCert.Meta.Numeral.toRat? e


-- @@ L44-44 verbatim
end LeanCert.Tactic.Auto
