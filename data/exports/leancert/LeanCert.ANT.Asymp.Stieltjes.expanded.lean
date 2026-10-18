/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp.Env
import Mathlib.Algebra.BigOperators.Module


-- @@ L9-15 verbatim
/-!
# Stieltjes-Abel envelope kernel

This file contains the exact finite summation-by-parts kernel used by the
Stieltjes side of CAEE.  The analytic checker layer should target the semantic
certificate wrapper at the bottom of the file.
-/


-- @@ L17-17 verbatim
namespace LeanCert.ANT.Asymp


-- @@ L19-19 verbatim
open scoped BigOperators

-- @@ L20-20 verbatim
open LeanCert.Core


-- @@ L22-25 verbatim
/-- Weighted sum over a half-open interval `[m, n)`. -/
noncomputable def weightedIntervalSumReal
    (a w : Nat → ℝ) (m n : Nat) : ℝ :=
  ∑ i ∈ Finset.Ico m n, w i * a i


-- @@ L27-30 verbatim
/-- Weighted prefix sum over `i ≤ N`. -/
noncomputable def weightedPrefixSumReal
    (a w : Nat → ℝ) (N : Nat) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), w i * a i


-- @@ L32-34 verbatim
/-- The discrete weight `1 / n`, with Lean's harmless convention `0⁻¹ = 0`. -/
noncomputable def oneOverNWeight (n : Nat) : ℝ :=
  ((n : ℝ)⁻¹)


-- @@ L36-38 verbatim
/-- AST representation of the Stieltjes weight `1 / x`. -/
def oneOverNExpr : Expr :=
  Expr.inv (Expr.var 0)


-- @@ L40-46 verbatim
/-- Abel transform over an arbitrary real prefix function. -/
noncomputable def abelTransformOfPrefixReal
    (w : Nat → ℝ) (A : Nat → ℝ) (m n : Nat) : ℝ :=
  w (n - 1) * A n -
    w m * A m -
      ∑ i ∈ Finset.Ico m (n - 1),
        (w (i + 1) - w i) * A (i + 1)


-- @@ L48-53 verbatim
/-- Weighted prefixes are ordinary prefixes of the pointwise weighted sequence. -/
theorem weightedPrefixSumReal_eq_prefixSum
    (a w : Nat → ℝ) (N : Nat) :
    weightedPrefixSumReal a w N =
      prefixSum (fun n => w n * a n) (N + 1) := by
  rfl


-- @@ L55-62 verbatim
/-- Abel's finite summation-by-parts identity for real weights. -/
theorem weightedIntervalSumReal_eq_abelTransformOfPrefixReal
    {a w : Nat → ℝ} {m n : Nat} (hmn : m < n) :
    weightedIntervalSumReal a w m n =
      abelTransformOfPrefixReal w (prefixSum a) m n := by
  unfold weightedIntervalSumReal abelTransformOfPrefixReal
  have h := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ) w a hmn
  simpa [prefixSum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h


-- @@ L64-71 verbatim
/-- Prefix version of Abel's identity, valid for `N + 1 > 0` by construction. -/
theorem weightedPrefixSumReal_eq_abelTransformOfPrefixReal
    (a w : Nat → ℝ) (N : Nat) :
    weightedPrefixSumReal a w N =
      abelTransformOfPrefixReal w (prefixSum a) 0 (N + 1) := by
  simpa [weightedPrefixSumReal, weightedIntervalSumReal, Nat.Ico_zero_eq_range] using
    (weightedIntervalSumReal_eq_abelTransformOfPrefixReal
      (a := a) (w := w) (m := 0) (n := N + 1) (Nat.succ_pos N))


-- @@ L73-75 verbatim
@[simp] theorem oneOverNWeight_eq_evalAtNat (N : Nat) :
    oneOverNWeight N = evalAtNat oneOverNExpr N := by
  rfl


-- @@ L77-82 verbatim
/-- Abel's identity specialized to the foundational ANT weight `1 / n`. -/
theorem weightedPrefixSumReal_oneOverN_eq_abelTransformOfPrefixReal
    (a : Nat → ℝ) (N : Nat) :
    weightedPrefixSumReal a oneOverNWeight N =
      abelTransformOfPrefixReal oneOverNWeight (prefixSum a) 0 (N + 1) := by
  exact weightedPrefixSumReal_eq_abelTransformOfPrefixReal a oneOverNWeight N


-- @@ L84-101 verbatim
/-- A certified Stieltjes transform payload for a fixed source envelope. -/
structure StieltjesCert (A : AsympEnv) where
  /-- The discrete weight `f(n)`. -/
  weight : Nat → ℝ
  /-- First endpoint from which the transformed envelope is valid. -/
  cutoff : Nat
  /-- Main term for the weighted summatory function. -/
  mainTerm : Expr
  /-- Error term for the weighted summatory function. -/
  errorTerm : Expr
  /-- Semantic certificate, supplied by a checker or direct proof. -/
  cert :
    ∀ N, cutoff ≤ N →
      |weightedPrefixSumReal A.seq weight N - evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N
  /-- Error terms are genuine nonnegative envelope radii. -/
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N


-- @@ L103-120 verbatim
/-- Certified Stieltjes payload for the canonical ANT weight `1 / n`. -/
structure OneOverNStieltjesCert (A : AsympEnv) where
  /-- First endpoint from which the transformed envelope is valid. -/
  cutoff : Nat
  /-- The `1 / n` transform is intended for positive natural endpoints. -/
  cutoff_pos : 1 ≤ cutoff
  /-- Main term for `∑_{n ≤ N} a_n / n`. -/
  mainTerm : Expr
  /-- Error term for `∑_{n ≤ N} a_n / n`. -/
  errorTerm : Expr
  /-- Semantic certificate, supplied by a checker or direct proof. -/
  cert :
    ∀ N, cutoff ≤ N →
      |weightedPrefixSumReal A.seq oneOverNWeight N - evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N
  /-- Error terms are genuine nonnegative envelope radii. -/
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N


-- @@ L122-144 verbatim
/-- Generated Abel-side certificate for the canonical `1 / n` transform.

Checker generators should target this structure: prove the Abel transform of
the source prefix is close to a proposed main term, then convert it to a
`OneOverNStieltjesCert` through the exact finite Abel identity. -/
structure OneOverNAbelCert (A : AsympEnv) where
  /-- First endpoint from which the transformed envelope is valid. -/
  cutoff : Nat
  /-- The `1 / n` transform is intended for positive natural endpoints. -/
  cutoff_pos : 1 ≤ cutoff
  /-- Main term for `∑_{n ≤ N} a_n / n`. -/
  mainTerm : Expr
  /-- Error term for `∑_{n ≤ N} a_n / n`. -/
  errorTerm : Expr
  /-- Generated Abel-transform certificate. -/
  cert :
    ∀ N, cutoff ≤ N →
      |abelTransformOfPrefixReal oneOverNWeight (prefixSum A.seq) 0 (N + 1) -
          evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N
  /-- Error terms are genuine nonnegative envelope radii. -/
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N


-- @@ L146-146 verbatim
namespace StieltjesCert


-- @@ L148-158 verbatim
/-- Convert a certified Stieltjes transform into a new asymptotic envelope. -/
noncomputable def toAsympEnv {A : AsympEnv} (C : StieltjesCert A) :
    AsympEnv where
  seq := fun n => C.weight n * A.seq n
  cutoff := C.cutoff
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := by
    intro N hN
    simpa [weightedPrefixSumReal_eq_prefixSum] using C.cert N hN
  error_nonneg := C.error_nonneg


-- @@ L160-160 verbatim
end StieltjesCert


-- @@ L162-162 verbatim
namespace OneOverNStieltjesCert


-- @@ L164-172 verbatim
/-- Forget the `1 / n` specialization into the generic Stieltjes certificate. -/
noncomputable def toStieltjesCert {A : AsympEnv}
    (C : OneOverNStieltjesCert A) : StieltjesCert A where
  weight := oneOverNWeight
  cutoff := C.cutoff
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := C.cert
  error_nonneg := C.error_nonneg


-- @@ L174-177 verbatim
/-- Convert a certified `1 / n` Stieltjes transform into an asymptotic envelope. -/
noncomputable def toAsympEnv {A : AsympEnv} (C : OneOverNStieltjesCert A) :
    AsympEnv :=
  C.toStieltjesCert.toAsympEnv


-- @@ L179-179 verbatim
end OneOverNStieltjesCert


-- @@ L181-181 verbatim
namespace OneOverNAbelCert


-- @@ L183-195 verbatim
/-- Convert a generated Abel-side `1 / n` certificate into the public
Stieltjes certificate. -/
noncomputable def toOneOverNStieltjesCert {A : AsympEnv}
    (C : OneOverNAbelCert A) : OneOverNStieltjesCert A where
  cutoff := C.cutoff
  cutoff_pos := C.cutoff_pos
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := by
    intro N hN
    rw [weightedPrefixSumReal_oneOverN_eq_abelTransformOfPrefixReal]
    exact C.cert N hN
  error_nonneg := C.error_nonneg


-- @@ L197-201 verbatim
/-- Convert a generated Abel-side `1 / n` certificate directly into an
asymptotic envelope. -/
noncomputable def toAsympEnv {A : AsympEnv} (C : OneOverNAbelCert A) :
    AsympEnv :=
  C.toOneOverNStieltjesCert.toAsympEnv


-- @@ L203-209 verbatim
/-- Convert a generated Abel-side `1 / n` certificate into an envelope with a
public target error term, using an error-domination certificate. -/
noncomputable def toAsympEnvWithTargetError {A : AsympEnv}
    (C : OneOverNAbelCert A) (targetError : Expr)
    (D : ErrorDomination C.errorTerm targetError) (hcut : D.cutoff ≤ C.cutoff) :
    AsympEnv :=
  ErrorDomination.weakenAsympEnv C.toAsympEnv targetError D hcut


-- @@ L211-211 verbatim
end OneOverNAbelCert


-- @@ L213-219 verbatim
/-- Golden theorem for a certified Stieltjes-Abel transform payload. -/
theorem verify_stieltjes_envelope {A : AsympEnv} (C : StieltjesCert A) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnv).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.toAsympEnv.cert N hN


-- @@ L221-228 verbatim
/-- Golden theorem for the certified `1 / n` Stieltjes-Abel transform. -/
theorem verify_one_over_n_stieltjes_envelope {A : AsympEnv}
    (C : OneOverNStieltjesCert A) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnv).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.toAsympEnv.cert N hN


-- @@ L230-237 verbatim
/-- Golden theorem for a generated Abel-side `1 / n` certificate. -/
theorem verify_one_over_n_abel_envelope {A : AsympEnv}
    (C : OneOverNAbelCert A) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnv).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.toAsympEnv.cert N hN


-- @@ L239-249 verbatim
/-- Golden theorem for a generated Abel-side `1 / n` certificate after
dominating its generated error by a public target error. -/
theorem verify_one_over_n_abel_envelope_with_target_error {A : AsympEnv}
    (C : OneOverNAbelCert A) (targetError : Expr)
    (D : ErrorDomination C.errorTerm targetError) (hcut : D.cutoff ≤ C.cutoff) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnvWithTargetError targetError D hcut).summatory N -
          evalAtNat C.mainTerm N| ≤
        evalAtNat targetError N := by
  intro N hN
  exact (C.toAsympEnvWithTargetError targetError D hcut).cert N hN


-- @@ L251-251 verbatim
end LeanCert.ANT.Asymp
