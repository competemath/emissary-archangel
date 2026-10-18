/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic
import LeanCert.CertifiedBounds.BKLNW


-- @@ L9-15 verbatim
/-!
# PrimeNumberTheoremAnd BKLNW certificate patterns

Adapted from `IEANTN/BKLNW/BKLNW_a2_bounds.lean`. This exercises the
definition bridge, floor arithmetic, certificate application through `simpa`,
and the `max` glue used by the downstream development.
-/


-- @@ L17-17 verbatim
open Real Finset


-- @@ L19-19 verbatim
namespace LeanCert.Test.DownstreamPatterns.BKLNW


-- @@ L21-23 verbatim
/-- Local copy of the downstream definition, deliberately outside LeanCert's namespace. -/
noncomputable def downstreamF (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 ⌊log x / log 2⌋₊, x ^ ((1 : ℝ) / k - 1 / 3)


-- @@ L25-26 verbatim
private lemma downstreamF_eq :
    downstreamF = LeanCert.CertifiedBounds.BKLNW.f := rfl


-- @@ L28-34 verbatim
private lemma floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ 20 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]
    interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]
    interval_decide


-- @@ L36-40 verbatim
private lemma exp_lower :
    (1.4262 : ℝ) ≤
      (1 + 193571378 / (10 : ℝ) ^ 16) * downstreamF (exp (20 : ℝ)) := by
  simpa [downstreamF_eq] using
    LeanCert.CertifiedBounds.BKLNW.a2_20_exp_lower


-- @@ L42-46 verbatim
private lemma exp_upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * downstreamF (exp (20 : ℝ)) ≤
      (1.4262 : ℝ) + (1 : ℝ) / 10 ^ 4 := by
  simpa [downstreamF_eq] using
    LeanCert.CertifiedBounds.BKLNW.a2_20_exp_upper


-- @@ L48-52 verbatim
private lemma pow29_upper :
    (1 + 193571378 / (10 : ℝ) ^ 16) * downstreamF ((2 : ℝ) ^ (29 : ℕ)) ≤
      (1.4262 : ℝ) + (1 : ℝ) / 10 ^ 4 := by
  rw [downstreamF_eq]
  exact LeanCert.CertifiedBounds.BKLNW.pow29_upper


-- @@ L54-64 verbatim
/-- Complete downstream composition for the first BKLNW table point. -/
example :
    (1 + 193571378 / (10 : ℝ) ^ 16) *
        max (downstreamF (exp 20))
          (downstreamF ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1))) ∈
      Set.Icc (1.4262 : ℝ) ((1.4262 : ℝ) + (1 : ℝ) / 10 ^ 4) := by
  rw [floor_20, mul_max_of_nonneg _ _
    (by positivity : (0 : ℝ) ≤ 1 + 193571378 / (10 : ℝ) ^ 16)]
  constructor
  · exact le_trans exp_lower (le_max_left _ _)
  · exact max_le exp_upper pow29_upper


-- @@ L66-66 verbatim
end LeanCert.Test.DownstreamPatterns.BKLNW
