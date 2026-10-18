/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Chebyshev.Psi


-- @@ L8-18 verbatim
/-!
# Certified ψ(N) ≤ 1.11 * N bounds

This file provides certified bounds on the Chebyshev function ψ(N) ≤ 1.11 * N
for all N ≤ 11723, verified via `native_decide`.

## Interface

The main theorem is `psi_le_mul_11723`: for all 0 < x ≤ 11723, ψ(x) ≤ 1.11 * x.
This corresponds to PNT issue #844 (`psi_num_2`).
-/


-- @@ L20-20 verbatim
open Chebyshev (psi)

-- @@ L21-21 verbatim
open LeanCert.Engine.Chebyshev.Psi


-- @@ L23-23 verbatim
namespace LeanCert.Examples.PNT_PsiBounds


-- @@ L25-25 verbatim
/-! ### Core verification fact -/


-- @@ L27-28 verbatim
/-- The incremental checker verifies ψ(N) ≤ 1.11 * N for all N = 1, ..., 11723. -/
theorem allChecks_11723_slope111_100 : checkAllPsiLeMulWith 11723 (111 / 100) 20 = true := by native_decide


-- @@ L30-35 verbatim
/-- For each N ≤ 11723, `checkPsiLeMulWith` holds at slope `111/100`.
    Derived from allChecks_11723_slope111_100 via the formal bridge
    `checkAllPsiLeMulWith_implies_checkPsiLeMulWith`. -/
theorem checkPsiLeMul_le_11723 (N : ℕ) (hN : 0 < N) (hNb : N ≤ 11723) :
    checkPsiLeMulWith N (111 / 100) 20 = true :=
  checkAllPsiLeMulWith_implies_checkPsiLeMulWith 11723 (111 / 100) 20 allChecks_11723_slope111_100 N hN hNb


-- @@ L37-37 verbatim
/-! ### Main theorems -/


-- @@ L39-45 verbatim
/-- ψ(N) ≤ 1.11 * N for all natural N ≤ 11723. -/
theorem psi_le_nat (N : ℕ) (hN : 0 < N) (hNb : N ≤ 11723) :
    psi (N : ℝ) ≤ 111 / 100 * N := by
  have h :=
    psi_le_of_checkPsiLeMulWith N 20 (111 / 100) (checkPsiLeMul_le_11723 N hN hNb)
  have hcast : ((111 / 100 : ℚ) : ℝ) = 111 / 100 := by norm_num
  simpa [hcast] using h


-- @@ L47-61 verbatim
/-- ψ(x) ≤ 1.11 * x for all real 0 < x ≤ 11723.
    This is the main theorem needed by PNT's `psi_num_2`. -/
theorem psi_le_mul_11723 (x : ℝ) (hx : 0 < x) (hxb : x ≤ 11723) :
    psi x ≤ 111 / 100 * x := by
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  have hnn : (0 : ℝ) ≤ x := le_of_lt hx
  have hfloor_le : ⌊x⌋₊ ≤ 11723 := Nat.floor_le_of_le hxb
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with hf | hf
  · -- x < 1, so ⌊x⌋₊ = 0 and ψ(0) = 0
    simp only [hf, Nat.cast_zero]
    rw [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0:ℝ) < 2)]
    linarith
  · have h1 := psi_le_nat ⌊x⌋₊ hf hfloor_le
    calc psi (⌊x⌋₊ : ℝ) ≤ 111 / 100 * ⌊x⌋₊ := h1
      _ ≤ 111 / 100 * x := by gcongr; exact Nat.floor_le hnn


-- @@ L63-63 verbatim
end LeanCert.Examples.PNT_PsiBounds

