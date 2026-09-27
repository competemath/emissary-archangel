/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Order.Antidiag.Nat


-- @@ L10-12 verbatim
/-!
# LeanPool.SelbergSieve4.ForMathlib.ProdsAntidiagonal
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open scoped ArithmeticFunction.omega


-- @@ L18-18 verbatim
namespace Nat


-- @@ L20-22 verbatim
/-- Alias for the multiplicative antidiagonal indexed by `Fin d`. -/
abbrev finMulAntidiagonal (d n : ℕ) : Finset (Fin d → ℕ) :=
  finMulAntidiag d n


-- @@ L24-27 verbatim
/-- Membership in the multiplicative antidiagonal. -/
theorem mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 :=
  mem_finMulAntidiag


-- @@ L29-32 verbatim
theorem finMulAntidiagonal_univ_eq {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiagonal d m =
      (Fintype.piFinset fun _ : Fin d => n.divisors).filter (fun f => ∏ i, f i = m) :=
  finMulAntidiag_eq_piFinset_divisors_filter hmn hn


-- @@ L34-36 verbatim
theorem card_finMulAntidiagonal {d n : ℕ} (hn : Squarefree n) :
    (finMulAntidiagonal d n).card = d ^ ω n := by
  simpa [finMulAntidiagonal] using card_finMulAntidiag_of_squarefree (d := d) hn


-- @@ L38-38 verbatim
end Nat
