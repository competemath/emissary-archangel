/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Bounds


-- @@ L8-38 verbatim
/-!
# Certificate-Driven Verification Examples

This file demonstrates the certificate-driven verification system.
All proofs use `native_decide` to execute the boolean checkers.

## Design

The golden theorems (`verify_upper_bound`, etc.) take:
1. The expression `e`
2. A proof `hsupp` that `e` is in `ExprSupportedCore`
3. The interval `I`
4. The bound `c`
5. An `EvalConfig` specifying Taylor depth
6. A proof `h_cert` that the checker returns `true`

The last argument is discharged by `native_decide`.

## Examples

### Basic algebraic bounds
- `x² ≤ 1` on `[0, 1]` with depth 10

### Transcendental bounds with varying depth
- `exp(x) ≤ 3` on `[0, 1]` with depth 10
- `sin(x) ≤ 1` on `[0, 1]` with depth 10
- Tighter bounds with higher depth

### Demonstrating depth sensitivity
- Same bound may require different depths for different interval widths
-/


-- @@ L40-40 verbatim
namespace LeanCert.Examples.Certificate


-- @@ L42-42 verbatim
open LeanCert.Core

-- @@ L43-43 verbatim
open LeanCert.Engine

-- @@ L44-44 verbatim
open LeanCert.Validity


-- @@ L46-46 verbatim
/-! ### Setup: Expressions and intervals -/


-- @@ L48-49 verbatim
/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L51-52 verbatim
/-- The interval [0, 1.2] -/
def I012 : IntervalRat := ⟨0, 6/5, by norm_num⟩


-- @@ L54-55 verbatim
/-- The expression x² -/
def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)


-- @@ L57-59 verbatim
/-- Support proof for x² -/
theorem exprXSq_core : ExprSupportedCore exprXSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)


-- @@ L61-62 verbatim
/-- The expression exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)


-- @@ L64-66 verbatim
/-- Support proof for exp(x) -/
theorem exprExp_core : ExprSupportedCore exprExp :=
  ExprSupportedCore.exp (ExprSupportedCore.var 0)


-- @@ L68-69 verbatim
/-- The expression sin(x) -/
def exprSin : Expr := Expr.sin (Expr.var 0)


-- @@ L71-73 verbatim
/-- Support proof for sin(x) -/
theorem exprSin_core : ExprSupportedCore exprSin :=
  ExprSupportedCore.sin (ExprSupportedCore.var 0)


-- @@ L75-76 verbatim
/-- The expression cos(x) -/
def exprCos : Expr := Expr.cos (Expr.var 0)


-- @@ L78-80 verbatim
/-- Support proof for cos(x) -/
theorem exprCos_core : ExprSupportedCore exprCos :=
  ExprSupportedCore.cos (ExprSupportedCore.var 0)


-- @@ L82-83 verbatim
/-- The expression x * exp(x) -/
def exprXExp : Expr := Expr.mul (Expr.var 0) (Expr.exp (Expr.var 0))


-- @@ L85-88 verbatim
/-- Support proof for x * exp(x) -/
theorem exprXExp_core : ExprSupportedCore exprXExp :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0)
    (ExprSupportedCore.exp (ExprSupportedCore.var 0))


-- @@ L90-90 verbatim
/-! ### Basic algebraic bounds -/


-- @@ L92-94 verbatim
/-- x² ≤ 1 on [0, 1] with default depth 10 -/
theorem xsq_le_one_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) :=
  verify_upper_bound exprXSq exprXSq_core I01 1 {} (by native_decide)


-- @@ L96-98 verbatim
/-- 0 ≤ x² on [0, 1] with default depth 10 -/
theorem zero_le_xsq_cert : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXSq :=
  verify_lower_bound exprXSq exprXSq_core I01 0 {} (by native_decide)


-- @@ L100-100 verbatim
/-! ### Transcendental bounds -/


-- @@ L102-104 verbatim
/-- exp(x) ≤ 3 on [0, 1] with depth 10 -/
theorem exp_le_three_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) :=
  verify_upper_bound exprExp exprExp_core I01 3 { taylorDepth := 10 } (by native_decide)


-- @@ L106-110 verbatim
/-- 9/10 ≤ exp(x) on [0, 1] with depth 10
    Note: The Taylor model gives a conservative lower bound slightly below 1,
    so we use 9/10 as a safe lower bound that the interval arithmetic can verify. -/
theorem nine_tenths_le_exp_cert : ∀ x ∈ I01, (9/10 : ℚ) ≤ Expr.eval (fun _ => x) exprExp :=
  verify_lower_bound exprExp exprExp_core I01 (9/10) { taylorDepth := 10 } (by native_decide)


-- @@ L112-114 verbatim
/-- sin(x) ≤ 1 on [0, 1] -/
theorem sin_le_one_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprSin ≤ (1 : ℚ) :=
  verify_upper_bound exprSin exprSin_core I01 1 { taylorDepth := 10 } (by native_decide)


-- @@ L116-118 verbatim
/-- cos(x) ≤ 1 on [0, 1] -/
theorem cos_le_one_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprCos ≤ (1 : ℚ) :=
  verify_upper_bound exprCos exprCos_core I01 1 { taylorDepth := 10 } (by native_decide)


-- @@ L120-123 verbatim
/-! ### Tighter bounds with higher depth

Higher Taylor depth allows tighter bounds to be verified.
-/


-- @@ L125-127 verbatim
/-- exp(x) ≤ 2.75 on [0, 1] requires higher depth for tighter bound -/
theorem exp_le_275_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (11/4 : ℚ) :=
  verify_upper_bound exprExp exprExp_core I01 (11/4) { taylorDepth := 15 } (by native_decide)


-- @@ L129-136 verbatim
/-! ### Combined expression: x * exp(x)

This demonstrates the certificate system on a more complex expression.
On [0, 1], we have:
- x ∈ [0, 1]
- exp(x) ∈ [1, e]
- x * exp(x) ∈ [0, e] ≈ [0, 2.718]
-/


-- @@ L138-140 verbatim
/-- x * exp(x) ≤ 3 on [0, 1] -/
theorem xexp_le_three_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXExp ≤ (3 : ℚ) :=
  verify_upper_bound exprXExp exprXExp_core I01 3 { taylorDepth := 10 } (by native_decide)


-- @@ L142-144 verbatim
/-- 0 ≤ x * exp(x) on [0, 1] -/
theorem zero_le_xexp_cert : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXExp :=
  verify_lower_bound exprXExp exprXExp_core I01 0 { taylorDepth := 10 } (by native_decide)


-- @@ L146-146 verbatim
/-! ### Strict bounds -/


-- @@ L148-150 verbatim
/-- x² < 2 on [0, 1] (strict upper bound) -/
theorem xsq_lt_two_cert : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq < (2 : ℚ) :=
  verify_strict_upper_bound exprXSq exprXSq_core I01 2 {} (by native_decide)


-- @@ L152-154 verbatim
/-- -1 < x² on [0, 1] (strict lower bound) -/
theorem neg_one_lt_xsq_cert : ∀ x ∈ I01, (-1 : ℚ) < Expr.eval (fun _ => x) exprXSq :=
  verify_strict_lower_bound exprXSq exprXSq_core I01 (-1) {} (by native_decide)


-- @@ L156-156 verbatim
/-! ### Two-sided bounds -/


-- @@ L158-161 verbatim
/-- 0 ≤ x² ≤ 1 on [0, 1] -/
theorem xsq_bounds_cert : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXSq ∧
    Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) :=
  verify_bounds exprXSq exprXSq_core I01 0 1 {} (by native_decide)


-- @@ L163-166 verbatim
/-- 9/10 ≤ exp(x) ≤ 3 on [0, 1] -/
theorem exp_bounds_cert : ∀ x ∈ I01, (9/10 : ℚ) ≤ Expr.eval (fun _ => x) exprExp ∧
    Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) :=
  verify_bounds exprExp exprExp_core I01 (9/10) 3 { taylorDepth := 15 } (by native_decide)


-- @@ L168-172 verbatim
/-! ### Example: RPC workflow simulation

This section demonstrates what Python-generated code would look like.
Python determines the required depth, then generates a one-liner proof.
-/


-- @@ L174-176 verbatim
/-- Simulated RPC call: Python found depth 12 sufficient for exp(x) ≤ 2.8 on [0,1] -/
theorem rpc_exp_bound : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (14/5 : ℚ) :=
  verify_upper_bound exprExp exprExp_core I01 (14/5) { taylorDepth := 12 } (by native_decide)


-- @@ L178-178 verbatim
end LeanCert.Examples.Certificate
