/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.RootFinding.Krawczyk


-- @@ L8-13 verbatim
/-!
# Golden theorems for system root certificates

The checker and certificate live in the Engine.  This module provides the
stable Validity-layer theorem name intended for downstream proofs.
-/


-- @@ L15-15 verbatim
namespace LeanCert.Validity


-- @@ L17-17 verbatim
open LeanCert.Core

-- @@ L18-18 verbatim
open LeanCert.Engine


-- @@ L20-25 verbatim
/-- A successful Krawczyk check certifies exactly one real system root in the box. -/
theorem verify_unique_system_root {n : Nat} (F : Fin n → Expr)
    (X : Fin n → IntervalRat) (cert : KrawczykCert n) (cfg : EvalConfig)
    (h : krawczykCheck F X cert cfg = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x :=
  krawczykCheck_sound F X cert cfg h


-- @@ L27-32 verbatim
/-- A successful Krawczyk check supplies a real system root in the box. -/
theorem verify_system_root_exists {n : Nat} (F : Fin n → Expr)
    (X : Fin n → IntervalRat) (cert : KrawczykCert n) (cfg : EvalConfig)
    (h : krawczykCheck F X cert cfg = true) :
    ∃ x, FinBoxMem x X ∧ SystemZero F x :=
  (verify_unique_system_root F X cert cfg h).exists


-- @@ L34-40 verbatim
/-- A successful Krawczyk check makes any two roots in the box equal. -/
theorem verify_system_root_unique {n : Nat} (F : Fin n → Expr)
    (X : Fin n → IntervalRat) (cert : KrawczykCert n) (cfg : EvalConfig)
    (h : krawczykCheck F X cert cfg = true)
    {x y : Fin n → ℝ} (hx : FinBoxMem x X ∧ SystemZero F x)
    (hy : FinBoxMem y X ∧ SystemZero F y) : x = y :=
  (verify_unique_system_root F X cert cfg h).unique hx hy


-- @@ L42-42 verbatim
end LeanCert.Validity
