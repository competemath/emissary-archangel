/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Bounds
import LeanCert.Tactic


-- @@ L9-14 verbatim
/-!
# Evaluation-backend and verification-route independence

Both theorems use the same public Dyadic-backed Boolean checker. Only the
tactic-side verification route changes.
-/


-- @@ L16-16 verbatim
namespace LeanCert.Test.PublicAPI.TrustAxes


-- @@ L18-18 verbatim
open LeanCert LeanCert.Core


-- @@ L20-20 verbatim
def positive : IntervalRat := ⟨1, 2, by norm_num⟩

-- @@ L21-21 verbatim
def logarithm : Expr := .log (.var 0)


-- @@ L23-27 verbatim
set_option leancert.trust "kernel" in
theorem dyadicCheckKernelVerified :
    ∀ x ∈ positive, Expr.eval (fun _ => x) logarithm ≤ (1 : ℚ) := by
  apply API.Bounds.verifyUpperBound (precision := {})
  leancert_verify_cert


-- @@ L29-33 verbatim
set_option leancert.trust "native" in
theorem dyadicCheckNativeVerified :
    ∀ x ∈ positive, Expr.eval (fun _ => x) logarithm ≤ (1 : ℚ) := by
  apply API.Bounds.verifyUpperBound (precision := {})
  leancert_verify_cert


-- @@ L35-35 verbatim
#assert_trust kernel dyadicCheckKernelVerified

-- @@ L36-36 verbatim
#assert_trust native dyadicCheckNativeVerified


-- @@ L38-38 verbatim
end LeanCert.Test.PublicAPI.TrustAxes
