/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Blocking


-- @@ L9-18 verbatim
/-!
# Repeated words

`evalWord_replicate`, the elementary identity for evaluating a tensor on a
`List.replicate`-built word, now lives in `TNLean/Kraus/Blocking.lean`,
alongside the rest of the physical-blocking
word-evaluation layer. This file keeps the one matrix-product-vector
consequence, `mpv_const_eq_trace_pow`, which packages that identity as an
`mpv` statement.
-/


-- @@ L20-20 verbatim
open scoped Matrix


-- @@ L22-22 verbatim
namespace MPSTensor


-- @@ L24-24 verbatim
variable {d D : ℕ}


-- @@ L26-29 verbatim
/-- The MPV of a constant configuration is the trace of a matrix power. -/
lemma mpv_const_eq_trace_pow (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    mpv A (fun _ : Fin L => i) = Matrix.trace ((A i) ^ L) := by
  simp only [mpv, coeff, List.ofFn_const, evalWord_replicate]


-- @@ L31-31 verbatim
end MPSTensor
