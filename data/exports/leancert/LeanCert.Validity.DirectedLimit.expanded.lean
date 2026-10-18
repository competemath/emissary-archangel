/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.Cast.Order


-- @@ L10-37 verbatim
/-!
# Directed-limit certificates

A recurring proof shape in verified numerics: a real limit object `x`
(an infinite series, an infinite product integral, a directed `sInf`/`sSup`)
is approximated by computable rational truncations `approx N`, with

* every truncation an upper bound: `x ≤ approx N`, and
* a computable tail majorant: `approx N - tail N ≤ x`.

Given these two inequality families, a two-sided rational enclosure of `x`
is a boolean check at a single index `N`. This module provides the checker,
the golden theorem, a packaging structure, and the convergence corollary
(`approx N → x` whenever `tail N → 0`).

Existing instances of this shape in the library include the prime q-product
sandwich (`LeanCert.QProduct.primeLambda_sandwich`, packaged as a
`DirectedLimitCert` in `LeanCert.QProduct.LimitCert`) and the tail-interval
decompositions in the Li2 and BKLNW developments. The symmetric (monotone
from below) variant is obtained by negation and is not duplicated here.

## Main definitions

* `checkLimitInterval` — boolean enclosure check at one truncation index
* `verify_limit_interval` — golden theorem: check ⟹ real enclosure
* `DirectedLimitCert` — packaging of the two inequality families
* `DirectedLimitCert.approx_tendsto_limit` — vanishing tails ⟹ convergence
-/


-- @@ L39-39 verbatim
namespace LeanCert.Validity


-- @@ L41-41 verbatim
open Filter Topology


-- @@ L43-47 verbatim
/-- Boolean enclosure check for a directed limit at truncation index `N`:
the lower endpoint is cleared by the tail-corrected truncation and the upper
endpoint by the truncation itself. -/
def checkLimitInterval (approx tail : ℕ → ℚ) (N : ℕ) (lo hi : ℚ) : Bool :=
  decide (lo ≤ approx N - tail N) && decide (approx N ≤ hi)


-- @@ L49-65 verbatim
/-- Golden theorem for directed-limit certificates: a successful
`checkLimitInterval` at any single index yields a two-sided real enclosure
of the limit object. -/
theorem verify_limit_interval {x : ℝ} {approx tail : ℕ → ℚ}
    (hupper : ∀ N, x ≤ (approx N : ℝ))
    (hlower : ∀ N, (approx N : ℝ) - (tail N : ℝ) ≤ x)
    (N : ℕ) (lo hi : ℚ)
    (hcheck : checkLimitInterval approx tail N lo hi = true) :
    (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ) := by
  unfold checkLimitInterval at hcheck
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hcheck
  constructor
  · calc (lo : ℝ) ≤ ((approx N - tail N : ℚ) : ℝ) := by exact_mod_cast hcheck.1
      _ = (approx N : ℝ) - (tail N : ℝ) := by push_cast; ring
      _ ≤ x := hlower N
  · calc x ≤ (approx N : ℝ) := hupper N
      _ ≤ (hi : ℝ) := by exact_mod_cast hcheck.2


-- @@ L67-80 verbatim
/-- A directed-limit certificate: a real limit object enclosed from above by
computable rational truncations and from below by truncation minus a
computable tail majorant. -/
structure DirectedLimitCert where
  /-- Computable rational truncation values. -/
  approx : ℕ → ℚ
  /-- Computable tail majorant at each truncation index. -/
  tail : ℕ → ℚ
  /-- The semantic limit object. -/
  limit : ℝ
  /-- Every truncation bounds the limit from above. -/
  limit_le_approx : ∀ N, limit ≤ (approx N : ℝ)
  /-- The tail-corrected truncation bounds the limit from below. -/
  approx_sub_tail_le_limit : ∀ N, (approx N : ℝ) - (tail N : ℝ) ≤ limit


-- @@ L82-82 verbatim
namespace DirectedLimitCert


-- @@ L84-91 verbatim
/-- Golden theorem, packaged form. -/
theorem verify_interval (C : DirectedLimitCert) {approx tail : ℕ → ℚ}
    (hA : C.approx = approx) (hT : C.tail = tail)
    (N : ℕ) (lo hi : ℚ)
    (hcheck : checkLimitInterval approx tail N lo hi = true) :
    (lo : ℝ) ≤ C.limit ∧ C.limit ≤ (hi : ℝ) :=
  verify_limit_interval (hA ▸ C.limit_le_approx)
    (by rw [← hA, ← hT]; exact C.approx_sub_tail_le_limit) N lo hi hcheck


-- @@ L93-107 verbatim
/-- Vanishing tails imply convergence of the truncations to the limit. -/
theorem approx_tendsto_limit (C : DirectedLimitCert)
    (htail : Tendsto (fun N => (C.tail N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (C.approx N : ℝ)) atTop (𝓝 C.limit) := by
  have hupper : ∀ N, (C.approx N : ℝ) ≤ C.limit + (C.tail N : ℝ) := by
    intro N
    have := C.approx_sub_tail_le_limit N
    linarith
  have hconst : Tendsto (fun _ : ℕ => C.limit) atTop (𝓝 C.limit) :=
    tendsto_const_nhds
  have hplus : Tendsto (fun N => C.limit + (C.tail N : ℝ)) atTop
      (𝓝 (C.limit + 0)) := hconst.add htail
  rw [add_zero] at hplus
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hconst hplus
    C.limit_le_approx hupper


-- @@ L109-109 verbatim
end DirectedLimitCert


-- @@ L111-111 verbatim
end LeanCert.Validity
