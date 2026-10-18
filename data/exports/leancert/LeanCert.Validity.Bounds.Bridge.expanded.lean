/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Bounds.Smart
import LeanCert.Engine.Integrate


-- @@ L9-34 verbatim
/-!
# Set.Icc Bridge Theorems and Subdivision

This module provides bridge theorems between IntervalRat-based proofs and Set.Icc goals,
as well as subdivision theorems for combining bounds from interval partitions.

## Main definitions

### Set.Icc Bridge Theorems
* `verify_upper_bound_Icc` - Bridge for upper bounds (smart version)
* `verify_lower_bound_Icc` - Bridge for lower bounds (smart version)
* `verify_upper_bound_Icc_core` - Bridge for upper bounds (core version)
* `verify_lower_bound_Icc_core` - Bridge for lower bounds (core version)
* `verify_strict_upper_bound_Icc_core` - Bridge for strict upper bounds
* `verify_strict_lower_bound_Icc_core` - Bridge for strict lower bounds

### Subdivision Theorems
* `verify_upper_bound_split` - Combine upper bounds from two halves
* `verify_lower_bound_split` - Combine lower bounds from two halves
* `verify_strict_upper_bound_split` - Combine strict upper bounds
* `verify_strict_lower_bound_split` - Combine strict lower bounds

### General Split Theorems
* `verify_upper_bound_general_split` - Combine from arbitrary split points
* `verify_lower_bound_general_split` - Combine from arbitrary split points
-/


-- @@ L36-36 verbatim
namespace LeanCert.Validity


-- @@ L38-38 verbatim
open LeanCert.Core

-- @@ L39-39 verbatim
open LeanCert.Engine


-- @@ L41-45 verbatim
/-! ### Set.Icc Bridge Theorems

These theorems bridge between IntervalRat-based proofs and Set.Icc goals,
allowing tactics to work with the more natural Set.Icc syntax.
-/


-- @@ L47-55 verbatim
/-- Bridge from IntervalRat proof to Set.Icc upper bound goal -/
theorem verify_upper_bound_Icc (e : Expr) (hsupp : ADSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L57-65 verbatim
/-- Bridge from IntervalRat proof to Set.Icc lower bound goal -/
theorem verify_lower_bound_Icc (e : Expr) (hsupp : ADSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L67-76 verbatim
/-- Bridge from IntervalRat proof to Set.Icc upper bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkUpperBound (no monotonicity). -/
theorem verify_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L78-87 verbatim
/-- Bridge from IntervalRat proof to Set.Icc lower bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkLowerBound (no monotonicity). -/
theorem verify_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L89-97 verbatim
/-- Bridge from IntervalRat proof to Set.Icc strict upper bound goal (Core version). -/
theorem verify_strict_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L99-107 verbatim
/-- Bridge from IntervalRat proof to Set.Icc strict lower bound goal (Core version). -/
theorem verify_strict_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L109-114 verbatim
/-! ### Subdivision Theorems

These theorems allow combining bounds from interval subdivisions.
When interval arithmetic gives overly wide bounds, subdividing the domain
and proving bounds on each piece can help.
-/


-- @@ L116-126 verbatim
/-- Combine upper bounds from two halves using splitMid.
    If f ≤ c on both halves, then f ≤ c on the whole interval. -/
theorem verify_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR


-- @@ L128-137 verbatim
/-- Combine lower bounds from two halves using splitMid. -/
theorem verify_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR


-- @@ L139-148 verbatim
/-- Combine strict upper bounds from two halves. -/
theorem verify_strict_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR


-- @@ L150-159 verbatim
/-- Combine strict lower bounds from two halves. -/
theorem verify_strict_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR


-- @@ L161-170 verbatim
/-- Bridge from subdivision to Set.Icc upper bound goal. -/
theorem verify_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L172-181 verbatim
/-- Bridge from subdivision to Set.Icc lower bound goal. -/
theorem verify_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L183-192 verbatim
/-- Bridge from subdivision to Set.Icc strict upper bound goal. -/
theorem verify_strict_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L194-203 verbatim
/-- Bridge from subdivision to Set.Icc strict lower bound goal. -/
theorem verify_strict_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L205-209 verbatim
/-! ### General Split Theorems

These theorems work with arbitrary split points, not just midpoints.
Useful for adaptive subdivision algorithms.
-/


-- @@ L211-220 verbatim
/-- Any x in [lo, hi] is in [lo, mid] or [mid, hi] for any mid in between -/
theorem mem_split_general {lo mid hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ))
    (_hLeMid : lo ≤ mid) (_hMidLe : mid ≤ hi) :
    x ∈ Set.Icc (lo : ℝ) (mid : ℝ) ∨ x ∈ Set.Icc (mid : ℝ) (hi : ℝ) := by
  simp only [Set.mem_Icc] at hx ⊢
  by_cases! h : x ≤ mid
  · left; exact ⟨hx.1, h⟩
  · right
    exact ⟨le_of_lt h, hx.2⟩


-- @@ L222-232 verbatim
/-- Combine already-certified upper bounds on adjacent intervals.  Unlike the
checker-specific theorem below, this supports recursive subdivision proofs. -/
theorem combine_upper_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), Expr.eval (fun _ => x) e ≤ c)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR


-- @@ L234-243 verbatim
/-- Combine already-certified lower bounds on adjacent intervals. -/
theorem combine_lower_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), c ≤ Expr.eval (fun _ => x) e)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR


-- @@ L245-254 verbatim
/-- Combine already-certified strict upper bounds on adjacent intervals. -/
theorem combine_strict_upper_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), Expr.eval (fun _ => x) e < c)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR


-- @@ L256-265 verbatim
/-- Combine already-certified strict lower bounds on adjacent intervals. -/
theorem combine_strict_lower_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), c < Expr.eval (fun _ => x) e)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR


-- @@ L267-279 verbatim
/-- Combine upper bounds from two arbitrary adjacent intervals.
    If f ≤ c on [lo, mid] and f ≤ c on [mid, hi], then f ≤ c on [lo, hi]. -/
theorem verify_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L281-292 verbatim
/-- Combine lower bounds from two arbitrary adjacent intervals. -/
theorem verify_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L294-305 verbatim
/-- Combine strict upper bounds from two arbitrary adjacent intervals. -/
theorem verify_strict_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L307-318 verbatim
/-- Combine strict lower bounds from two arbitrary adjacent intervals. -/
theorem verify_strict_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]


-- @@ L320-320 verbatim
end LeanCert.Validity
