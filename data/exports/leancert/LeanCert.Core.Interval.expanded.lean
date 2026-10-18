/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.Basic


-- @@ L9-25 verbatim
/-!
# Abstract Interval Interface

This file defines the abstract notion of intervals as subsets of ℝ,
with semantic properties. This provides the mathematical foundation
that `IntervalReal` will implement computationally.

## Main definitions

* Lemmas about `Set.Icc` (closed intervals) relevant to interval arithmetic
* Convexity and integrability properties

## Design notes

We primarily use `Set.Icc a b` from Mathlib as our semantic interval type.
This file collects lemmas and abstractions useful for verified numerics.
-/


-- @@ L27-27 verbatim
namespace LeanCert.Core


-- @@ L29-29 verbatim
/-! ### Interval membership and operations -/


-- @@ L31-32 verbatim
/-- A real number is in the interval [a, b] -/
abbrev mem_Icc (x a b : ℝ) : Prop := a ≤ x ∧ x ≤ b


-- @@ L34-34 verbatim
theorem mem_Icc_iff (x a b : ℝ) : mem_Icc x a b ↔ x ∈ Set.Icc a b := Iff.rfl


-- @@ L36-40 verbatim
/-! ### Interval arithmetic semantics

These lemmas establish the semantic foundation for interval arithmetic:
if x ∈ [a, b] and y ∈ [c, d], then x ⊕ y ∈ [a ⊕ c, b ⊕ d] (for appropriate ⊕).
-/


-- @@ L42-46 verbatim
/-- Addition preserves interval membership -/
theorem add_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x + y ∈ Set.Icc (a + c) (b + d) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith


-- @@ L48-52 verbatim
/-- Negation reverses interval bounds -/
theorem neg_mem_Icc {x a b : ℝ} (hx : x ∈ Set.Icc a b) :
    -x ∈ Set.Icc (-b) (-a) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith


-- @@ L54-58 verbatim
/-- Subtraction on intervals -/
theorem sub_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x - y ∈ Set.Icc (a - d) (b - c) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith


-- @@ L60-60 verbatim
/-! ### Convexity -/


-- @@ L62-63 verbatim
/-- Closed intervals are convex -/
theorem Icc_convex (a b : ℝ) : Convex ℝ (Set.Icc a b) := convex_Icc a b


-- @@ L65-65 verbatim
/-! ### Compactness -/


-- @@ L67-68 verbatim
/-- Nonempty closed bounded intervals are compact -/
theorem Icc_compact (a b : ℝ) : IsCompact (Set.Icc a b) := isCompact_Icc


-- @@ L70-70 verbatim
/-! ### Continuous functions on intervals -/


-- @@ L72-84 verbatim
/-- A continuous function on a compact interval attains its bounds -/
theorem continuous_Icc_bounds {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) :
    ∃ (lo hi : ℝ), (∀ x ∈ Set.Icc a b, lo ≤ f x ∧ f x ≤ hi) ∧
      (∃ x ∈ Set.Icc a b, f x = lo) ∧ (∃ x ∈ Set.Icc a b, f x = hi) := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨xmin, hxmin_mem, hxmin⟩ := hcpt.exists_isMinOn hne hf.continuousOn
  obtain ⟨xmax, hxmax_mem, hxmax⟩ := hcpt.exists_isMaxOn hne hf.continuousOn
  exact ⟨f xmin, f xmax,
    fun x hx => ⟨hxmin hx, hxmax hx⟩,
    ⟨xmin, hxmin_mem, rfl⟩,
    ⟨xmax, hxmax_mem, rfl⟩⟩


-- @@ L86-86 verbatim
end LeanCert.Core
