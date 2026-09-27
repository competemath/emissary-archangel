/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


-- @@ L12-17 verbatim
/-!
# Definitions in the public statement

The maximal operator is defined on real-valued integrable functions using Lebesgue measure.
These definitions agree with the independently stated upstream comparator challenge.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open MeasureTheory Metric

-- @@ L24-24 verbatim
open scoped ENNReal


-- @@ L26-26 verbatim
namespace LeanPool.CenteredMaximal


-- @@ L28-34 verbatim
/-- The centred Hardy–Littlewood maximal function of `f : ℝᵈ → ℝ` over axis-parallel cubes:
`M f (x) = sup_{r > 0} |Q(x, r)|⁻¹ ∫_{Q(x, r)} |f|`, with values in `[0, ∞]`.

Since `Fin d → ℝ` carries the sup norm, `closedBall x r` is the closed cube `∏ᵢ [xᵢ - r, xᵢ + r]`
of side length `2r` centred at `x`; `volume` is Lebesgue measure. -/
def maximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ


-- @@ L36-40 verbatim
/-- `C` is a weak type `(1, 1)` bound for the centred maximal operator in dimension `d`: for every
integrable `f : ℝᵈ → ℝ` and every level `α ∈ [0, ∞]`, `α · |{x : M f (x) > α}| ≤ C · ‖f‖₁`. -/
def IsWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : (Fin d → ℝ) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < maximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ


-- @@ L42-45 verbatim
/-- The weak type `(1, 1)` constant `c_d` of the centred Hardy–Littlewood maximal operator over
axis-parallel cubes in `ℝᵈ`: the least weak type bound. -/
def weakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsWeakTypeBound d C}


-- @@ L47-57 verbatim
/-- The constant `Φ = 1.68550999335552518…`, an explicit radical expression:
`Φ = ((77 + 16√22)/2 - (8 + √22 - √(70 + 8√22)) (11 + √22 - 2√2 - 2√11 - √(17 + 4√22)))
/ (26 + 4√22)`.

It bounds the covered area per unit mass of a periodic measure from below: unit masses and masses
`w = (17 + 4√22)/9` alternate along the columns `x = i h`, `h = (5 + √22)/6`, and the rows are
`y = j V`, `V = (11 + √22)/6`. -/
def phi : ℝ :=
  ((77 + 16 * √22) / 2 -
      (8 + √22 - √(70 + 8 * √22)) * (11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22))) /
    (26 + 4 * √22)


-- @@ L59-59 verbatim
end LeanPool.CenteredMaximal
