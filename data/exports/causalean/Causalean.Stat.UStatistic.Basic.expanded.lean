module
public import Causalean.Stat.Sample
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L6-30 verbatim
/-!
# Order-2 U-statistics

This module defines the ordered off-diagonal order-2 statistic `uStatistic`, its
population mean `uMean`, first projection `uProj`, and degenerate residual
`uDegen`.  It proves the algebraic Hoeffding identity `hoeffding_decomp`, the
centering and integrability facts for the first projection, and
`uDegen_integral_right_eq_zero`, the one-coordinate degeneracy property of the
second-order residual.

The statistic averages a two-argument kernel over ordered distinct sample
pairs. For symmetric kernels, this agrees with the usual average over unordered
pairs. The residual identity is

  `h(x, y) = θ + h₁(x) + h₁(y) + g(x, y)`.

The module also proves that the first projection is centered and that the
residual integrates to zero in one coordinate under the stated assumptions.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
namespace Causalean.Stat


-- @@ L36-36 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L38-39 verbatim
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}


-- @@ L41-41 verbatim
/-! ## Definitions -/


-- @@ L43-57 verbatim
/-- For [a sample space and an outcome space, each equipped with a
σ-algebra](hyp:Ω,X), [an independent and identically distributed sample with probability law
$\mu$ and marginal law $P$](hyp:μ,P,S), [a real-valued two-argument kernel](hyp:h), and
[a nonnegative integer $n$](hyp:n), [the order-two U-statistic](goal) is the random
variable that, at each sample outcome, equals $(n(n-1))^{-1}$ times the sum of the kernel
over all ordered distinct pairs among the first $n$ observations.

The order-2 U-statistic with kernel `h` over the first `n` sample points is
`(n(n−1))⁻¹ Σ_{(i,j) ∈ offDiag (range n)} h(Zᵢ, Zⱼ)`. The off-diagonal sum ranges over
ordered pairs `i ≠ j`; for a symmetric kernel this is the usual
`(n choose 2)⁻¹ Σ_{i<j}`. -/
noncomputable def uStatistic (S : IIDSample Ω X μ P) (h : X → X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
    ∑ p ∈ (Finset.range n).offDiag, h (S.Z p.1 ω) (S.Z p.2 ω)


-- @@ L59-66 verbatim
/-- For [an outcome space equipped with a σ-algebra](hyp:X),
[a real-valued two-argument kernel](hyp:h), and [a measure $P$ on that space](hyp:P),
[the population mean of the kernel](goal) is its iterated integral with respect to $P$ in
both arguments.

The population mean of the kernel is `θ = ∬ h dP dP`. -/
noncomputable def uMean (h : X → X → ℝ) (P : Measure X) : ℝ :=
  ∫ x, (∫ y, h x y ∂P) ∂P


-- @@ L68-75 verbatim
/-- For [an outcome space equipped with a σ-algebra](hyp:X),
[a real-valued two-argument kernel](hyp:h), and [a measure $P$ on that space](hyp:P),
[the first centered Hoeffding projection](goal) assigns to each outcome $x$ the integral
of the kernel with first argument $x$ under $P$, minus the population mean of the kernel.

The first Hoeffding projection is centered: `h₁(x) = ∫ h(x, ·) dP − θ`. -/
noncomputable def uProj (h : X → X → ℝ) (P : Measure X) : X → ℝ :=
  fun x => (∫ y, h x y ∂P) - uMean h P


-- @@ L77-85 verbatim
/-- For [an outcome space equipped with a σ-algebra](hyp:X),
[a real-valued two-argument kernel](hyp:h), and [a measure $P$ on that space](hyp:P),
[the degenerate second-order kernel](goal) assigns to outcomes $x$ and $y$ the original
kernel value minus its population mean and minus its first centered Hoeffding projections
at $x$ and $y$.

The degenerate second-order kernel is `g(x, y) = h(x, y) − θ − h₁(x) − h₁(y)`. -/
noncomputable def uDegen (h : X → X → ℝ) (P : Measure X) : X → X → ℝ :=
  fun x y => h x y - uMean h P - uProj h P x - uProj h P y


-- @@ L87-87 verbatim
/-! ## Hoeffding decomposition -/


-- @@ L89-97 verbatim
/-- **Hoeffding decomposition (pointwise identity).** For [a kernel `h`](hyp:h), [population law
`P`](hyp:P), and [points `x` and `y`](hyp:x,y), [the kernel value decomposes as
`h(x, y) = θ + h₁(x) + h₁(y) + g(x, y)`](goal), the population mean plus the two first-order
Hoeffding projections plus the degenerate second-order residual.

Purely algebraic. -/
theorem hoeffding_decomp (h : X → X → ℝ) (P : Measure X) (x y : X) :
    h x y = uMean h P + uProj h P x + uProj h P y + uDegen h P x y := by
  simp only [uDegen]; ring


-- @@ L99-106 expanded
/-- The first projection integrates to zero: `∫ h₁ dP = 0`. -/
theorem uProj_integral_eq_zero [IsProbabilityMeasure P] {h : X → X → ℝ}
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P) : ∫ x, uProj h P x ∂P = 0 :=
  by
  unfold uProj
  first
  |
    simp (disch :=
      first
      | assumption
      | fun_prop) only [MeasureTheory.integral_add,
      MeasureTheory.integral_add', MeasureTheory.integral_sub, MeasureTheory.integral_sub',
      MeasureTheory.integral_neg, MeasureTheory.integral_neg', MeasureTheory.integral_finsetSum,
      MeasureTheory.integral_smul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_mul_const, MeasureTheory.integral_div]
  |
    fail "integral_linearity: nothing to normalize.\n\
                  The normal form is: `+`, `-`, negation, `•`, a factor independent of the \
                  integration variable, and finite sums all outside the `∫`. Either the goal is \
                  already in that form, or the integrand's linear structure is hidden (unfold or \
                  `integral_congr_ae` first), or an integrability side condition could not be \
                  discharged by `assumption` or `fun_prop` (state it as a `have`)."
  rw [integral_const]
  simp [uMean]


-- @@ L108-114 verbatim
/-- The first projection is integrable whenever `x ↦ ∫ h(x, ·) dP` is. -/
@[fun_prop]
theorem uProj_integrable [IsFiniteMeasure P] {h : X → X → ℝ}
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P) :
    Integrable (uProj h P) P := by
  unfold uProj
  exact hint.sub (integrable_const _)


-- @@ L116-135 expanded
/-- **Degeneracy of the second-order kernel.**  For every fixed `x`,
`∫ g(x, ·) dP = 0`.  This is the defining property that makes the U-statistic's
quadratic remainder negligible at the `√n` scale. -/
theorem uDegen_integral_right_eq_zero [IsProbabilityMeasure P] {h : X → X → ℝ}
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P) (x : X) (hx : Integrable (fun y => h x y) P) :
    ∫ y, uDegen h P x y ∂P = 0 :=
  by
  have hproj_int : Integrable (uProj h P) P := uProj_integrable hint
  have hproj_zero : ∫ y, uProj h P y ∂P = 0 := uProj_integral_eq_zero hint
  have key :
    ∫ y, uDegen h P x y ∂P = (∫ y, h x y ∂P) - (∫ y, uProj h P y ∂P) - (uMean h P + uProj h P x) :=
    by
    rw [show
        (fun y => uDegen h P x y) = (fun y => (h x y - uProj h P y) - (uMean h P + uProj h P x))
        from funext fun y => by simp only [uDegen]; ring]
    first
    |
      simp (disch :=
        first
        | assumption
        | fun_prop) only [MeasureTheory.integral_add,
        MeasureTheory.integral_add', MeasureTheory.integral_sub, MeasureTheory.integral_sub',
        MeasureTheory.integral_neg, MeasureTheory.integral_neg', MeasureTheory.integral_finsetSum,
        MeasureTheory.integral_smul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_mul_const, MeasureTheory.integral_div]
    |
      fail "integral_linearity: nothing to normalize.\n\
                    The normal form is: `+`, `-`, negation, `•`, a factor independent of the \
                    integration variable, and finite sums all outside the `∫`. Either the goal is \
                    already in that form, or the integrand's linear structure is hidden (unfold or \
                    `integral_congr_ae` first), or an integrability side condition could not be \
                    discharged by `assumption` or `fun_prop` (state it as a `have`)."
    simp only [integral_const, probReal_univ, one_smul]
  rw [key, hproj_zero]
    -- goal: (∫ h x y dP) - 0 - (θ + h₁ x) = 0, where h₁ x = (∫ h x y dP) - θ
    
  unfold uProj
  ring


-- @@ L137-137 verbatim
end Causalean.Stat
