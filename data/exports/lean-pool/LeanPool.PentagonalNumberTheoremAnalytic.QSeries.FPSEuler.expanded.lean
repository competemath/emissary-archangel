/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FPS


-- @@ L10-20 verbatim
/-!
# FPS Euler Second Identity

We prove the Euler second identity purely algebraically in the formal power series ring:
  `qPochhammerInf(-a) = Σ_{n≥0} X^{C(n,2)} · aⁿ · (qPochhammer(X, n))⁻¹`

The proof uses the finite q-binomial theorem (which holds in any commutative ring)
and takes the limit in the pi topology. The key step is showing that the
Gaussian binomial coefficient `qBinom(N, k, X)` converges to `(qPochhammer(X, k))⁻¹`
as N → ∞.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open scoped MvPowerSeries.WithPiTopology

-- @@ L27-27 verbatim
open PowerSeries Finset


-- @@ L29-29 verbatim
namespace QSeries.FormalPowerSeries


-- @@ L31-31 verbatim
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]


-- @@ L33-41 verbatim
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The constant term of `qPochhammer X n` is 1. -/
theorem constantCoeff_qPochhammer_X (n : ℕ) :
    constantCoeff (qPochhammer (X : R⟦X⟧) n) = 1 := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [qPochhammer_succ]
    simp [map_mul, map_sub, ih]


-- @@ L43-47 verbatim
omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammer X n` is a unit in `R⟦X⟧` (its constant term is 1). -/
theorem isUnit_qPochhammer_X (n : ℕ) : IsUnit (qPochhammer (X : R⟦X⟧) n) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPochhammer_X]
  exact isUnit_one


-- @@ L49-58 verbatim
/-- `qPochhammerInf a = qPochhammer a n · qPochhammerInf (a · X^n)`. -/
theorem qPochhammerInf_eq_qPochhammer_mul (a : R⟦X⟧) (n : ℕ) :
    qPochhammerInf a = qPochhammer a n * qPochhammerInf (a * X ^ n) := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [ih, qPochhammer_succ, mul_assoc]
    congr 1
    rw [qPochhammerInf_eq_one_sub_mul]
    ring_nf


-- @@ L60-63 verbatim
/-- `qPochhammerInf X = qPochhammer X n · qPochhammerInf (X * X^n)`. -/
theorem qPochhammerInf_X_eq_qPochhammer_mul (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) = qPochhammer X n * qPochhammerInf (X * X ^ n) :=
  qPochhammerInf_eq_qPochhammer_mul X n


-- @@ L65-65 verbatim
end QSeries.FormalPowerSeries


-- @@ L67-67 verbatim
end
