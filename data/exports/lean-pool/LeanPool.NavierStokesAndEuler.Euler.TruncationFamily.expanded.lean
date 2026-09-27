/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField


-- @@ L11-12 verbatim
/-! Concrete data required of compact solenoidal velocity truncations.
The actual radial-potential construction supplies this record separately. -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Set MeasureTheory EulerSmoothLimit

-- @@ L19-19 verbatim
open scoped ContDiff


-- @@ L21-21 verbatim
namespace Euler.ComparatorBridge


-- @@ L23-37 verbatim
/-- A family of smooth bounded truncations on a fixed unit time interval,
with uniform kinetic energy and agreement inside the prescribed radius. -/
structure FiniteEnergyTruncationFamily (v : Space → ℝ → Space) where
  /-- Coefficient of `FiniteEnergyTruncationFamily`, of type `ℝ → SmoothTimeField (Icc (0 : ℝ)
  1) Space Space`. -/
  coefficient : ℝ → SmoothTimeField (Icc (0 : ℝ) 1) Space Space
  /-- Energy of `FiniteEnergyTruncationFamily`, of type `ℝ`. -/
  energy : ℝ
  divergence : ∀ R, 0 < R → ∀ t x,
    EulerSmoothLimit.divergence ((coefficient R).field t : Space → Space) x = 0
  memLp : ∀ R, 0 < R → ∀ t, MemLp ((coefficient R).field t : Space → Space) 2 volume
  energy_bound : ∀ R, 0 < R → ∀ t,
    (∫ x, ‖(coefficient R).field t x‖ ^ 2) ≤ energy
  agrees : ∀ R, 0 < R → ∀ t : Icc (0 : ℝ) 1, ∀ x, ‖x‖ < R →
    (coefficient R).field t x = v x t


-- @@ L39-39 verbatim
end Euler.ComparatorBridge
