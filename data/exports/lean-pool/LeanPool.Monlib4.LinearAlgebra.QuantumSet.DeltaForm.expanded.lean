/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L11-15 verbatim
/-!
# LeanPool.Monlib4.LinearAlgebra.QuantumSet.DeltaForm

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.QuantumSet.DeltaForm`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open scoped ComplexOrder


-- @@ L21-21 verbatim
open Coalgebra


-- @@ L23-30 verbatim
/-- Delta-form quantum sets satisfy `m ∘ comul = δ • 1` for a positive scalar `δ`. -/
class QuantumSetDeltaForm (A : Type*) [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A] where
  /-- The positive delta scalar. -/
  delta : ℂ
  /-- Positivity of the delta scalar. -/
  delta_pos : 0 < delta
  /-- Multiplication after comultiplication is scalar multiplication by delta. -/
  mul_comp_comul_eq : LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul = delta • 1


-- @@ L32-40 verbatim
/-- In delta form, `m ∘ comul` is invertible. -/
@[reducible, instance]
noncomputable def QuantumSet.DeltaForm.mulCompComulIsInvertible {A : Type*} [starAlgebra A]
  [QuantumSet A] [CoalgebraStruct ℂ A] [FiniteDimensional ℂ A] [hA2 : QuantumSetDeltaForm A] :
  Invertible (LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul) := by
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, hA2.mul_comp_comul_eq, LinearMap.ker_smul,
    Module.End.one_eq_id, LinearMap.ker_id]
  exact ne_of_gt hA2.delta_pos
