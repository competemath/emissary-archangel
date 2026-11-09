/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import ModularCurves.Vendored.RiemannRoch.FunctionField.Divisor
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.Basic


-- @@ L12-18 verbatim
/-!
# Basic divisor API aliases

This file re-exports the coordinate divisor API from `FunctionField.Divisor` under the names
used in downstream modules (`degA`, `placeDegA`), and hosts the standing
`IsFullConstantField` hypothesis.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open scoped nonZeroDivisors Polynomial RatFunc


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace FunctionField


-- @@ L28-28 verbatim
open Chart


-- @@ L30-33 verbatim
variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]


-- @@ L35-36 verbatim
/-- Backward-compatible alias for `placeDegree`. -/
abbrev placeDegA (v : PlaceA k K) : ℕ := placeDegree k K v


-- @@ L38-39 verbatim
/-- Backward-compatible alias for `deg`. -/
noncomputable abbrev degA (D : DivisorA k K) : ℤ := deg k K D


-- @@ L41-48 verbatim
/-- Every element of `K` that is algebraic over the base field `k` is already in `k`.

This is the standing hypothesis for the Stichtenoth/Serre adelic proof track. It is equivalent
to `k` being relatively algebraically closed in `K`, i.e. Mathlib's `algebraicClosure k K = ⊥`;
see `FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot`. -/
class IsFullConstantField (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  /-- Every element of `K` that is algebraic over `k` already lies in the image of `k`. -/
  algebraic_mem : ∀ x : K, IsAlgebraic k x → ∃ c : k, x = algebraMap k K c


-- @@ L50-50 verbatim
namespace IsFullConstantField


-- @@ L52-52 verbatim
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [IsFullConstantField k K]


-- @@ L54-57 verbatim
theorem mem_range {x : K} (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k K) := by
  obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem (k := k) (K := K) x hx
  exact ⟨c, hc.symm⟩


-- @@ L59-59 verbatim
end IsFullConstantField


-- @@ L61-76 verbatim
/-- `IsFullConstantField k K` is exactly the statement that `k` is relatively algebraically
closed in `K`, i.e. it coincides with Mathlib's `algebraicClosure k K = ⊥`. This identifies the
standing hypothesis with the standard field-theoretic notion. -/
theorem isFullConstantField_iff_algebraicClosure_eq_bot (k K : Type*) [Field k] [Field K]
    [Algebra k K] : IsFullConstantField k K ↔ algebraicClosure k K = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := h.algebraic_mem x (mem_algebraicClosure_iff.mp hx)
    exact (⊥ : IntermediateField k K).algebraMap_mem c
  · intro h
    refine ⟨fun x hx => ?_⟩
    have hxb : x ∈ (⊥ : IntermediateField k K) := h ▸ mem_algebraicClosure_iff.mpr hx
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hxb
    exact ⟨c, hc.symm⟩


-- @@ L78-81 verbatim
instance ratFuncIsFullConstantField : IsFullConstantField k (RatFunc k) where
  algebraic_mem x hx := by
    by_contra h
    exact RatFunc.transcendental_of_ne_C x h hx


-- @@ L83-83 verbatim
end FunctionField


-- @@ L85-85 verbatim
end
