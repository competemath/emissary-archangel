/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs


-- @@ L12-38 verbatim
/-!

# Effect-valued measures

## i. Overview

An effect-valued measure assigns each measurable set an effect, with `∅ ↦ 0`, `univ ↦ 1`, and
countable additivity: the effects of a pairwise disjoint countable family have partial sums
(computed in `E`, since `Effect E` is not itself closed under addition) whose least upper bound
is the effect of their union.

Once `E` is the self-adjoint part of an operator algebra, `Effect E` is a set of bounded
operators and this is exactly what the physics literature calls a POVM (positive
operator-valued measure). Nothing here is an operator, though: this layer only ever needed
`Effect E` to be bounded elements of an ordered vector space, which is why the name doesn't
mention operators.

## ii. Key definitions and results

- `EffectValuedMeasure Ω E`

## iii. Table of contents

- A. Effect-valued measures
- B. Basic API

-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-43 verbatim
variable {Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [One E] [IsOrderUnit E]


-- @@ L45-45 verbatim
/-! ## A. Effect-valued measures -/


-- @@ L47-62 verbatim
/-- An effect-valued measure: `∅ ↦ 0`, `univ ↦ 1`, countably additive up to least upper bound. -/
structure EffectValuedMeasure (Ω : Type*) [MeasurableSpace Ω] (E : Type*) [AddCommGroup E]
    [PartialOrder E] [IsOrderedAddMonoid E] [One E] [IsOrderUnit E] where
  /-- The underlying assignment of outcomes to effects. -/
  toFun : ∀ s : Set Ω, MeasurableSet s → Effect E
  /-- The impossible outcome gets no weight. -/
  map_empty' : toFun ∅ MeasurableSet.empty = 0
  /-- The certain outcome gets full weight. -/
  map_univ' : toFun Set.univ MeasurableSet.univ = 1
  /-- The partial sums of a pairwise disjoint countable family have least upper bound the effect
  of their union. -/
  countably_additive' : ∀ s : ℕ → Set Ω, ∀ hsm : ∀ n, MeasurableSet (s n),
    ∀ _hs : ∀ m n, m ≠ n → Disjoint (s m) (s n),
      IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N,
        ((toFun (s n) (hsm n) : Effect E) : E))
        ((toFun (⋃ n, s n) (MeasurableSet.iUnion hsm) : Effect E) : E)


-- @@ L64-64 verbatim
namespace EffectValuedMeasure


-- @@ L66-66 verbatim
/-! ## B. Basic API -/


-- @@ L68-69 verbatim
instance : CoeFun (EffectValuedMeasure Ω E) fun _ => ∀ s : Set Ω, MeasurableSet s → Effect E where
  coe m := m.toFun


-- @@ L71-77 verbatim
@[ext]
lemma ext {μ ν : EffectValuedMeasure Ω E} (h : ∀ s hs, μ s hs = ν s hs) : μ = ν := by
  cases μ
  cases ν
  simp_all only [EffectValuedMeasure.mk.injEq]
  funext s hs
  exact h s hs


-- @@ L79-80 verbatim
@[simp]
lemma map_empty (μ : EffectValuedMeasure Ω E) : μ ∅ MeasurableSet.empty = 0 := μ.map_empty'


-- @@ L82-83 verbatim
@[simp]
lemma map_univ (μ : EffectValuedMeasure Ω E) : μ Set.univ MeasurableSet.univ = 1 := μ.map_univ'


-- @@ L85-89 verbatim
lemma countably_additive (μ : EffectValuedMeasure Ω E) (s : ℕ → Set Ω)
    (hsm : ∀ n, MeasurableSet (s n)) (hs : ∀ m n, m ≠ n → Disjoint (s m) (s n)) :
    IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, ((μ (s n) (hsm n) : Effect E) : E))
      ((μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : Effect E) : E) :=
  μ.countably_additive' s hsm hs


-- @@ L91-91 verbatim
end EffectValuedMeasure
