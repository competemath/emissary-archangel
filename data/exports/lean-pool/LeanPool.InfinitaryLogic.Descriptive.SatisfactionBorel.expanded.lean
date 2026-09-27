/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Descriptive.Measurable
public import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorelOn
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

-- @@ L15-28 verbatim
/-!
# Satisfaction of Lω₁ω Formulas is Borel

This file specializes the carrier-parametric result to structures on `ℕ`.

## Main Definitions

- `ModelsOfBounded`: The set of codes where a bounded formula is realized.
- `ModelsOf`: The set of codes where a sentence is realized.

## Main Results

- `modelsOf_measurableSet`: Satisfaction of any Lω₁ω sentence is measurable.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
universe u v u'


-- @@ L34-34 verbatim
namespace FirstOrder


-- @@ L36-36 verbatim
namespace Language


-- @@ L38-38 verbatim
open Structure MeasureTheory


-- @@ L40-40 verbatim
variable {L : Language.{u, v}}


-- @@ L42-42 verbatim
section Measurability


-- @@ L44-44 verbatim
variable [L.IsRelational] [Countable (Σ l, L.Relations l)]


-- @@ L46-51 verbatim
/-- The set of codes where a bounded formula is realized, given variable assignments. -/
def ModelsOfBounded
    {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    Set (StructureSpace L) :=
  {c | @BoundedFormulaω.Realize L ℕ c.toStructure α n φ v xs}


-- @@ L53-55 verbatim
/-- The set of codes where a sentence is realized. -/
def ModelsOf (φ : L.Sentenceω) : Set (StructureSpace L) :=
  ModelsOfBounded φ Empty.elim Fin.elim0


-- @@ L57-63 verbatim
omit [Countable (Σ l, L.Relations l)] in
/-- Satisfaction of any Lω₁ω sentence in a countable relational language
is measurable on the structure space. -/
theorem modelsOf_measurableSet (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) := by
  change MeasurableSet (ModelsOfOn (α := ℕ) φ)
  exact modelsOfOn_measurableSet φ


-- @@ L65-65 verbatim
end Measurability


-- @@ L67-67 verbatim
end Language


-- @@ L69-69 verbatim
end FirstOrder
