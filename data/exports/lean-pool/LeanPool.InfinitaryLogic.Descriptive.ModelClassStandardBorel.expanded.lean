/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorel
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LeanPool.InfinitaryLogic.Descriptive.Polish

-- @@ L11-22 verbatim
/-!
# Standard Borel Structure on the Model Class

This file shows that `ModelsOf φ` (the set of coded ℕ-models of an Lω₁ω sentence φ)
inherits `StandardBorelSpace` as a measurable subspace of the structure space.

## Main Results

- `modelsOf_isClopenable`: `ModelsOf φ` is clopenable (admits a finer Polish
  topology making it clopen).
- `modelsOf_standardBorel`: The subtype `↥(ModelsOf φ)` is standard Borel.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
namespace FirstOrder


-- @@ L30-30 verbatim
namespace Language


-- @@ L32-32 verbatim
variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]


-- @@ L34-39 verbatim
/-- The subtype of coded ℕ-models of φ is standard Borel: it inherits a
standard Borel structure as a measurable subspace of the standard Borel
structure space. -/
instance modelsOf_standardBorel (φ : L.Sentenceω) :
    StandardBorelSpace ↥(ModelsOf φ) :=
  (modelsOf_measurableSet φ).standardBorel


-- @@ L41-41 verbatim
end Language


-- @@ L43-43 verbatim
end FirstOrder
