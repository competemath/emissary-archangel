/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

-- @@ L10-32 verbatim
/-!
# Conditional Counting Dichotomy for Models

This file states the Silver–Burgess dichotomy as an explicit hypothesis, defines the
isomorphism equivalence relation on coded ℕ-models, and derives a conditional
counting theorem: for Lω₁ω sentences whose ℕ-models have bounded Scott height,
the number of isomorphism classes is either ≤ ℵ₀ or exactly 2^ℵ₀.

## Main Definitions

- `SilverBurgessDichotomy`: The Silver–Burgess dichotomy for Borel equivalence
  relations on standard Borel spaces.

The isomorphism relation `isoSetoid` this file counts is defined in
`Descriptive/StructureIsoSetoid.lean`, as the restriction of the ambient relation on
`StructureSpace L`.

## Main Results

- `counting_coded_models_dichotomy`: Conditional on `SilverBurgessDichotomy`, for
  any Lω₁ω sentence with bounded Scott height, the number of isomorphism classes
  among coded ℕ-models is either ≤ ℵ₀ or exactly 2^ℵ₀.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
universe u v w


-- @@ L38-38 verbatim
namespace FirstOrder


-- @@ L40-40 verbatim
namespace Language


-- @@ L42-42 verbatim
open Cardinal Ordinal


-- @@ L44-51 verbatim
/-- The Silver–Burgess dichotomy for Borel equivalence relations:
on a standard Borel space, a Borel equivalence relation has either
at most countably many classes or exactly continuum-many. -/
def SilverBurgessDichotomy : Prop :=
  ∀ {X : Type w} [MeasurableSpace X] [StandardBorelSpace X]
    (r : Setoid X),
    MeasurableSet {p : X × X | r.r p.1 p.2} →
    (#(Quotient r) ≤ ℵ₀) ∨ (#(Quotient r) = Cardinal.continuum)



-- @@ L54-54 verbatim
end Language


-- @@ L56-56 verbatim
end FirstOrder
