/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import LeanPool.Circuitlib.Circuit.Gate
public import Mathlib.CategoryTheory.Category.Basic


-- @@ L11-17 verbatim
/-! # Circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Circuit


-- @@ L23-23 verbatim
open CategoryTheory

-- @@ L24-24 verbatim
open OfNat


-- @@ L26-48 verbatim
/-- A category of circuits. -/
class CircuitCategory
    (V : outParam Type*)
    [Preorder V]
    (G : outParam Type*)
    [Gate V G]
    (C : Type u)
    [∀ n, OfNat C n]
    [Category C] where
  /-- Morphism to introduce a gate. -/
  gate (g : G) : (ofNat (Gate.inputs g) : C) ⟶ ofNat (Gate.outputs g)

  /-- Morphism to introduce a wire. -/
  stub : (ofNat 0 : C) ⟶ 1

  /-- Morphism to eliminate a wire. -/
  drop : (ofNat 1 : C) ⟶ 0

  /-- Morphism to fork a wire. -/
  fork : (ofNat 1 : C) ⟶ 2

  /-- Morphism to join two wires. -/
  join : (ofNat 2 : C) ⟶ 1


-- @@ L50-50 verbatim
end Circuit
