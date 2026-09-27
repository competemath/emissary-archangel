/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Descriptive.Topology
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import LeanPool.InfinitaryLogic.Descriptive.Measurable

-- @@ L11-37 verbatim
/-!
# Polish Space and Borel Space Structure on the Structure Space

This file proves that `StructureSpace L` is a Polish space, a Borel space, and
a standard Borel space when the language has countably many relation symbols.

## Strategy

`StructureSpace L = RelQuery L → Bool` with the product topology. When
`RelQuery L` is countable, `Encodable.ofCountable` provides an encoding, and
Mathlib's instances for products of discrete spaces give:
- `CompactSpace`, `MetrizableSpace`, `SecondCountableTopology` (from `Pi.*`)
- `IsCompletelyMetrizableSpace` (compact + metrizable → complete)
- `PolishSpace` = `SecondCountableTopology` + `IsCompletelyMetrizableSpace`
- `BorelSpace` (product σ-algebra = Borel σ-algebra for second-countable spaces)
- `StandardBorelSpace` (from `PolishSpace` + `BorelSpace`)

Since `StructureSpace L` is a `def` (not `abbrev`), type class resolution cannot
see through it. We provide the intermediate instances explicitly.

## Main Results

- `PolishSpace (StructureSpace L)`: The structure space is Polish.
- `BorelSpace (StructureSpace L)`: The product σ-algebra equals the Borel σ-algebra.
- `StandardBorelSpace (StructureSpace L)`: The structure space is standard Borel.
- Analogous instances for the pair space `StructureSpace L × StructureSpace L`.
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
universe u v


-- @@ L43-43 verbatim
namespace FirstOrder


-- @@ L45-45 verbatim
namespace Language


-- @@ L47-50 verbatim
variable (L : Language.{u, v}) [Countable (Σ l, L.Relations l)]

-- Bridge instances: StructureSpace L is a def, so TC can't unfold it.
-- We explicitly provide what Mathlib proves for `RelQuery L → Bool`.


-- @@ L52-53 verbatim
instance : SecondCountableTopology (StructureSpace L) := by
  unfold StructureSpace; infer_instance


-- @@ L55-56 verbatim
instance : TopologicalSpace.IsCompletelyMetrizableSpace (StructureSpace L) := by
  unfold StructureSpace; infer_instance


-- @@ L58-61 verbatim
/-- The structure space is Polish: second-countable and completely metrizable.
This follows from `StructureSpace L = RelQuery L → Bool` being a countable product
of finite discrete spaces, hence compact and metrizable. -/
instance : PolishSpace (StructureSpace L) := PolishSpace.mk


-- @@ L63-65 verbatim
/-- The product σ-algebra on the structure space equals the Borel σ-algebra. -/
instance : BorelSpace (StructureSpace L) := by
  unfold StructureSpace at *; infer_instance


-- @@ L67-68 verbatim
/-- The structure space is standard Borel (Polish + Borel). -/
instance : StandardBorelSpace (StructureSpace L) := inferInstance


-- @@ L70-70 verbatim
end Language


-- @@ L72-72 verbatim
end FirstOrder
