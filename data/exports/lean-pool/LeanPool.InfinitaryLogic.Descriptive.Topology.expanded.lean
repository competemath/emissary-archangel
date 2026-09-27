/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Descriptive.StructureSpace
public import Mathlib.Topology.Constructions
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability.Init
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L16-27 verbatim
/-!
# Product Topology on the Structure Space

This file equips `StructureSpace L` with the product topology (from `RelQuery L → Bool`
with `Bool` discrete) and proves that cylinder sets are clopen.

## Main Results

- `instTopologicalSpaceStructureSpace`: Product topology on `StructureSpace L`.
- `isClopen_relHolds`: The set `{c | c q = true}` is clopen for each query `q`.
- `isOpen_relHolds`, `isClosed_relHolds`: Components of the clopen result.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
universe u v


-- @@ L33-33 verbatim
namespace FirstOrder


-- @@ L35-35 verbatim
namespace Language


-- @@ L37-37 verbatim
variable {L : Language.{u, v}}


-- @@ L39-41 verbatim
/-- `StructureSpace L` inherits the product topology from `RelQuery L → Bool`.
Since `Bool` has the discrete topology, this is the product of discrete spaces. -/
instance : TopologicalSpace (StructureSpace L) := Pi.topologicalSpace


-- @@ L43-43 verbatim
end Language


-- @@ L45-45 verbatim
end FirstOrder
