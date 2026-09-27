/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Forms.Finiteness
public import LeanPool.JacobianDiffgeo.Forms.Genus
public import LeanPool.JacobianDiffgeo.Path.Periods
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L14-31 verbatim
/-!
# `basis`, `periodVector`, `periodSubgroup` (CC9)

Unit: jacobian-construction (`docs/design/jacobian-construction.md` §Periods, `core-choices.md`
CC9). Fixes the basis of `Form1 X` used throughout the unit and packages the period subgroup
`Λ ≤ (Fin (genus X) → ℂ)`, the ℤ-span of the period vectors of based loops at a fixed (but
arbitrary) basepoint. Basepoint-independence is not re-proved here (it is a corollary of
paths-and-integrals' `RS.period_conj`, not needed downstream): any two basepoints give loop sets
whose period vectors generate the *same* subgroup, via connecting paths and conjugation, so the
choice of basepoint below is immaterial to `periodSubgroup`.

Main declarations:
* `RS.basis X : Module.Basis (Fin (genus X)) ℂ (RS.Form1 X)` — `Module.finBasis`, so that
  `Fin (Module.finrank ℂ (Form1 X)) = Fin (genus X)` definitionally (`genus` *is*
  `Module.finrank ℂ (Form1 X)`, holomorphic-forms' `Genus.lean`).
* `RS.periodSubgroup X : AddSubgroup (Fin (genus X) → ℂ)` — `AddSubgroup.closure` of the range of
  `periodVector (basis X)` over based loops at a fixed basepoint.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
open scoped ContDiff Manifold

-- @@ L36-36 verbatim
open IsManifold Module


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace RS


-- @@ L42-43 verbatim
variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]


-- @@ L45-48 verbatim
/-- A fixed basis of `Form1 X`, indexed by `Fin (genus X)` (CC9). Definitionally
`Module.finBasis ℂ (Form1 X)`, whose index type `Fin (Module.finrank ℂ (Form1 X))` is
`Fin (genus X)` by the definition of `genus`. -/
noncomputable def basis : Basis (Fin (genus X)) ℂ (Form1 X) := Module.finBasis ℂ (Form1 X)


-- @@ L50-54 verbatim
/-- The period subgroup `Λ ≤ Fin (genus X) → ℂ`: the `ℤ`-span (as an additive subgroup) of the
period vectors of based loops at a fixed basepoint. -/
def periodSubgroup : AddSubgroup (Fin (genus X) → ℂ) :=
  AddSubgroup.closure (Set.range fun γ : Path (Classical.arbitrary X) (Classical.arbitrary X) =>
    periodVector (basis X) γ)


-- @@ L56-56 verbatim
end RS


-- @@ L58-58 verbatim
end
