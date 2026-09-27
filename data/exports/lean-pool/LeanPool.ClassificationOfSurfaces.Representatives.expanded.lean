/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Positivity.Finset


-- @@ L11-17 verbatim
/-!
# Eval representatives and normal-form indices

The Lean-Eval challenge owns `Complex.ClosedUnitDisc`, `OrientableRel`, and
`NonOrientableRel`; they are imported verbatim from `LeanEval/ChallengeDeps.lean`. This file adds
only the project-owned sphere abbreviation and the index type used by the normal-form reduction.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace LeanEval

-- @@ L22-22 verbatim
namespace Topology

-- @@ L23-23 verbatim
namespace ClassificationOfSurfaces


-- @@ L25-27 verbatim
/-- The sphere branch in the eval theorem. -/
abbrev SphereRepresentative : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1


-- @@ L29-34 verbatim
/-- The named normal forms that should eventually be realized by quotient spaces. -/
inductive NormalForm where
  | sphere
  | orientable (handles boundaryComponents : ℕ)
  | nonOrientable (crosscaps boundaryComponents : ℕ)
deriving DecidableEq, Repr


-- @@ L36-45 verbatim
/-- The normal forms that actually appear in the Lean Eval conclusion.

The orientable sphere is represented by the separate sphere branch, so an orientable polygonal
normal form must have a handle or a boundary component; nonorientable forms must have at least one
crosscap. -/
def NormalForm.IsEvalAdmissible : NormalForm → Prop
  | NormalForm.sphere => True
  | NormalForm.orientable handles boundaryComponents =>
      1 ≤ handles ∨ 1 ≤ boundaryComponents
  | NormalForm.nonOrientable crosscaps _boundaryComponents => 1 ≤ crosscaps


-- @@ L47-47 verbatim
end ClassificationOfSurfaces

-- @@ L48-48 verbatim
end Topology

-- @@ L49-49 verbatim
end LeanEval
