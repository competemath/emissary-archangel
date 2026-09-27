/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.LeanEval.ChallengeDeps


-- @@ L10-17 verbatim
/-!
# Sanity checks for the Lean-Eval representatives

The carrier and gluing relations are vendored verbatim in `ChallengeDeps.lean`. This file proves
small project-owned consequences without changing those trusted definitions. In particular,
radius is constant across every generating identification, so it descends to both quotient
families and distinguishes the disk center from its boundary.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Complex


-- @@ L23-28 verbatim
/-- Every point produced by `bdyPtOfReal` lies on the unit circle. -/
@[simp]
theorem ClosedUnitDisc.norm_bdyPtOfReal (r : ℝ) :
    ‖(ClosedUnitDisc.bdyPtOfReal r : ℂ)‖ = 1 := by
  apply mem_sphere_zero_iff_norm.mp
  exact r.fourierChar.2


-- @@ L30-30 verbatim
end Complex


-- @@ L32-32 verbatim
namespace LeanEval

-- @@ L33-33 verbatim
namespace Topology

-- @@ L34-34 verbatim
namespace ClassificationOfSurfaces


-- @@ L36-36 verbatim
open Complex


-- @@ L38-42 verbatim
/-- Radius descends through every orientable boundary identification. -/
noncomputable def orientableQuotRadius (p n : ℕ) : Quot (OrientableRel p n) → ℝ :=
  Quot.lift (fun z : ClosedUnitDisc ↦ ‖(z : ℂ)‖) (by
    intro a b hab
    cases hab <;> simp)


-- @@ L44-49 verbatim
/-- Radius descends through every non-orientable boundary identification. -/
noncomputable def nonOrientableQuotRadius (p n : ℕ) :
    Quot (NonOrientableRel p n) → ℝ :=
  Quot.lift (fun z : ClosedUnitDisc ↦ ‖(z : ℂ)‖) (by
    intro a b hab
    cases hab <;> simp)


-- @@ L51-61 verbatim
/-- No orientable representative collapses to a point: the disk center and boundary have
different radii in the quotient. -/
theorem not_subsingleton_orientableQuot (p n : ℕ) :
    ¬Subsingleton (Quot (OrientableRel p n)) := by
  intro h
  have hcollapse :
      Quot.mk (OrientableRel p n) (0 : ClosedUnitDisc) =
        Quot.mk (OrientableRel p n) (ClosedUnitDisc.bdyPtOfReal 0) :=
    h.elim _ _
  have hradius := congrArg (orientableQuotRadius p n) hcollapse
  norm_num [orientableQuotRadius] at hradius


-- @@ L63-72 verbatim
/-- No non-orientable representative collapses to a point. -/
theorem not_subsingleton_nonOrientableQuot (p n : ℕ) :
    ¬Subsingleton (Quot (NonOrientableRel p n)) := by
  intro h
  have hcollapse :
      Quot.mk (NonOrientableRel p n) (0 : ClosedUnitDisc) =
        Quot.mk (NonOrientableRel p n) (ClosedUnitDisc.bdyPtOfReal 0) :=
    h.elim _ _
  have hradius := congrArg (nonOrientableQuotRadius p n) hcollapse
  norm_num [nonOrientableQuotRadius] at hradius


-- @@ L74-76 verbatim
/-- Regression check: the torus representative is not a point. -/
example : ¬Subsingleton (Quot (OrientableRel 1 0)) :=
  not_subsingleton_orientableQuot 1 0


-- @@ L78-80 verbatim
/-- Regression check: the projective-plane representative is not a point. -/
example : ¬Subsingleton (Quot (NonOrientableRel 1 0)) :=
  not_subsingleton_nonOrientableQuot 1 0


-- @@ L82-82 verbatim
end ClassificationOfSurfaces

-- @@ L83-83 verbatim
end Topology

-- @@ L84-84 verbatim
end LeanEval
