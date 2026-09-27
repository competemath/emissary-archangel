/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.PackageTransport
public import LeanPool.Wallace.RationalAssembly
import Mathlib.CategoryTheory.Category.Init
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.NumberField.Basic


-- @@ L14-20 verbatim
/-!
# The rational proposition on the additive group of real numbers

The paper writes `ℚ^(𝔠) ≅ ℝ`.  This module formalizes that algebraic identification using the
rational Hamel dimension of `ℝ`, then transports the fully constructed character package rather
than merely asserting that a suitable topology can be transferred.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open Cardinal Module


-- @@ L26-26 verbatim
namespace Wallace


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open RationalTriangularPreprocess


-- @@ L32-34 verbatim
theorem rank_continuumRationalGroup :
  Module.rank ℚ ContinuumRationalGroup = 𝔠 := by
  rw [rank_finsupp_self', TriangularPreprocess.mk_continuumIndex]


-- @@ L36-39 verbatim
/-- A rational-linear equivalence `ℚ^(𝔠) ≃ₗ[ℚ] ℝ`. -/
def continuumRationalGroupLinearEquivReal : ContinuumRationalGroup ≃ₗ[ℚ] ℝ :=
  Classical.choice <| nonempty_linearEquiv_of_rank_eq <| by
    rw [rank_continuumRationalGroup, Real.rank_rat_real]


-- @@ L41-43 verbatim
/-- The algebraic isomorphism explicitly invoked in the paper's rational proposition. -/
def continuumRationalGroupAddEquivReal : ContinuumRationalGroup ≃+ ℝ :=
  continuumRationalGroupLinearEquivReal.toAddEquiv


-- @@ L45-48 verbatim
/-- The concrete rational character package transported to the additive group of real numbers. -/
def realFullCharacterPackage : FullCharacterPackage ℝ :=
  RationalAssembly.fullCharacterPackage.comapAddEquiv
    continuumRationalGroupAddEquivReal.symm


-- @@ L50-54 verbatim
/-- **Rational proposition of the paper, in its literal real-group form.**  The additive group
of real numbers admits a Hausdorff countably compact group topology in which every convergent
sequence is eventually constant. -/
theorem realAdditiveGroup_mainTheorem : HasMainGroupTopology ℝ :=
  realFullCharacterPackage.hasMainGroupTopology


-- @@ L56-61 verbatim
/-- A single declaration recording both presentations used in the paper,
`ℚ^(𝔠)` and the additively isomorphic group `ℝ`. -/
theorem continuumRationalGroup_and_real_mainTheorem :
    HasMainGroupTopology ContinuumRationalGroup ∧ HasMainGroupTopology ℝ :=
  ⟨RationalAssembly.continuumRationalGroup_mainTheorem,
    realAdditiveGroup_mainTheorem⟩


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end Wallace
