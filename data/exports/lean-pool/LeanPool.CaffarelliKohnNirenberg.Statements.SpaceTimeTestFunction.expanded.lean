/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.Calculus.ContDiff.Operations


-- @@ L11-15 verbatim
/-!
# Space Time Test Function

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Set

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace CKN


-- @@ L27-32 verbatim
/-- The smooth compactly supported test-function class on `Ω × I` from paper label `def:sws`; its
  ordinary product space follows the test-function convention of docs/DESIGN_NOTES.md. -/
def spaceTimeTestFunction {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ω : Set Vec3) (I : Set ℝ) : Set (Vec3 × ℝ → V) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ spaceTimeSet Ω I}


-- @@ L34-34 verbatim
end CKN
