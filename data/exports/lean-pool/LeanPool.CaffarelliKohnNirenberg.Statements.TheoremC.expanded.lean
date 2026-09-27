/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremC
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremCPaper
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet


-- @@ L16-20 verbatim
/-!
# Theorem C

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open MeasureTheory Set Filter

-- @@ L25-25 verbatim
open scoped ENNReal NNReal Topology

-- @@ L26-26 verbatim
open CKN.Foundation.Parabolic



-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace CKN


-- @@ L33-41 verbatim
/-- Theorem C, paper label `thm:C`; as explained in docs/DESIGN_NOTES.md, it uses Mathlib's
  parabolic Hausdorff measure. -/
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 :=
by exact CKN.Main.caffarelliKohnNirenbergPaper q hq


-- @@ L43-43 verbatim
end CKN
