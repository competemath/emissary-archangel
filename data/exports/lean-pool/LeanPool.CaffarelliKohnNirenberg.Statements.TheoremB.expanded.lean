/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremB
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremBPaper
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq


-- @@ L16-20 verbatim
/-!
# Theorem B

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


-- @@ L33-47 verbatim
/-- Theorem B from paper label `thm:B`, with the gradient limsup taken in `ℝ≥0∞`. -/
theorem epsilonRegularityGradient (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolution Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ :=
by exact CKN.Main.epsilonRegularityGradientPaper q hq


-- @@ L49-49 verbatim
end CKN
