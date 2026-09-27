/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems


-- @@ L10-14 verbatim
/-!
# Theorem BPaper

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory Set Filter

-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic


-- @@ L22-22 verbatim
noncomputable section

-- @@ L23-23 verbatim
namespace CKN.Main


-- @@ L25-41 verbatim
/-- The gradient regularity criterion, under the suitable weak-solution class
of `def:sws`. -/
theorem epsilonRegularityGradientPaper (q : ℝ) (hq : 5 / 2 < q) :
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
by
  exact CKN.epsilonRegularityGradient_paper q hq


-- @@ L43-43 verbatim
end CKN.Main
