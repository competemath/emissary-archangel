/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremCOfB
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremB


-- @@ L11-15 verbatim
/-!
# Theorem C

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
section


-- @@ L21-25 verbatim
/-!
# Theorem CProvider

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L27-27 verbatim
open MeasureTheory Set Filter

-- @@ L28-28 verbatim
open scoped ENNReal NNReal Topology

-- @@ L29-29 verbatim
open CKN.Foundation.Parabolic



-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace CKN


-- @@ L36-38 verbatim
/-! This module assembles Theorem C from the gradient criterion of Theorem B
for `IsSuitableWeakSolutionIntegrable`.  It is imported by `CKN.Main.TheoremC`
and participates in the public theorem assembly. -/


-- @@ L40-62 verbatim
/-- Conditional assembly of Theorem C from the reduction in
`TheoremCOfB.lean`. -/
theorem caffarelliKohnNirenberg_provider_of_epsilonRegularityGradient
    (hB : ∀ (q : ℝ), 5 / 2 < q →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧
        ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
          (Du : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
          (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) →
          ∀ z₀ ∈ spaceTimeSet Ω I,
            Filter.limsup (fun r : ℝ =>
                (ENNReal.ofReal r)⁻¹ *
                  ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                    ENNReal.ofReal (spatialGradientSq u Du w))
              (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
            IsRegularPoint Ω I u z₀) :
    ∀ (q : ℝ), 5 / 2 < q →
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 := by
  exact caffarelliKohnNirenberg_of_epsilonRegularityGradient hB


-- @@ L64-64 verbatim
end CKN

-- @@ L65-65 verbatim
end


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
open MeasureTheory Set Filter

-- @@ L70-70 verbatim
open scoped ENNReal NNReal Topology

-- @@ L71-71 verbatim
open CKN.Foundation.Parabolic



-- @@ L74-74 verbatim
noncomputable section


-- @@ L76-76 verbatim
namespace CKN.Main


-- @@ L78-87 verbatim
/-- The parabolic singular set of a suitable weak solution has zero one dimensional Hausdorff
  measure. -/
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 := by
  exact CKN.caffarelliKohnNirenberg_provider_of_epsilonRegularityGradient
    CKN.Main.epsilonRegularityGradient q hq


-- @@ L89-89 verbatim
end CKN.Main
