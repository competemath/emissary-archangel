/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBCloser
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCollarAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorant


-- @@ L12-12 verbatim
/-! # The gradient regularity criterion for suitable weak solutions -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open MeasureTheory Set Filter

-- @@ L17-17 verbatim
open scoped ENNReal NNReal Topology

-- @@ L18-18 verbatim
open CKN.Foundation.Parabolic CKN.Core.Step4



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace CKN.Core.Endgame


-- @@ L25-40 verbatim
/-- Small scaled gradient energy implies regularity of a suitable weak solution. -/
theorem epsilonRegularityGradient_unconditional (q : ℝ) (hq : 5 / 2 < q) :
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
          IsRegularPoint Ω I u z₀ := by
  exact epsilonRegularityGradient_closer_of_small_cell_majorant q hq
    (shared_binder_of_remainder_majorant fixed_remainder_temporal_majorant_of_sws)


-- @@ L42-42 verbatim
end CKN.Core.Endgame
