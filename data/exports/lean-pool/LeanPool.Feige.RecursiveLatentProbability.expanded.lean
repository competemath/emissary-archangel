/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import LeanPool.Feige.ProductTwoPointKernel


-- @@ L10-12 verbatim
/-!
# Probability instance for the recursive latent product
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open MeasureTheory


-- @@ L18-18 verbatim
namespace Feige


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-40 verbatim
instance recursiveAugmentedLatent_isProbability
    (n : ℕ)
    (latent : Fin n → Measure AugmentedTwoPointParams)
    [∀ i, IsProbabilityMeasure (latent i)] :
    IsProbabilityMeasure (recursiveAugmentedLatent n latent) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedLatent
      infer_instance
  | succ n ih =>
      let : ∀ i : Fin n,
          IsProbabilityMeasure (latent (Fin.succ i)) :=
        fun i ↦ inferInstance
      let : IsProbabilityMeasure
          (recursiveAugmentedLatent n
            (fun i ↦ latent (Fin.succ i))) :=
        ih (fun i ↦ latent (Fin.succ i))
      unfold recursiveAugmentedLatent
      infer_instance


-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end Feige
