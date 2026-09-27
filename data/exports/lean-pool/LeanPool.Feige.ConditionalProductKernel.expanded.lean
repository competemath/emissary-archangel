/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import LeanPool.Feige.ProductTwoPointKernel


-- @@ L10-16 verbatim
/-!
# Conditional product law of the recursive augmented kernel

The recursively measurable kernel used for the finite mixture construction
has, at every fixed latent parameter vector, exactly the ordinary finite
product of the selected one-coordinate laws.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L22-22 verbatim
namespace Feige


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-49 verbatim
theorem recursiveAugmentedKernel_apply_eq_conditionalProduct
    (n : ℕ) (p : Fin n → AugmentedTwoPointParams) :
    recursiveAugmentedKernel n p = augmentedConditionalProduct p := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel augmentedConditionalProduct
      rw [Measure.pi_of_empty]
      congr
  | succ n ih =>
      unfold recursiveAugmentedKernel augmentedConditionalProduct
      rw [Kernel.map_apply _ (finHeadTailEquiv ℝ n).symm.measurable]
      rw [Kernel.comap_apply]
      rw [Kernel.parallelComp_apply]
      change
        Measure.map (finHeadTailEquiv ℝ n).symm
          ((augmentedTwoPointKernel (p 0)).prod
            (recursiveAugmentedKernel n
              (fun i : Fin n ↦ p (Fin.succ i)))) =
          Measure.pi (fun i : Fin (n + 1) ↦ augmentedTwoPointKernel (p i))
      rw [ih (fun i : Fin n ↦ p (Fin.succ i))]
      unfold augmentedConditionalProduct
      exact
        (measurePreserving_piFinSuccAbove
          (fun i : Fin (n + 1) ↦ augmentedTwoPointKernel (p i)) 0).symm.map_eq


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end Feige
