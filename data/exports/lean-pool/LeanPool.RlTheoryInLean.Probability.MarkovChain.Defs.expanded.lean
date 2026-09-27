/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.Comp


-- @@ L11-13 verbatim
/-!
# LeanPool.RlTheoryInLean.Probability.MarkovChain.Defs
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open MeasureTheory MeasureTheory.Measure ProbabilityTheory.Kernel ProbabilityTheory

-- @@ L18-18 verbatim
open Finset NNReal ENNReal Preorder Function


-- @@ L20-20 verbatim
namespace ProbabilityTheory


-- @@ L22-22 verbatim
namespace MarkovChain


-- @@ L24-24 verbatim
universe u

-- @@ L25-25 verbatim
variable (S : Type u) [MeasurableSpace S]


-- @@ L27-34 verbatim
/-- A homogeneous Markov chain specified by its transition kernel and initial law. -/
structure HomMarkovChainSpec (S : Type u) [MeasurableSpace S] where
  /-- The one-step transition kernel. -/
  kernel : Kernel S S
  /-- The transition kernel is Markov. -/
  markov_kernel : IsMarkovKernel kernel
  /-- The initial distribution. -/
  init : ProbabilityMeasure S


-- @@ L36-39 verbatim
/-- Iterates of the transition kernel of a Markov chain. -/
noncomputable def Kernel.iter (κ : Kernel S S) : ℕ → Kernel S S
| 0       => Kernel.id
| (n + 1) => ((iter κ) n).comp κ


-- @@ L41-41 verbatim
end MarkovChain


-- @@ L43-43 verbatim
end ProbabilityTheory
