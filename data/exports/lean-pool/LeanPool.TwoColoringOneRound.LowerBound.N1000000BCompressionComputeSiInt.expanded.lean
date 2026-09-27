/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6
import Mathlib.Tactic.Positivity.Finset


-- @@ L18-20 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiInt
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L26-26 verbatim
namespace N1000000BCompressionCompute


-- @@ L28-38 verbatim
theorem siIntGoal_all :
    ∀ r : Block, ∀ i : Var, ∀ p q : Fin 3, SiIntGoal (r := r) (i := i) p q := by
  intro r i p q
  fin_cases r
  · simpa using (siIntGoal_block0 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block1 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block2 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block3 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block4 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block5 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block6 (i := i) (p := p) (q := q))


-- @@ L40-40 verbatim
end N1000000BCompressionCompute


-- @@ L42-42 verbatim
end Distributed2Coloring.LowerBound
