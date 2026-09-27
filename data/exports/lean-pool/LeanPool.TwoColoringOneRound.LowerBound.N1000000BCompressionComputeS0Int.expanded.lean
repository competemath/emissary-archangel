/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntGoal
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock0
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock1
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock2
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock3
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock4
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock5
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock6
import Mathlib.Tactic.Positivity.Finset


-- @@ L18-20 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0Int
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L26-26 verbatim
namespace N1000000BCompressionCompute


-- @@ L28-36 verbatim
theorem s0IntGoal_all (r : Block) (p q : Fin 3) : S0IntGoal r p q := by
  fin_cases r <;> first
    | simpa using (s0IntGoal_block0 (p := p) (q := q))
    | simpa using (s0IntGoal_block1 (p := p) (q := q))
    | simpa using (s0IntGoal_block2 (p := p) (q := q))
    | simpa using (s0IntGoal_block3 (p := p) (q := q))
    | simpa using (s0IntGoal_block4 (p := p) (q := q))
    | simpa using (s0IntGoal_block5 (p := p) (q := q))
    | simpa using (s0IntGoal_block6 (p := p) (q := q))


-- @@ L38-38 verbatim
end N1000000BCompressionCompute


-- @@ L40-40 verbatim
end Distributed2Coloring.LowerBound

