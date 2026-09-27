/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import Mathlib.Tactic.Positivity.Finset


-- @@ L11-13 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3Vars20to22
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L19-21 verbatim
namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `20`.

-- @@ L22-27 verbatim
theorem siIntGoal_block3_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `21`.

-- @@ L28-33 verbatim
theorem siIntGoal_block3_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `22`.

-- @@ L34-37 verbatim
theorem siIntGoal_block3_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  decide +kernel


-- @@ L39-39 verbatim
end N1000000BCompressionCompute


-- @@ L41-41 verbatim
end Distributed2Coloring.LowerBound
