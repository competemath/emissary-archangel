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
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars16to19
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L19-21 verbatim
namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `16`.

-- @@ L22-27 verbatim
theorem siIntGoal_block0_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `17`.

-- @@ L28-33 verbatim
theorem siIntGoal_block0_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `18`.

-- @@ L34-39 verbatim
theorem siIntGoal_block0_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `19`.

-- @@ L40-43 verbatim
theorem siIntGoal_block0_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel


-- @@ L45-45 verbatim
end N1000000BCompressionCompute


-- @@ L47-47 verbatim
end Distributed2Coloring.LowerBound
