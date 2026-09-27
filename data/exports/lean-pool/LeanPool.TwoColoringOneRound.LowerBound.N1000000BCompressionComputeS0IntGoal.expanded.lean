/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
import Mathlib.Tactic.Positivity.Finset


-- @@ L11-13 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntGoal
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L19-19 verbatim
namespace N1000000BCompressionCompute


-- @@ L21-21 verbatim
open Distributed2Coloring.LowerBound.N1000000Data

-- @@ L22-22 verbatim
open Distributed2Coloring.LowerBound.N1000000WeakDuality

-- @@ L23-23 verbatim
open Distributed2Coloring.LowerBound.N1000000WedderburnData

-- @@ L24-24 verbatim
open Distributed2Coloring.LowerBound.N1000000Z


-- @@ L26-33 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev S0IntGoal (r : Block) (p q : Fin 3) : Prop :=
  let s : Int := N1000000Z.matGet (S0Num r) p.1 q.1
  let g : Nat := Nat.gcd s.natAbs D
  let s' : Int := s / (g : Int)
  let D' : Nat := D / g
  compBasisIntEntry (r := r) (d := idDirIdx) p q * Int.ofNat ((blockScales[r.1]! : Q).den * D') =
    (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r)


-- @@ L35-35 verbatim
end N1000000BCompressionCompute


-- @@ L37-37 verbatim
end Distributed2Coloring.LowerBound

