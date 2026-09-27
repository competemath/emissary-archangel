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
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
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
open Distributed2Coloring.LowerBound.N1000000StructureConstants

-- @@ L24-24 verbatim
open Distributed2Coloring.LowerBound.N1000000Witness

-- @@ L25-25 verbatim
open Distributed2Coloring.LowerBound.N1000000WedderburnData

-- @@ L26-26 verbatim
open Distributed2Coloring.LowerBound.N1000000Z


-- @@ L28-42 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SiIntGoal (r : Block) (i : Var) (p q : Fin 3) : Prop :=
  let d : DirIdx := varOrbit i
  let s : Int := N1000000Z.matGet (SiNum r i) p.1 q.1
  let g : Nat := Nat.gcd s.natAbs D
  let s' : Int := s / (g : Int)
  let D' : Nat := D / g
  if tTr[d.1]! = d.1 then
    compBasisIntEntry (r := r) (d := d) p q * Int.ofNat ((blockScales[r.1]! : Q).den * D') =
      (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r)
  else
    (compBasisIntEntry (r := r) (d := d) p q +
          compBasisIntEntry (r := r) (d := invDir d) p q) *
        Int.ofNat ((blockScales[r.1]! : Q).den * D') =
      (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r)


-- @@ L44-44 verbatim
end N1000000BCompressionCompute


-- @@ L46-46 verbatim
end Distributed2Coloring.LowerBound
