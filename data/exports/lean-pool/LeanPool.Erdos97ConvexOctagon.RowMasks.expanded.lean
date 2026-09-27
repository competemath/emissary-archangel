/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.Incidence
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L15-15 verbatim
/-! # Explicit row masks for the finite incidence-table search -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Erdos97Octagon.RawIncidence


-- @@ L21-23 verbatim
/-- The seven canonical first-row masks, in certificate order. -/
def canonicalRowMask : Fin 7 → UInt64 :=
  ![29, 45, 101, 225, 60, 108, 228]


-- @@ L25-30 verbatim
/-- All first-row masks in the lexicographic search order. -/
def rowOneMask : Fin 35 → UInt64 := ![
  29, 45, 77, 141, 53, 85, 149, 101, 165, 197, 57, 89, 153, 105, 169, 201,
  113, 177, 209, 225, 60, 92, 156, 108, 172, 204, 116, 180, 212, 228, 120,
  184, 216, 232, 240
]


-- @@ L32-37 verbatim
/-- All second-row masks in the lexicographic search order. -/
def rowTwoMask : Fin 35 → UInt64 := ![
  27, 43, 75, 139, 51, 83, 147, 99, 163, 195, 57, 89, 153, 105, 169, 201,
  113, 177, 209, 225, 58, 90, 154, 106, 170, 202, 114, 178, 210, 226, 120,
  184, 216, 232, 240
]


-- @@ L39-40 verbatim
/-- Order in which the direct audit assigns the five noncanonical rows. -/
def searchCentres : List Vertex := [3, 4, 7, 6, 5]


-- @@ L42-42 verbatim
end Erdos97Octagon.RawIncidence
