/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.FiniteModel
public import LeanPool.Erdos97ConvexOctagon.Relabelling
public import LeanPool.Erdos97ConvexOctagon.RowMasks
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateSoundness


-- @@ L13-18 verbatim
/-!
# Exhaustive coverage contradiction

The compact kernel-checked coverage certificate excludes all seven canonical
first rows.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Erdos97Octagon.RawIncidence


-- @@ L24-34 verbatim
/-- Every normalized counterexample with a canonical first row contradicts
the exhaustive coverage certificate. -/
theorem canonicalBranch_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    (hN : Q.Normalized) (hSparse : Q.PairSparse) (hBalanced : Q.Balanced)
    (rowOneIndex : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask rowOneIndex)) :
    False :=
  coverageCanonicalBranch_impossible hC hR hN hSparse hBalanced
    rowOneIndex hrowOne


-- @@ L36-36 verbatim
end Erdos97Octagon.RawIncidence
