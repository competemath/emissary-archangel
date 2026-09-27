/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import LeanPool.BruhatTits.Graph.Orientation
public import LeanPool.BruhatTits.Graph.Regular
public import LeanPool.BruhatTits.Harmonic.Basic
import LeanPool.BruhatTits.Graph.Tree


-- @@ L13-18 verbatim
/-!
# Surjectivity of the Bruhat-Tits Laplacian

In this file we show that the Laplacian of the Bruhat-Tits tree is surjective.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open Module



-- @@ L25-25 verbatim
open IsLocalRing


-- @@ L27-27 verbatim
suppress_compilation


-- @@ L29-31 verbatim
namespace BruhatTits

-- Let R be a discrete valuation ring and K its field of fractions

-- @@ L32-32 verbatim
variable {K : Type*} [Field K]

-- @@ L33-33 verbatim
variable (R : Subring K) [IsDiscreteValuationRing R] [IsFractionRing R K]

-- @@ L34-34 verbatim
variable [Finite (ResidueField R)]


-- @@ L36-40 verbatim
open Classical in
/-- The Laplacian on the Bruhat-Tits tree with coefficients in any `A`-module `M`. -/
def BTlaplace (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] :
    ((BTgraph (R := R)).edgeSet → M) →ₗ[A] (Vertices R → M) :=
  (BTgraph (R := R)).laplaceLinearMap (BTweight A)


-- @@ L42-42 verbatim
variable (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]


-- @@ L44-48 verbatim
open Classical in
lemma BTlaplace_surjective : Function.Surjective (BTlaplace R A M) :=
  SimpleGraph.laplace_surjective BTtree (BTweight A) <| fun v ↦ by
    simp only [btgraph_degree, Nat.reduceLeDiff]
    apply Finite.card_pos


-- @@ L50-50 verbatim
end BruhatTits
