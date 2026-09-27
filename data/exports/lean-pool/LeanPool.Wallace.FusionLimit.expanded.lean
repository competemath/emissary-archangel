/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.AddCircle


-- @@ L12-19 verbatim
/-!
# Pointwise limits of character fusions

The fusion construction produces a sequence of circle-valued homomorphisms.  Every group
element is eventually protected, so its values form a Cauchy sequence.  This file isolates the
complete metric argument: the pointwise limit is again a homomorphism, and a geometric bound on
a tail gives an explicit bound from the first point of that tail to the limit.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Filter Topology

-- @@ L24-24 verbatim
open scoped ENNReal


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
namespace Wallace


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
variable {G : Type u} [AddGroup G]


-- @@ L34-46 verbatim
/-- The pointwise limit of a pointwise-Cauchy sequence of additive characters. -/
def pointwiseLimitCharacter
    (f : ℕ → G →+ UnitAddCircle)
    (hf : ∀ x, CauchySeq (fun n ↦ f n x)) : G →+ UnitAddCircle where
  toFun x := limUnder atTop (fun n ↦ f n x)
  map_zero' := by
    apply tendsto_nhds_unique (hf 0).tendsto_limUnder
    simp
  map_add' x y := by
    apply tendsto_nhds_unique (hf (x + y)).tendsto_limUnder
    have hx := (hf x).tendsto_limUnder
    have hy := (hf y).tendsto_limUnder
    simpa only [map_add] using hx.add hy


-- @@ L48-53 verbatim
/-- The defining sequence converges pointwise to `pointwiseLimitCharacter`. -/
theorem tendsto_pointwiseLimitCharacter
    (f : ℕ → G →+ UnitAddCircle)
    (hf : ∀ x, CauchySeq (fun n ↦ f n x)) (x : G) :
    Tendsto (fun n ↦ f n x) atTop (nhds (pointwiseLimitCharacter f hf x)) :=
  (hf x).tendsto_limUnder


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
end Wallace
