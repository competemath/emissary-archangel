/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.Replication
public import LeanPool.CencovPetz.MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
import LeanPool.CencovPetz.LeftInverseIsometry
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L18-23 verbatim
/-!
# `CencovPetz.ReplicationInvariance`

For a monotone metric family (Čencov setting), replication maps `α → α × Fin m` are isometries:
they have a deterministic left inverse (coarsening), so monotonicity holds in both directions.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace LeanPool.CencovPetz

-- @@ L28-28 verbatim
open scoped BigOperators


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
variable {α : Type u} [Fintype α]


-- @@ L34-34 verbatim
namespace MonotoneMetricFamily


-- @@ L36-52 verbatim
lemma comp_eq_of_replicate (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)).comp
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α (α × Fin m) := MarkovMorphism.replicate (α := α) m hm
  let κ' : MarkovMorphism (α × Fin m) α := MarkovMorphism.coarsen (α := α) m hm
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.coarsen_pushforward_replicate
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.coarsen_tangentPushforward_replicate
        (α := α) (m := m) (hm := hm) (u := u)


-- @@ L54-71 verbatim
lemma eq_of_replicate (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforward u)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforward v)
      = G.g (α := α) p u v := by
  classical
  let κ : MarkovMorphism α (α × Fin m) := MarkovMorphism.replicate (α := α) m hm
  let κ' : MarkovMorphism (α × Fin m) α := MarkovMorphism.coarsen (α := α) m hm
  refine MonotoneMetricFamily.eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_ u v
  · simpa [κ, κ'] using
      MarkovMorphism.coarsen_pushforward_replicate
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.coarsen_tangentPushforward_replicate
        (α := α) (m := m) (hm := hm) (u := u)


-- @@ L73-73 verbatim
end MonotoneMetricFamily

-- @@ L74-74 verbatim
end LeanPool.CencovPetz
