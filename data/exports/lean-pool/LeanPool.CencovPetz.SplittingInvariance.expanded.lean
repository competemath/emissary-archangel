/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.Splitting
public import LeanPool.CencovPetz.MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
import LeanPool.CencovPetz.LeftInverseIsometry
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L18-24 verbatim
/-!
# `CencovPetz.SplittingInvariance`

For a monotone metric family (Čencov setting), fiberwise splitting maps `α → Σ a, Fin (m a)` are
isometries: they have a deterministic left inverse (merge), so monotonicity holds in both
directions.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace LeanPool.CencovPetz

-- @@ L29-29 verbatim
open scoped BigOperators


-- @@ L31-31 verbatim
universe u


-- @@ L33-33 verbatim
variable {α : Type u} [Fintype α]


-- @@ L35-35 verbatim
namespace MonotoneMetricFamily


-- @@ L37-57 verbatim
lemma comp_eq_of_split (G : MonotoneMetricFamily)
    (m : α → ℕ) (hm : ∀ a, 0 < m a) (p : Simplex α) :
    (G.g (α := MarkovMorphism.SplitTarget (α := α) m)
        ((MarkovMorphism.split (α := α) m hm).pushforward p)).comp
        ((MarkovMorphism.split (α := α) m hm).tangentPushforwardLinear)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α (MarkovMorphism.SplitTarget (α := α) m) :=
    MarkovMorphism.split (α := α) m hm
  let κ' : MarkovMorphism (MarkovMorphism.SplitTarget (α := α) m) α :=
    MarkovMorphism.merge (α := α) m hm
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.merge_pushforward_split
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.merge_tangentPushforward_split
        (α := α) (m := m) (hm := hm) (u := u)


-- @@ L59-80 verbatim
lemma eq_of_split (G : MonotoneMetricFamily)
    (m : α → ℕ) (hm : ∀ a, 0 < m a) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := MarkovMorphism.SplitTarget (α := α) m)
        ((MarkovMorphism.split (α := α) m hm).pushforward p)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforward u)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforward v)
      = G.g (α := α) p u v := by
  classical
  let κ : MarkovMorphism α (MarkovMorphism.SplitTarget (α := α) m) :=
    MarkovMorphism.split (α := α) m hm
  let κ' : MarkovMorphism (MarkovMorphism.SplitTarget (α := α) m) α :=
    MarkovMorphism.merge (α := α) m hm
  refine MonotoneMetricFamily.eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_ u v
  · simpa [κ, κ'] using
      MarkovMorphism.merge_pushforward_split
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.merge_tangentPushforward_split
        (α := α) (m := m) (hm := hm) (u := u)


-- @@ L82-82 verbatim
end MonotoneMetricFamily

-- @@ L83-83 verbatim
end LeanPool.CencovPetz
