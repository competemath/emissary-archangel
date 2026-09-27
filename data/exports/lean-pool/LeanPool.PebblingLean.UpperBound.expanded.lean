/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import LeanPool.PebblingLean.Hypercube
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Bound.Init


-- @@ L13-19 verbatim
/-!
# Upper-bound scaffolding

This file records the definitions and elementary lemmas used by the
probabilistic high-demand part of the upper bound.  The probabilistic estimates
themselves are not asserted here; they will be formalized as separate lemmas.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace PebblingLean


-- @@ L25-25 verbatim
namespace Hypercube


-- @@ L27-27 verbatim
open Pebbling


-- @@ L29-32 verbatim
/-- Centers whose distance from `target` lies between the inner and outer
radii. -/
def annulus (n rIn rOut : ℕ) (target : HypercubeVertex n) : Finset (HypercubeVertex n) :=
  Finset.univ.filter fun center => rIn ≤ dist center target ∧ dist center target ≤ rOut


-- @@ L34-38 verbatim
@[simp]
theorem mem_annulus {n rIn rOut : ℕ} {target center : HypercubeVertex n} :
    center ∈ annulus n rIn rOut target ↔
      rIn ≤ dist center target ∧ dist center target ≤ rOut := by
  simp [annulus]


-- @@ L40-46 verbatim
/-- Contribution of one stack of size `2^rOut` at `center` toward `target`,
counting only centers in the annulus. -/
def annulusContribution {n : ℕ} (rIn rOut : ℕ) (target center : HypercubeVertex n) : ℕ :=
  if rIn ≤ dist center target ∧ dist center target ≤ rOut then
    2 ^ (rOut - dist center target)
  else
    0


-- @@ L48-52 verbatim
theorem annulusContribution_eq_of_mem {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∈ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 2 ^ (rOut - dist center target) := by
  simp [annulusContribution, mem_annulus.mp hmem]


-- @@ L54-60 verbatim
theorem annulusContribution_eq_zero_of_notMem {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∉ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 0 := by
  have hnot : ¬ (rIn ≤ dist center target ∧ dist center target ≤ rOut) := by
    simp_all
  simp [annulusContribution, hnot]


-- @@ L62-70 verbatim
/-- One annulus contribution is bounded by the stack size `2^rOut`. -/
theorem annulusContribution_le_stackSize {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ rOut := by
  unfold annulusContribution
  by_cases h : rIn ≤ dist center target ∧ dist center target ≤ rOut
  · simpa [h] using
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le rOut (dist center target))
  · simp [h]


-- @@ L72-82 verbatim
/-- If the center is counted, the annulus contribution is bounded by the width
of the annulus rather than by the full stack size. -/
theorem annulusContribution_le_width {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ (rOut - rIn) := by
  unfold annulusContribution
  by_cases h : rIn ≤ dist center target ∧ dist center target ≤ rOut
  · have hsub : rOut - dist center target ≤ rOut - rIn :=
      tsub_le_tsub_left h.1 rOut
    simpa [h] using Nat.pow_le_pow_right (by decide : 0 < 2) hsub
  · simp [h]


-- @@ L84-99 verbatim
/-- The square bound used in the Bernstein step: `Z^2 ≤ B_0 Z`, where
`B_0 = 2^(rOut-rIn)` is the annulus-width contribution bound. -/
theorem annulusContribution_sq_le_width_mul {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ^ 2 ≤
      2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by
  have hle := annulusContribution_le_width (rIn := rIn) (rOut := rOut) target center
  calc
    annulusContribution rIn rOut target center ^ 2
        = annulusContribution rIn rOut target center *
          annulusContribution rIn rOut target center := by
          rw [pow_two]
    _ ≤ annulusContribution rIn rOut target center * 2 ^ (rOut - rIn) := by
          exact Nat.mul_le_mul_left _ hle
    _ = 2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by
          rw [Nat.mul_comm]


-- @@ L101-105 verbatim
/-- The total annulus contribution of a finite list of centers to a fixed
target. This is the Lean version of `X_t` in the proof. -/
def annulusTotalContribution {n : ℕ} (rIn rOut : ℕ) (target : HypercubeVertex n)
    (centers : List (HypercubeVertex n)) : ℕ :=
  (centers.map (annulusContribution rIn rOut target)).sum


-- @@ L107-114 verbatim
/-- The high-demand conclusion used as a target for the probabilistic lemma:
a `T`-solvable distribution whose size is bounded and whose occupied piles are
large. -/
def HasHighDemandDistribution (n T : ℕ) (costBound minPile : ℕ) : Prop :=
  ∃ D : Pebbling (HypercubeVertex n),
    size D ≤ costBound ∧
      SolvableAtLeast (graph n) D T ∧
        MinOccupiedPileSize D minPile


-- @@ L116-121 verbatim
theorem HasHighDemandDistribution.to_hasSolvableAtMostSize
    {n T costBound minPile : ℕ}
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasSolvableAtMostSize (graph n) T costBound := by
  rcases h with ⟨D, hsize, hsolv, _hmin⟩
  exact ⟨D, hsize, hsolv⟩


-- @@ L123-127 verbatim
theorem HasHighDemandDistribution.to_ordinary_hasSolvableAtMostSize
    {n T costBound minPile : ℕ} (hT : 1 ≤ T)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasSolvableAtMostSize (graph n) 1 costBound :=
  Pebbling.hasSolvableAtMostSize_mono_demand hT h.to_hasSolvableAtMostSize


-- @@ L129-134 verbatim
theorem HasHighDemandDistribution.mono_cost {n T costBound costBound' minPile : ℕ}
    (hcost : costBound ≤ costBound')
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound' minPile := by
  rcases h with ⟨D, hsize, hsolv, hmin⟩
  exact ⟨D, hsize.trans hcost, hsolv, hmin⟩


-- @@ L136-141 verbatim
theorem HasHighDemandDistribution.mono_minPile {n T costBound minPile minPile' : ℕ}
    (hminPile : minPile' ≤ minPile)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound minPile' := by
  rcases h with ⟨D, hsize, hsolv, hmin⟩
  exact ⟨D, hsize, hsolv, fun v hv => hminPile.trans (hmin v hv)⟩


-- @@ L143-148 verbatim
theorem HasHighDemandDistribution.mono
    {n T costBound costBound' minPile minPile' : ℕ}
    (hcost : costBound ≤ costBound') (hminPile : minPile' ≤ minPile)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound' minPile' :=
  (h.mono_cost hcost).mono_minPile hminPile


-- @@ L150-152 verbatim
/-- The constant distribution with `S` pebbles on every vertex. -/
def constantDistribution (n S : ℕ) : Pebbling (HypercubeVertex n) :=
  fun _ => S


-- @@ L154-156 verbatim
theorem size_constantDistribution (n S : ℕ) :
    size (constantDistribution n S) = 2 ^ n * S := by
  simp [constantDistribution, size, Finset.sum_const]


-- @@ L158-161 verbatim
theorem solvableAtLeast_constantDistribution (n S : ℕ) :
    SolvableAtLeast (graph n) (constantDistribution n S) S := by
  intro target
  exact ⟨constantDistribution n S, Relation.ReflTransGen.refl, by simp [constantDistribution]⟩


-- @@ L163-166 verbatim
theorem minOccupiedPileSize_constantDistribution (n S : ℕ) :
    MinOccupiedPileSize (constantDistribution n S) S := by
  intro v _hv
  simp [constantDistribution]


-- @@ L168-172 verbatim
theorem hasHighDemandDistribution_constant (n S : ℕ) :
    HasHighDemandDistribution n S (2 ^ n * S) S := by
  exact ⟨constantDistribution n S, by rw [size_constantDistribution],
    solvableAtLeast_constantDistribution n S,
    minOccupiedPileSize_constantDistribution n S⟩


-- @@ L174-174 verbatim
end Hypercube


-- @@ L176-176 verbatim
end PebblingLean
