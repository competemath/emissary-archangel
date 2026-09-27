/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import LeanPool.PebblingLean.Basic
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators


-- @@ L13-19 verbatim
/-!
# Product constructions

This file begins the deterministic part of the upper-bound proof.  The main
result here is the slice simulation lemma: a pebbling sequence in one factor of
a Cartesian product can be executed inside a fixed slice of the product.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace PebblingLean


-- @@ L25-25 verbatim
universe u v


-- @@ L27-27 verbatim
namespace Graph


-- @@ L29-29 verbatim
variable {V : Type u} {W : Type v}


-- @@ L31-44 verbatim
/-- Cartesian product of simple graphs. -/
def cartesianProduct (G : Graph V) (H : Graph W) : Graph (V × W) where
  Adj p q :=
    (G.Adj p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ H.Adj p.2 q.2)
  symm := by
    intro p q h
    rcases h with h | h
    · exact Or.inl ⟨G.symm h.1, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, H.symm h.2⟩
  loopless := by
    intro p h
    rcases h with h | h
    · exact (G.loopless p.1) h.1
    · exact (H.loopless p.2) h.2


-- @@ L46-46 verbatim
end Graph


-- @@ L48-48 verbatim
namespace Pebbling


-- @@ L50-50 verbatim
variable {V : Type u} {W : Type v}



-- @@ L53-56 verbatim
/-- A product distribution assembled from first-factor fibers indexed by the
second factor.  The value at `(x, z)` is the value of the `z`-fiber at `x`. -/
def fibersDistribution (F : W → Pebbling V) : Pebbling (V × W) :=
  fun p => F p.2 p.1


-- @@ L58-61 verbatim
@[simp]
theorem fibersDistribution_apply (F : W → Pebbling V) (x : V) (z : W) :
    fibersDistribution F (x, z) = F z x :=
  rfl


-- @@ L63-66 verbatim
/-- Replace one first-factor fiber in a family of fibers. -/
def replaceFiber [DecidableEq W] (F : W → Pebbling V) (z : W) (E : Pebbling V) :
    W → Pebbling V :=
  fun z' => if z' = z then E else F z'


-- @@ L68-71 verbatim
/-- The family obtained by replacing all fibers in `s` by their target fibers. -/
def updateFibers [DecidableEq W] (F F' : W → Pebbling V) (s : Finset W) :
    W → Pebbling V :=
  fun z => if z ∈ s then F' z else F z


-- @@ L73-80 verbatim
/-- Total size of a fiber-assembled product distribution. -/
theorem size_fibersDistribution [Fintype V] [Fintype W] (F : W → Pebbling V) :
    size (fibersDistribution F) = ∑ z, size (F z) := by
  classical
  rw [size]
  change (∑ p : V × W, F p.2 p.1) = ∑ z : W, size (F z)
  rw [Fintype.sum_prod_type_right]
  simp [size]


-- @@ L82-88 verbatim
/-- A pointwise fiber cost bound gives a product cost bound. -/
theorem size_fibersDistribution_le [Fintype V] [Fintype W] {F : W → Pebbling V}
    {cost : W → ℕ} (hcost : ∀ z : W, size (F z) ≤ cost z) :
    size (fibersDistribution F) ≤ ∑ z, cost z := by
  classical
  rw [size_fibersDistribution]
  exact Finset.sum_le_sum fun z _ => hcost z


-- @@ L90-93 verbatim
/-- A distribution supported in the slice `{x} × W`, with profile `E` in the
second coordinate. -/
def sliceDistribution [DecidableEq V] (x : V) (E : Pebbling W) : Pebbling (V × W) :=
  fun p => if p.1 = x then E p.2 else 0


-- @@ L95-98 verbatim
@[simp]
theorem sliceDistribution_apply_on [DecidableEq V] (x : V) (E : Pebbling W) (z : W) :
    sliceDistribution x E (x, z) = E z := by
  simp [sliceDistribution]


-- @@ L100-104 verbatim
@[simp]
theorem sliceDistribution_apply_off [DecidableEq V] {x x' : V} (E : Pebbling W) (z : W)
    (h : x' ≠ x) :
    sliceDistribution x E (x', z) = 0 := by
  simp [sliceDistribution, h]


-- @@ L106-136 verbatim
/-- One move in the first factor can be replayed inside a fixed fiber of the
Cartesian product, leaving all other fibers unchanged. -/
theorem replaceFiber_move_left [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hmove : Move G E F) :
    Move (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by
  rcases hmove with ⟨u, v, huv, hE, rfl⟩
  refine ⟨(u, z), (v, z), ?_, ?_, ?_⟩
  · exact Or.inl ⟨huv, rfl⟩
  · simpa [fibersDistribution, replaceFiber] using hE
  · funext p
    cases p with
    | mk x z' =>
      by_cases hz' : z' = z
      · subst z'
        by_cases hxu : x = u
        · subst x
          simp [fibersDistribution, replaceFiber, moveDistribution]
        · by_cases hxv : x = v
          · subst x
            have hvu : v ≠ u := by
              simp_all
            simp [fibersDistribution, replaceFiber, moveDistribution, hvu]
          · simp [fibersDistribution, replaceFiber, moveDistribution, hxu, hxv]
      · have hp_ne_from : (x, z') ≠ (u, z) := by
          simp_all
        have hp_ne_to : (x, z') ≠ (v, z) := by
          simp_all
        simp [fibersDistribution, replaceFiber, moveDistribution, hz', hp_ne_from, hp_ne_to]


-- @@ L138-151 verbatim
/-- A pebbling sequence in the first factor can be replayed inside a fixed
fiber of the product. -/
theorem replaceFiber_reaches_left [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hreach : Reaches G E F) :
    Reaches (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ hfiber
    exact Relation.ReflTransGen.head
      (replaceFiber_move_left (G := G) (H := H) (Fs := Fs) (z := z) hmove) hfiber


-- @@ L153-214 verbatim
/-- Independent first-factor preparations in every fiber can be composed into
one product pebbling sequence. -/
theorem fibers_reaches_of_forall_reaches [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {F F' : W → Pebbling V}
    (hreach : ∀ z : W, Reaches G (F z) (F' z)) :
    Reaches (Graph.cartesianProduct G H) (fibersDistribution F) (fibersDistribution F') := by
  classical
  let := Fintype.ofFinite W
  have hstep :
      ∀ s : Finset W,
        Reaches (Graph.cartesianProduct G H)
          (fibersDistribution F)
          (fibersDistribution (updateFibers F F' s)) := by
    intro s
    refine Finset.induction_on s ?base ?insert
    · have hbase :
          fibersDistribution (updateFibers F F' ∅) = fibersDistribution F := by
        funext p
        cases p with
        | mk x z =>
          simp [fibersDistribution, updateFibers]
      rw [hbase]
      exact Relation.ReflTransGen.refl
    · intro z s hz_not_mem ih
      have hreplace :
          Reaches (Graph.cartesianProduct G H)
            (fibersDistribution (replaceFiber (updateFibers F F' s) z (F z)))
            (fibersDistribution (replaceFiber (updateFibers F F' s) z (F' z))) :=
        replaceFiber_reaches_left (G := G) (H := H)
          (Fs := updateFibers F F' s) (z := z) (hreach z)
      have hstart :
          fibersDistribution (replaceFiber (updateFibers F F' s) z (F z)) =
            fibersDistribution (updateFibers F F' s) := by
        funext p
        cases p with
        | mk x z' =>
          by_cases hz' : z' = z
          · subst z'
            simp [fibersDistribution, replaceFiber, updateFibers, hz_not_mem]
          · simp [fibersDistribution, replaceFiber, updateFibers, hz']
      have hfinish :
          fibersDistribution (replaceFiber (updateFibers F F' s) z (F' z)) =
            fibersDistribution (updateFibers F F' (insert z s)) := by
        funext p
        cases p with
        | mk x z' =>
          by_cases hz' : z' = z
          · subst z'
            simp [fibersDistribution, replaceFiber, updateFibers]
          · simp [fibersDistribution, replaceFiber, updateFibers, hz']
      have hreplace' :
          Reaches (Graph.cartesianProduct G H)
            (fibersDistribution (updateFibers F F' s))
            (fibersDistribution (updateFibers F F' (insert z s))) := by
        simpa [hstart, hfinish] using hreplace
      exact Relation.ReflTransGen.trans ih hreplace'
  have hfinal : fibersDistribution (updateFibers F F' Finset.univ) = fibersDistribution F' := by
    funext p
    cases p with
    | mk x z =>
      simp [fibersDistribution, updateFibers]
  simpa [hfinal] using hstep Finset.univ


-- @@ L216-238 verbatim
/-- One move in the second factor can be replayed inside a fixed product slice. -/
theorem slice_move_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hmove : Move H E F) :
    Move (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by
  rcases hmove with ⟨u, v, huv, hE, rfl⟩
  refine ⟨(x, u), (x, v), ?_, ?_, ?_⟩
  · exact Or.inr ⟨rfl, huv⟩
  · simpa [sliceDistribution] using hE
  · funext p
    by_cases hpx : p.1 = x
    · cases p with
      | mk x' z =>
        simp only at hpx
        subst x'
        by_cases hzu : z = u
        · simp_all
        · by_cases hzv : z = v
          · simp_all
          · simp [sliceDistribution, moveDistribution, hzu, hzv]
    · cases p with
      | mk x' z =>
        simp_all


-- @@ L240-250 verbatim
/-- A pebbling sequence in the second factor can be replayed inside a fixed
slice of the product. -/
theorem slice_reaches_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hreach : Reaches H E F) :
    Reaches (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ hslice
    exact Relation.ReflTransGen.head (slice_move_right (G := G) (H := H) (x := x) hmove) hslice


-- @@ L252-260 verbatim
/-- If `E` solves a target in the second factor, then the corresponding slice
distribution solves the corresponding product target. -/
theorem slice_canReachAtLeast_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E : Pebbling W} {x : V} {target : W} {T : ℕ}
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) (sliceDistribution x E) (x, target) T := by
  rcases hcan with ⟨F, hreach, htarget⟩
  exact ⟨sliceDistribution x F, slice_reaches_right (G := G) (H := H) (x := x) hreach, by
    simpa using htarget⟩


-- @@ L262-271 verbatim
/-- Once a product distribution dominates a prepared slice, any target reachable
from the slice is also reachable from the product distribution. -/
theorem canReachAtLeast_of_dominates_slice_right [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hdom : Dominates D (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T :=
  canReachAtLeast_of_dominates
    (slice_canReachAtLeast_right (G := G) (H := H) (x := x) hcan) hdom


-- @@ L273-286 verbatim
/-- Composition bridge for the deterministic product step: if a first phase
reaches a distribution dominating the prepared slice `{x} × W`, then a solution
inside the `W` factor can be appended to solve the product target. -/
theorem canReachAtLeast_after_prepared_slice_right [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D Dprep : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hprepReach : Reaches (Graph.cartesianProduct G H) D Dprep)
    (hprepDom : Dominates Dprep (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T := by
  rcases canReachAtLeast_of_dominates_slice_right (G := G) (H := H)
      (D := Dprep) (E := E) (x := x) hprepDom hcan with
    ⟨Dfinish, hfinishReach, htarget⟩
  exact ⟨Dfinish, Relation.ReflTransGen.trans hprepReach hfinishReach, htarget⟩


-- @@ L288-306 verbatim
/-- If every fiber can prepare the number of pebbles prescribed by `E` at the
same first-coordinate target `x`, then the product distribution can be moved to
a distribution dominating the slice `{x} × W` with profile `E`. -/
theorem fibers_prepare_slice_right [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V} {x : V}
    (hcan : ∀ z : W, CanReachAtLeast G (F z) x (E z)) :
    ∃ Dprep : Pebbling (V × W),
      Reaches (Graph.cartesianProduct G H) (fibersDistribution F) Dprep ∧
        Dominates Dprep (sliceDistribution x E) := by
  classical
  choose F' hreach htarget using hcan
  refine ⟨fibersDistribution F', ?_, ?_⟩
  · exact fibers_reaches_of_forall_reaches (G := G) (H := H) hreach
  · intro p
    cases p with
    | mk v z =>
      by_cases hv : v = x
      · simp_all
      · simp [fibersDistribution, sliceDistribution, hv]


-- @@ L308-324 verbatim
/-- Deterministic product step.  If `E` solves `H`, and each `z`-fiber has
enough demand-solvability in `G` to prepare `E z` pebbles at any chosen
first-coordinate target, then the assembled product distribution solves
`G □ H`. -/
theorem solvable_product_of_fiber_demands [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V}
    (hE : Solvable H E)
    (hF : ∀ z : W, SolvableAtLeast G (F z) (E z)) :
    Solvable (Graph.cartesianProduct G H) (fibersDistribution F) := by
  intro target
  rcases target with ⟨x, y⟩
  rcases fibers_prepare_slice_right (G := G) (H := H) (E := E) (F := F) (x := x)
      (fun z => hF z x) with
    ⟨Dprep, hprepReach, hprepDom⟩
  exact canReachAtLeast_after_prepared_slice_right (G := G) (H := H)
    (D := fibersDistribution F) (Dprep := Dprep) (E := E) (x := x) (target := y)
    hprepReach hprepDom (hE y)


-- @@ L326-352 verbatim
/-- Costed form of the deterministic product step, matching the recursive
upper-bound bookkeeping: only occupied vertices of `E` need nonzero demand
distributions in the first factor. -/
theorem hasSolvableAtMostSize_product_of_fiber_demands
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {cost : W → ℕ}
    (hE : Solvable H E)
    (hcost : ∀ z : W, E z ≠ 0 → HasSolvableAtMostSize G (E z) (cost z)) :
    HasSolvableAtMostSize (Graph.cartesianProduct G H) 1
      (∑ z, if E z = 0 then 0 else cost z) := by
  classical
  let F : W → Pebbling V := fun z =>
    if hz : E z = 0 then (fun _ : V => 0) else Classical.choose (hcost z hz)
  have hFsolv : ∀ z : W, SolvableAtLeast G (F z) (E z) := by
    intro z
    by_cases hz : E z = 0
    · rw [hz]
      exact solvableAtLeast_zero G (F z)
    · simpa [F, hz] using (Classical.choose_spec (hcost z hz)).2
  have hFsize : ∀ z : W, size (F z) ≤ if E z = 0 then 0 else cost z := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz]
    · simpa [F, hz] using (Classical.choose_spec (hcost z hz)).1
  refine ⟨fibersDistribution F, ?_, ?_⟩
  · exact size_fibersDistribution_le hFsize
  · exact solvable_product_of_fiber_demands (G := G) (H := H) hE hFsolv


-- @@ L354-354 verbatim
end Pebbling


-- @@ L356-356 verbatim
end PebblingLean
