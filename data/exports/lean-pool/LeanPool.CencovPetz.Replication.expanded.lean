/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.MarkovMorphism
public import LeanPool.CencovPetz.UniformSimplex
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus



-- @@ L16-20 verbatim
/-!
# `CencovPetz.Replication`

Replication Markov morphisms `α → α × Fin m` that split each outcome into `m` copies uniformly.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace LeanPool.CencovPetz

-- @@ L25-25 verbatim
open scoped BigOperators


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
variable {α : Type u} [Fintype α]


-- @@ L31-31 verbatim
namespace MarkovMorphism


-- @@ L33-55 verbatim
/-- Replication Markov morphism `α → α × Fin m`:
each input `a` is sent uniformly to the `m` outputs `(a,i)`.

This is a standard “splitting” map used in finite Čencov uniqueness proofs. -/
noncomputable def replicate (m : ℕ) (hm : 0 < m) : MarkovMorphism α (α × Fin m) := by
  classical
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := hm_pos.ne'
  refine
    { K := fun a b => if a = b.1 then (1 : ℝ) / m else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : a = b.1 <;> simp [h, hm_pos.le]
  · intro a
    -- Sum over `α × Fin m` by splitting into a sum over `α` and over `Fin m`.
    -- `Fintype.sum_prod_type` is the fiberwise-sum identity.
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, hm0]
  · intro b
    refine ⟨b.1, ?_⟩
    simp_all


-- @@ L57-61 verbatim
lemma replicate_pushforward_apply (m : ℕ) (hm : 0 < m) (p : Simplex α) (a : α) (i : Fin m) :
    ((replicate (α := α) m hm).pushforward p).p (a, i) = p.p a / m := by
  classical
  -- Only the term `a' = a` contributes.
  simp [MarkovMorphism.pushforward_apply, replicate, mul_ite, div_eq_mul_inv]


-- @@ L63-75 verbatim
lemma replicate_pushforward_uniform [Nonempty α] (m : ℕ) (hm : 0 < m) :
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (α × Fin m) := by
        simp_all
    (replicate (α := α) m hm).pushforward (Simplex.uniform (α := α))
      =
      Simplex.uniform (α := α × Fin m) := by
  classical
  ext b
  rcases b with ⟨a, i⟩
  rw [replicate_pushforward_apply (α := α) (m := m) (hm := hm) (p := Simplex.uniform (α := α))
        (a := a) (i := i)]
  simp [Simplex.uniform_apply, div_eq_mul_inv, mul_comm]


-- @@ L77-82 verbatim
lemma replicate_tangentPushforward_apply (m : ℕ) (hm : 0 < m)
    (u : tangentSpace (α := α)) (a : α) (i : Fin m) :
    ((replicate (α := α) m hm).tangentPushforward u : α × Fin m → ℝ) (a, i) =
      (u : α → ℝ) a / m := by
  classical
  simp [MarkovMorphism.tangentPushforward_apply, replicate, mul_ite, div_eq_mul_inv]


-- @@ L84-89 verbatim
/-- Coarsening map `α × Fin m → α` that forgets the replica index. -/
noncomputable def coarsen (m : ℕ) (hm : 0 < m) : MarkovMorphism (α × Fin m) α := by
  classical
  refine MarkovMorphism.deterministic (α := α × Fin m) (β := α) Prod.fst ?_
  intro a
  refine ⟨(a, ⟨0, hm⟩), rfl⟩


-- @@ L91-126 verbatim
lemma coarsen_pushforward_replicate (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (coarsen (α := α) m hm).pushforward ((replicate (α := α) m hm).pushforward p) = p := by
  classical
  ext a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  set q : Simplex (α × Fin m) := (replicate (α := α) m hm).pushforward p
  have hq (b : α × Fin m) : q.p b = p.p b.1 / m := by
    rcases b with ⟨a', i⟩
    simpa [q] using (replicate_pushforward_apply (α := α) m hm p a' i)
  -- Coarsening is a deterministic pushforward along `Prod.fst`, so it sums `q` over the fiber.
  calc
    ((coarsen (α := α) m hm).pushforward q).p a
        = ∑ b with b.1 = a, q.p b := by
              simpa [coarsen, q] using
                (MarkovMorphism.deterministic_pushforward_apply (α := α × Fin m) (β := α)
                  (g := Prod.fst) (hg := fun a => ⟨(a, ⟨0, hm⟩), rfl⟩) q a)
    _ = ∑ b : α × Fin m, if b.1 = a then q.p b else 0 := by
          -- Convert a filtered sum to an `if`-sum.
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset (α × Fin m)))
              (p := fun b : α × Fin m => b.1 = a)
              (f := fun b => q.p b))
    _ = ∑ b : α × Fin m, if b.1 = a then p.p b.1 / m else 0 := by
          simp [hq]
    _ = p.p a := by
          -- Split the sum over `α × Fin m` and evaluate.
          have : (m : ℝ) * (p.p a * (m : ℝ)⁻¹) = p.p a := by
            -- Rearrange to use `m * m⁻¹ = 1`.
            calc
              (m : ℝ) * (p.p a * (m : ℝ)⁻¹)
                  = p.p a * ((m : ℝ) * (m : ℝ)⁻¹) := by
                      simp [mul_assoc, mul_comm]
              _ = p.p a := by simp [hm0]
          simpa [Fintype.sum_prod_type, Finset.sum_const,
            Finset.card_univ, div_eq_mul_inv] using this


-- @@ L128-161 verbatim
lemma coarsen_tangentPushforward_replicate (m : ℕ) (hm : 0 < m)
    (u : tangentSpace (α := α)) :
    (coarsen (α := α) m hm).tangentPushforward
      ((replicate (α := α) m hm).tangentPushforward u) = u := by
  classical
  ext a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  set q : tangentSpace (α := α × Fin m) := (replicate (α := α) m hm).tangentPushforward u
  have hq (b : α × Fin m) : (q : α × Fin m → ℝ) b = (u : α → ℝ) b.1 / m := by
    rcases b with ⟨a', i⟩
    simpa [q] using (replicate_tangentPushforward_apply (α := α) m hm u a' i)
  calc
    ((coarsen (α := α) m hm).tangentPushforward q : α → ℝ) a
        = ∑ b with b.1 = a, (q : α × Fin m → ℝ) b := by
              simpa [coarsen, q] using
                (MarkovMorphism.deterministic_tangentPushforward_apply (α := α × Fin m) (β := α)
                  (g := Prod.fst) (hg := fun a => ⟨(a, ⟨0, hm⟩), rfl⟩) q a)
    _ = ∑ b : α × Fin m, if b.1 = a then (q : α × Fin m → ℝ) b else 0 := by
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset (α × Fin m)))
              (p := fun b : α × Fin m => b.1 = a)
              (f := fun b => (q : α × Fin m → ℝ) b))
    _ = ∑ b : α × Fin m, if b.1 = a then (u : α → ℝ) b.1 / m else 0 := by
          simp [hq]
    _ = (u : α → ℝ) a := by
          have : (m : ℝ) * ((u : α → ℝ) a * (m : ℝ)⁻¹) = (u : α → ℝ) a := by
            calc
              (m : ℝ) * ((u : α → ℝ) a * (m : ℝ)⁻¹)
                  = (u : α → ℝ) a * ((m : ℝ) * (m : ℝ)⁻¹) := by
                      simp [mul_assoc, mul_comm]
              _ = (u : α → ℝ) a := by simp [hm0]
          simpa [Fintype.sum_prod_type, Finset.sum_const,
            Finset.card_univ, div_eq_mul_inv] using this


-- @@ L163-163 verbatim
end MarkovMorphism

-- @@ L164-164 verbatim
end LeanPool.CencovPetz
