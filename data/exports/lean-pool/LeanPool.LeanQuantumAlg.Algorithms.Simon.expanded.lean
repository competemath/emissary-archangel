/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Core.Cost
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Bound.Init


-- @@ L15-38 verbatim
/-!
# Simon's problem

Simon's problem gives oracle access to a function on bit strings with an
unknown nonzero mask `s`: two inputs have the same oracle value exactly when
they are equal or differ by `s` [dW19, qcnotes.tex:1407, 1409-1410].

This module formalizes the problem at the standard post-sampling abstraction
boundary. A run of Simon's quantum circuit yields a vector `y` satisfying the
linear equation `y · s = 0` over `𝔽₂` [dW19, qcnotes.tex:1459-1460]. Once
the collected equations cut the solution set
down to `{0, s}`, any nonzero candidate satisfying all of them is the hidden
mask [dW19, qcnotes.tex:1460].

## Main results

- `LeanPool.LeanQuantumAlg.Simon.Promise` — explicit Simon promise for an oracle and hidden
  mask over bit vectors `Fin n → ZMod 2`.
- `LeanPool.LeanQuantumAlg.Simon.CompleteEquations` — the collected `𝔽₂`-linear equations
  have exactly the two expected solutions, `0` and `s`.
- `LeanPool.LeanQuantumAlg.SimonsProblem.main` — under the explicit promise and complete linear
  post-processing equations, every nonzero candidate satisfying the equations
  is the hidden nonzero mask.
-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
namespace QuantumAlg


-- @@ L44-44 verbatim
universe u


-- @@ L46-46 verbatim
namespace Simon


-- @@ L48-49 verbatim
/-- The two-element field used for Simon bit strings. -/
abbrev F₂ : Type := ZMod 2


-- @@ L51-52 verbatim
/-- An `n`-bit vector, represented as a vector space over `𝔽₂`. -/
abbrev BitVec (n : ℕ) : Type := Fin n → F₂


-- @@ L54-54 verbatim
variable {n : ℕ} {α : Type u}


-- @@ L56-58 verbatim
/-- A Simon oracle maps bit vectors to arbitrary classical values. The promise,
not the codomain representation, carries the algorithmic content. -/
abbrev Oracle (n : ℕ) (α : Type u) : Type u := BitVec n → α


-- @@ L60-62 verbatim
/-- Dot product over `𝔽₂`. -/
def dot (x y : BitVec n) : F₂ :=
  ∑ i, x i * y i


-- @@ L64-65 verbatim
/-- Two bit vectors are orthogonal when their `𝔽₂` dot product vanishes. -/
def Orthogonal (x y : BitVec n) : Prop := dot x y = 0


-- @@ L67-69 verbatim
/-- The two-element fiber relation induced by a Simon mask: `x` and `y` are
equal modulo the hidden period `s`. -/
def SameFiber (s x y : BitVec n) : Prop := y = x ∨ y = x + s


-- @@ L71-75 verbatim
/-- The explicit Simon promise: `s` is nonzero, and oracle fibers are exactly
pairs of equal inputs or inputs separated by `s`. -/
structure Promise (f : Oracle n α) (s : BitVec n) : Prop where
  nonzero : s ≠ 0
  fiber_iff : ∀ x y, f x = f y ↔ SameFiber s x y


-- @@ L77-79 verbatim
/-- A sampled Simon equation says that the sampled vector is orthogonal to a
candidate mask. -/
def SatisfiesEquation (y t : BitVec n) : Prop := Orthogonal y t


-- @@ L81-83 verbatim
/-- A candidate mask satisfies every collected linear equation. -/
def SatisfiesEquations (samples : Finset (BitVec n)) (t : BitVec n) : Prop :=
  ∀ y ∈ samples, SatisfiesEquation y t


-- @@ L85-89 verbatim
/-- The collected equations are complete when their common solution set is
exactly `{0, s}`. This is the linear-algebraic post-processing condition
implemented by Gaussian elimination over `𝔽₂`. -/
def CompleteEquations (samples : Finset (BitVec n)) (s : BitVec n) : Prop :=
  ∀ t, SatisfiesEquations samples t ↔ t = 0 ∨ t = s


-- @@ L91-93 verbatim
/-- A nonzero candidate returned by the classical post-processing step. -/
def Candidate (samples : Finset (BitVec n)) (t : BitVec n) : Prop :=
  t ≠ 0 ∧ SatisfiesEquations samples t


-- @@ L95-102 verbatim
/-- Trusted representative resource profile for the public Simon statement:
expected linear oracle samples, quadratic Hadamard gates, and cubic classical
linear algebra over `ZMod 2`. -/
def expectedResourceProfile (n : ℕ) : ResourceProfile where
  oracleQueries := n
  hadamardGates := n ^ 2
  elementaryGates := 0
  classicalOps := n ^ 3


-- @@ L104-106 verbatim
theorem expectedResourceProfile_exact (n : ℕ) :
    ResourceProfile.HasExactCounts (expectedResourceProfile n) n (n ^ 2) 0 (n ^ 3) := by
  simp [ResourceProfile.HasExactCounts, expectedResourceProfile]


-- @@ L108-110 verbatim
@[simp]
theorem dot_zero_left (x : BitVec n) : dot (0 : BitVec n) x = 0 := by
  simp [dot]


-- @@ L112-114 verbatim
@[simp]
theorem dot_zero_right (x : BitVec n) : dot x (0 : BitVec n) = 0 := by
  simp [dot]


-- @@ L116-121 verbatim
/-- The `𝔽₂` dot product is symmetric. -/
theorem dot_comm (x y : BitVec n) : dot x y = dot y x := by
  unfold dot
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [mul_comm]


-- @@ L123-126 verbatim
/-- Right additivity of the `𝔽₂` dot product. -/
theorem dot_add_right (x y z : BitVec n) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]


-- @@ L128-131 verbatim
/-- Left additivity of the `𝔽₂` dot product. -/
theorem dot_add_left (x y z : BitVec n) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]


-- @@ L133-137 verbatim
/-- The zero vector satisfies every collected Simon equation. -/
theorem satisfiesEquations_zero (samples : Finset (BitVec n)) :
    SatisfiesEquations samples (0 : BitVec n) := by
  intro y _
  simp [SatisfiesEquation, Orthogonal]


-- @@ L139-146 verbatim
/-- Sums of solutions to the collected equations are again solutions; the
solution set is a linear subspace over `𝔽₂`. -/
theorem satisfiesEquations_add {samples : Finset (BitVec n)} {a b : BitVec n}
    (ha : SatisfiesEquations samples a) (hb : SatisfiesEquations samples b) :
    SatisfiesEquations samples (a + b) := by
  intro y hy
  rw [SatisfiesEquation, Orthogonal, dot_add_right, ha y hy, hb y hy]
  simp


-- @@ L148-153 verbatim
/-- If the equations are complete, the unknown nonzero string itself satisfies all of
them. -/
theorem hiddenMask_satisfiesEquations {samples : Finset (BitVec n)}
    {s : BitVec n} (hcomplete : CompleteEquations samples s) :
    SatisfiesEquations samples s := by
  exact (hcomplete s).2 (Or.inr rfl)


-- @@ L155-164 verbatim
/-- Complete Simon equations identify the unknown nonzero string among nonzero
candidates. -/
theorem recover_from_complete_equations {samples : Finset (BitVec n)}
    {s t : BitVec n} (hcomplete : CompleteEquations samples s)
    (hcandidate : Candidate samples t) :
    t = s := by
  rcases hcandidate with ⟨ht_ne_zero, ht_eqs⟩
  rcases (hcomplete t).1 ht_eqs with ht_zero | ht_s
  · exact False.elim (ht_ne_zero ht_zero)
  · exact ht_s


-- @@ L166-174 verbatim
/-- The Simon promise determines a unique nonzero mask for an oracle. -/
theorem promise_mask_unique {f : Oracle n α} {s t : BitVec n}
    (hs : Promise f s) (ht : Promise f t) :
    s = t := by
  have hf0t : f 0 = f t := by
    exact (ht.fiber_iff 0 t).2 (Or.inr (by simp))
  rcases (hs.fiber_iff 0 t).1 hf0t with ht_zero | ht_s
  · exact False.elim (ht.nonzero ht_zero)
  · simpa using ht_s.symm


-- @@ L176-176 verbatim
end Simon


-- @@ L178-189 verbatim
/-- **Simon correctness**: assume an oracle satisfies Simon's promise with
hidden nonzero mask `s`. If the sampled `𝔽₂`-linear equations are complete
and classical post-processing returns a nonzero candidate satisfying all of
those equations, then that candidate is exactly the hidden nonzero mask. -/
theorem SimonsProblem.main {n : ℕ} {α : Type u} {f : Simon.Oracle n α}
    {s t : Simon.BitVec n} {samples : Finset (Simon.BitVec n)}
    (hpromise : Simon.Promise f s)
    (hcomplete : Simon.CompleteEquations samples s)
    (hcandidate : Simon.Candidate samples t) :
    t = s ∧ s ≠ 0 := by
  exact ⟨Simon.recover_from_complete_equations hcomplete hcandidate,
    hpromise.nonzero⟩


-- @@ L191-205 verbatim
/-- Simon supporting theorem for the public statement at the current
post-sampling boundary: complete sampled equations recover the unknown nonzero
string, and the trusted public resource profile records the accepted expected
costs. -/
theorem SimonsProblem.main_with_resources {n : ℕ} {α : Type u}
    {f : Simon.Oracle n α} {s t : Simon.BitVec n}
    {samples : Finset (Simon.BitVec n)}
    (hpromise : Simon.Promise f s)
    (hcomplete : Simon.CompleteEquations samples s)
    (hcandidate : Simon.Candidate samples t) :
    (t = s ∧ s ≠ 0) ∧
      ResourceProfile.HasExactCounts (Simon.expectedResourceProfile n) n (n ^ 2) 0 (n ^ 3) := by
  constructor
  · exact SimonsProblem.main hpromise hcomplete hcandidate
  · exact Simon.expectedResourceProfile_exact n



-- @@ L208-208 verbatim
end QuantumAlg
