/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

-- @@ L18-34 verbatim
/-!
# Shannon.Entropy.Core

Foundational definitions for the Shannon characterization development:

- finite probability distributions (`ProbDist`);
- Shannon-style condition bundle (`ShannonEntropyAxioms`);
- basic constructions used in all later phases
  (`uniformPNat`, `composeProb`, `relabelProb`).

Global roadmap (matching Shannon Appendix 2):
1. Equiprobable case: `Apos H (n * m) = Apos H n + Apos H m`, then `Apos H n = K * log n`.
2. Rational case: grouped equiprobable refinement implies
   `H p = -K * ∑ p_i log p_i` for rational probabilities.
3. Real case: floor-count rational approximants `approxProb p N` converge to `p`;
   continuity upgrades the rational formula to all real probabilities.
-/


-- @@ L36-36 verbatim
@[expose] public section

-- @@ L37-37 verbatim
namespace LeanPool.Shannon1948Formalization


-- @@ L39-39 verbatim
noncomputable section

-- @@ L40-40 verbatim
open Filter

-- @@ L41-41 verbatim
open scoped Topology


-- @@ L43-45 verbatim
/-- `p` has nonnegative masses that sum to one. -/
def IsProbDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1


-- @@ L47-51 verbatim
/--
A probability distribution over a finite type `α`, bundled with simplex proofs.
This keeps API signatures clean (no separate `IsProbDist` assumptions everywhere).
-/
abbrev ProbDist (α : Type) [Fintype α] := {p : α → ℝ // IsProbDist p}


-- @@ L53-54 verbatim
instance {α : Type} [Fintype α] : CoeFun (ProbDist α) (fun _ => α → ℝ) where
  coe p := p.1


-- @@ L56-57 verbatim
lemma prob_nonneg {α : Type} [Fintype α] (p : ProbDist α) (a : α) : 0 ≤ p a :=
  p.2.1 a


-- @@ L59-60 verbatim
lemma prob_sum_eq_one {α : Type} [Fintype α] (p : ProbDist α) : (∑ a, p a) = 1 :=
  p.2.2


-- @@ L62-63 verbatim
lemma prob_le_one {α : Type} [Fintype α] (p : ProbDist α) (a : α) : p a ≤ 1 :=
  (prob_sum_eq_one p) ▸ Finset.single_le_sum (fun b _ => prob_nonneg p b) (Finset.mem_univ a)


-- @@ L65-68 verbatim
/-- Uniform distribution on `Fin (n + 1)`. -/
def uniformFin (n : ℕ) : ProbDist (Fin (n + 1)) :=
  ⟨fun _ => 1 / (n + 1 : ℝ), fun _ => by positivity,
    by simp [Finset.card_univ, show (n + 1 : ℝ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n]⟩


-- @@ L70-76 verbatim
/--
Uniform distribution on `Fin n` for positive natural `n : ℕ+`.
This avoids `n + 1` index gymnastics when formalizing Appendix 2.
-/
def uniformPNat (n : ℕ+) : ProbDist (Fin n) :=
  ⟨fun _ => 1 / (n : ℝ), fun _ => by positivity,
    by simp [Finset.card_univ, show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt n.2]⟩


-- @@ L78-88 verbatim
/-- Composite distribution for a two-stage random choice. -/
def composeProb
    {α : Type} [Fintype α]
    {β : α → Type} [∀ a, Fintype (β a)]
    (p : ProbDist α)
    (q : (a : α) → ProbDist (β a)) :
    ProbDist (Sigma β) :=
  ⟨fun x => p x.1 * q x.1 x.2,
    fun x => mul_nonneg (prob_nonneg p x.1) (prob_nonneg (q x.1) x.2),
    by simp_rw [Fintype.sum_sigma, ← Finset.mul_sum, prob_sum_eq_one (q _), mul_one,
        prob_sum_eq_one p]⟩


-- @@ L90-94 verbatim
/-- Equivalence between two-stage finite outcomes and `Fin (n * m)`. -/
def sigmaConstFinEquivFinMul (n m : ℕ+) :
    Sigma (fun _ : Fin n => Fin m) ≃ Fin (n * m : ℕ+) :=
  (Equiv.sigmaEquivProdOfEquiv (fun _ : Fin n => (Equiv.refl (Fin m)))).trans
    finProdFinEquiv


-- @@ L96-106 verbatim
/--
Relabel a distribution along an equivalence of finite types.
This is the formal "event names do not matter" transport map.
-/
def relabelProb
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β)
    (p : ProbDist α) :
    ProbDist β :=
  ⟨fun b => p (e.symm b), fun b => prob_nonneg p (e.symm b),
    by simpa using (e.symm.sum_comp (fun a => p a)).trans (prob_sum_eq_one p)⟩


-- @@ L108-135 verbatim
/--
Shannon's three conditions for a finite-choice uncertainty functional `H`.
The final theorem will show any such `H` has entropy form up to a positive scale.
-/
structure ShannonEntropyAxioms
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ) : Prop where
  /-- Continuity in probabilities (for each finite alphabet). -/
  continuous :
    ∀ {α : Type} [Fintype α], Continuous fun p : ProbDist α => H p

  /-- On uniform distributions, uncertainty is monotone in alphabet size. -/
  uniformMonotone :
    StrictMono fun n : ℕ+ => H (uniformPNat n)

  /-- Invariance under relabeling outcomes by a finite equivalence. -/
  relabelInvariant :
    ∀ {α β : Type} [Fintype α] [Fintype β]
      (e : α ≃ β)
      (p : ProbDist α),
      H (relabelProb e p) = H p

  /-- Grouping (recursivity): a two-stage choice decomposes additively. -/
  grouping :
    ∀ {α : Type} [Fintype α]
      {β : α → Type} [∀ a, Fintype (β a)]
      (p : ProbDist α)
      (q : (a : α) → ProbDist (β a)),
      H (composeProb p q) = H p + ∑ a, p a * H (q a)


-- @@ L137-144 verbatim
/--
`A_H(n)` is Shannon's notation for uncertainty on the uniform distribution
with `n + 1` equiprobable outcomes.
-/
def A
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (n : ℕ) : ℝ :=
  H (uniformFin n)


-- @@ L146-152 verbatim
/--
`Apos H n` is uncertainty for exactly `n` equiprobable outcomes (`n : ℕ+`).
-/
def Apos
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (n : ℕ+) : ℝ :=
  H (uniformPNat n)



-- @@ L155-155 verbatim
end


-- @@ L157-157 verbatim
end LeanPool.Shannon1948Formalization
