/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L19-19 verbatim
/-! # Erdős 97 convex-octagon formalization: Incidence -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Erdos97Octagon


-- @@ L25-25 verbatim
open scoped BigOperators


-- @@ L27-28 verbatim
/-- The labelled vertex set of an octagon. -/
abbrev Vertex := Fin 8


-- @@ L30-37 verbatim
/-- Four selected equidistant witnesses around every labelled octagon vertex. -/
structure OctagonIncidence where
  /-- The four selected witnesses associated with a centre. -/
  targets : Vertex → Finset Vertex
  /-- Every witness row has exactly four vertices. -/
  card_targets : ∀ v, (targets v).card = 4
  /-- A centre is not one of its own positive-radius witnesses. -/
  centre_not_mem : ∀ v, v ∉ targets v


-- @@ L39-44 verbatim
@[ext]
theorem OctagonIncidence.ext {Q R : OctagonIncidence} (h : Q.targets = R.targets) : Q = R := by
  cases Q
  cases R
  cases h
  rfl


-- @@ L46-46 verbatim
namespace OctagonIncidence


-- @@ L48-50 verbatim
/-- The number of witness rows containing `a`. -/
def indegree (Q : OctagonIncidence) (a : Vertex) : ℕ :=
  ∑ v, if a ∈ Q.targets v then 1 else 0


-- @@ L52-54 verbatim
/-- The number of witness rows containing both `a` and `b`. -/
def pairMultiplicity (Q : OctagonIncidence) (a b : Vertex) : ℕ :=
  ∑ v, if a ∈ Q.targets v ∧ b ∈ Q.targets v then 1 else 0


-- @@ L56-58 verbatim
/-- No distinct pair occurs together in more than two witness rows. -/
def PairSparse (Q : OctagonIncidence) : Prop :=
  ∀ ⦃a b⦄, a ≠ b → Q.pairMultiplicity a b ≤ 2


-- @@ L60-62 verbatim
/-- Every vertex occurs in exactly four witness rows. -/
def Balanced (Q : OctagonIncidence) : Prop :=
  ∀ a, Q.indegree a = 4


-- @@ L64-79 verbatim
private lemma row_pair_sum (Q : OctagonIncidence) (a v : Vertex) :
    (∑ b ∈ Finset.univ.erase a,
        if a ∈ Q.targets v ∧ b ∈ Q.targets v then (1 : ℕ) else 0) =
      if a ∈ Q.targets v then 3 else 0 := by
  classical
  by_cases ha : a ∈ Q.targets v
  · have hfilter :
        (Finset.univ.erase a).filter (fun b => b ∈ Q.targets v) =
          (Q.targets v).erase a := by
      ext b
      simp [and_comm]
    rw [ite_eq_left ha]
    simp only [ha, true_and, Finset.sum_boole, hfilter]
    rw [Finset.card_erase_of_mem ha, Q.card_targets]
    norm_num
  · simp [ha]


-- @@ L81-92 verbatim
/-- Double-count pairs in the witness rows containing a fixed vertex. -/
theorem sum_pairMultiplicity (Q : OctagonIncidence) (a : Vertex) :
    (∑ b ∈ Finset.univ.erase a, Q.pairMultiplicity a b) =
      3 * Q.indegree a := by
  classical
  simp only [pairMultiplicity, indegree]
  rw [Finset.sum_comm]
  simp_rw [row_pair_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases ha : a ∈ Q.targets v <;> simp [ha]


-- @@ L94-103 verbatim
/-- Every vertex has indegree at most four when pair multiplicities are at most two. -/
theorem indegree_le_four (Q : OctagonIncidence) (hQ : Q.PairSparse) (a : Vertex) :
    Q.indegree a ≤ 4 := by
  have hsum :
      (∑ b ∈ Finset.univ.erase a, Q.pairMultiplicity a b) ≤
        ∑ _b ∈ Finset.univ.erase a, 2 := by
    exact Finset.sum_le_sum fun b hb => hQ (Finset.ne_of_mem_erase hb).symm
  rw [Q.sum_pairMultiplicity] at hsum
  norm_num at hsum
  omega


-- @@ L105-122 verbatim
/-- There are exactly 32 selected incidences in an octagon witness system. -/
theorem sum_indegree (Q : OctagonIncidence) :
    ∑ a, Q.indegree a = 32 := by
  classical
  simp only [indegree]
  rw [Finset.sum_comm]
  calc
    (∑ v : Vertex, ∑ a : Vertex, if a ∈ Q.targets v then 1 else 0) =
        ∑ v : Vertex, (Q.targets v).card := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_boole]
      norm_num
    _ = ∑ _v : Vertex, 4 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Q.card_targets v
    _ = 32 := by norm_num


-- @@ L124-150 verbatim
private lemma eq_of_bounded_sum
    {α : Type*} [Fintype α]
    (f : α → ℕ) (k : ℕ) (hle : ∀ a, f a ≤ k)
    (hsum : ∑ a, f a = Fintype.card α * k) (a : α) :
    f a = k := by
  classical
  have ha : a ∈ (Finset.univ : Finset α) := Finset.mem_univ a
  have hrest :
      (∑ x ∈ (Finset.univ.erase a), f x) ≤
        (Finset.univ.erase a).card • k :=
    Finset.sum_le_card_nsmul _ _ _ fun x _ => hle x
  have hsplit := Finset.sum_erase_add Finset.univ f ha
  have hcard := Finset.card_erase_add_one ha
  simp only [Finset.card_univ, nsmul_eq_mul] at hrest hcard
  have hmul :
      Fintype.card α * k = (Finset.univ.erase a).card * k + k := by
    rw [← hcard, Nat.add_mul]
    simp
  have htotal_le :
      (∑ x, f x) ≤ (Finset.univ.erase a).card * k + f a := by
    calc
      (∑ x, f x) = (∑ x ∈ Finset.univ.erase a, f x) + f a := hsplit.symm
      _ ≤ (Finset.univ.erase a).card * k + f a :=
        Nat.add_le_add_right hrest (f a)
  rw [hsum] at htotal_le
  rw [hmul] at htotal_le
  exact Nat.le_antisymm (hle a) (Nat.le_of_add_le_add_left htotal_le)


-- @@ L152-157 verbatim
/-- Pair sparsity forces the four-in/four-out balanced incidence condition. -/
theorem balanced_of_pairSparse (Q : OctagonIncidence) (hQ : Q.PairSparse) :
    Q.Balanced := by
  intro a
  apply eq_of_bounded_sum Q.indegree 4 (Q.indegree_le_four hQ)
  simpa using Q.sum_indegree


-- @@ L159-159 verbatim
end OctagonIncidence


-- @@ L161-161 verbatim
end Erdos97Octagon
