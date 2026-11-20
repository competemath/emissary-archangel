/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import Tnorms.Util.IsTopOne


-- @@ L10-42 verbatim
/-!
General TODOs:
  * Clean up the proofs
  * Add a docstring to the top of each file
  * Fix naming convention
    * Spelling of Continuous in identifiers should be 'continuous'
    * Spelling of UniformContinuous is ...
    * Spelling of PrincipleOfCharity (should it really be pocat?)
  * Use IsZeroBotClass and make an IsOneTopClass (and IsZeroTopClass?)
  * Add definition of Pseudo-Archimedean from Product of t-norms paper.
      This might help with generalizations to partial orders
  * Think again about whether to assume DenselyOrdered or PreconnectedSpace
      They are equivalent in a ConditionallyCompleteLinearOrder, but in a partial order,
      neither implies the other.
  * Fix the files in the Other folder so that they compile and prove stuff
  * Add ordinal sums?
  * Weaken typeclasses when possible
    I'm okay with assuming some things indiscriminately:
    * Completeness
    * CommMonoidWithZero, IsOrderedMonoid
    * OrderTopology
    * IsZeroBotClass, IsOneTopClass, Nontrivial
    But I'd like to try and weaken these in particular:
    * LinearOrder (does a PartialOrder or a Lattice suffice?)
    * FirstCountableTopology
        * I think that if we use the mathlib results instead of ContinuousSup, then we can just get
          rid of this assumption throughout.  More investigation is needed.
    * DenselyOrdered, PreconnectedSpace
    In general, I just want to be sure that the typeclasses stated are needed.
    If possible, I would like to provide counterexamples to some major results to show that
      no assumptions can be weakened.
    Perhaps we even make a file / folder of formalized counterexamples to important theorems
-/


-- @@ L44-47 verbatim
section Tnorm

-- This could be "weakened" to a ConditionallyCompleteLinearOrder, but in this
--   case, those are equivalent, since we have a top (1) and a bottom (0)

-- @@ L48-50 verbatim
@[ext]
class Tnorm (M : Type*) [CompleteLinearOrder M] [TopologicalSpace M] extends
  CommMonoidWithZero M, IsOrderedMonoid M, IsTopOneClass M, OrderTopology M


-- @@ L52-52 verbatim
variable {M : Type*} [CompleteLinearOrder M] [TopologicalSpace M]


-- @@ L54-82 verbatim
@[ext high]
lemma ext_mul {T₁ T₂ : Tnorm M} (h : ∀ a b : M, T₁.mul a b = T₂.mul a b) : T₁ = T₂ := by
  have h1 : T₁.one = T₂.one := by
    have ht : T₁.one = ⊤ :=
      @one_eq_top M _ T₁.toOne T₁.toIsTopOneClass _
    have ht' : T₂.one = ⊤ := one_eq_top
    rw [ht, ht']
  have hm : T₁.mul = T₂.mul := by
    ext a b
    exact h a b
  ext1
  · exact hm
  · exact h1
  · ext n a
    rw [@npow_eq_pow M T₁.toMonoid, @npow_eq_pow M T₂.toMonoid]
    induction n with
    | zero =>
      rw [pow_zero, @pow_zero M T₁.toMonoid]
      exact h1
    | succ n ih =>
      simp [pow_succ, @pow_succ M T₁.toMonoid, HMul.hMul, hm, ih]
  · have ht : T₁.zero = ⊥ :=
      let : @IsBotZeroClass M _ T₁.toZero :=
        @instIsBotZeroClassOfIsTopOneClassLeft M _ T₁.toMulZeroOneClass
          (@IsOrderedMonoid.toMulLeftMono M T₁.toCommMonoid _ T₁.toIsOrderedMonoid)
          T₁.toIsTopOneClass
      (@bot_eq_zero M _ T₁.toZero this _).symm
    have ht' : T₂.zero = ⊥ := bot_eq_zero.symm
    rw [ht, ht']


-- @@ L84-84 verbatim
end Tnorm




-- @@ L88-90 verbatim
section LeftRightContinuousMul

-- Basics of Left and Right Continuous Multiplication


-- @@ L92-92 verbatim
variable (M : Type*) [Mul M] [Preorder M] [TopologicalSpace M]


-- @@ L94-98 verbatim
class LeftContinuousMul where
  monotone_continuous_mul : ∀ x y : ℕ → M, ∀ p q : M, Monotone x → Monotone y →
    Filter.Tendsto x Filter.atTop (nhds p)
    → Filter.Tendsto y Filter.atTop (nhds q)
    → Filter.Tendsto (fun n => (x n) * (y n)) Filter.atTop (nhds (p * q))


-- @@ L100-104 verbatim
class RightContinuousMul where
  antitone_continuous_mul : ∀ x y : ℕ → M, ∀ p q : M, Antitone x → Antitone y →
    Filter.Tendsto x Filter.atTop (nhds p)
    → Filter.Tendsto y Filter.atTop (nhds q)
    → Filter.Tendsto (fun n => (x n) * (y n)) Filter.atTop (nhds (p * q))


-- @@ L106-111 verbatim
lemma monotone_continuous_mul [LeftContinuousMul M] : ∀ x y : ℕ → M, ∀ p q : M,
    Monotone x → Monotone y →
    Filter.Tendsto x Filter.atTop (nhds p)
    → Filter.Tendsto y Filter.atTop (nhds q)
    → Filter.Tendsto (fun n => (x n) * (y n)) Filter.atTop (nhds (p * q)) := by
  exact fun x y p q a a_1 a_2 a_3 ↦ LeftContinuousMul.monotone_continuous_mul x y p q a a_1 a_2 a_3


-- @@ L113-118 verbatim
lemma antitone_continuous_mul [RightContinuousMul M] : ∀ x y : ℕ → M, ∀ p q : M,
    Antitone x → Antitone y →
    Filter.Tendsto x Filter.atTop (nhds p)
    → Filter.Tendsto y Filter.atTop (nhds q)
    → Filter.Tendsto (fun n => (x n) * (y n)) Filter.atTop (nhds (p * q)) := by
  exact fun x y p q a a_1 a_2 a_3 ↦ RightContinuousMul.antitone_continuous_mul x y p q a a_1 a_2 a_3


-- @@ L120-121 verbatim
instance [ContinuousMul M] : LeftContinuousMul M where
  monotone_continuous_mul _ _ _ _ _ _ := Filter.Tendsto.mul


-- @@ L123-124 verbatim
instance [ContinuousMul M] : RightContinuousMul M where
  antitone_continuous_mul _ _ _ _ _ _ := Filter.Tendsto.mul



-- @@ L127-127 verbatim
end LeftRightContinuousMul




-- @@ L131-131 verbatim
section FuzzyLogic


-- @@ L133-134 verbatim
class abbrev IsFuzzyLogic (M : Type*) [CompleteLinearOrder M] [TopologicalSpace M] [Tnorm M] :=
  LeftContinuousMul M, FirstCountableTopology M


-- @@ L136-136 verbatim
variable {M : Type*} [CompleteLinearOrder M] [TopologicalSpace M] [Tnorm M]


-- @@ L138-138 verbatim
def LImp : M → M → M := fun p q => sSup {r : M | p * r ≤ q}


-- @@ L140-140 verbatim
infixl:60 " ⇒ " => LImp


-- @@ L142-143 expanded
lemma LImp_def {p q : M} : LImp p q = sSup {r : M | p * r ≤ q} := by simp [LImp]


-- @@ L145-147 expanded
@[simp]
lemma zero_LImp (p : M) : LImp (0 : M) p = (1 : M) := by simp [LImp_def, zero_le, one_eq_top]


-- @@ L149-150 expanded
lemma LImp_self (p : M) : LImp p p = 1 := by simp [LImp_def, mul_le_left, one_eq_top]


-- @@ L152-152 verbatim
variable [IsFuzzyLogic M]


-- @@ L154-174 expanded
lemma mul_LImp (p q : M) : p * (LImp p q) ≤ q :=
  by
  simp only [LImp_def]
  have hre : {r | p * r ≤ q}.Nonempty := by
    use 0
    simp [zero_le]
  have hrbd : BddAbove {r | p * r ≤ q} := by
    rw [bddAbove_def]
    use 1
    grind [le_one]
  obtain ⟨u, hum, hut, hus⟩ := exists_seq_tendsto_sSup hre hrbd
  simp only [Set.mem_setOf_eq] at hus
  have ht :=
    monotone_continuous_mul _ (fun n ↦ p) u p (LImp p q) monotone_const hum tendsto_const_nhds hut
  simp only [LImp_def, tendsto_order, Filter.eventually_atTop, gt_iff_lt] at ht
  apply And.left at ht
  contrapose! ht
  use q
  simp only [ht, true_and]
  intro n
  use n
  grind


-- @@ L176-183 expanded
lemma le_LImp_iff_mul_le (p q r : M) : r ≤ LImp p q ↔ r * p ≤ q :=
  by
  constructor
  · intro h
    rw [mul_comm]
    refine le_trans (mul_le_mul_right h p) (mul_LImp p q)
  · intro h
    rw [LImp_def]
    exact le_sSup (by grind)


-- @@ L185-187 expanded
lemma LImp_lt_iff_lt_mul (p q r : M) : LImp p q < r ↔ q < r * p :=
  by
  contrapose!
  exact le_LImp_iff_mul_le _ _ _


-- @@ L189-209 expanded
lemma map_LImp (M N : Type*) [CompleteLinearOrder M] [CompleteLinearOrder N] [TopologicalSpace M]
    [TopologicalSpace N] [Tnorm M] [Tnorm N] [IsFuzzyLogic M] [IsFuzzyLogic N] (e : M ≃*o N)
    (p q : M) : e (LImp p q) = (LImp (e p) (e q)) :=
  by
  simp only [LImp_def, map_sSup]
  congr
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro ⟨y, hpq, hy⟩
    rw [← hy, ← map_mul, map_le_map_iff]
    exact hpq
  · intro h
    use e.symm x
    simp only [OrderMonoidIso.apply_symm_apply, and_true]
    rw [← map_inv_le_iff, show EquivLike.inv e (e p * x) = e.symm (e p * x) by rfl, map_mul,
      OrderMonoidIso.symm_apply_apply] at h
    exact h


-- @@ L212-212 verbatim
end FuzzyLogic


-- @@ L214-217 verbatim
section

-- abbrev StrictlyMonotone := PosMulStrictMono
-- abbrev Cancellative := IsCancelMulZero


-- @@ L219-219 verbatim
abbrev IsNontrivial {M : Type*} [Zero M] [One M] (p : M) := p ≠ 0 ∧ p ≠ 1


-- @@ L221-221 verbatim
variable (M : Type*)


-- @@ L223-226 verbatim
@[mk_iff]
class ConditionalCancellative [Mul M] [Zero M] where
  right_cancel_of_mul_ne_zero : ∀ {p q r : M}, r * p ≠ 0 → q * p = r * p → q = r
  left_cancel_of_mul_ne_zero : ∀ {p q r : M}, p * r ≠ 0 → p * q = p * r → q = r


-- @@ L228-230 verbatim
@[mk_iff]
class MulArchimedeanDualWithZero [Preorder M] [MonoidWithZero M] where
  arch : ∀ {x y : M}, 0 < x → y < 1 → ∃ n : ℕ, y ^ n < x


-- @@ L232-234 verbatim
@[mk_iff]
class NoNontrivialIdempotents [Mul M] [Zero M] [One M] where
  no_idem : ∀ p : M, IsIdempotentElem p → ¬ IsNontrivial p


-- @@ L236-238 verbatim
@[mk_iff]
class abbrev Strict [TopologicalSpace M] [Mul M] [Zero M] [Preorder M] :=
  ContinuousMul M, PosMulStrictMono M


-- @@ L240-241 verbatim
class Nilpotent [TopologicalSpace M] [MonoidWithZero M] extends ContinuousMul M where
  nilpt : ∀ p : M, p ≠ 1 → IsNilpotent p


-- @@ L243-243 verbatim
variable [Zero M] [One M]


-- @@ L245-247 verbatim
@[mk_iff]
class NontrivialZeroOne where
  exists_ne : ∃ a : M, a ≠ 0 ∧ a ≠ 1


-- @@ L249-251 verbatim
@[mk_iff]
class SubsingletonZeroOne where
  allEq_zero_or_one : ∀ a : M, a = 0 ∨ a = 1


-- @@ L253-253 verbatim
variable {M}


-- @@ L255-257 verbatim
lemma eq_one_of_ne_zero [SubsingletonZeroOne M] {a : M} (ha : a ≠ 0) : a = 1 := by
  have := SubsingletonZeroOne.allEq_zero_or_one a
  grind


-- @@ L259-261 verbatim
lemma eq_zero_of_ne_one [SubsingletonZeroOne M] {a : M} (ha : a ≠ 1) : a = 0 := by
  have := SubsingletonZeroOne.allEq_zero_or_one a
  grind


-- @@ L263-263 verbatim
end
