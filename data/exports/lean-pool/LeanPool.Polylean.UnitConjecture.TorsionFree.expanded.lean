/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import LeanPool.Polylean.UnitConjecture.GardamGroup
import LeanPool.Polylean.UnitConjecture.Tactics.AesopRuleSets
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset


-- @@ L18-35 verbatim
/-!
## Torsion-freeness of `P`

This file contains a proof that the group `P` defined is in fact torsion-free.

Roughly, the steps are as follows (further details can be found in the corresponding
`.md` file):
1. Define a function `sq : P -> K` taking a group element `(q, k)` to its square. This
   element lies in the kernel as the group `ℤ/2 × ℤ/2` has exponent `2`.
2. Show that elements in `K`, which are integer triples of the form `(a, b, c)`, do not
   have torsion. This requires the fact that the group `ℤ`, and hence `ℤ³`, is
   torsion-free.
3. Show that no element of `P` has order precisely `2`. This is an argument by cases on
   the `Q` part of a general element of `P`.
4. Finally, show that if an element `g : G` of a group `G` satisfies `g ^ n = (1 : G)`,
   then it also satisfies `(g ^ 2) ^ n = (1 : G)`.
5. Together, these statements show that `P` is torsion-free.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
namespace LeanPool.Polylean


-- @@ L41-43 verbatim
open scoped P

-- import Mathlib.Algebra.GroupPower.Basic



-- @@ L46-48 verbatim
/-!
### Torsion-free groups
-/


-- @@ L50-54 verbatim
/-- The definition of a torsion-free group. -/
class TorsionFree (G : Type _) [Group G] where
  /-- A group is *torsion-free* if the only element with non-trivial torsion is the
  identity element. -/
  torsionFree : ∀ g : G, ∀ n : ℕ, g ^ n.succ = 1 → g = 1


-- @@ L56-60 verbatim
/-- The definition of torsion-free additive groups. -/
class AddTorsionFree (A : Type _) [AddGroup A] where
  /-- An additive group is *torsion-free* if the only element with non-trivial torsion is
  the identity element. -/
  torsionFree : ∀ a : A, ∀ n : ℕ, n.succ • a = 0 → a = 0


-- @@ L62-67 verbatim
/-- ℤ is torsion-free, since it is an integral domain. -/
instance : AddTorsionFree ℤ where
  torsionFree := fun a n (h : n.succ * a = 0) => by
    cases Int.mul_eq_zero.mp h with
    | inl hyp => injection hyp; contradiction
    | inr h => exact h


-- @@ L69-75 verbatim
/-- The product of torsion-free additive groups is torsion-free. -/
instance {A B : Type _} [AddGroup A] [AddGroup B] [AddTorsionFree A]
    [AddTorsionFree B] : AddTorsionFree (A × B) where
  torsionFree := fun (a, b) n h => by
    have h' : (n.succ • a, n.succ • b) = 0 := h
    simp only [Prod.mk.injEq, Prod.zero_eq_mk] at h'
    exact Prod.ext (AddTorsionFree.torsionFree a n h'.1) (AddTorsionFree.torsionFree b n h'.2)

-- @@ L76-76 verbatim
/-! ### **Step 1:** Defining the square of an element of `P`. -/


-- @@ L78-84 verbatim
/-- The function taking an element of `P` to its square, which lies in the kernel `K`. -/
@[aesop norm unfold (rule_sets := [P]), reducible]
def _root_.LeanPool.Polylean.P.sq : P → K
  | ((p, q, r), .e) => (p + p, q + q, r + r)
  | ((_, q, _), .b) => (0, q + q + 1, 0)
  | ((p, _, _), .a) => (p + p + 1, 0, 0)
  | ((_, _, r), .c) => (0, 0, r + r + 1)


-- @@ L86-86 verbatim
open P


-- @@ L88-105 verbatim
/-- A proof that the function `sq` indeed takes an element of `P` to its square in `K`. -/
@[aesop norm apply (rule_sets := [P]), simp]
theorem sq_square : ∀ g : P, g * g = (P.sq g, .e)
    | ((p, q, r), .e) => by
        refine (P.mul (p, q, r) (p, q, r) Q.e Q.e).trans ?_
        simp [P.sq, Q.e, action, cocycle]
    | ((p, q, r), .a) => by
        refine (P.mul (p, q, r) (p, q, r) Q.a Q.a).trans ?_
        rw [show cocycle Q.a Q.a = K.x by rfl]
        simp [P.sq, Q.e, Q.a, K.x, action]
    | ((p, q, r), .b) => by
        refine (P.mul (p, q, r) (p, q, r) Q.b Q.b).trans ?_
        rw [show cocycle Q.b Q.b = K.y by rfl]
        simp [P.sq, Q.e, Q.b, K.y, action]
    | ((p, q, r), .c) => by
        refine (P.mul (p, q, r) (p, q, r) Q.c Q.c).trans ?_
        rw [show cocycle Q.c Q.c = K.z by rfl]
        simp [P.sq, Q.e, Q.c, K.z, action]


-- @@ L107-107 verbatim
/-! ### **Step 2:** Proving that `K` (= `ℤ³`) is torsion-free. -/


-- @@ L109-110 verbatim
/-- The kernel `ℤ³` is torsion-free. -/
instance _root_.LeanPool.Polylean.K.torsionFree : AddTorsionFree K := inferInstance


-- @@ L112-112 verbatim
/-! ### **Step 3:** Showing that no element of `P` has order precisely two. -/


-- @@ L114-114 verbatim
namespace Int


-- @@ L116-116 verbatim
/-! Some basic lemmas about integers needed to prove facts about `P`. -/


-- @@ L118-119 verbatim
lemma add_twice_eq_mul_two {a : ℤ} : a + a = a * 2 := by
  rw [show (2 : ℤ) = 1 + 1 by rfl, mul_add, mul_one]


-- @@ L121-121 verbatim
attribute [local simp] add_twice_eq_mul_two


-- @@ L123-124 verbatim
/-- No odd integer is zero. -/
lemma odd_ne_zero : ∀ a : ℤ, ¬(a + a + 1 = 0) := by omega


-- @@ L126-127 verbatim
/-- If the sum of an integer with itself is zero, then the integer is itself zero. -/
lemma zero_of_twice_zero : ∀ a : ℤ, a + a = 0 → a = 0 := by omega


-- @@ L129-129 verbatim
end Int


-- @@ L131-176 verbatim
/-- The only element of `P` with order dividing `2` is the identity. -/
theorem square_free : ∀ {g : P}, g * g = (1 : P) → g = (1 : P)
  | ((p, q, r), .e) => by
      intro h
      let g : P := ((p, q, r), Q.e)
      have hg : g * g = 1 := h
      rw [sq_square] at hg
      change ((p + p, q + q, r + r), Q.e) = (((0, 0, 0) : K), Q.e) at hg
      injection hg with hk _
      injection hk with hp hqr
      injection hqr with hq hr
      have hp0 := Int.zero_of_twice_zero p hp
      have hq0 := Int.zero_of_twice_zero q hq
      have hr0 := Int.zero_of_twice_zero r hr
      rw [P.one]
      simp [hp0, hq0, hr0]
      rfl
  | ((p, q, r), .a) => by
      intro h
      let g : P := ((p, q, r), Q.a)
      have hg : g * g = 1 := h
      rw [sq_square] at hg
      change ((p + p + 1, 0, 0), Q.e) = (((0, 0, 0) : K), Q.e) at hg
      injection hg with hk _
      injection hk with hp _
      exact False.elim (Int.odd_ne_zero p hp)
  | ((p, q, r), .b) => by
      intro h
      let g : P := ((p, q, r), Q.b)
      have hg : g * g = 1 := h
      rw [sq_square] at hg
      change ((0, q + q + 1, 0), Q.e) = (((0, 0, 0) : K), Q.e) at hg
      injection hg with hk _
      injection hk with _ hqr
      injection hqr with hq _
      exact False.elim (Int.odd_ne_zero q hq)
  | ((p, q, r), .c) => by
      intro h
      let g : P := ((p, q, r), Q.c)
      have hg : g * g = 1 := h
      rw [sq_square] at hg
      change ((0, 0, r + r + 1), Q.e) = (((0, 0, 0) : K), Q.e) at hg
      injection hg with hk _
      injection hk with _ hqr
      injection hqr with _ hr
      exact False.elim (Int.odd_ne_zero r hr)



-- @@ L179-179 verbatim
/-! ### **Step 4:** Showing square powers of torsion elements are trivial. -/


-- @@ L181-184 verbatim
/-- If `g` is a torsion element of a group, then so is `g ^ 2`. -/
lemma torsion_implies_square_torsion {G : Type _} [Group G] (g : G) (n : ℕ)
    (g_tor : g ^ n = 1) : (g ^ 2) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, g_tor, one_pow]


-- @@ L186-186 verbatim
/-! ### **Step 5:** Putting the facts together. -/


-- @@ L188-203 verbatim
/-- `P` is torsion-free. -/
instance _root_.LeanPool.Polylean.P.torsionFree : TorsionFree P where
  torsionFree := by
    intros g n g_tor -- assume `g` is a torsion element
    -- then `g ^ 2` is also a torsion element
    have square_tor : (g ^ 2) ^ n.succ = ((0, 0, 0), Q.e) :=
      torsion_implies_square_torsion g n.succ g_tor
    erw [pow_two, sq_square, P.kernel_pow, Prod.mk.injEq] at square_tor
    -- since `g ^ 2 = s g`, we have that `s g` is a torsion element
    have s_tor : n.succ • (P.sq g) = 0 := square_tor.left
    -- since `s g` lies in the kernel and the kernel is torsion-free, `s g = 0`
    have square_zero : (P.sq g, Q.e) = (0, Q.e) :=
      congrArg (·, Q.e) (K.torsionFree.torsionFree (P.sq g) n s_tor)
    rw [← sq_square] at square_zero
    -- this means `g ^ 2 = e`, and also `g = e` because `P` has no order 2 elements
    exact square_free square_zero


-- @@ L205-205 verbatim
end LeanPool.Polylean
