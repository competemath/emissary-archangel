/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import Mathlib.Data.ZMod.Aut
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L22-24 verbatim
/-!
# LeanPool.OrderPQ.MulZMod
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
section MulZMod


-- @@ L30-31 verbatim
/-- `ZMod n` viewed as a multiplicative group. -/
def MulZMod (n : ℕ) : Type := Multiplicative (ZMod n)


-- @@ L33-33 verbatim
attribute [local implicit_reducible] MulZMod


-- @@ L35-35 verbatim
instance {n : ℕ} : DecidableEq (MulZMod n) := instDecidableEqMultiplicative


-- @@ L37-37 verbatim
instance {n : ℕ} [NeZero n] : Fintype (MulZMod n) := Multiplicative.fintype


-- @@ L39-39 verbatim
instance {n : ℕ} : Mul (MulZMod n) := Multiplicative.mul


-- @@ L41-41 verbatim
instance {n : ℕ} : MulOneClass (MulZMod n) := Multiplicative.mulOneClass


-- @@ L43-43 verbatim
instance {n : ℕ} : Group (MulZMod n) := Multiplicative.group


-- @@ L45-46 verbatim
attribute [local implicit_reducible]
  instMulMulZMod instMulOneClassMulZMod instGroupMulZMod


-- @@ L48-48 verbatim
instance {n : ℕ} : IsCyclic (MulZMod n) := isCyclic_multiplicative


-- @@ L50-54 verbatim
@[simp]
lemma card_mulZMod {n : ℕ} [NeZero n] : Fintype.card (MulZMod n) = n := by
  have : Fintype.card (MulZMod n) = Fintype.card (ZMod n) :=
    Fintype.card_multiplicative (ZMod n)
  rw [this, ZMod.card]


-- @@ L56-56 verbatim
lemma nat_card_mulZMod {n : ℕ} [NeZero n] : Nat.card (MulZMod n) = n := by simp


-- @@ L58-58 verbatim
variable {p : ℕ} [hp : Fact p.Prime]


-- @@ L60-63 verbatim
/-- A nonzero element of `ZMod p` (with `p` prime) viewed as a unit. -/
def unitOfNeZero (x : ZMod p) (hx : x ≠ 0) : (ZMod p)ˣ := by
  refine ZMod.unitOfCoprime x.val (Nat.coprime_of_lt_prime ?_ (ZMod.val_lt x) hp.elim).symm
  simp only [ne_eq, ZMod.val_eq_zero, hx, not_false_eq_true]


-- @@ L65-67 verbatim
@[simp]
lemma val_unitOfNeZero (x : ZMod p) (hx : x ≠ 0) : ((unitOfNeZero x hx) : ZMod p) = x := by
  simp [unitOfNeZero, ZMod.coe_unitOfCoprime]


-- @@ L69-72 verbatim
@[simp]
lemma unitOfNeZero_val (x : (ZMod p)ˣ) : unitOfNeZero x (Units.ne_zero _) = x := by
  ext
  exact val_unitOfNeZero _ (Units.ne_zero _)


-- @@ L74-81 verbatim
/-- Multiplication by a unit in `ZMod p` as an additive automorphism. -/
@[simps -isSimp]
def addAutOfUnit (x : (ZMod p)ˣ) : AddAut (ZMod p) where
  toFun a := x.val * a
  invFun a := x.inv * a
  left_inv _ := by simp_rw [← mul_assoc, x.inv_val, one_mul]
  right_inv _ := by simp_rw [← mul_assoc, x.val_inv, one_mul]
  map_add' a b := by simp_rw [mul_add]


-- @@ L83-83 verbatim
variable (p)


-- @@ L85-88 verbatim
/-- The group of additive automorphisms of `ZMod p` (with `p` prime) is isomorphic to the
group of units of `ZMod p`. -/
def mulEquivAddAutZMod : AddAut (ZMod p) ≃+ Additive (ZMod p)ˣ :=
  ZMod.AddAutEquivUnits p


-- @@ L90-93 verbatim
/-- The group of multiplicative automorphisms of `MulZMod p` (with `p` prime) is isomorphic
to the group of units of `ZMod p`. -/
def mulEquivMulAutMulZMod : MulAut (MulZMod p) ≃* (ZMod p)ˣ :=
  (MulAutMultiplicative (ZMod p)).trans (AddEquiv.toMultiplicativeLeft (mulEquivAddAutZMod p))


-- @@ L95-96 verbatim
noncomputable instance : Fintype (MulAut (MulZMod p)) :=
  Fintype.ofEquiv (ZMod p)ˣ (mulEquivMulAutMulZMod p).symm.toEquiv


-- @@ L98-99 verbatim
lemma mulAut_MulZMod_isCyclic : IsCyclic (MulAut (MulZMod p)) :=
  isCyclic_of_surjective (mulEquivMulAutMulZMod p).symm (mulEquivMulAutMulZMod p).symm.surjective


-- @@ L101-103 verbatim
lemma addAut_ZMod_isCyclic : IsCyclic (Multiplicative (AddAut (ZMod p))) :=
  isCyclic_of_surjective (AddEquiv.toMultiplicativeLeft (mulEquivAddAutZMod p)).symm
    (AddEquiv.toMultiplicativeLeft (mulEquivAddAutZMod p)).symm.surjective


-- @@ L105-109 verbatim
@[simp]
lemma card_mulAut_mulZMod :
    Fintype.card (MulAut (MulZMod p)) = p - 1 := by
  rw [Fintype.card_congr (mulEquivMulAutMulZMod p).toEquiv,
    ZMod.card_units_eq_totient, Nat.totient_prime hp.elim]


-- @@ L111-113 verbatim
lemma nat_card_mulAut_mulZMod :
    Nat.card (MulAut (MulZMod p)) = p - 1 := by
  simp only [Nat.card_eq_fintype_card, card_mulAut_mulZMod]


-- @@ L115-115 verbatim
end MulZMod
