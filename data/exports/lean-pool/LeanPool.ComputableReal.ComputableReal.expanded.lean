/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.ComputableReal.ComputableRSeq
import Mathlib.Algebra.Order.Archimedean.Real.Basic


-- @@ L11-19 verbatim
/-!
# The quotient field of interval-Cauchy sequences

`Computableℝ` is the quotient of `ComputableℝSeq` by the equivalence relation of
converging to the same real value. This file equips it with its commutative ring,
field, and linear order structures. The ring operations are executable interval
arithmetic; inversion and the comparison `Decidable` instances go through the
classical `ComputableℝSeq.sign` and are `noncomputable`.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-28 verbatim
/-- Computable reals, defined as the quotient of ComputableℝSeq sequences -- sequences with
  Cauchy sequences of lower and upper bounds that converge to the same value -- by the equivalence
  relation of having the same converged value. This is similar to how reals are quotients of Cauchy
  sequence (without any guarantees on lower/upper bounds). -/
def Computableℝ :=
  @Quotient ComputableℝSeq ComputableℝSeq.equiv


-- @@ L30-30 verbatim
attribute [local implicit_reducible] Computableℝ ComputableℝSeq.nzSeq


-- @@ L32-32 verbatim
namespace Computableℝ


-- @@ L34-36 verbatim
/-- Definition of `mk`. -/
def mk : ComputableℝSeq → Computableℝ :=
  Quotient.mk ComputableℝSeq.equiv


-- @@ L38-39 verbatim
/-- Definition of `val`. -/
def val : Computableℝ → ℝ := Quotient.lift ComputableℝSeq.val (fun _ _ h ↦ h)


-- @@ L41-43 verbatim
@[simp]
theorem val_mk_eq_val : (mk x).val = x.val :=
  rfl


-- @@ L45-47 verbatim
@[simp]
theorem val_quot_eq_val (x : ComputableℝSeq) : val (⟦x⟧ : Computableℝ) = x.val :=
  rfl


-- @@ L49-50 verbatim
theorem eq_iff_seq_val (x y : ComputableℝSeq) : (mk x).val = (mk y).val ↔ mk x = mk y :=
  ⟨fun h ↦ Quotient.eq.2 h, Quotient.eq.1⟩


-- @@ L52-60 verbatim
@[simp]
theorem eq_iff_eq_val (x y : Computableℝ) : x.val = y.val ↔ x = y :=
  ⟨by
    let ⟨x',hx'⟩ := Quotient.exists_rep x
    let ⟨y',hy'⟩ := Quotient.exists_rep y
    subst hx'
    subst hy'
    exact (eq_iff_seq_val x' y').1,
  congrArg val⟩


-- @@ L62-66 verbatim
/-- Alternate version of mapℝ that doesn't directly refer to f₂, so it stays
  computable even if f₂ isn't. -/
def mapℝ' (f : ComputableℝSeq → ComputableℝSeq) (h : ∃ f₂ : ℝ → ℝ, ∀ x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  Quotient.map f (fun a b h₂ ↦ h.elim fun _ h ↦ (h₂ ▸ h a).trans (h b).symm)


-- @@ L68-71 verbatim
/-- Given a unary function on sequences that clearly matches function on reals, lift it. -/
def mapℝ (f : ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ} (h : ∀ x, (f x).val = f₂ x.val) :
    Computableℝ → Computableℝ :=
  mapℝ' f ⟨f₂, h⟩


-- @@ L73-74 verbatim
theorem mapℝ'_eq_mapℝ : mapℝ' f h = mapℝ f h₂ := by
  rfl


-- @@ L76-80 verbatim
/-- Alternate version of map₂ℝ that doesn't directly refer to f₂, so it stays
  computable even if f₂ isn't. -/
def map₂ℝ' (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) (h : ∃ f₂ : ℝ → ℝ → ℝ, ∀ x y,
    (f x y).val = f₂ x.val y.val) : Computableℝ → Computableℝ → Computableℝ :=
  Quotient.map₂ f (fun a b h₂ y z h₃ ↦ h.elim fun _ h ↦ (h₂ ▸ h₃ ▸ h a y).trans (h b z).symm)


-- @@ L82-86 verbatim
/-- Given a binary function that clearly mimics a standard real function, lift that. -/
def map₂ℝ (f : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq) {f₂ : ℝ → ℝ → ℝ}
    (h : ∀ x y, (f x y).val = f₂ x.val y.val) :
    Computableℝ → Computableℝ → Computableℝ :=
  map₂ℝ' f ⟨f₂, h⟩


-- @@ L88-90 verbatim
theorem map₂ℝ'_eq_map₂ℝ : map₂ℝ' f h = map₂ℝ f h₂ := by
  ext
  rw [map₂ℝ]


-- @@ L92-97 verbatim
@[simp]
theorem val_mapℝ_eq_val : (@mapℝ f f₂ h x).val = f₂ x.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  rw [mapℝ, mapℝ', Quotient.map_mk]
  apply h


-- @@ L99-106 verbatim
@[simp]
theorem val_map₂ℝ_eq_val : (@map₂ℝ f f₂ h x y).val = f₂ x.val y.val := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [map₂ℝ, map₂ℝ', Quotient.map₂_mk]
  apply h


-- @@ L108-109 verbatim
instance instComputableAdd : Add Computableℝ :=
  ⟨map₂ℝ (· + ·) ComputableℝSeq.val_add⟩


-- @@ L111-112 verbatim
instance instComputableMul : Mul Computableℝ :=
  ⟨map₂ℝ (· * ·) ComputableℝSeq.val_mul⟩


-- @@ L114-115 verbatim
instance instComputableNeg : Neg Computableℝ :=
  ⟨mapℝ (- ·) ComputableℝSeq.val_neg⟩


-- @@ L117-118 verbatim
instance instComputableSub : Sub Computableℝ :=
  ⟨map₂ℝ (· - ·) ComputableℝSeq.val_sub⟩


-- @@ L120-121 verbatim
instance instComputableZero : Zero Computableℝ :=
  ⟨mk 0⟩


-- @@ L123-124 verbatim
instance instComputableOne : One Computableℝ :=
  ⟨mk 1⟩


-- @@ L126-126 verbatim
variable (x y : Computableℝ)


-- @@ L128-130 verbatim
@[simp]
theorem val_add : (x + y).val = x.val + y.val :=
  val_map₂ℝ_eq_val


-- @@ L132-134 verbatim
@[simp]
theorem val_mul : (x * y).val = x.val * y.val :=
  val_map₂ℝ_eq_val


-- @@ L136-138 verbatim
@[simp]
theorem val_neg : (-x).val = -(x.val) :=
  val_mapℝ_eq_val


-- @@ L140-142 verbatim
@[simp]
theorem val_sub : (x - y).val = x.val - y.val :=
  val_map₂ℝ_eq_val


-- @@ L144-146 verbatim
@[simp]
theorem val_zero : (0 : Computableℝ).val = 0 :=
  ComputableℝSeq.val_zero


-- @@ L148-150 verbatim
@[simp]
theorem val_one : (1 : Computableℝ).val = 1 :=
  ComputableℝSeq.val_one


-- @@ L152-153 verbatim
theorem add_mk (x y : ComputableℝSeq) : mk x + mk y = mk (x + y) :=
  rfl


-- @@ L155-156 verbatim
theorem mul_mk (x y : ComputableℝSeq) : mk x * mk y = mk (x * y) :=
  rfl


-- @@ L158-159 verbatim
theorem sub_mk (x y : ComputableℝSeq) : mk x - mk y = mk (x - y) :=
  rfl


-- @@ L161-162 verbatim
theorem neg_mk (x : ComputableℝSeq) : -mk x = mk (-x) :=
  rfl


-- @@ L164-186 verbatim
instance instCommRing : CommRing Computableℝ := by
  refine { natCast := fun n => mk n
           intCast := fun z => mk z
           zero := 0
           one := 1
           mul := (· * ·)
           add := (· + ·)
           neg := (- ·)
           sub := (· - ·)
           npow := npowRec --todo faster instances
           nsmul := nsmulRec
           zsmul := zsmulRec
           add_assoc := ?_, zero_add := ?_, add_zero := ?_, add_comm := ?_,
           left_distrib := ?_, right_distrib := ?_, zero_mul := ?_, mul_zero := ?_,
           mul_assoc := ?_, one_mul := ?_, mul_one := ?_, neg_add_cancel := ?_,
           mul_comm := ?_, natCast_succ := ?_, sub_eq_add_neg := ?_ }
  all_goals
    intros
    first
    | rfl
    | rw [← eq_iff_eq_val]
      simp
      try ring_nf!


-- @@ L188-193 verbatim
@[simp]
theorem val_natpow (x : Computableℝ) (n : ℕ) : (x ^ n).val = x.val ^ n := by
  induction n
  · rw [pow_zero, val_one, pow_zero]
  · rename_i ih
    rw [pow_succ, pow_succ, val_mul, ih]


-- @@ L195-198 verbatim
theorem val_nsmul (x : Computableℝ) (n : ℕ) : (n • x).val = n • x.val := by
  induction n
  · simp
  · simp_all


-- @@ L200-200 verbatim
section safeInv


-- @@ L202-213 verbatim
/-- Identify nonzero computable reals with the quotient of their nonzero representatives. -/
def nzQuotEquiv := Equiv.subtypeQuotientEquivQuotientSubtype
    (fun x : ComputableℝSeq ↦ x.val ≠ 0)
    (fun x : Computableℝ ↦ x ≠ 0)
    (fun _ ↦ ⟨
      fun h h₂ ↦ by
        rw [← eq_iff_eq_val, val_zero] at h₂
        exact h h₂,
      fun (h : ¬_ = 0) h₂ ↦ by
        rw [← eq_iff_eq_val, val_zero] at h
        exact h h₂⟩)
    (fun _ _ ↦ Iff.rfl)


-- @@ L215-220 verbatim
/-- Auxiliary inverse definition that operates on the nonzero Computableℝ values. -/
noncomputable def safeInv' : { x : Computableℝ // x ≠ 0 } → { x : Computableℝ // x ≠ 0 } :=
  fun v ↦ nzQuotEquiv.invFun <| Quotient.map ComputableℝSeq.invNz fun x y h₁ ↦ by
    change (ComputableℝSeq.invNz x).val.val = (ComputableℝSeq.invNz y).val.val
    rw [ComputableℝSeq.val_invNz x, ComputableℝSeq.val_invNz y, h₁]
  (nzQuotEquiv.toFun v)


-- @@ L222-223 verbatim
/-- Inverse of a nonzero Computableℝ, safe (terminating) as long as x is nonzero. -/
noncomputable irreducible_def safeInv (hnz : x ≠ 0) : Computableℝ := safeInv' ⟨x, hnz⟩


-- @@ L225-238 verbatim
@[simp]
theorem safeInv_val (hnz : x ≠ 0) : (x.safeInv hnz).val = x.val⁻¹ := by
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  subst hx'
  have : (nzQuotEquiv { val := ⟦x'⟧, property := hnz : { x : Computableℝ // x ≠ 0 } }) =
      ⟦{ val := x', property := (by
        rw [show (0 : Computableℝ) = ⟦0⟧ by rfl] at hnz
        contrapose! hnz
        rwa [← Computableℝ.val_zero, ← val_quot_eq_val, eq_iff_eq_val] at hnz
      )}⟧ := by
    apply Equiv.subtypeQuotientEquivQuotientSubtype_mk
  rw [safeInv, safeInv', val, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Quotient.lift_mk, this,
    Quotient.map_mk, nzQuotEquiv, Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk,
    Quotient.lift_mk, ComputableℝSeq.val_invNz]


-- @@ L240-240 verbatim
end safeInv


-- @@ L242-242 verbatim
section field


-- @@ L244-245 verbatim
noncomputable instance instComputableInv : Inv Computableℝ :=
  ⟨mapℝ' (·⁻¹) ⟨(·⁻¹), ComputableℝSeq.val_inv⟩⟩


-- @@ L247-251 verbatim
@[simp]
theorem inv_val : (x⁻¹).val = (x.val)⁻¹ := by
  change (mapℝ' _ _ _).val = (x.val)⁻¹
  rw [mapℝ'_eq_mapℝ]
  exact val_mapℝ_eq_val (h := ComputableℝSeq.val_inv)


-- @@ L253-265 verbatim
noncomputable instance instField : Field Computableℝ := { instCommRing with
  qsmul := _
  nnqsmul := _
  exists_pair_ne := ⟨0, 1, by
    rw [ne_eq, ← eq_iff_eq_val, val_zero, val_one]
    exact zero_ne_one⟩
  mul_inv_cancel := by
    intro a ha
    rw [← eq_iff_eq_val, val_mul, inv_val, val_one]
    have : val a ≠ 0 := by rwa [← val_zero, ne_eq, eq_iff_eq_val]
    field_simp
  inv_zero := by rw [← eq_iff_eq_val]; simp
    }


-- @@ L267-271 verbatim
@[simp]
theorem div_val : (x / y).val = x.val / y.val := by
  change (x * y⁻¹).val = _
  rw [val_mul, inv_val]
  field_simp


-- @@ L273-273 verbatim
end field


-- @@ L275-275 verbatim
section ordered


-- @@ L277-277 verbatim
variable (x y : Computableℝ)


-- @@ L279-284 verbatim
/-- Definition of `lt`. -/
def lt : Prop := by
  apply Quotient.lift (fun z ↦ z.sign = SignType.pos) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]


-- @@ L286-287 verbatim
instance instLT : LT Computableℝ :=
  ⟨lt⟩


-- @@ L289-294 verbatim
/-- Definition of `le`. -/
def le : Prop := by
  apply Quotient.lift (fun z ↦ SignType.zero ≤ z.sign) ?_ (y - x)
  intro a b h
  dsimp
  rw [ComputableℝSeq.sign_sound, ComputableℝSeq.sign_sound, h]


-- @@ L296-297 verbatim
instance instLE : LE Computableℝ :=
  ⟨le⟩


-- @@ L299-307 verbatim
@[simp]
theorem lt_iff_lt : x.val < y.val ↔ x < y := by
  change x.val < y.val ↔ lt x y
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [lt, ← mk, val_mk_eq_val, val_mk_eq_val, sub_mk, mk, Quotient.lift_mk]
  rw [ComputableℝSeq.sign_pos_iff, ComputableℝSeq.val_sub, sub_pos]


-- @@ L309-318 verbatim
@[simp]
theorem le_iff_le : x.val ≤ y.val ↔ x ≤ y := by
  change x.val ≤ y.val ↔ le x y
  let ⟨x',hx'⟩ := Quotient.exists_rep x
  let ⟨y',hy'⟩ := Quotient.exists_rep y
  subst hx'
  subst hy'
  rw [le, ← mk, val_mk_eq_val, val_mk_eq_val, sub_mk, mk, Quotient.lift_mk]
  rw [ComputableℝSeq.sign_sound, SignType.zero_eq_zero, sign_nonneg_iff]
  rw [ComputableℝSeq.val_sub, sub_nonneg]


-- @@ L320-326 verbatim
noncomputable instance instDecidableLE : DecidableRel (fun (x y : Computableℝ) ↦ x ≤ y) :=
  fun a b ↦ by
    change Decidable (le a b)
    rw [le]
    infer_instance

--TODO: add a faster `min` and `max` that don't require sign computation.

-- @@ L327-336 verbatim
noncomputable instance instPartialOrder : PartialOrder Computableℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl a := by simp only [← le_iff_le]; exact le_refl _
  le_trans a b c hab hbc := by
    simp only [← le_iff_le] at *; linarith
  le_antisymm a b hab hba := by
    rw [← eq_iff_eq_val]; simp only [← le_iff_le] at *; linarith
  lt_iff_le_not_ge a b := by
    simp only [← le_iff_le, ← lt_iff_lt]; exact lt_iff_le_not_ge


-- @@ L338-342 verbatim
noncomputable instance instLinearOrder : LinearOrder Computableℝ where
  toPartialOrder := instPartialOrder
  toDecidableLE := inferInstance
  le_total a b := by
    simp only [← le_iff_le]; exact le_total _ _


-- @@ L344-347 verbatim
instance instIsOrderedAddMonoid : IsOrderedAddMonoid Computableℝ where
  add_le_add_left a b hab c := by
    simp only [← le_iff_le, val_add] at *
    linarith


-- @@ L349-352 verbatim
instance instZeroLEOneClass : ZeroLEOneClass Computableℝ where
  zero_le_one := by
    simp only [← le_iff_le, val_zero, val_one]
    exact zero_le_one


-- @@ L354-357 verbatim
instance instIsStrictOrderedRing : IsStrictOrderedRing Computableℝ :=
  .of_mul_pos fun a b ha hb => by
    simp only [← lt_iff_lt, val_mul, val_zero] at *
    exact mul_pos ha hb


-- @@ L359-359 verbatim
end ordered


-- @@ L361-361 verbatim
end Computableℝ
