/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import LeanPool.ZFLean.Integers
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring.RingNF


-- @@ L12-16 verbatim
/-! # ZFC Rational Numbers

This file defines the rational numbers in ZFC, based on the integers and using the `ZFInt` type.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace ZFSet

-- @@ L21-22 verbatim
/-- Imported ZFLean declaration. -/
abbrev ZFInt' := {x : ZFInt // x ≠ 0}


-- @@ L24-25 verbatim
/-- The equivalence relation on `ℤ × ℤ⋆` that defines the rational numbers. -/
protected abbrev qrel (p q : ZFInt × ZFInt') : Prop := p.1 * q.2 = p.2 * q.1


-- @@ L27-58 verbatim
protected theorem qrel_eq : Equivalence ZFSet.qrel where
  refl x := ZFInt.mul_comm x.1 x.2
  symm h := by
    unfold ZFSet.qrel at h ⊢
    rw [ZFInt.mul_comm, ←h, ZFInt.mul_comm]
  trans := by
    rintro ⟨p, q, hq⟩ ⟨u, v, hv⟩ ⟨s, t, ht⟩ hpq huv
    dsimp [ZFSet.qrel] at hpq huv ⊢
    have : p * t * u * v = q * s * u * v := by
      suffices p * v * u * t = q * u * s * v by
        rw [
          mul_assoc, mul_assoc,
          mul_comm t, mul_comm u,
          ←mul_assoc, ←mul_assoc,
          this,
          mul_assoc, mul_assoc,
          mul_comm u, mul_assoc, mul_comm v,
          ←mul_assoc, ←mul_assoc]
      rw [hpq, mul_assoc, huv, mul_comm v s, ← mul_assoc]
    conv at this =>
      conv => lhs; rw [mul_assoc]
      conv => rhs; rw [mul_assoc]
    by_cases u_mul_v : u * v = 0
    · rw [ZFInt.mul_comm] at u_mul_v
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero u_mul_v hv
      rw [ZFInt.mul_zero, ZFInt.mul_comm] at hpq
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero hpq hv
      rw [ZFInt.zero_mul] at huv
      symm at huv
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero huv hv
      rw [ZFInt.mul_zero, ZFInt.zero_mul]
    · rwa [ZFInt.mul_right_cancel_iff u_mul_v] at this


-- @@ L60-63 verbatim
/-- `ℤ × ℤ⋆` equipped with `qrel` is a setoid. -/
protected instance instSetoidZFIntZFInt' : Setoid (ZFInt × ZFInt') where
  r := ZFSet.qrel
  iseqv := ZFSet.qrel_eq


-- @@ L65-66 verbatim
/-- `ℚ` is defined as `ℤ × ℤ⋆` quotiented by `qrel` -/
abbrev ZFRat := Quotient ZFSet.instSetoidZFIntZFInt'


-- @@ L68-68 verbatim
namespace ZFRat

-- @@ L69-70 verbatim
/-- Imported ZFLean declaration. -/
def mk : ZFInt × ZFInt' → ZFRat := Quotient.mk''


-- @@ L72-73 verbatim
@[simp]
theorem mk_eq (x : ZFInt × ZFInt') : @Eq ZFRat ⟦x⟧ (mk x) := rfl


-- @@ L75-76 verbatim
@[simp]
theorem mk_out : ∀ x : ZFRat, mk x.out = x := Quotient.out_eq


-- @@ L78-78 verbatim
theorem eq {x y : ZFInt × ZFInt'} : mk x = mk y ↔ ZFSet.qrel x y := Quotient.eq


-- @@ L80-80 verbatim
theorem sound {x y : ZFInt × ZFInt'} (h : ZFSet.qrel x y) : mk x = mk y := Quotient.sound h

-- @@ L81-81 verbatim
theorem exact {x y : ZFInt × ZFInt'} : mk x = mk y → ZFSet.qrel x y := Quotient.exact

-- @@ L82-83 verbatim
/-- Imported ZFLean declaration. -/
abbrev zero : ZFRat := mk (0, ⟨1, ZFInt.one_ne_zero⟩)

-- @@ L84-85 verbatim
/-- Imported ZFLean declaration. -/
abbrev one : ZFRat := mk (1, ⟨1, ZFInt.one_ne_zero⟩)


-- @@ L87-87 verbatim
protected instance : Zero ZFRat := ⟨zero⟩

-- @@ L88-88 verbatim
protected instance : One ZFRat := ⟨one⟩


-- @@ L90-90 verbatim
instance : Inhabited ZFRat := ⟨0⟩


-- @@ L92-92 verbatim
theorem zero_eq : (0 : ZFRat) = mk (0, ⟨1, ZFInt.one_ne_zero⟩) := rfl

-- @@ L93-93 verbatim
theorem one_eq : (1 : ZFRat) = mk (1, ⟨1, ZFInt.one_ne_zero⟩) := rfl


-- @@ L95-103 verbatim
theorem mk_eq_zero_iff {n m} : ZFRat.mk (n,m) = 0 ↔ n = 0 where
  mp := by
    intro h
    rw [zero_eq, eq, ZFSet.qrel] at h
    simpa only [mul_one, ne_eq, mul_zero] using h
  mpr := by
    rintro rfl
    apply ZFRat.sound
    rw [ZFSet.qrel, mul_one, mul_zero]


-- @@ L105-113 verbatim
theorem mk_eq_one_iff {n m} : ZFRat.mk (n,m) = 1 ↔ n = m where
  mp := by
    intro h
    rw [one_eq, eq, ZFSet.qrel] at h
    simpa only [ne_eq, mul_one] using h
  mpr := by
    rintro rfl
    apply ZFRat.sound
    rw [ZFSet.qrel, mul_one]


-- @@ L115-118 verbatim
theorem one_ne_zero : (1 : ZFRat) ≠ 0 := by
  intro h
  rw [one_eq, zero_eq, eq, ZFSet.qrel, mul_one, mul_zero] at h
  nomatch ZFInt.one_ne_zero h

-- @@ L119-139 verbatim
/-- Imported ZFLean declaration. -/
noncomputable abbrev add (n m : ZFRat) : ZFRat :=
  Quotient.liftOn₂ n m (fun ⟨a, b⟩ ⟨c, d⟩ ↦
    mk (a * d + b * c, ⟨b.1 * d.1, fun c ↦ nomatch d.2 (ZFInt.mul_eq_zero_of_ne_zero c b.2)⟩))
    fun ⟨x₁, x₂, hx₂⟩ ⟨y₁, y₂, hy₂⟩ ⟨u₁, u₂, hu₂⟩ ⟨v₁, v₂, hv₂⟩ hxu hyv ↦ sound (by
      have h1 : x₁ * u₂ = x₂ * u₁ := hxu
      have h2 : y₁ * v₂ = y₂ * v₁ := hyv
      simp only [ZFSet.qrel]
      conv_lhs =>
        rw [right_distrib]
        conv =>
          lhs
          rw [
            ←mul_assoc, mul_assoc x₁, mul_comm y₂, ←mul_assoc,
            h1, mul_assoc x₂, mul_comm u₁, ←mul_assoc, mul_assoc (x₂ * y₂)]
        conv =>
          rhs
          rw [
            mul_comm u₂, ←mul_assoc, mul_assoc x₂, h2,
            ←mul_assoc, mul_assoc, mul_comm v₁, ←mul_assoc, mul_assoc (x₂ * y₂)]
      rw [←left_distrib])


-- @@ L141-141 verbatim
protected noncomputable instance : Add ZFRat := ⟨ZFRat.add⟩

-- @@ L142-144 verbatim
theorem add_eq (n m : ZFInt × ZFInt') :
  mk n + mk m = mk (n.1 * m.2 + n.2 * m.1,
    ⟨n.2.1 * m.2.1, fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := rfl


-- @@ L146-155 verbatim
theorem add_assoc (n m k : ZFRat) : n + (m + k) = n + m + k := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  induction k using Quotient.ind
  rename_i n m k
  obtain ⟨n₁, n₂, hn₂⟩ := n
  obtain ⟨m₁, m₂, hm₂⟩ := m
  obtain ⟨k₁, k₂, hk₂⟩ := k
  apply ZFRat.sound
  ring


-- @@ L157-164 verbatim
theorem add_comm (n m : ZFRat) : n + m = m + n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  rename_i n m
  obtain ⟨n₁, n₂, hn₂⟩ := n
  obtain ⟨m₁, m₂, hm₂⟩ := m
  apply ZFRat.sound
  ring


-- @@ L166-167 verbatim
lemma add_left_comm (n m k : ZFRat) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]


-- @@ L169-170 verbatim
lemma add_right_comm (n m k : ZFRat) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]


-- @@ L172-174 verbatim
theorem add_zero {x : ZFRat} : x + 0 = x := by
  induction x using Quotient.ind
  simp_rw [mk_eq, zero_eq, ZFRat.add_eq, mul_one, ne_eq, mul_zero, ZFInt.add_zero]


-- @@ L176-177 verbatim
theorem zero_add {x : ZFRat} : 0 + x = x := by
  rw [add_comm, add_zero]

-- @@ L178-183 verbatim
/-- Imported ZFLean declaration. -/
protected abbrev neg (n : ZFRat) : ZFRat := Quotient.liftOn n (fun ⟨x, y⟩ => mk (-x, y))
  fun ⟨x, y, hy⟩ ⟨u, v, hv⟩ h ↦ sound (ZFSet.qrel_eq.symm (by
    dsimp [HasEquiv.Equiv, instHasEquivOfSetoid, ZFSet.instSetoidZFIntZFInt'] at h
    simp only [ZFSet.qrel] at h ⊢
    rw [←ZFInt.neg_mul_distrib, mul_comm, ←h, ZFInt.neg_mul_distrib, mul_comm]))


-- @@ L185-185 verbatim
protected instance : Neg ZFRat := ⟨ZFRat.neg⟩

-- @@ L186-186 verbatim
theorem neg_eq (n : ZFInt × ZFInt') : -mk n = mk (-n.1, n.2) := rfl


-- @@ L188-192 verbatim
theorem neg_neg (n : ZFRat) : -(-n) = n := by
  induction n using Quotient.ind
  apply sound
  rw [_root_.neg_neg]
  exact eq.mp rfl


-- @@ L194-194 verbatim
theorem neg_zero : -(0 : ZFRat) = 0 := rfl


-- @@ L196-197 verbatim
theorem neg_inj {a b : ZFRat} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← neg_neg a, ← neg_neg b, h], congrArg _⟩


-- @@ L199-199 verbatim
theorem neg_eq_zero {a : ZFRat} : -a = 0 ↔ a = 0 := ZFRat.neg_inj (b := 0)

-- @@ L200-200 verbatim
theorem neg_ne_zero {a : ZFRat} : -a ≠ 0 ↔ a ≠ 0 := not_congr neg_eq_zero


-- @@ L202-205 verbatim
theorem add_left_neg {a : ZFRat} : -a + a = 0 := by
  induction a using Quotient.ind
  apply sound
  ring


-- @@ L207-209 verbatim
theorem add_right_neg (a : ZFRat) : a + -a = 0 := by
  rw [add_comm]
  exact add_left_neg


-- @@ L211-212 verbatim
theorem neg_eq_of_add_eq_zero {a b : ZFRat} (h : a + b = 0) : -a = b := by
  rw [← @add_zero (-a), ← h, add_assoc, add_left_neg, zero_add]


-- @@ L214-215 verbatim
theorem eq_neg_of_eq_neg {a b : ZFRat} (h : a = -b) : b = -a := by
  rw [h, neg_neg]


-- @@ L217-217 verbatim
theorem eq_neg_comm {a b : ZFRat} : a = -b ↔ b = -a := ⟨eq_neg_of_eq_neg, eq_neg_of_eq_neg⟩


-- @@ L219-220 verbatim
theorem neg_eq_comm {a b : ZFRat} : -a = b ↔ -b = a := by
  rw [eq_comm, eq_neg_comm, eq_comm]


-- @@ L222-223 verbatim
theorem neg_add_cancel_left (a b : ZFRat) : -a + (a + b) = b := by
  rw [add_assoc, add_left_neg, zero_add]


-- @@ L225-226 verbatim
theorem add_neg_cancel_left (a b : ZFRat) : a + (-a + b) = b := by
  rw [add_assoc, add_right_neg, zero_add]


-- @@ L228-229 verbatim
theorem add_neg_cancel_right (a b : ZFRat) : a + b + -b = a := by
  rw [← add_assoc, add_right_neg, add_zero]


-- @@ L231-232 verbatim
theorem neg_add_cancel_right (a b : ZFRat) : a + -b + b = a := by
  rw [← add_assoc, add_left_neg, add_zero]


-- @@ L234-237 verbatim
theorem add_left_cancel {a b c : ZFRat} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp only [add_assoc, add_left_neg, zero_add] at h₁
  exact h₁


-- @@ L239-241 verbatim
theorem neg_add {a b : ZFRat} : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_right_neg, add_comm a, add_assoc, ← add_assoc b, add_right_neg, add_zero, add_right_neg]



-- @@ L244-245 verbatim
/-- Rational subtraction in the ZF rational model. -/
noncomputable abbrev sub (n m : ZFRat) : ZFRat := n + -m

-- @@ L246-247 verbatim
/-- Imported ZFLean declaration. -/
protected noncomputable instance : Sub ZFRat := ⟨ZFRat.sub⟩

-- @@ L248-252 verbatim
theorem sub_eq (n m : ZFInt × ZFInt') :
  mk n - mk m = mk (n.1 * m.2 - m.1 * n.2, ⟨n.2 * m.2,
    fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := by
  apply sound
  ring


-- @@ L254-254 verbatim
theorem sub_eq_add_neg {a b : ZFRat} : a - b = a + -b := rfl


-- @@ L256-256 verbatim
theorem add_neg_one (i : ZFRat) : i + -1 = i - 1 := rfl


-- @@ L258-258 verbatim
theorem sub_self (a : ZFRat) : a - a = 0 := by rw [sub_eq_add_neg, add_right_neg]


-- @@ L260-260 verbatim
theorem sub_zero (a : ZFRat) : a - 0 = a := by rw [sub_eq_add_neg, neg_zero, add_zero]


-- @@ L262-262 verbatim
theorem zero_sub (a : ZFRat) : 0 - a = -a := by rw [sub_eq_add_neg, zero_add]


-- @@ L264-264 verbatim
theorem sub_eq_zero_of_eq {a b : ZFRat} (h : a = b) : a - b = 0 := by rw [h, sub_self]


-- @@ L266-269 verbatim
theorem eq_of_sub_eq_zero {a b : ZFRat} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [sub_eq_add_neg, neg_add_cancel_right] at this


-- @@ L271-271 verbatim
theorem sub_eq_zero {a b : ZFRat} : a - b = 0 ↔ a = b := ⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩


-- @@ L273-274 verbatim
theorem sub_sub (a b c : ZFRat) : a - b - c = a - (b + c) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, add_assoc]


-- @@ L276-277 verbatim
theorem neg_sub (a b : ZFRat) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]


-- @@ L279-280 verbatim
theorem sub_sub_self (a b : ZFRat) : a - (a - b) = b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_neg_cancel_left]


-- @@ L282-282 verbatim
theorem sub_neg (a b : ZFRat) : a - -b = a + b := by rw [sub_eq_add_neg, neg_neg]

-- @@ L283-283 verbatim
theorem sub_add_cancel (a b : ZFRat) : a - b + b = a := neg_add_cancel_right a b


-- @@ L285-285 verbatim
theorem add_sub_cancel (a b : ZFRat) : a + b - b = a := add_neg_cancel_right a b


-- @@ L287-288 verbatim
theorem add_sub_assoc (a b c : ZFRat) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]


-- @@ L290-292 verbatim
theorem sub_left_cancel (a b c : ZFRat) : a - c = b - c → a = b := by
  intro h
  rwa [← sub_eq_zero, sub_sub, sub_eq_zero, ← add_sub_assoc, add_comm, add_sub_cancel] at h


-- @@ L294-296 verbatim
theorem sub_right_cancel (a b c : ZFRat) : c - a = c - b → a = b := by
  rw [← neg_sub a, ← neg_sub b, neg_inj]
  apply sub_left_cancel


-- @@ L298-300 verbatim
theorem add_eq_sub_iff {a b c : ZFRat} : a + b = c ↔ a = c - b where
  mp := fun h => by rw [← h, add_sub_cancel]
  mpr := fun h => by rw [h, sub_add_cancel]



-- @@ L303-306 verbatim
/-- Repeated addition by a natural-number scalar. -/
noncomputable abbrev nsmul : ℕ → ZFRat → ZFRat
  | 0, _ => 0
  | n+1, m => m + nsmul n m


-- @@ L308-312 verbatim
/-- Integer scalar multiplication defined using repeated addition and negation. -/
noncomputable abbrev zsmul (n : ℤ) (x : ZFRat) : ZFRat :=
  match n with
  | .ofNat n => nsmul n x
  | .negSucc n => -nsmul (n+1) x

-- @@ L313-323 verbatim
/-- Imported ZFLean declaration. -/
noncomputable abbrev mul (n m : ZFRat) : ZFRat :=
  Quotient.liftOn₂ n m
    (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ ↦ mk (a * c,
      ⟨b * d, fun c ↦ nomatch hd (ZFInt.mul_eq_zero_of_ne_zero c hb)⟩))
    fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ ⟨i, j, hi⟩ h h' ↦ by
      apply sound
      unfold_projs at h h'
      simp only [ZFSet.qrel] at h h' ⊢
      ac_change (a * f) * (c * j) = (b * e) * (d * i)
      rw [h, h']


-- @@ L325-325 verbatim
noncomputable instance : Mul ZFRat := ⟨ZFRat.mul⟩

-- @@ L326-328 verbatim
theorem mul_eq (n m : ZFInt × ZFInt') :
  mk n * mk m = mk (n.1 * m.1, ⟨n.2 * m.2,
    fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := rfl


-- @@ L330-334 verbatim
theorem mul_comm (n m : ZFRat) : n * m = m * n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  apply sound
  ring


-- @@ L336-341 verbatim
theorem left_distrib (a b c : ZFRat) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  ring


-- @@ L343-344 verbatim
theorem right_distrib (a b c : ZFRat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm b c]


-- @@ L346-349 verbatim
theorem zero_mul (a : ZFRat) : 0 * a = 0 := by
  induction a using Quotient.ind
  apply sound
  ring


-- @@ L351-352 verbatim
theorem mul_zero (a : ZFRat) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]


-- @@ L354-359 verbatim
theorem mul_assoc (a b c : ZFRat) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  ring


-- @@ L361-364 verbatim
theorem one_mul (a : ZFRat) : 1 * a = a := by
  induction a using Quotient.ind
  apply sound
  ring


-- @@ L366-367 verbatim
theorem mul_one (a : ZFRat) : a * 1 = a := by
  rw [mul_comm, one_mul]


-- @@ L369-378 verbatim
theorem mul_eq_zero_iff {a b : ZFRat} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    induction a using Quotient.ind
    induction b using Quotient.ind
    simp_rw [mk_eq, mul_eq, zero_eq, eq, ZFSet.qrel, ZFInt.mul_zero, ZFInt.mul_one] at h ⊢
    rwa [←ZFInt.mul_eq_zero_iff]
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]



-- @@ L381-404 verbatim
noncomputable instance : CommRing ZFRat where
  zero := 0
  one := 1
  add := add
  add_assoc _ _ _ := by rw [add_assoc]
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFRat.nsmul
  nsmul_zero _ := rfl
  nsmul_succ _ _ := add_comm _ _
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zsmul := ZFSet.ZFRat.zsmul
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := add_comm _ _
  zsmul_neg' _ _ := rfl
  neg_add_cancel _ := add_left_neg



-- @@ L407-408 verbatim
/-- The subtype of nonzero ZF rational numbers. -/
abbrev ZFRat' := {x : ZFRat // x ≠ 0}

-- @@ L409-426 verbatim
/-- Imported ZFLean declaration. -/
protected noncomputable abbrev inv : ZFRat' → ZFRat' := fun ⟨x, hx⟩ ↦ by
  let a := x.out.1
  let hb := x.out.2.2
  set b := x.out.2.1
  have : a ≠ 0 := by
    intro contr
    have : mk (0, ⟨b, hb⟩) = x := by
      have : x.out = (0, ⟨b, hb⟩) := Prod.ext contr rfl
      rw [←this]
      exact mk_out x
    obtain rfl : x = 0 := by
      rw [←this, zero_eq, eq, ZFSet.qrel, ZFInt.mul_one, ZFInt.mul_zero]
    contradiction
  exact ⟨mk (b, ⟨a, this⟩), by
    intro h
    rw [mk_eq_zero_iff] at h
    contradiction⟩


-- @@ L428-428 verbatim
noncomputable instance : Inv ZFRat' := ⟨ZFRat.inv⟩

-- @@ L429-431 verbatim
open Classical in
noncomputable instance : Inv ZFRat where
  inv x := if hx : x ≠ 0 then ZFRat.inv ⟨x, hx⟩ else 0


-- @@ L433-435 verbatim
theorem inv_eq {a : ZFRat} (ha : a ≠ 0) : a⁻¹ = (⟨a, ha⟩ : ZFRat')⁻¹ := by
  dsimp [Inv.inv]
  rw [dite_eq_left ha]


-- @@ L437-438 verbatim
/-- Division by a nonzero ZF rational. -/
noncomputable abbrev hdiv (n : ZFRat) (m : ZFRat') : ZFRat := n * m⁻¹

-- @@ L439-442 verbatim
open Classical in
/-- Division on ZF rational numbers, with division by zero sent to zero. -/
noncomputable abbrev div (n m : ZFRat) : ZFRat :=
  if hm : m ≠ 0 then hdiv n ⟨m, hm⟩ else 0

-- @@ L443-444 verbatim
/-- Imported ZFLean declaration. -/
noncomputable instance : HDiv ZFRat ZFRat' ZFRat := ⟨hdiv⟩

-- @@ L445-446 verbatim
/-- Imported ZFLean declaration. -/
noncomputable instance : Div ZFRat := ⟨div⟩



-- @@ L449-449 verbatim
theorem div_eq {n m : ZFRat} (hm : m ≠ 0) : n / m = n / (⟨m, hm⟩:ZFRat') := rfl

-- @@ L450-452 verbatim
theorem div_eq_mul_inv {n m : ZFRat} (hm : m ≠ 0) : n / m = n * (⟨m, hm⟩:ZFRat')⁻¹ := by
  dsimp [HDiv.hDiv, Div.div]
  rw [div, dite_eq_left hm]


-- @@ L454-464 verbatim
@[simp]
theorem mul_inv' {a : ZFRat'} : a.1 * a⁻¹ = 1 := by
  obtain ⟨a, ha⟩ := a
  induction a using Quotient.ind
  rename_i a
  apply sound
  rw [ZFSet.qrel]
  simp only [mk_eq, ZFInt.mul_one, ne_eq]
  change ZFSet.qrel ⟨a.1, ⟨a.2.1, a.2.2⟩⟩ (mk a).out
  rw [←eq]
  simp_all

-- @@ L465-466 verbatim
theorem mul_inv {a : ZFRat} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_eq ha, @mul_inv' (⟨a, ha⟩ : ZFRat')]


-- @@ L468-470 verbatim
theorem inv_mul' {a : ZFRat'} : a⁻¹ * a.1 = 1 := by
  rw [mul_comm]
  exact mul_inv'

-- @@ L471-473 verbatim
theorem inv_mul {a : ZFRat} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv ha


-- @@ L475-476 verbatim
noncomputable instance : RatCast ZFRat where
  ratCast q := ((q.num : ZFRat) / (q.den : ZFRat))


-- @@ L478-479 verbatim
/-- Rational scalar multiplication through the encoded rational field. -/
noncomputable def qsmul (k : ℚ) (m : ZFRat) : ZFRat := (k : ZFRat) * m


-- @@ L481-483 verbatim
/-- Nonnegative rational scalar multiplication through the encoded rational field. -/
noncomputable def nnqsmul : ℚ≥0 → ZFRat → ZFRat :=
  fun ⟨k, _⟩ m ↦ qsmul k m


-- @@ L485-520 verbatim
open Classical in
noncomputable instance : DivisionRing ZFRat where
  exists_pair_ne := ⟨1, 0, one_ne_zero⟩
  mul_inv_cancel _ := mul_inv
  inv_zero := by
    simp only [Inv.inv, ne_eq, not_true_eq_false, dite_false]
  div_eq_mul_inv := by
    intro a b
    by_cases hb : b = 0
    · subst b
      dsimp [HDiv.hDiv, Div.div, div, Inv.inv]
      simp_all
    · rw [div_eq_mul_inv hb, ←inv_eq]
  qsmul := qsmul
  nnqsmul := nnqsmul
  ratCast_def _ := rfl
  qsmul_def _ _ := by rfl
  nnqsmul_def := by
    rintro ⟨k, hk⟩ m
    unfold nnqsmul qsmul
    dsimp
    unfold_projs
    have : (↑k.num.natAbs : ZFRat) = ↑k.num := by
      unfold Int.natAbs
      cases k using Rat.casesOn with
      | mk' n d hd _ =>
        simp only [Rat.le_iff, Rat.num_ofNat, MulZeroClass.zero_mul, Rat.den_ofNat, Nat.cast_one,
          _root_.mul_one] at hk
        dsimp
        have : n = Int.ofNat n.natAbs := by
          rw [Int.ofNat_eq_natCast, ←Int.eq_natAbs_of_nonneg hk]
        rw [this]
        rfl
    dsimp [NNRat.cast, NNRatCast.nnratCast, NNRat.castRec]
    rw [this]
    rfl


-- @@ L522-522 verbatim
noncomputable instance : Field ZFRat := {}


-- @@ L524-524 verbatim
end ZFRat

-- @@ L525-525 verbatim
end ZFSet
