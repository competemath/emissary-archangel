/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Basic.IOpen
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L13-13 verbatim
/-! # Pow2 -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Arith


-- @@ L23-23 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L25-25 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L27-27 verbatim
section «lp_section_1»


-- @@ L29-29 expanded
variable [ModelsTheory V iOpen]


-- @@ L31-32 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Pow2 (a : V) : Prop := 0 < a ∧ ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r


-- @@ L34-36 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pow2Def : Sg0.Semisentence 1 :=
  .mkSigma
    (Wedge.wedge (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, #0])
      (Semiformula.ballLTSucc (#0)
        (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 1, #0])
          (Arrow.arrow (LO.FirstOrder.Rewriting.substitute dvd.val (vecCons (#0) (vecCons #1 ![])))
            (LO.FirstOrder.Rewriting.substitute dvd.val
              (vecCons (Semiterm.numeral 2) (vecCons #0 ![])))))))
    (by simp [])


-- @@ L38-41 expanded
lemma pow2_defined : DefinedPred Sg0 (Pow2 : V → Prop) pow2Def :=
  by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Pow2, pow2Def,
    le_iff_lt_succ, dvd_defined.df.iff, numeral_eq_natCast]


-- @@ L43-43 expanded
instance pow2_definable : BoldfacePred Sg0 (Pow2 : V → Prop) :=
  pow2_defined.to_definable


-- @@ L45-45 verbatim
lemma _root_.LO.Arith.Pow2.pos {a : V} (h : Pow2 a) : 0 < a := h.1


-- @@ L47-49 verbatim
lemma _root_.LO.Arith.Pow2.dvd {a : V} (h : Pow2 a) {r} (hr : r ≤ a) :
    1 < r → r ∣ a → 2 ∣ r :=
  h.2 r hr


-- @@ L51-52 verbatim
@[simp] lemma pow2_one : Pow2 (1 : V) := ⟨by simp, by
  simp_all⟩


-- @@ L54-54 verbatim
@[simp] lemma not_pow2_zero : ¬Pow2 (0 : V) := by intro h; have := h.pos; simp at this


-- @@ L56-58 verbatim
lemma _root_.LO.Arith.Pow2.two_dvd {a : V} (h : Pow2 a) (lt : 1 < a) :
    2 ∣ a :=
  h.dvd (le_refl _) lt (by simp)


-- @@ L60-65 verbatim
lemma _root_.LO.Arith.Pow2.two_dvd' {a : V} (h : Pow2 a) (lt : a ≠ 1) : 2 ∣ a :=
  h.dvd (le_refl _) (by
    by_contra A
    have A : a = 0 ∨ a = 1 := le_one_iff_eq_zero_or_one.mp (not_lt.mp A)
    rcases A with (rfl | rfl) <;> simp at h lt)
    (by simp)


-- @@ L67-73 verbatim
lemma _root_.LO.Arith.Pow2.of_dvd {a b : V} (h : b ∣ a) : Pow2 a → Pow2 b := by
  intro ha
  have : 0 < b := by
    by_contra e
    simp_all
  exact ⟨this, fun r hr ltr hb ↦
    ha.dvd (show r ≤ a from le_trans hr (le_of_dvd ha.pos h)) ltr (dvd_trans hb h)⟩


-- @@ L75-87 verbatim
lemma pow2_mul_two {a : V} : Pow2 (2 * a) ↔ Pow2 a :=
  ⟨by intro H
      have : ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r := by
        intro r hr ltr dvd
        exact H.dvd (show r ≤ 2 * a from le_trans hr (le_mul_of_one_le_left (by simp) one_le_two))
          ltr (Dvd.dvd.mul_left dvd 2)
      exact ⟨by simpa using H.pos, this⟩,
   by intro H
      exact ⟨by simpa using H.pos, by
        intro r _ hr hd
        rcases two_prime.left_dvd_or_dvd_right_of_dvd_mul hd with (hd | hd)
        · exact hd
        · exact H.dvd (show r ≤ a from le_of_dvd H.pos hd) hr hd⟩⟩


-- @@ L89-90 verbatim
lemma pow2_mul_four {a : V} : Pow2 (4 * a) ↔ Pow2 a := by
  simp [←two_mul_two_eq_four, mul_assoc, pow2_mul_two]


-- @@ L92-100 verbatim
lemma _root_.LO.Arith.Pow2.elim {p : V} : Pow2 p ↔ p = 1 ∨ ∃ q, p = 2 * q ∧ Pow2 q :=
  ⟨by intro H
      by_cases hp : 1 < p
      · have : 2 ∣ p := H.two_dvd hp
        rcases this with ⟨q, rfl⟩
        right; exact ⟨q, rfl, pow2_mul_two.mp H⟩
      · have : p = 1 := le_antisymm (by simpa using hp) (pos_iff_one_le.mp H.pos)
        left; exact this,
   by rintro (rfl | ⟨q, rfl, hq⟩) <;> simp [pow2_one, pow2_mul_two, *]⟩


-- @@ L102-102 verbatim
@[simp] lemma pow2_two : Pow2 (2 : V) := Pow2.elim.mpr (Or.inr ⟨1, by simp⟩)


-- @@ L104-107 verbatim
lemma _root_.LO.Arith.Pow2.div_two {p : V} (h : Pow2 p) (ne : p ≠ 1) : Pow2 (p / 2) := by
  rcases Pow2.elim.mp h with (rfl | ⟨q, rfl, pq⟩)
  · simp at ne
  simpa


-- @@ L109-112 verbatim
lemma _root_.LO.Arith.Pow2.two_mul_div_two {p : V} (h : Pow2 p) (ne : p ≠ 1) : 2 * (p / 2) = p := by
  rcases Pow2.elim.mp h with (rfl | ⟨q, rfl, _⟩)
  · simp at ne
  simp


-- @@ L114-115 verbatim
lemma _root_.LO.Arith.Pow2.div_two_mul_two {p : V} (h : Pow2 p) (ne : p ≠ 1) : (p / 2) * 2 = p := by
  simp [mul_comm, h.two_mul_div_two ne]


-- @@ L117-121 verbatim
lemma _root_.LO.Arith.Pow2.elim' {p : V} : Pow2 p ↔ p = 1 ∨ 1 < p ∧ ∃ q, p = 2 * q ∧ Pow2 q := by
  by_cases hp : 1 < p <;> simp only [hp, true_and, false_and, or_false]
  · exact Pow2.elim
  · have : p = 0 ∨ p = 1 := le_one_iff_eq_zero_or_one.mp (show p ≤ 1 from by simpa using hp)
    rcases this with (rfl | rfl) <;> simp



-- @@ L124-124 verbatim
section «lp_section_2»


-- @@ L126-127 verbatim
/-- $\mathrm{LenBit} (2^i, a) \iff \text{$i$th-bit of $a$ is $1$}$. -/
def LenBit (i a : V) : Prop := ¬2 ∣ (a / i)


-- @@ L129-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.lenbitDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute divDef.val
          (vecCons (#0) (vecCons (#2) (vecCons #1 ![]))))
        (Tilde.tilde
          (LO.FirstOrder.Rewriting.substitute dvd.val
            (vecCons (Semiterm.numeral 2) (vecCons #0 ![]))))))
    (by simp)


-- @@ L133-134 expanded
lemma lenbit_defined : DefinedRel Sg0 (LenBit : V → V → Prop) lenbitDef := by intro v;
  simp [lenbitDef, LenBit, numeral_eq_natCast]


-- @@ L136-137 verbatim
@[simp] lemma lenbit_defined_iff (v) :
    Semiformula.Evalbm V v lenbitDef.val ↔ LenBit (v 0) (v 1) := lenbit_defined.df.iff v


-- @@ L139-139 expanded
instance lenbit_definable : BoldfaceRel Sg0 (LenBit : V → V → Prop) :=
  lenbit_defined.to_definable


-- @@ L141-142 verbatim
lemma _root_.LO.Arith.LenBit.le {i a : V} (h : LenBit i a) : i ≤ a := by
  by_contra A; simp [LenBit, show a < i from by simpa using A] at h


-- @@ L144-144 verbatim
lemma not_lenbit_of_lt {i a : V} (h : a < i) : ¬LenBit i a := by intro A; exact not_le.mpr h A.le


-- @@ L146-146 verbatim
@[simp] lemma _root_.LO.Arith.LenBit.zero (a : V) : ¬LenBit 0 a := by simp [LenBit]


-- @@ L148-148 verbatim
@[simp] lemma _root_.LO.Arith.LenBit.on_zero (a : V) : ¬LenBit a 0 := by simp [LenBit]


-- @@ L150-150 verbatim
lemma _root_.LO.Arith.LenBit.one (a : V) : LenBit 1 a ↔ ¬2 ∣ a := by simp [LenBit]


-- @@ L152-154 verbatim
lemma _root_.LO.Arith.LenBit.iff_rem {i a : V} : LenBit i a ↔ (a / i) % 2 = 1 := by
  simp only [LenBit, ←mod_eq_zero_iff_dvd]
  simp_all


-- @@ L156-157 verbatim
lemma not_lenbit_iff_rem {i a : V} : ¬LenBit i a ↔ (a / i) % 2 = 0 := by
  simp [LenBit, ←mod_eq_zero_iff_dvd]


-- @@ L159-160 verbatim
@[simp] lemma _root_.LO.Arith.LenBit.self {a : V} (pos : 0 < a) :
    LenBit a a := by simp [LenBit.iff_rem, pos]


-- @@ L162-176 verbatim
lemma _root_.LO.Arith.LenBit.mod {i a k : V} (h : 2 * i ∣ k) : LenBit i (a % k) ↔ LenBit i a := by
  have : 0 ≤ i := zero_le i
  rcases (eq_or_lt_of_le this) with (rfl | pos)
  · simp
  rcases h with ⟨k', hk'⟩
  calc
    LenBit i (a % k) ↔ ((a % k) / i) % 2 = 1                            := LenBit.iff_rem
    _                  ↔ ((2 * k') * (a / k) + a % k / i) % 2 = 1       := by simp [mul_assoc]
    _                  ↔ (((2 * k') * (a / k) * i + a % k) / i) % 2 = 1 := by
      simp [div_mul_add_self, pos]
    _                  ↔ ((k * (a / k) + a % k) / i) % 2 = 1            := iff_of_eq (by
      congr 3
      simp [mul_right_comm _ (a / k), mul_right_comm 2 k' i, ←hk'])
    _                  ↔ LenBit i a                                     := by
      simp [div_add_mod a k, LenBit.iff_rem]


-- @@ L178-180 verbatim
@[simp] lemma _root_.LO.Arith.LenBit.mod_two_mul_self {a i : V} :
    LenBit i (a % (2 * i)) ↔ LenBit i a :=
  LenBit.mod (by simp)


-- @@ L182-191 verbatim
lemma _root_.LO.Arith.LenBit.add {i a b : V} (h : 2 * i ∣ b) : LenBit i (a + b) ↔ LenBit i a := by
  have : 0 ≤ i := zero_le i
  rcases (eq_or_lt_of_le this) with (rfl | pos)
  · simp
  rcases h with ⟨b', hb'⟩
  have hb' : b = 2 * b' * i := by simp [hb', mul_right_comm]
  calc
    LenBit i (a + b) ↔ ((a + b) / i) % 2 = 1    := LenBit.iff_rem
    _                ↔ (a / i + 2 * b') % 2 = 1 := by rw [hb', div_add_mul_self _ _ pos]
    _                ↔ LenBit i a               := by simp [LenBit.iff_rem]


-- @@ L193-195 verbatim
lemma _root_.LO.Arith.LenBit.add_self {i a : V} (h : a < i) : LenBit i (a + i) := by
  have pos : 0 < i := by exact pos_of_gt h
  simp [LenBit.iff_rem, div_add_self_right _ pos, h]


-- @@ L197-201 verbatim
lemma _root_.LO.Arith.LenBit.add_self_of_not_lenbit {a i : V} (pos : 0 < i) (h : ¬LenBit i a) :
    LenBit i (a + i) := by
  have : a / i % 2 = 0 := by simpa [LenBit.iff_rem] using h
  simp only [LenBit.iff_rem, div_add_self_right _ pos]
  rw [mod_add] <;> simp [this]


-- @@ L203-207 verbatim
lemma _root_.LO.Arith.LenBit.add_self_of_lenbit {a i : V} (pos : 0 < i) (h : LenBit i a) :
    ¬LenBit i (a + i) := by
  have : a / i % 2 = 1 := by simpa [LenBit.iff_rem] using h
  simp only [LenBit.iff_rem, div_add_self_right _ pos]
  rw [mod_add] <;> simp [this, one_add_one_eq_two]


-- @@ L209-213 verbatim
lemma _root_.LO.Arith.LenBit.sub_self_of_lenbit {a i : V} (pos : 0 < i) (h : LenBit i a) :
    ¬LenBit i (a - i) := by
  intro h'
  have : ¬LenBit i a := by simpa [sub_add_self_of_le h.le] using LenBit.add_self_of_lenbit pos h'
  contradiction


-- @@ L215-215 verbatim
end «lp_section_2»


-- @@ L217-217 verbatim
end «lp_section_1»


-- @@ L219-219 verbatim
section «lp_section_3»


-- @@ L221-221 expanded
variable [ModelsTheory V (iSigma 0)]


-- @@ L223-223 verbatim
namespace Pow2


-- @@ L225-247 expanded
lemma mul {a b : V} (ha : Pow2 a) (hb : Pow2 b) : Pow2 (a * b) :=
  by
  wlog hab : a ≤ b
  · simpa [mul_comm] using this hb ha (lt_of_not_ge hab).le
  suffices ∀ b : V, ∀ a ≤ b, Pow2 a → Pow2 b → Pow2 (a * b) by exact this b a hab ha hb
  intro b
  induction b using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind IH a b IH =>
    intro a hab ha hb
    have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ Pow2 a' := Pow2.elim'.mp ha
    rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
    · simpa using hb
    · have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ Pow2 b' := Pow2.elim'.mp hb
      rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
      · simpa using ha
      · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr <| by rintro rfl; simp at ltb)
        have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
        have : Pow2 (a * b) := IH b ltb a hab (by assumption) (by assumption)
        suffices Pow2 (4 * a * b)
          by
          have : (2 * a) * (2 * b) = 4 * a * b := by
            simp [mul_assoc, mul_left_comm a 2 b, ← two_mul_two_eq_four]
          simpa [this]
        simpa [mul_assoc, pow2_mul_four] using this


-- @@ L249-250 verbatim
@[simp] lemma mul_iff {a b : V} : Pow2 (a * b) ↔ Pow2 a ∧ Pow2 b :=
  ⟨fun h ↦ ⟨h.of_dvd (by simp), h.of_dvd (by simp)⟩, by rintro ⟨ha, hb⟩; exact ha.mul hb⟩


-- @@ L252-252 verbatim
@[simp] lemma sq_iff {a : V} : Pow2 (a ^ 2) ↔ Pow2 a := by simp [_root_.sq]


-- @@ L254-254 verbatim
lemma sq {a : V} : Pow2 a → Pow2 (a ^ 2) := by simp [_root_.sq]


-- @@ L256-272 expanded
lemma dvd_of_le {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b → a ∣ b :=
  by
  suffices ∀ b : V, ∀ a ≤ b, Pow2 a → Pow2 b → a ∣ b by intro hab; exact this b a hab ha hb
  intro b; induction b using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind b IH =>
    intro a hab ha hb
    have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ Pow2 b' := Pow2.elim'.mp hb
    rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
    · rcases le_one_iff_eq_zero_or_one.mp hab with (rfl | rfl) <;> simp
      · simp at ha
    · have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ Pow2 a' := Pow2.elim'.mp ha
      rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
      · simp
      · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr <| by rintro rfl; simp at ltb)
        have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
        exact mul_dvd_mul_left 2 <| IH b ltb a hab (by assumption) (by assumption)


-- @@ L274-275 verbatim
lemma le_iff_dvd {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b ↔ a ∣ b :=
  ⟨Pow2.dvd_of_le ha hb, le_of_dvd hb.pos⟩


-- @@ L277-277 verbatim
lemma two_le {a : V} (pa : Pow2 a) (ne1 : a ≠ 1) : 2 ≤ a := le_of_dvd pa.pos (pa.two_dvd' ne1)


-- @@ L279-295 verbatim
lemma le_iff_lt_two {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b ↔ a < 2 * b := by
  constructor
  · intro h; exact lt_of_le_of_lt h (lt_two_mul_self hb.pos)
  · intro h
    by_cases ea : a = 1
    · rcases ea with rfl
      simpa [←pos_iff_one_le] using hb.pos
    · suffices a ∣ b from le_of_dvd hb.pos this
      have : a / 2 ∣ b := by
        have : 2 * (a / 2) ∣ 2 * b := by
          simpa [ha.two_mul_div_two ea] using dvd_of_le ha (by simpa using hb) (LT.lt.le h)
        exact (mul_dvd_mul_iff_left (by simp)).mp this
      rcases this with ⟨b', rfl⟩
      have hb' : Pow2 b' := (mul_iff.mp hb).2
      have : 2 ∣ b' := hb'.two_dvd' (by rintro rfl; simp [ha.two_mul_div_two ea] at h)
      rcases this with ⟨b'', rfl⟩
      simp [←mul_assoc, ha.div_two_mul_two ea]


-- @@ L297-300 verbatim
lemma lt_iff_two_mul_le {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a < b ↔ 2 * a ≤ b := by
  by_cases eb : b = 1
  · simp [eb, ←lt_two_iff_le_one]
  · rw [←hb.two_mul_div_two eb]; simp [le_iff_lt_two ha (hb.div_two eb)]


-- @@ L302-316 expanded
lemma sq_or_dsq {a : V} (pa : Pow2 a) : ∃ b, a = b ^ 2 ∨ a = 2 * b ^ 2 :=
  by
  suffices ∃ b ≤ a, a = b ^ 2 ∨ a = 2 * b ^ 2
    by
    rcases this with ⟨b, _, h⟩
    exact ⟨b, h⟩
  induction a using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind a IH =>
    rcases Pow2.elim'.mp pa with (rfl | ⟨ha, a, rfl, pa'⟩)
    · exact ⟨1, by simp⟩
    · have : 0 < a := by simpa [← pos_iff_one_le] using one_lt_iff_two_le.mp ha
      rcases IH a (lt_mul_of_one_lt_left this one_lt_two) pa' with ⟨b, _, (rfl | rfl)⟩
      · exact ⟨b, le_trans (by simp) le_two_mul_left, by right; rfl⟩
      · exact ⟨2 * b, by simp_all, by left; simp [_root_.sq, mul_assoc, mul_left_comm]⟩


-- @@ L318-318 expanded
lemma sqrt {a : V} (h : Pow2 a) (hsq : (sqrt a) ^ 2 = a) : Pow2 (sqrt a) := by rw [← hsq] at h;
  simpa using h


-- @@ L320-323 verbatim
@[simp] lemma not_three : ¬Pow2 (3 : V) := by
  intro h
  have : (2 : V) ∣ 3 := h.two_dvd (by simp [←two_add_one_eq_three])
  simp [←two_add_one_eq_three, ←mod_eq_zero_iff_dvd] at this


-- @@ L325-329 verbatim
lemma four_le {i : V} (hi : Pow2 i) (lt : 2 < i) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;>
    simp at lt hi


-- @@ L331-344 verbatim
lemma mul_add_lt_of_mul_lt_of_pos {a b p q : V} (hp : Pow2 p) (hq : Pow2 q)
    (h : a * p < q) (hb : b < p) (hbq : b < q) : a * p + b < q := by
  rcases zero_le a with (rfl | pos)
  · simp [hbq]
  have hpq : p < q :=
    lt_of_le_of_lt (le_mul_of_pos_left (a := p) pos) (by simpa [mul_comm a p] using h)
  have : p ∣ q := dvd_of_le hp hq (le_of_lt hpq)
  rcases this with ⟨q, rfl⟩
  have : a < q := lt_of_mul_lt_mul_right (a := p) (by simpa [mul_comm] using h)
  calc
    a * p + b < (a + 1) * p := by simp [add_mul, hb]
    _         ≤ p * q       := by
      rw [mul_comm p q]
      exact mul_le_mul_right (lt_iff_succ_le.mp this)


-- @@ L346-346 verbatim
end Pow2


-- @@ L348-350 verbatim
lemma _root_.LO.Arith.LenBit.mod_pow2 {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : i < j) :
    LenBit i (a % j) ↔ LenBit i a :=
  LenBit.mod (by rw [←Pow2.le_iff_dvd] <;> simp [pi, pj, ←Pow2.lt_iff_two_mul_le, h])


-- @@ L352-354 verbatim
lemma _root_.LO.Arith.LenBit.add_pow2 {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : i < j) :
    LenBit i (a + j) ↔ LenBit i a :=
  LenBit.add (by rw [←Pow2.le_iff_dvd] <;> simp [pi, pj, ←Pow2.lt_iff_two_mul_le, h])


-- @@ L356-365 verbatim
lemma _root_.LO.Arith.LenBit.add_pow2_iff_of_lt {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h :
    a < j) :
    LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self h]
  · have : a + j < i := calc
      a + j < 2 * j  := by simp[two_mul, h]
      _     ≤ i      := (pj.lt_iff_two_mul_le pi).mp hij
    simp [not_lenbit_of_lt this, not_lenbit_of_lt (show a < i from lt_trans h hij), hij.ne.symm]


-- @@ L367-380 verbatim
lemma lenbit_iff_add_mul {i a : V} (hi : Pow2 i) :
    LenBit i a ↔ ∃ k, ∃ r < i, a = k * (2 * i) + i + r := by
  constructor
  · intro h
    have : 2 * ((a / i) / 2) + 1 = a / i := by
      simpa [LenBit.iff_rem.mp h] using div_add_mod (a / i) 2
    have : a = ((a / i) / 2) * (2 * i) + i + (a % i) := calc
      a = i * (a / i) + (a % i)                  := Eq.symm <| div_add_mod a i
      _ = i * (2 * ((a / i) / 2) + 1) + (a % i) := by simp [this]
      _ = ((a / i) / 2) * (2 * i) + i + (a % i) := by
        simp [mul_add, ←mul_assoc, mul_comm i 2, mul_comm (2 * i)]
    exact ⟨(a / i) / 2, a % i, by simp [hi.pos], this⟩
  · rintro ⟨k, r, h, rfl⟩
    simp [LenBit.iff_rem, ←mul_assoc, add_assoc, div_mul_add_self, hi.pos, h]


-- @@ L382-394 verbatim
lemma not_lenbit_iff_add_mul {i a : V} (hi : Pow2 i) :
    ¬LenBit i a ↔ ∃ k, ∃ r < i, a = k * (2 * i) + r := by
  constructor
  · intro h
    have : 2 * ((a / i) / 2) = a / i := by
      simpa [not_lenbit_iff_rem.mp h] using div_add_mod (a / i) 2
    have : a = ((a / i) / 2) * (2 * i) + (a % i) := calc
      a = i * (a / i) + (a % i)              := Eq.symm <| div_add_mod a i
      _ = i * (2 * ((a / i) / 2)) + (a % i) := by simp [this]
      _ = ((a / i) / 2) * (2 * i) + (a % i) := by simp [←mul_assoc, mul_comm i 2, mul_comm (2 * i)]
    exact ⟨(a / i) / 2, a % i, by simp [hi.pos], this⟩
  · rintro ⟨k, r, h, rfl⟩
    simp [not_lenbit_iff_rem, ←mul_assoc, div_mul_add_self, hi.pos, h]


-- @@ L396-414 verbatim
lemma lenbit_mul_add {i j a r : V} (pi : Pow2 i) (pj : Pow2 j) (hr : r < j) :
    LenBit (i * j) (a * j + r) ↔ LenBit i a := by
  by_cases h : LenBit i a
  · simp only [h, iff_true]
    rcases (lenbit_iff_add_mul pi).mp h with ⟨a, b, hb, rfl⟩
    have : b * j + r < i * j :=
      pj.mul_add_lt_of_mul_lt_of_pos (by simp[pi,
        pj]) (Arith.mul_lt_mul b i j hb pj.pos) hr (lt_of_lt_of_le hr <| le_mul_of_pos_left <|
            pi.pos)
    exact (lenbit_iff_add_mul (by simp [pi, pj])).mpr ⟨a, b * j + r, this, by simp [add_mul,
      add_assoc, mul_assoc]⟩
  · simp only [h, iff_false]
    rcases (not_lenbit_iff_add_mul pi).mp h with ⟨a, b, hb, rfl⟩
    have : b * j + r < i * j :=
      pj.mul_add_lt_of_mul_lt_of_pos (by simp[pi,
        pj]) (Arith.mul_lt_mul b i j hb pj.pos) hr (lt_of_lt_of_le hr <| le_mul_of_pos_left <|
            pi.pos)
    exact (not_lenbit_iff_add_mul (by simp [pi, pj])).mpr ⟨a, b * j + r, this, by simp [add_mul,
      add_assoc, mul_assoc]⟩


-- @@ L416-435 verbatim
lemma lenbit_add_pow2_iff_of_not_lenbit {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : ¬LenBit j a) :
    LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self_of_not_lenbit pi.pos, h]
  · simp only [ne_of_gt hij, false_or]
    have : 2 * j ∣ i := Pow2.dvd_of_le (by simp [pj]) pi <| (pj.lt_iff_two_mul_le pi).mp hij
    rcases this with ⟨i, rfl⟩
    rcases (not_lenbit_iff_add_mul pj).mp h with ⟨a, r, hr, rfl⟩
    have pi' : Pow2 i := (Pow2.mul_iff.mp pi).2
    have pj' : Pow2 j := (Pow2.mul_iff.mp (Pow2.mul_iff.mp pi).1).2
    calc
      LenBit (2 * j * i) (a * (2 * j) + r + j) ↔ LenBit (i * (2 * j)) (a * (2 * j) + (r + j)) := by
        simp [mul_comm (2 * j), add_assoc]
      _                                        ↔ LenBit i a                                   :=
        lenbit_mul_add pi' (by simpa using pj') (by simp [two_mul, hr])
      _                                        ↔ LenBit (i * (2 * j)) (a * (2 * j) + r)       :=
        Iff.symm <| lenbit_mul_add pi' (by simpa using pj') (lt_of_lt_of_le hr <| by simp)
      _                                        ↔ LenBit (2 * j * i) (a * (2 * j) + r)         := by
        simp [mul_comm]


-- @@ L437-449 verbatim
lemma lenbit_sub_pow2_iff_of_lenbit {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : LenBit j a) :
    LenBit i (a - j) ↔ i ≠ j ∧ LenBit i a := by
  generalize ha' : a - j = a'
  have h' : ¬LenBit j a' := by simpa [←ha'] using LenBit.sub_self_of_lenbit pj.pos h
  have : a = a' + j := by simp [←ha', sub_add_self_of_le h.le]
  rcases this with rfl
  have : LenBit i (a' + j) ↔ i = j ∨ LenBit i a' := lenbit_add_pow2_iff_of_not_lenbit pi pj h'
  rw [this]
  simp only [and_or_left, ne_eq]
  constructor
  · intro hi
    exact Or.inr ⟨by rintro rfl; exact h' hi, hi⟩
  · simp_all


-- @@ L451-451 verbatim
end «lp_section_3»


-- @@ L453-453 verbatim
end Arith

-- @@ L454-454 verbatim
end LO


-- @@ L456-456 verbatim
end «lp_nc_section_1»
