/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaZero.Exponential.Exp
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L12-12 verbatim
/-! # Log -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L19-19 verbatim
open scoped Length


-- @@ L21-21 verbatim
namespace LO

-- @@ L22-22 verbatim
namespace Arith


-- @@ L24-24 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L26-26 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L28-28 verbatim
section «lp_section_1»


-- @@ L30-30 expanded
variable [ModelsTheory V (iSigma 0)]


-- @@ L32-64 expanded
lemma log_exists_unique_pos {y : V} (hy : 0 < y) :
    ∃! x, x < y ∧ ∃ y' ≤ y, Exponential x y' ∧ y < 2 * y' :=
  by
  have : ∃ x < y, ∃ y' ≤ y, Exponential x y' ∧ y < 2 * y' :=
    by
    induction y using hierarchy_polynomial_induction_oRing_sigma₀
    · aesop  (config := { terminal := true })  (rule_sets := [Definability])
    case zero => simp at hy
    case even y _
      IH =>
      rcases (IH (by simpa using hy) : ∃ x < y, ∃ y' ≤ y, Exponential x y' ∧ y < 2 * y') with
        ⟨x, hxy, y', gey, H, lty⟩
      exact
        ⟨x + 1, lt_of_lt_of_le (by simp [hxy]) (succ_le_double_of_pos (pos_of_gt hxy)), 2 * y', by
          simpa using gey, Exponential.exponential_succ_mul_two.mpr H, by simpa using lty⟩
    case odd y IH =>
      rcases (zero_le y : 0 ≤ y) with (rfl | pos)
      · simp
      · rcases (IH pos : ∃ x < y, ∃ y' ≤ y, Exponential x y' ∧ y < 2 * y') with
          ⟨x, hxy, y', gey, H, lty⟩
        exact
          ⟨x + 1, by simp only [add_lt_add_iff_right]; exact lt_of_lt_of_le hxy (by simp), 2 * y',
            le_trans (by simpa using gey) le_self_add, Exponential.exponential_succ_mul_two.mpr H,
            two_mul_add_one_lt_two_mul_of_lt lty⟩
  rcases this with ⟨x, hx⟩
  exact
    ExistsUnique.intro x hx
      (fun x' ↦ by
        intro hx'
        by_contra A
        wlog lt : x < x'
        · exact this hy x' hx' x hx (Ne.symm A) (lt_of_le_of_ne (by simpa using lt) A)
        rcases hx with ⟨_, z, _, H, hyz⟩
        rcases hx' with ⟨_, z', hzy', H', _⟩
        have : z < z' := Exponential.monotone H H' lt
        have : y < y :=
          calc
            y < 2 * z := hyz
            _ ≤ z' := ((Pow2.lt_iff_two_mul_le H.range_pow2 H'.range_pow2).mp this)
            _ ≤ y := hzy'
        simp at this)


-- @@ L66-70 verbatim
lemma log_exists_unique (y : V) :
    ∃! x, (y = 0 → x = 0) ∧ (0 < y → x < y ∧ ∃ y' ≤ y, Exponential x y' ∧ y < 2 * y') := by
  by_cases hy : y = 0
  · rcases hy; simp
  · simp [hy, pos_iff_ne_zero.mpr hy, log_exists_unique_pos]


-- @@ L72-73 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def log (a : V) : V := Classical.choose! (log_exists_unique a)


-- @@ L75-76 verbatim
@[simp] lemma log_zero : log (0 : V) = 0 :=
  (Classical.choose!_spec (log_exists_unique (0 : V))).1 rfl


-- @@ L78-79 verbatim
lemma log_pos {y : V} (pos : 0 < y) : ∃ y' ≤ y, Exponential (log y) y' ∧ y < 2 * y' :=
  ((Classical.choose!_spec (log_exists_unique y)).2 pos).2


-- @@ L81-82 verbatim
lemma log_lt_self_of_pos {y : V} (pos : 0 < y) : log y < y :=
  ((Classical.choose!_spec (log_exists_unique y)).2 pos).1


-- @@ L84-87 verbatim
@[simp] lemma log_le_self (a : V) : log a ≤ a := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact le_of_lt <| log_lt_self_of_pos pos


-- @@ L89-91 verbatim
lemma log_graph {x y : V} :
    x = log y ↔ (y = 0 → x = 0) ∧ (0 < y → x < y ∧ ∃ y' ≤ y, Exponential x y' ∧ y < 2 * y') :=
  Classical.choose!_eq_iff _


-- @@ L93-95 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.logDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]))
      (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, #1])
        (Wedge.wedge (Semiformula.Operator.operator Operator.LT.lt ![#0, #1])
          (Semiformula.bexLTSucc (#1)
            (Wedge.wedge
              (LO.FirstOrder.Rewriting.substitute exponentialDef (vecCons (#1) (vecCons #0 ![])))
              (Semiformula.Operator.operator Operator.LT.lt
                ![#2, Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0]]))))))
    (by simp)


-- @@ L97-98 expanded
lemma log_defined : DefinedFunction₁ Sg0 (log : V → V) logDef := by intro v;
  simp [logDef, log_graph, numeral_eq_natCast]


-- @@ L100-101 verbatim
@[simp] lemma log_defined_iff (v) :
    Semiformula.Evalbm V v logDef.val ↔ v 0 = log (v 1) := log_defined.df.iff v


-- @@ L103-103 expanded
instance log_definable : BoldfaceFunction₁ Sg0 (log : V → V) :=
  log_defined.to_definable


-- @@ L105-105 verbatim
instance : Bounded₁ (log : V → V) := ⟨#0, fun _ ↦ by simp⟩


-- @@ L107-111 verbatim
lemma log_eq_of_pos {x y : V} (pos : 0 < y) {y'} (H : Exponential x y') (hy' : y' ≤ y) (hy :
    y < 2 * y') :
    log y = x :=
  (log_exists_unique_pos pos).unique ⟨log_lt_self_of_pos pos,
    log_pos pos⟩ ⟨lt_of_lt_of_le H.lt hy', y', hy', H, hy⟩


-- @@ L113-114 verbatim
@[simp] lemma log_one : log (1 : V) = 0 :=
  log_eq_of_pos (by simp) (y' := 1) (by simp) (by rfl) (by simp [])


-- @@ L116-117 verbatim
@[simp] lemma log_two : log (2 : V) = 1 :=
  log_eq_of_pos (by simp) (y' := 2) (by simp) (by rfl) (by simp [])


-- @@ L119-122 verbatim
lemma log_two_mul_of_pos {y : V} (pos : 0 < y) : log (2 * y) = log y + 1 := by
  rcases log_pos pos with ⟨y', hy', H, hy⟩
  exact log_eq_of_pos (by simpa using pos) (Exponential.exponential_succ_mul_two.mpr H) (by simpa
    using hy') (by simpa using hy)


-- @@ L124-127 verbatim
lemma log_two_mul_add_one_of_pos {y : V} (pos : 0 < y) : log (2 * y + 1) = log y + 1 := by
  rcases log_pos pos with ⟨y', hy', H, hy⟩
  exact log_eq_of_pos (by simp) (Exponential.exponential_succ_mul_two.mpr H)
    (le_trans (by simpa using hy') le_self_add) (two_mul_add_one_lt_two_mul_of_lt hy)


-- @@ L129-130 verbatim
lemma _root_.LO.Arith.Exponential.log_eq_of_exp {x y : V} (H : Exponential x y) : log y = x :=
  log_eq_of_pos H.range_pos H (by { rfl }) (lt_mul_of_pos_of_one_lt_left H.range_pos one_lt_two)


-- @@ L132-140 verbatim
lemma exponential_of_pow2 {p : V} (pp : Pow2 p) : Exponential (log p) p := by
  rcases log_pos pp.pos with ⟨q, hq, H, hp⟩
  suffices p = q by simpa [this] using H
  by_contra ne
  have : q < p := lt_of_le_of_ne hq (Ne.symm ne)
  have : 2 * q < 2 * q := calc
    2 * q ≤ p     := (Pow2.lt_iff_two_mul_le H.range_pow2 pp).mp this
    _     < 2 * q := hp
  simp at this


-- @@ L142-154 verbatim
lemma log_mul_pow2_add_of_lt {a p b : V} (pos : 0 < a) (pp : Pow2 p) (hb : b < p) :
    log (a * p + b) = log a + log p := by
  rcases log_pos pos with ⟨a', ha', Ha, ha⟩
  rcases log_pos pp.pos with ⟨p', hp', Hp, hp⟩
  exact log_eq_of_pos (lt_of_lt_of_le (mul_pos pos pp.pos) le_self_add)
    (Exponential.add_mul Ha Hp) (le_trans (mul_le_mul' ha' hp') le_self_add) (by
      rcases Hp.uniq (exponential_of_pow2 pp)
      calc
        a * p + b < a * p + p    := by simp [hb]
        _         = (a + 1) * p  := by simp [add_mul]
        _         ≤ 2 * (a' * p) := by
          rw [←mul_assoc]
          exact mul_le_mul_right (lt_iff_succ_le.mp ha))


-- @@ L156-157 verbatim
lemma log_mul_pow2 {a p : V} (pos : 0 < a) (pp : Pow2 p) : log (a * p) = log a + log p := by
  simpa using log_mul_pow2_add_of_lt pos pp pp.pos


-- @@ L159-173 verbatim
lemma log_monotone {a b : V} (h : a ≤ b) : log a ≤ log b := by
  rcases zero_le a with (rfl | posa)
  · simp
  rcases zero_le b with (rfl | posb)
  · have := lt_of_lt_of_le posa h; simp_all
  rcases log_pos posa with ⟨a', ha', Ha, _⟩
  rcases log_pos posb with ⟨b', _, Hb, hb⟩
  by_contra lt
  have : b' < a' := (Exponential.monotone_iff Hb Ha).mp (by simpa using lt)
  have : b < b := calc
    b < 2 * b' := hb
    _ ≤ a'     := (Pow2.lt_iff_two_mul_le Hb.range_pow2 Ha.range_pow2).mp this
    _ ≤ a      := ha'
    _ ≤ b      := h
  simp_all


-- @@ L175-176 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def binaryLength (a : V) : V := if 0 < a then log a + 1 else 0


-- @@ L178-179 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance : Length V := ⟨binaryLength⟩


-- @@ L181-181 verbatim
lemma length_eq_binaryLength (a : V) : ‖a‖ = if 0 < a then log a + 1 else 0 := rfl


-- @@ L183-183 verbatim
@[simp] lemma length_zero : ‖(0 : V)‖ = 0 := by simp [length_eq_binaryLength]


-- @@ L185-185 verbatim
lemma length_of_pos {a : V} (pos : 0 < a) : ‖a‖ = log a + 1 := by simp [length_eq_binaryLength, pos]


-- @@ L187-190 verbatim
@[simp] lemma length_le (a : V) : ‖a‖ ≤ a := by
  rcases zero_le a with (rfl | pos)
  · simp
  · simp [pos, length_of_pos, ←lt_iff_succ_le, log_lt_self_of_pos]


-- @@ L192-196 verbatim
lemma length_graph {i a : V} :
    i = ‖a‖ ↔ (0 < a → ∃ k ≤ a, k = log a ∧ i = k + 1) ∧ (a = 0 → i = 0) := by
  rcases zero_le a with (rfl | pos)
  · simp
  · simp [length_of_pos, pos, pos_iff_ne_zero.mp pos]


-- @@ L198-200 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.lengthDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, #1])
        (Semiformula.bexLTSucc (#1)
          (Wedge.wedge (LO.FirstOrder.Rewriting.substitute logDef (vecCons (#0) (vecCons #2 ![])))
            (Semiformula.Operator.operator Operator.Eq.eq
              ![#1, Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]]))))
      (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])))
    (by simp)


-- @@ L202-203 expanded
lemma length_defined : DefinedFunction₁ Sg0 (‖·‖ : V → V) lengthDef := by intro v;
  simp [lengthDef, length_graph]


-- @@ L205-206 verbatim
@[simp] lemma length_defined_iff (v) :
    Semiformula.Evalbm V v lengthDef.val ↔ v 0 = ‖v 1‖ := length_defined.df.iff v


-- @@ L208-208 expanded
instance length_definable : BoldfaceFunction₁ Sg0 (‖·‖ : V → V) :=
  length_defined.to_definable


-- @@ L210-210 verbatim
instance : Bounded₁ (‖·‖ : V → V) := ⟨#0, fun _ ↦ by simp⟩


-- @@ L212-212 verbatim
@[simp] lemma length_one : ‖(1 : V)‖ = 1 := by simp [length_eq_binaryLength]


-- @@ L214-215 verbatim
lemma _root_.LO.Arith.Exponential.length_eq {x y : V} (H : Exponential x y) : ‖y‖ = x + 1 := by
  rw [length_of_pos H.range_pos, H.log_eq_of_exp]


-- @@ L217-218 verbatim
lemma length_two_mul_of_pos {a : V} (pos : 0 < a) : ‖2 * a‖ = ‖a‖ + 1 := by
  simp [pos, length_of_pos, log_two_mul_of_pos]


-- @@ L220-223 verbatim
lemma length_two_mul_add_one (a : V) : ‖2 * a + 1‖ = ‖a‖ + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · simp [pos, length_of_pos, log_two_mul_add_one_of_pos]


-- @@ L225-228 verbatim
lemma length_mul_pow2_add_of_lt {a p b : V} (pos : 0 < a) (pp : Pow2 p) (hb : b < p) :
    ‖a * p + b‖ = ‖a‖ + log p := by
  simp [length_of_pos, pos, pp.pos, log_mul_pow2_add_of_lt pos pp hb,
    add_right_comm (log a) (log p) 1]


-- @@ L230-231 verbatim
lemma length_mul_pow2 {a p : V} (pos : 0 < a) (pp : Pow2 p) : ‖a * p‖ = ‖a‖ + log p := by
  simp [length_of_pos, pos, pp.pos, log_mul_pow2 pos pp, add_right_comm (log a) (log p) 1]


-- @@ L233-237 verbatim
lemma length_monotone {a b : V} (h : a ≤ b) : ‖a‖ ≤ ‖b‖ := by
  rcases zero_le a with (rfl | posa)
  · simp
  · rw [length_of_pos posa, length_of_pos (lt_of_lt_of_le posa h)]
    exact add_le_add_left (log_monotone h) 1


-- @@ L239-240 verbatim
lemma pos_of_lt_length {a b : V} (h : a < ‖b‖) : 0 < b := by
  by_contra A; rcases (show b = 0 from by simpa using A); simp_all


-- @@ L242-244 verbatim
@[simp] lemma length_pos_iff {a : V} : 0 < ‖a‖ ↔ 0 < a :=
  ⟨by intro h; by_contra A; rcases (show a = 0 from by simpa using A); simp_all,
   by intro h; exact pos_iff_one_le.mpr (by simpa using length_monotone (pos_iff_one_le.mp h))⟩


-- @@ L246-247 verbatim
@[simp] lemma length_eq_zero_iff {a : V} : ‖a‖ = 0 ↔ a = 0 :=
  not_iff_not.mp (by simp [←pos_iff_ne_zero])


-- @@ L249-251 verbatim
lemma le_log_of_lt_length {a b : V} (h : a < ‖b‖) : a ≤ log b := by
  have : 0 < b := pos_of_lt_length h
  exact le_iff_lt_succ.mpr (by simpa [length_of_pos this] using h)


-- @@ L253-255 verbatim
lemma exponential_log_le_self {a b : V} (pos : 0 < a) (h : Exponential (log a) b) : b ≤ a := by
  rcases log_pos pos with ⟨_, _, H, _⟩; rcases H.uniq h
  assumption


-- @@ L257-261 verbatim
lemma lt_exponential_log_self {a b : V} (h : Exponential (log a) b) : a < 2 * b := by
  rcases zero_le a with (rfl | pos)
  · simp at h; simp [h]
  rcases log_pos pos with ⟨_, _, H, _⟩; rcases H.uniq h
  assumption


-- @@ L263-268 verbatim
lemma lt_exp_len_self {a b : V} (h : Exponential ‖a‖ b) : a < b := by
  rcases zero_le a with (rfl | pos)
  · simp at h; simp [h]
  rw [length_of_pos pos] at h
  rcases Exponential.exponential_succ.mp h with ⟨b, rfl, H⟩
  exact lt_exponential_log_self H


-- @@ L270-274 verbatim
lemma le_iff_le_log_of_exp {x y a : V} (H : Exponential x y) (pos : 0 < a) : y ≤ a ↔ x ≤ log a :=
  ⟨by rcases H.log_eq_of_exp; exact log_monotone,
   fun h ↦ by
     rcases log_pos pos with ⟨a', ha', Haa', _⟩
     exact le_trans (Exponential.monotone_le H Haa' h) ha'⟩


-- @@ L276-280 verbatim
lemma le_iff_lt_length_of_exp {x y a : V} (H : Exponential x y) : y ≤ a ↔ x < ‖a‖ := by
  rcases zero_le a with (rfl | pos)
  · simp only [nonpos_iff_eq_zero, length_zero, not_lt_zero, iff_false]
    exact pos_iff_ne_zero.mp H.range_pos
  simp [le_iff_le_log_of_exp H pos, length_of_pos pos, ←le_iff_lt_succ]


-- @@ L282-284 verbatim
lemma _root_.LO.Arith.Exponential.lt_iff_log_lt {x y a : V} (H : Exponential x y) (pos : 0 < a) :
    a < y ↔ log a < x :=
  not_iff_not.mp (by simpa using le_iff_le_log_of_exp H pos)


-- @@ L286-288 verbatim
lemma _root_.LO.Arith.Exponential.lt_iff_len_le {x y a : V} (H : Exponential x y) :
    a < y ↔ ‖a‖ ≤ x :=
  not_iff_not.mp (by simpa using le_iff_lt_length_of_exp H)


-- @@ L290-293 verbatim
lemma _root_.LO.Arith.Exponential.le_of_lt_length {x y a : V} (H : Exponential x y) :
    x < ‖a‖ → y ≤ a :=
  fun h ↦
  (le_iff_lt_length_of_exp H).mpr h


-- @@ L295-296 verbatim
lemma _root_.LO.Arith.Exponential.le_log {x y : V} (H : Exponential x y) : x ≤ log y :=
  (le_iff_le_log_of_exp H H.range_pos).mp (by rfl)


-- @@ L298-299 verbatim
lemma _root_.LO.Arith.Exponential.lt_length {x y : V} (H : Exponential x y) : x < ‖y‖ :=
  (le_iff_lt_length_of_exp H).mp (by rfl)


-- @@ L301-301 verbatim
lemma lt_exponential_length {a b : V} (h : Exponential ‖a‖ b) : a < b := lt_exp_len_self h


-- @@ L303-327 expanded
lemma sq_len_le_three_mul (a : V) : ‖a‖ ^ 2 ≤ 3 * a :=
  by
  induction a using hierarchy_polynomial_induction_oRing_sigma₀
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case even a pos IH =>
    calc
      ‖2 * a‖ ^ 2 = (‖a‖ + 1) ^ 2 := by rw [length_two_mul_of_pos pos]
      _ = ‖a‖ ^ 2 + 2 * ‖a‖ + 1 := by simp [sq, add_mul_self_eq]
      _ ≤ 3 * a + 2 * ‖a‖ + 1 := by simpa using IH
      _ ≤ 3 * a + 2 * a + 1 := by simp
      _ ≤ 3 * a + 2 * a + a := by simp [← pos_iff_one_le, pos]
      _ = 3 * (2 * a) := by
        simp_all only [← two_add_one_eq_three, two_mul, add_mul, add_assoc, one_mul]
  case odd a IH =>
    rcases zero_le a with (rfl | pos)
    · simp [← two_add_one_eq_three]
    calc
      ‖2 * a + 1‖ ^ 2 = (‖a‖ + 1) ^ 2 := by rw [length_two_mul_add_one a]
      _ = ‖a‖ ^ 2 + 2 * ‖a‖ + 1 := by simp [sq, add_mul_self_eq]
      _ ≤ 3 * a + 2 * ‖a‖ + 1 := by simpa using IH
      _ ≤ 3 * a + 2 * a + 1 := by simp
      _ ≤ 3 * a + 2 * a + a := by simp [← pos_iff_one_le, pos]
      _ = 3 * (2 * a) := by
        simp_all only [← two_add_one_eq_three, two_mul, add_mul, add_assoc, one_mul]
      _ ≤ 3 * (2 * a + 1) := by simp


-- @@ L329-345 expanded
lemma brange_exists_unique (a : V) : ∀ x < ‖a‖, ∃! y, Exponential x y :=
  by
  suffices ∀ x < ‖a‖, ∃ y ≤ a, Exponential x y
    by
    intro x hx; rcases this x hx with ⟨_, _, H⟩
    exact ExistsUnique.intro _ H (fun y' H' ↦ H'.uniq H)
  intro x
  induction x using induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero =>
    intro ha
    have : 0 < a := pos_of_lt_length ha
    exact ⟨1, pos_iff_one_le.mp this, by simp⟩
  case succ x IH =>
    intro hx
    rcases (IH (lt_of_le_of_lt (by simp) hx) : ∃ y ≤ a, Exponential x y) with ⟨y, hy, H⟩
    have : 0 < a := by by_contra A; rcases (show a = 0 from by simpa using A); simp_all
    have : 2 * y ≤ a := (le_iff_le_log_of_exp H.succ this).mpr (le_log_of_lt_length hx)
    exact ⟨2 * y, this, H.succ⟩


-- @@ L347-353 verbatim
lemma bexp_exists_unique (a x : V) : ∃! y, (x < ‖a‖ → Exponential x y) ∧ (‖a‖ ≤ x → y = 0) := by
  by_cases hx : x < ‖a‖
  · rcases brange_exists_unique a x hx with ⟨y, Hy, Huniq⟩
    refine ⟨y, ⟨fun _ ↦ Hy, fun hle ↦ False.elim ((not_le.mpr hx) hle)⟩, ?_⟩
    intro y' hy'
    exact Huniq y' (hy'.1 hx)
  · simp [hx, show ‖a‖ ≤ x from by simpa using hx]


-- @@ L355-356 verbatim
/-- `bexp a x = exp x` if `x < ‖a‖`; `= 0` o.w. -/
def bexp (a x : V) : V := Classical.choose! (bexp_exists_unique a x)


-- @@ L358-359 verbatim
lemma exp_bexp_of_lt {a x : V} (h : x < ‖a‖) : Exponential x (bexp a x) :=
  (Classical.choose!_spec (bexp_exists_unique a x)).1 h


-- @@ L361-362 verbatim
lemma bexp_eq_zero_of_le {a x : V} (h : ‖a‖ ≤ x) : bexp a x = 0 :=
  (Classical.choose!_spec (bexp_exists_unique a x)).2 h


-- @@ L364-364 verbatim
@[simp] lemma bexp_zero (x : V) : bexp 0 x = 0 := bexp_eq_zero_of_le (by simp)


-- @@ L366-371 verbatim
@[simp] lemma exp_bexp_of_lt_iff {a x : V} : Exponential x (bexp a x) ↔ x < ‖a‖ :=
  ⟨by intro h; by_contra A
      have : bexp a x = 0 := bexp_eq_zero_of_le (not_lt.mp A)
      simp [this] at h
      have := h.range_pos; simp_all,
   exp_bexp_of_lt⟩


-- @@ L373-377 verbatim
@[simp] lemma bexp_le_self (a x : V) : bexp a x ≤ a := by
  rcases show x < ‖a‖ ∨ ‖a‖ ≤ x from lt_or_ge _ _ with (lt | le)
  · have : 0 < a := pos_of_lt_length lt
    exact (le_iff_le_log_of_exp (exp_bexp_of_lt lt) this).mpr (le_log_of_lt_length lt)
  · simp [bexp_eq_zero_of_le le]


-- @@ L379-385 verbatim
lemma bexp_graph {y a x : V} :
    y = bexp a x ↔ ∃ l ≤ a, l = ‖a‖ ∧ (x < l → Exponential x y) ∧ (l ≤ x → y = 0) :=
  ⟨by rintro rfl; exact ⟨‖a‖, by simp, rfl, exp_bexp_of_lt, bexp_eq_zero_of_le⟩, by
    rintro ⟨_, _, rfl, hlt, hle⟩
    rcases show x < ‖a‖ ∨ ‖a‖ ≤ x from lt_or_ge _ _ with (lt | le)
    · exact (hlt lt).uniq (exp_bexp_of_lt lt)
    · rcases hle le; simp [bexp_eq_zero_of_le le]⟩


-- @@ L387-389 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.bexpDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute lengthDef (vecCons (#0) (vecCons #2 ![])))
        (Wedge.wedge
          (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![#3, #0])
            (LO.FirstOrder.Rewriting.substitute exponentialDef (vecCons (#3) (vecCons #1 ![]))))
          (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#0, #3])
            (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0])))))
    (by simp)


-- @@ L391-392 expanded
lemma bexp_defined : DefinedFunction₂ Sg0 (bexp : V → V → V) bexpDef := by intro v;
  simp [bexpDef, bexp_graph]


-- @@ L394-395 verbatim
@[simp] lemma bexp_defined_iff (v) :
    Semiformula.Evalbm V v bexpDef.val ↔ v 0 = bexp (v 1) (v 2) := bexp_defined.df.iff v


-- @@ L397-397 expanded
instance bexp_definable : BoldfaceFunction₂ Sg0 (bexp : V → V → V) :=
  bexp_defined.to_definable


-- @@ L399-399 verbatim
instance : Bounded₂ (bexp : V → V → V) := ⟨#0, fun _ ↦ by simp⟩


-- @@ L401-402 verbatim
lemma bexp_monotone_iff {a i j : V} (hi : i < ‖a‖) (hj : j < ‖a‖) : bexp a i < bexp a j ↔ i < j :=
  Iff.symm <| Exponential.monotone_iff (by simp [hi]) (by simp [hj])


-- @@ L404-406 verbatim
lemma bexp_monotone_le_iff {a i j : V} (hi : i < ‖a‖) (hj : j < ‖a‖) :
    bexp a i ≤ bexp a j ↔ i ≤ j :=
  Iff.symm <| Exponential.monotone_le_iff (by simp [hi]) (by simp [hj])


-- @@ L408-411 verbatim
lemma bexp_eq_of_lt_length {i a a' : V} (ha : i < ‖a‖) (ha' : i < ‖a'‖) : bexp a i = bexp a' i := by
  have H : Exponential i (bexp a i) := by simp [ha]
  have H' : Exponential i (bexp a' i) := by simp [ha']
  exact H.uniq H'


-- @@ L413-413 verbatim
@[simp] lemma bexp_pow2 {a x : V} (h : x < ‖a‖) : Pow2 (bexp a x) := (exp_bexp_of_lt h).range_pow2


-- @@ L415-415 verbatim
@[simp] lemma lt_bexp {a x : V} (h : x < ‖a‖) : x < bexp a x := (exp_bexp_of_lt h).lt


-- @@ L417-417 verbatim
@[simp] lemma bexp_pos {a x : V} (h : x < ‖a‖) : 0 < bexp a x := (exp_bexp_of_lt h).range_pos


-- @@ L419-419 verbatim
lemma lt_bexp_len {a x : V} (h : ‖x‖ < ‖a‖) : x < bexp a ‖x‖ := lt_exp_len_self (exp_bexp_of_lt h)


-- @@ L421-422 verbatim
lemma bexp_eq_of_exp {a x : V} (h : x < ‖a‖) (H : Exponential x y) : bexp a x = y :=
  (exp_bexp_of_lt h).uniq H


-- @@ L424-425 verbatim
lemma log_bexp {a x : V} (h : x < ‖a‖) : log (bexp a x) = x :=
  Exponential.log_eq_of_exp (exp_bexp_of_lt h)


-- @@ L427-428 verbatim
lemma len_bexp {a x : V} (h : x < ‖a‖) :
    ‖bexp a x‖ = x + 1 := by rw [length_of_pos (bexp_pos h), log_bexp h]


-- @@ L430-430 verbatim
@[simp 1100] lemma bexp_zero_zero : bexp (0 : V) 0 = 0 := bexp_eq_zero_of_le (by simp)


-- @@ L432-433 verbatim
@[simp] lemma bexp_pos_zero {a : V} (h : 0 < a) : bexp a 0 = 1 :=
  bexp_eq_of_exp (by simpa) (by simp)


-- @@ L435-437 verbatim
lemma bexp_monotone {a₁ x₁ a₂ x₂ : V} (h₁ : x₁ < ‖a₁‖) (h₂ : x₂ < ‖a₂‖) :
  bexp a₁ x₁ < bexp a₂ x₂ ↔ x₁ < x₂ :=
    Iff.symm <| (exp_bexp_of_lt h₁).monotone_iff (exp_bexp_of_lt h₂)


-- @@ L439-441 verbatim
lemma bexp_monotone_le {a₁ x₁ a₂ x₂ : V} (h₁ : x₁ < ‖a₁‖) (h₂ : x₂ < ‖a₂‖) :
  bexp a₁ x₁ ≤ bexp a₂ x₂ ↔ x₁ ≤ x₂ :=
    Iff.symm <| (exp_bexp_of_lt h₁).monotone_le_iff (exp_bexp_of_lt h₂)


-- @@ L443-445 verbatim
lemma bexp_add {x₁ x₂ a : V} (h : x₁ + x₂ < ‖a‖) : bexp a (x₁ + x₂) = bexp a x₁ * bexp a x₂ :=
  (exp_bexp_of_lt h).uniq ((exp_bexp_of_lt (lt_of_le_of_lt le_self_add h)).add_mul (exp_bexp_of_lt
    (lt_of_le_of_lt le_add_self h)))


-- @@ L447-449 verbatim
lemma bexp_two_mul {a a' x : V} (hx : 2 * x < ‖a‖) (hx' : x < ‖a'‖) :
    bexp a (2 * x) = (bexp a' x) ^ 2 :=
  bexp_eq_of_exp hx (exp_bexp_of_lt hx').bit_zero


-- @@ L451-456 verbatim
lemma bexp_two_mul_succ {a i : V} : bexp (2 * a) (i + 1) = 2 * bexp a i := by
  rcases zero_le a with (rfl | pos)
  · simp
  rcases show i ≥ ‖a‖ ∨ i < ‖a‖ from le_or_gt ‖a‖ i with (h | h)
  · simp [bexp_eq_zero_of_le, h, show ‖2 * a‖ ≤ i + 1 from by simp [length_two_mul_of_pos pos, h]]
  · exact bexp_eq_of_exp (by simp [length_two_mul_of_pos pos, h]) (exp_bexp_of_lt h).succ


-- @@ L458-461 verbatim
lemma bexp_two_mul_add_one_succ {a i : V} : bexp (2 * a + 1) (i + 1) = 2 * bexp a i := by
  rcases show i ≥ ‖a‖ ∨ i < ‖a‖ from le_or_gt ‖a‖ i with (h | h)
  · simp [bexp_eq_zero_of_le, h, show ‖2 * a + 1‖ ≤ i + 1 from by simp [length_two_mul_add_one, h]]
  · exact bexp_eq_of_exp (by simp [length_two_mul_add_one, h]) (exp_bexp_of_lt h).succ


-- @@ L463-464 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fbit (a i : V) : V := (a / bexp a i) % 2


-- @@ L466-466 verbatim
@[simp] lemma fbit_lt_two (a i : V) : fbit a i < 2 := by simp [fbit]


-- @@ L468-468 verbatim
@[simp] lemma fbit_le_one (a i : V) : fbit a i ≤ 1 := lt_two_iff_le_one.mp (by simp [fbit])


-- @@ L470-471 verbatim
lemma fbit_eq_one_iff {a i : V} :
    fbit a i = 1 ↔ LenBit (bexp a i) a := by simp [fbit, LenBit.iff_rem]


-- @@ L473-474 verbatim
lemma fbit_eq_zero_iff {a i : V} :
    fbit a i = 0 ↔ ¬LenBit (bexp a i) a := by simp [fbit, LenBit.iff_rem]


-- @@ L476-477 verbatim
lemma fbit_eq_zero_of_le {a i : V} (hi : ‖a‖ ≤ i) :
    fbit a i = 0 := by simp [fbit, bexp_eq_zero_of_le hi]


-- @@ L479-481 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.fbitDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute bexpDef (vecCons (#0) (vecCons (#2) (vecCons #3 ![]))))
        (Semiformula.bexLTSucc (#2)
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute divDef
              (vecCons (#0) (vecCons (#3) (vecCons #1 ![]))))
            (LO.FirstOrder.Rewriting.substitute remDef
              (vecCons (#2) (vecCons (#0) (vecCons (Semiterm.numeral 2) ![]))))))))
    (by simp)


-- @@ L483-484 expanded
lemma fbit_defined : DefinedFunction₂ Sg0 (fbit : V → V → V) fbitDef := by intro v;
  simp [fbitDef, fbit, numeral_eq_natCast]


-- @@ L486-487 verbatim
@[simp] lemma fbit_defined_iff (v) :
    Semiformula.Evalbm V v fbitDef.val ↔ v 0 = fbit (v 1) (v 2) := fbit_defined.df.iff v


-- @@ L489-489 expanded
instance fbit_definable : BoldfaceFunction₂ Sg0 (fbit : V → V → V) :=
  fbit_defined.to_definable


-- @@ L491-491 expanded
instance : Bounded₂ (fbit : V → V → V) :=
  ⟨Semiterm.numeral 1, fun _ ↦ by simp⟩


-- @@ L493-493 verbatim
@[simp] lemma fbit_zero (i : V) : fbit 0 i = 0 := by simp [fbit]


-- @@ L495-496 verbatim
@[simp] lemma fbit_mul_two_mul (a i : V) : fbit (2 * a) (i + 1) = fbit a i := by
  simp [fbit, bexp_two_mul_succ, div_cancel_left]


-- @@ L498-499 verbatim
@[simp] lemma fbit_mul_two_add_one_mul (a i : V) : fbit (2 * a + 1) (i + 1) = fbit a i := by
  simp [fbit, bexp_two_mul_add_one_succ, div_mul]


-- @@ L501-505 verbatim
@[simp] lemma fbit_two_mul_zero_eq_zero (a : V) : fbit (2 * a) 0 = 0 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · have : bexp (2 * a) 0 = 1 := bexp_eq_of_exp (by simp [pos]) (by simp)
    simp [fbit, this]


-- @@ L507-508 verbatim
@[simp] lemma fbit_two_mul_add_one_zero_eq_one (a : V) :
    fbit (2 * a + 1) 0 = 1 := by simp [fbit]


-- @@ L510-510 verbatim
end «lp_section_1»


-- @@ L512-512 verbatim
section «lp_section_2»


-- @@ L514-514 expanded
variable [ModelsTheory V (iSigma 1)]


-- @@ L516-516 expanded
@[simp]
lemma log_exponential (a : V) : log (Exp.exp a) = a :=
  (exponential_exp a).log_eq_of_exp


-- @@ L518-521 expanded
lemma exp_log_le_self {a : V} (pos : 0 < a) : Exp.exp (log a) ≤ a :=
  by
  rcases log_pos pos with ⟨_, _, H, _⟩
  rcases H.uniq (exponential_exp (log a))
  assumption


-- @@ L523-526 expanded
lemma lt_two_mul_exponential_log {a : V} (pos : 0 < a) : a < 2 * Exp.exp (log a) :=
  by
  rcases log_pos pos with ⟨_, _, H, _⟩
  rcases H.uniq (exponential_exp (log a))
  assumption


-- @@ L528-528 expanded
@[simp]
lemma length_exponential (a : V) : ‖Exp.exp a‖ = a + 1 := by simp [length_of_pos (exp_pos a)]


-- @@ L530-531 expanded
lemma exp_add (a b : V) : Exp.exp (a + b) = Exp.exp a * Exp.exp b :=
  exp_of_exponential (Exponential.add_mul (exponential_exp a) (exponential_exp b))


-- @@ L533-534 expanded
lemma log_mul_exp_add_of_lt {a b : V} (pos : 0 < a) (i : V) (hb : b < Exp.exp i) :
    log (a * Exp.exp i + b) = log a + i := by simp [log_mul_pow2_add_of_lt pos (exp_pow2 i) hb]


-- @@ L536-537 expanded
lemma log_mul_exp {a : V} (pos : 0 < a) (i : V) : log (a * Exp.exp i) = log a + i := by
  simp [log_mul_pow2 pos (exp_pow2 i)]


-- @@ L539-540 expanded
lemma length_mul_exp_add_of_lt {a b : V} (pos : 0 < a) (i : V) (hb : b < Exp.exp i) :
    ‖a * Exp.exp i + b‖ = ‖a‖ + i := by simp [length_mul_pow2_add_of_lt pos (exp_pow2 i) hb]


-- @@ L542-543 expanded
lemma length_mul_exp {a : V} (pos : 0 < a) (i : V) : ‖a * Exp.exp i‖ = ‖a‖ + i := by
  simp [length_mul_pow2 pos (exp_pow2 i)]


-- @@ L545-547 expanded
lemma exp_le_iff_le_log {i a : V} (pos : 0 < a) : Exp.exp i ≤ a ↔ i ≤ log a :=
  ⟨by intro h; simpa using log_monotone h, fun h ↦
    le_trans (exp_monotone_le.mpr h) (exp_log_le_self pos)⟩


-- @@ L549-549 verbatim
end «lp_section_2»


-- @@ L551-551 verbatim
end Arith

-- @@ L552-552 verbatim
end LO


-- @@ L554-554 verbatim
end «lp_nc_section_1»
