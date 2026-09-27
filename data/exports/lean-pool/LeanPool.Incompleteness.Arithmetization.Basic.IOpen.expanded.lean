/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Basic.Ind
public import LeanPool.Incompleteness.Arithmetization.Basic.PeanoMinus
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L14-14 verbatim
/-! # IOpen -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace Arith


-- @@ L22-22 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L24-24 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L26-26 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L28-28 verbatim
section «lp_section_1»


-- @@ L30-30 expanded
variable [ModelsTheory V iOpen]


-- @@ L32-45 expanded
@[elab_as_elim]
lemma open_induction {P : V → Prop}
    (hP : ∃ p : Semiformula oRing V 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] id p)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (C := Semiformula.Open)
    (by
      rcases hP with ⟨p, hp, hhp⟩
      have : Inhabited V := Classical.inhabited_of_nonempty'
      exact
        ⟨p.fvarEnumInv, app (Rew.rewriteMap p.fvarEnum) p, by simp [hp],
          by
          intro x
          simp only [hhp, Nat.succ_eq_add_one, Nat.reduceAdd, Semiformula.eval_rewriteMap]
          exact
            Semiformula.eval_iff_of_funEqOn p
              (by
                intro z hz
                simp [Semiformula.fvarEnumInv_fvarEnum
                      (Semiformula.mem_fvarList_iff_fvar?.mpr hz)])⟩)
    zero succ


-- @@ L47-57 expanded
lemma open_leastNumber {P : V → Prop}
    (hP : ∃ p : Semiformula oRing V 1, p.Open ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] id p)
    (zero : P 0) {a} (counterex : ¬P a) : ∃ x, P x ∧ ¬P (x + 1) :=
  by
  by_contra A
  have : ∀ x, P x := by
    intro x; induction x using open_induction
    · exact hP
    case zero => exact zero
    case succ n ih => simp_all
  simp_all


-- @@ L59-78 expanded
lemma div_exists_unique_pos (a : V) {b} (pos : 0 < b) : ∃! u, b * u ≤ a ∧ a < b * (u + 1) :=
  by
  have : ∃ u, b * u ≤ a ∧ a < b * (u + 1) :=
    by
    have : a < b * (a + 1) → ∃ u, b * u ≤ a ∧ a < b * (u + 1) := by
      simpa using
        open_leastNumber (P := fun u ↦ b * u ≤ a)
          ⟨Semiformula.Operator.operator Operator.LE.le
              ![Semiterm.Operator.Mul.mul.operator ![&b, #0], &a],
            by simp, by intro x; simp⟩
    have hx : a < b * (a + 1) :=
      by
      have : a + 0 < b * a + b := add_lt_add_of_le_of_lt (le_mul_self_of_pos_left pos) pos
      simpa [mul_add] using this
    exact this hx
  rcases this with ⟨u, hu⟩
  exact
    ExistsUnique.intro u hu
      (by
        intro u' hu'
        by_contra ne
        wlog lt : u < u'
        · exact this a pos u' hu' u hu (Ne.symm ne) (Ne.lt_of_le ne <| by simpa using lt)
        have : a < a := by
          calc
            a < b * (u + 1) := hu.2
            _ ≤ b * u' := (Arith.mul_le_mul_left (a := b) (lt_iff_succ_le.mp lt))
            _ ≤ a := hu'.1
        exact LT.lt.false this)


-- @@ L80-80 verbatim
section «lp_section_2»


-- @@ L82-86 verbatim
lemma div_exists_unique (a b : V) :
    ∃! u, (0 < b → b * u ≤ a ∧ a < b * (u + 1)) ∧ (b = 0 → u = 0) := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  · simpa [pos_iff_ne_zero.mp pos] using div_exists_unique_pos a pos


-- @@ L88-89 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instDivV : Div V := ⟨fun a b ↦ Classical.choose! (div_exists_unique a b)⟩


-- @@ L91-92 verbatim
lemma mul_div_le_pos (a : V) (h : 0 < b) : b * (a / b) ≤ a :=
  ((Classical.choose!_spec (div_exists_unique a b)).1 h).1


-- @@ L94-95 verbatim
lemma lt_mul_div_succ (a : V) (h : 0 < b) : a < b * (a / b + 1) :=
  ((Classical.choose!_spec (div_exists_unique a b)).1 h).2


-- @@ L97-107 verbatim
lemma eq_mul_div_add_of_pos (a : V) {b} (hb : 0 < b) : ∃ r < b, a = b * (a / b) + r := by
  let r := a - b * (a / b)
  have e : a = b * (a / b) + r := by simp [r, add_tsub_self_of_le (mul_div_le_pos a hb)]
  exact ⟨r, by
    by_contra A
    have hyv : b ≤ r := by simpa using A
    have : a < a := by calc
          a < b * (a / b + 1) := lt_mul_div_succ a hb
          _ ≤ b * (a / b) + r := by simpa [mul_add] using hyv
          _ = a               := e.symm
    simp at this, e⟩


-- @@ L109-110 verbatim
@[simp] lemma div_spec_zero (a : V) : a / 0 = 0 :=
  (Classical.choose!_spec (div_exists_unique a 0)).2 (by simp)


-- @@ L112-114 verbatim
lemma div_graph {a b c : V} :
    c = a / b ↔ ((0 < b → b * c ≤ a ∧ a < b * (c + 1)) ∧ (b = 0 → c = 0)) :=
  Classical.choose!_eq_iff _


-- @@ L116-118 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.divDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, #2])
        (Wedge.wedge
          (Semiformula.Operator.operator Operator.LE.le
            ![Semiterm.Operator.Mul.mul.operator ![#2, #0], #1])
          (Semiformula.Operator.operator Operator.LT.lt
            ![#1,
              Semiterm.Operator.Mul.mul.operator
                ![#2, Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]]])))
      (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![#2, Semiterm.numeral 0])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])))
    (by simp [])


-- @@ L120-121 expanded
lemma div_defined : DefinedFunction₂ Sg0 ((· / ·) : V → V → V) divDef := by intro v;
  simp [div_graph, divDef]


-- @@ L123-124 verbatim
@[simp] lemma div_defined_iff (v) :
    Semiformula.Evalbm V v divDef.val ↔ v 0 = v 1 / v 2 := div_defined.df.iff v


-- @@ L126-127 verbatim
lemma div_spec_of_pos' (a : V) (h : 0 < b) : ∃ v < b, a = (a / b) * b + v := by
  simpa [mul_comm] using eq_mul_div_add_of_pos a h


-- @@ L129-131 verbatim
lemma div_eq_of {b : V} (hb : b * c ≤ a) (ha : a < b * (c + 1)) : a / b = c := by
  have pos : 0 < b := pos_of_mul_pos_left (pos_of_gt ha) (by simp)
  exact (div_exists_unique_pos a pos).unique ⟨mul_div_le_pos a pos, lt_mul_div_succ a pos⟩ ⟨hb, ha⟩


-- @@ L133-134 verbatim
lemma div_mul_add (a b : V) {r} (hr : r < b) : (a * b + r) / b = a :=
  div_eq_of (by simp [mul_comm]) (by simp [mul_comm b a, mul_add, hr])


-- @@ L136-137 verbatim
lemma div_mul_add' (a b : V) {r} (hr : r < b) :
    (b * a + r) / b = a := by simpa [mul_comm] using div_mul_add a b hr


-- @@ L139-142 verbatim
@[simp] lemma zero_div (a : V) : 0 / a = 0 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · exact div_eq_of (by simp) (by simpa)


-- @@ L144-158 verbatim
lemma div_mul (a b c : V) : a / (b * c) = a / b / c := by
  rcases zero_le b with (rfl | hb)
  · simp
  rcases zero_le c with (rfl | hc)
  · simp
  exact div_eq_of
    (by calc
          b * c * (a / b / c) ≤ b * (a / b) := by
            simpa [mul_assoc] using mul_le_mul_left (mul_div_le_pos (a / b) hc)
          _                   ≤ a := mul_div_le_pos a hb)
    (by calc
          a < b * (a / b + 1)         := lt_mul_div_succ a hb
          _ ≤ b * c * (a / b / c + 1) := by
            simpa [mul_assoc] using mul_le_mul_left (lt_iff_succ_le.mp <|
                lt_mul_div_succ (a / b) hc))


-- @@ L160-164 verbatim
@[simp] lemma mul_div_le (a b : V) : b * (a / b) ≤ a := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos) <;> simp [*]
  rcases eq_mul_div_add_of_pos a pos with ⟨v, _, e⟩
  simpa [← e] using show b * (a / b) ≤ b * (a / b) + v from le_self_add


-- @@ L166-172 verbatim
@[simp] lemma div_le (a b : V) : a / b ≤ a := by
  have : 0 ≤ b := zero_le b
  rcases this with (rfl | pos)
  · simp
  have : 1 * (a / b) ≤ b * (a / b) :=
    mul_le_mul_of_nonneg_right (le_iff_lt_succ.mpr (by simp[pos])) (by simp)
  simpa using le_trans this (mul_div_le a b)


-- @@ L174-174 verbatim
instance div_polybounded : Bounded₂ ((· / ·) : V → V → V) := ⟨#0, fun _ ↦ by simp⟩


-- @@ L176-176 expanded
instance div_definable : BoldfaceFunction₂ Sg0 ((· / ·) : V → V → V) :=
  div_defined.to_definable _


-- @@ L178-178 verbatim
@[simp] lemma div_mul_le (a b : V) : a / b * b ≤ a := by rw [mul_comm]; exact mul_div_le _ _


-- @@ L180-183 verbatim
lemma lt_mul_div (a : V) {b} (pos : 0 < b) : a < b * (a / b + 1) := by
  rcases eq_mul_div_add_of_pos a pos with ⟨v, hv, e⟩
  calc a = b * (a / b) + v := e
       _ < b * (a / b + 1) := by simp [mul_add, hv]


-- @@ L185-186 verbatim
@[simp] lemma div_one (a : V) : a / 1 = a :=
  le_antisymm (by simp) (le_iff_lt_succ.mpr <| by simpa using lt_mul_div a one_pos)


-- @@ L188-190 verbatim
lemma div_add_mul_self (a c : V) {b} (pos : 0 < b) : (a + c * b) / b = a / b + c := by
  rcases div_spec_of_pos' a pos with ⟨r, hr, ex⟩
  simpa [add_mul, add_right_comm, ← ex] using div_mul_add (a / b + c) _ hr


-- @@ L192-193 verbatim
lemma div_add_mul_self' (a c : V) {b} (pos : 0 < b) : (a + b * c) / b = a / b + c := by
  simpa [mul_comm] using div_add_mul_self a c pos


-- @@ L195-196 verbatim
lemma div_mul_add_self (a c : V) {b} (pos : 0 < b) : (a * b + c) / b = a + c / b := by
  simp [div_add_mul_self, pos, add_comm]


-- @@ L198-199 verbatim
lemma div_mul_add_self' (a c : V) {b} (pos : 0 < b) : (b * a + c) / b = a + c / b := by
  simp [mul_comm b a, div_mul_add_self, pos]


-- @@ L201-202 verbatim
@[simp] lemma div_mul_left (a : V) {b} (pos : 0 < b) : (a * b) / b = a := by
  simpa using div_mul_add a _ pos


-- @@ L204-205 verbatim
lemma div_mul_right (a : V) {b} (pos : 0 < b) : (b * a) / b = a := by
  simpa [mul_comm] using div_mul_add a _ pos


-- @@ L207-208 verbatim
@[simp] lemma div_eq_zero_of_lt (b : V) {a} (h : a < b) : a / b = 0 := by
  simpa using div_mul_add 0 b h


-- @@ L210-213 verbatim
@[simp] lemma div_sq (a : V) : a ^ 2 / a = a := by
  rcases zero_le a with (rfl | pos)
  · simp
  · simp [sq, pos]


-- @@ L215-215 verbatim
@[simp 1100] lemma div_self {a : V} (hx : 0 < a) : a / a = 1 := by simpa using div_mul_left 1 hx


-- @@ L217-217 verbatim
@[simp 1100] lemma div_mul' (a : V) {b} (pos : 0 < b) : (b * a) / b = a := div_mul_right a pos


-- @@ L219-220 verbatim
@[simp] lemma div_add_self_left {a} (pos : 0 < a) (b : V) : (a + b) / a = 1 + b / a := by
  simpa using div_mul_add_self 1 b pos


-- @@ L222-223 verbatim
@[simp] lemma div_add_self_right (a : V) {b} (pos : 0 < b) : (a + b) / b = a / b + 1 := by
  simpa using div_add_mul_self a 1 pos


-- @@ L225-230 verbatim
lemma mul_div_self_of_dvd {a b : V} : a * (b / a) = b ↔ a ∣ b := by
  rcases zero_le a with (rfl | pos)
  · simp[eq_comm]
  · constructor
    · intro e; rw [←e]; simp
    · rintro ⟨r, rfl⟩; simp [pos]


-- @@ L232-235 verbatim
lemma div_lt_of_pos_of_one_lt {a b : V} (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  rcases zero_le (a / b) with (e | lt)
  · simp [←e, ha]
  · exact lt_of_lt_of_le (lt_mul_of_one_lt_left lt hb) (mul_div_le a b)


-- @@ L237-239 verbatim
lemma le_two_mul_div_two_add_one (a : V) : a ≤ 2 * (a / 2) + 1 := by
  have : a < 2 * (a / 2 + 1) := lt_mul_div_succ a (show 0 < 2 from by simp)
  exact le_iff_lt_succ.mpr (by simpa [add_assoc, one_add_one_eq_two, mul_add] using this)


-- @@ L241-251 verbatim
lemma div_monotone {a b : V} (h : a ≤ b) (c : V) : a / c ≤ b / c := by
  rcases zero_le c with (rfl | pos)
  · simp
  by_contra A
  have : b / c + 1 ≤ a / c := succ_le_iff_lt.mpr (by simpa using A)
  have : a < a := calc
    a ≤ b               := h
    _ < c * (b / c + 1) := lt_mul_div b pos
    _ ≤ c * (a / c)     := mul_le_mul_left this
    _ ≤ a               := mul_div_le a c
  simp_all


-- @@ L253-260 verbatim
lemma div_lt_of_lt_mul {a b c : V} (h : a < b * c) : a / c < b := by
  by_contra hb
  have hb : b ≤ a / c := le_of_not_gt hb
  have : a < a := calc
    a < b * c     := h
    _ ≤ a / c * c := mul_le_mul_right hb
    _ ≤ a         := by simp
  simp_all


-- @@ L262-263 verbatim
lemma div_cancel_left {c} (pos : 0 < c) (a b : V) :
    (c * a) / (c * b) = a / b := by simp [div_mul, pos]


-- @@ L265-266 verbatim
lemma div_cancel_right {c} (pos : 0 < c) (a b : V) :
    (a * c) / (b * c) = a / b := by simp [mul_comm _ c, div_cancel_left pos]


-- @@ L268-268 verbatim
@[simp] lemma two_mul_add_one_div_two (a : V) : (2 * a + 1) / 2 = a := by simp [div_mul_add_self']


-- @@ L270-270 verbatim
end «lp_section_2»


-- @@ L272-272 verbatim
section «lp_section_3»


-- @@ L274-275 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def rem (a b : V) : V := a - b * (a / b)


-- @@ L277-278 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instModV : Mod V := ⟨rem⟩


-- @@ L280-280 verbatim
lemma mod_def (a b : V) : a % b = a - b * (a / b) := rfl


-- @@ L282-284 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.remDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute divDef.val
          (vecCons (#0) (vecCons (#2) (vecCons #3 ![]))))
        (LO.FirstOrder.Rewriting.substitute subDef.val
          (vecCons (#1)
            (vecCons (#2) (vecCons (Semiterm.Operator.Mul.mul.operator ![#3, #0]) ![]))))))
    (by simp)


-- @@ L286-286 verbatim
lemma rem_graph (a b c : V) : a = b % c ↔ ∃ x ≤ b, (x = b / c ∧ a = b - c * x) := by simp [mod_def]


-- @@ L288-289 expanded
lemma rem_defined : DefinedFunction₂ Sg0 ((· % ·) : V → V → V) remDef := by intro v;
  simp [remDef, rem_graph, Semiformula.eval_substs, le_iff_lt_succ]


-- @@ L291-292 verbatim
@[simp] lemma rem_defined_iff (v) :
    Semiformula.Evalbm V v remDef.val ↔ v 0 = v 1 % v 2 := rem_defined.df.iff v


-- @@ L294-294 expanded
instance rem_definable : BoldfaceFunction₂ Sg0 ((· % ·) : V → V → V) :=
  rem_defined.to_definable _


-- @@ L296-296 verbatim
lemma div_add_mod (a b : V) : b * (a / b) + (a % b) = a := add_tsub_self_of_le (mul_div_le a b)


-- @@ L298-298 verbatim
@[simp] lemma mod_zero (a : V) : a % 0 = a := by simp [mod_def]


-- @@ L300-300 verbatim
@[simp] lemma zero_mod (a : V) : 0 % a = 0 := by simp [mod_def]


-- @@ L302-305 verbatim
@[simp] lemma mod_self (a : V) : a % a = 0 := by
  rcases zero_le a with (rfl | h)
  · simp
  · simp [mod_def, h]


-- @@ L307-308 verbatim
lemma mod_mul_add_of_lt (a b : V) {r} (hr : r < b) : (a * b + r) % b = r := by
  simp [mod_def, div_mul_add a b hr, mul_comm]


-- @@ L310-311 verbatim
@[simp] lemma mod_mul_add (a c : V) (pos : 0 < b) : (a * b + c) % b = c % b := by
  simp [mod_def, div_mul_add_self, pos, mul_add, ←sub_sub, show b * a = a * b from mul_comm _ _]


-- @@ L313-314 verbatim
@[simp] lemma mod_add_mul (a b : V) (pos : 0 < c) : (a + b * c) % c = a % c := by
  simp [add_comm a (b * c), pos]


-- @@ L316-317 verbatim
@[simp] lemma mod_add_mul' (a b : V) (pos : 0 < c) : (a + c * b) % c = a % c := by
  simp [mul_comm c b, pos]


-- @@ L319-320 verbatim
@[simp] lemma mod_mul_add' (a c : V) (pos : 0 < b) : (b * a + c) % b = c % b := by
  simp [mul_comm b a, pos]


-- @@ L322-325 verbatim
@[simp] lemma mod_mul_self_left (a b : V) : (a * b) % b = 0 := by
  rcases zero_le b with (rfl | h)
  · simp
  · simpa using mod_mul_add_of_lt a b h


-- @@ L327-327 verbatim
@[simp] lemma mod_mul_self_right (a b : V) : (b * a) % b = 0 := by simp [mul_comm]


-- @@ L329-330 verbatim
@[simp] lemma mod_eq_self_of_lt {a b : V} (h : a < b) : a % b = a := by
  simpa using mod_mul_add_of_lt 0 b h


-- @@ L332-336 verbatim
@[simp] lemma mod_lt (a : V) {b} (pos : 0 < b) : a % b < b := by
  rcases div_spec_of_pos' a pos with ⟨r, hr, ha⟩
  have : ((a / b) * b + r) % b = r := mod_mul_add_of_lt _ _ hr
  have : a % b = r := by simpa [←ha] using this
  simp [this, hr]


-- @@ L338-338 verbatim
@[simp] lemma mod_le (a b : V) : a % b ≤ a := by simp [mod_def]


-- @@ L340-340 verbatim
instance mod_polybounded : Bounded₂ ((· % ·) : V → V → V) := ⟨#0, by intro v; simp⟩


-- @@ L342-346 verbatim
lemma mod_eq_zero_iff_dvd {a b : V} : b % a = 0 ↔ a ∣ b := by
  simp only [mod_def, sub_eq_zero_iff_le]
  constructor
  · intro H; exact mul_div_self_of_dvd.mp (le_antisymm (mul_div_le b a) H)
  · intro H; simp [mul_div_self_of_dvd.mpr H]


-- @@ L348-349 verbatim
@[simp] lemma mod_add_remove_right {a b : V} (pos : 0 < b) : (a + b) % b = a % b := by
  simpa using mod_add_mul a 1 pos


-- @@ L351-352 verbatim
lemma mod_add_remove_right_of_dvd {a b m : V} (h : m ∣ b) (pos : 0 < m) : (a + b) % m = a % m := by
  rcases h with ⟨b, rfl⟩; simp [pos]


-- @@ L354-355 verbatim
@[simp] lemma mod_add_remove_left {a b : V} (pos : 0 < a) : (a + b) % a = b % a := by
  simpa using mod_mul_add 1 b pos


-- @@ L357-358 verbatim
lemma mod_add_remove_left_of_dvd {a b m : V} (h : m ∣ a) (pos : 0 < m) : (a + b) % m = b % m := by
  rcases h with ⟨b, rfl⟩; simp [pos]


-- @@ L360-364 verbatim
lemma mod_add {a b m : V} (pos : 0 < m) : (a + b) % m = (a % m + b % m) % m := calc
  (a + b) % m = ((m * (a / m) + a % m) + (m * (b / m) + b % m)) % m := by simp [div_add_mod]
  _           = (m * (a / m) + m * (b / m) + (a % m) + (b % m)) % m := by
    simp [←add_assoc, add_right_comm]
  _           = (a % m + b % m) % m                                 := by simp [add_assoc, pos]


-- @@ L366-369 verbatim
lemma mod_mul {a b m : V} (pos : 0 < m) : (a * b) % m = ((a % m) * (b % m)) % m := calc
  (a * b) % m = ((m * (a / m) + (a % m)) * (m * (b / m) + b % m)) % m := by simp [div_add_mod]
  _           = ((a % m) * (b % m)) % m                               := by
    simp [add_mul, mul_add, pos, mul_left_comm _ m, add_assoc, mul_assoc]


-- @@ L371-374 verbatim
@[simp] lemma mod_div (a b : V) : a % b / b = 0 := by
  rcases zero_le b with (rfl | pos)
  · simp
  · exact div_eq_zero_of_lt b (by simp [pos])


-- @@ L376-376 verbatim
@[simp] lemma mod_one (a : V) : a % 1 = 0 := lt_one_iff_eq_zero.mp <| mod_lt a (by simp)


-- @@ L378-379 verbatim
lemma mod_two (a : V) : a % 2 = 0 ∨ a % 2 = 1 :=
  le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| mod_lt a (b := 2) (by simp)


-- @@ L381-382 verbatim
@[simp] lemma mod_two_not_zero_iff {a : V} : ¬a % 2 = 0 ↔ a % 2 = 1 := by
  rcases mod_two a with (h | h) <;> simp [*]


-- @@ L384-385 verbatim
@[simp] lemma mod_two_not_one_iff {a : V} : ¬a % 2 = 1 ↔ a % 2 = 0 := by
  rcases mod_two a with (h | h) <;> simp [*]


-- @@ L387-387 verbatim
end «lp_section_3»


-- @@ L389-401 verbatim
lemma two_dvd_mul {a b : V} : 2 ∣ a * b → 2 ∣ a ∨ 2 ∣ b := by
  intro H; by_contra A
  push Not at A
  have ha : a % 2 = 1 := by
    have : a % 2 = 0 ∨ a % 2 = 1 := mod_two a
    simpa [show a % 2 ≠ 0 from by simpa [←mod_eq_zero_iff_dvd] using A.1] using this
  have hb : b % 2 = 1 := by
    have : b % 2 = 0 ∨ b % 2 = 1 :=
      le_one_iff_eq_zero_or_one.mp <| lt_two_iff_le_one.mp <| mod_lt b (b := 2) (by simp)
    simpa [show b % 2 ≠ 0 from by simpa [←mod_eq_zero_iff_dvd] using A.2] using this
  have : a * b % 2 = 1 := by simp [mod_mul, ha, hb]
  have : ¬2 ∣ a * b := by simp [←mod_eq_zero_iff_dvd, this]
  contradiction


-- @@ L403-406 verbatim
lemma even_or_odd (a : V) : ∃ x, a = 2 * x ∨ a = 2 * x + 1 :=
  ⟨a / 2, by
    have : 2 * (a / 2) + (a % 2) = a := div_add_mod a 2
    rcases mod_two a with (e | e) <;> { simp[e] at this; simp [this] }⟩


-- @@ L408-410 verbatim
lemma even_or_odd' (a : V) : a = 2 * (a / 2) ∨ a = 2 * (a / 2) + 1 := by
  have : 2 * (a / 2) + (a % 2) = a := div_add_mod a 2
  rcases mod_two a with (e | e) <;>  simp [e] at this <;> simp [*]


-- @@ L412-412 verbatim
lemma two_prime : Prime (2 : V) := ⟨by simp, by simp, by intro a b h; exact two_dvd_mul h⟩


-- @@ L414-414 verbatim
section «lp_section_4»


-- @@ L416-435 expanded
lemma sqrt_exists_unique (a : V) : ∃! x, x * x ≤ a ∧ a < (x + 1) * (x + 1) :=
  by
  have : ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) :=
    by
    have : a < (a + 1) * (a + 1) → ∃ x, x * x ≤ a ∧ a < (x + 1) * (x + 1) := by
      simpa using
        open_leastNumber (P := fun x ↦ x * x ≤ a)
          ⟨Semiformula.Operator.operator Operator.LE.le
              ![Semiterm.Operator.Mul.mul.operator ![#0, #0], &a],
            by simp, by simp⟩
    have hn : a < (a + 1) * (a + 1) :=
      calc
        a ≤ a * a := le_mul_self a
        _ < a * a + 1 := (lt_add_one (a * a))
        _ ≤ (a + 1) * (a + 1) := by simp [add_mul_self_eq]
    exact this hn
  rcases this with ⟨x, hx⟩
  exact
    ExistsUnique.intro x hx
      (by
        intro y hy
        by_contra ne
        wlog lt : x < y
        · exact this a y hy x hx (Ne.symm ne) (Ne.lt_of_le ne <| by simpa using lt)
        have : a < a :=
          calc
            a < (x + 1) * (x + 1) := hx.2
            _ ≤ y * y := (mul_self_le_mul_self (by simp) (lt_iff_succ_le.mp lt))
            _ ≤ a := hy.1
        simp at this)


-- @@ L437-438 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sqrt (a : V) : V := Classical.choose! (sqrt_exists_unique a)


-- @@ L440-441 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:75 "√" => sqrt


-- @@ L443-444 expanded
@[simp]
lemma sqrt_spec_le (a : V) : sqrt a * sqrt a ≤ a :=
  (Classical.choose!_spec (sqrt_exists_unique a)).1


-- @@ L446-447 expanded
@[simp]
lemma sqrt_spec_lt (a : V) : a < (sqrt a + 1) * (sqrt a + 1) :=
  (Classical.choose!_spec (sqrt_exists_unique a)).2


-- @@ L449-450 expanded
lemma sqrt_graph {a b : V} : b = sqrt a ↔ b * b ≤ a ∧ a < (b + 1) * (b + 1) :=
  Classical.choose!_eq_iff _


-- @@ L452-454 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.sqrtDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Wedge.wedge
      (Semiformula.Operator.operator Operator.LE.le
        ![Semiterm.Operator.Mul.mul.operator ![#0, #0], #1])
      (Semiformula.Operator.operator Operator.LT.lt
        ![#1,
          Semiterm.Operator.Mul.mul.operator
            ![Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1],
              Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]]]))
    (by simp [])


-- @@ L456-457 expanded
lemma sqrt_defined : DefinedFunction₁ Sg0 (fun a : V ↦ sqrt a) sqrtDef := by intro v;
  simp [sqrt_graph, sqrtDef]


-- @@ L459-460 expanded
@[simp]
lemma sqrt_defined_iff (v) : Semiformula.Evalbm V v sqrtDef.val ↔ v 0 = sqrt (v 1) :=
  sqrt_defined.df.iff v


-- @@ L462-462 expanded
instance sqrt_definable : BoldfaceFunction₁ Sg0 ((sqrt ·) : V → V) :=
  sqrt_defined.to_definable


-- @@ L464-465 expanded
lemma eq_sqrt (x a : V) : x * x ≤ a ∧ a < (x + 1) * (x + 1) → x = sqrt a :=
  Classical.choose_uniq (sqrt_exists_unique a)


-- @@ L467-468 expanded
lemma sqrt_eq_of_le_of_lt {x a : V} (le : x * x ≤ a) (lt : a < (x + 1) * (x + 1)) : sqrt a = x :=
  Eq.symm <| eq_sqrt x a ⟨le, lt⟩


-- @@ L470-473 expanded
lemma sqrt_eq_of_le_of_le {x a : V} (le : x * x ≤ a) (h : a ≤ x * x + 2 * x) : sqrt a = x :=
  sqrt_eq_of_le_of_lt le
    (by
      rw [add_mul_self_eq]
      simpa using le_iff_lt_succ.mp h)


-- @@ L475-475 expanded
@[simp]
lemma sq_sqrt_le (a : V) : (sqrt a) ^ 2 ≤ a := by simp [sq]


-- @@ L477-477 expanded
@[simp]
lemma sqrt_lt_sq (a : V) : a < (sqrt a + 1) ^ 2 := by simp [sq]


-- @@ L479-482 expanded
@[simp]
lemma sqrt_mul_self (a : V) : sqrt (a * a) = a :=
  Eq.symm <|
    eq_sqrt a (a * a)
      (by
        simp only [Std.le_refl, true_and]
        exact mul_self_lt_mul_self (by simp) (by simp))


-- @@ L484-484 expanded
@[simp]
lemma sqrt_sq (a : V) : sqrt (a ^ 2) = a := by simp [sq]


-- @@ L486-486 expanded
@[simp]
lemma sqrt_zero : sqrt (0 : V) = 0 := by simpa using sqrt_mul_self (0 : V)


-- @@ L488-488 expanded
@[simp]
lemma sqrt_one : sqrt (1 : V) = 1 := by simpa using sqrt_mul_self (1 : V)


-- @@ L490-490 expanded
lemma sqrt_two : sqrt (2 : V) = 1 :=
  Eq.symm <| eq_sqrt 1 2 (by simp [one_add_one_eq_two])


-- @@ L492-494 expanded
lemma sqrt_three : sqrt (3 : V) = 1 :=
  Eq.symm <|
    eq_sqrt 1 3 <| by simp [one_add_one_eq_two, two_mul_two_eq_four, ← three_add_one_eq_four]


-- @@ L496-496 expanded
@[simp]
lemma sqrt_four : sqrt (4 : V) = 2 := by simp [← two_mul_two_eq_four]


-- @@ L498-501 expanded
@[simp]
lemma two_ne_square (a : V) : 2 ≠ a ^ 2 := by
  intro h
  rcases show a = sqrt 2 from by rw [h]; simp with rfl
  simp [sqrt_two] at h


-- @@ L503-504 expanded
@[simp]
lemma sqrt_le_add (a : V) : a ≤ sqrt a * sqrt a + 2 * sqrt a :=
  le_iff_lt_succ.mpr (by have := sqrt_spec_lt a; rw [add_mul_self_eq] at this; simpa using this)


-- @@ L506-512 expanded
@[simp]
lemma sqrt_le_self (a : V) : sqrt a ≤ a := by
  by_contra A
  have : a < a :=
    calc
      a ≤ a ^ 2 := le_sq a
      _ < (sqrt a) ^ 2 := by simpa [sq] using mul_self_lt_mul_self (by simp) (by simpa using A)
      _ ≤ a := sq_sqrt_le a
  simp_all


-- @@ L514-514 expanded
instance : Bounded₁ ((sqrt ·) : V → V) :=
  ⟨#0, by intro v; simp⟩


-- @@ L516-520 expanded
lemma sqrt_lt_self_of_one_lt {a : V} (h : 1 < a) : sqrt a < a :=
  by
  by_contra A
  have : a * a ≤ sqrt a * sqrt a := mul_self_le_mul_self (by simp) (by simpa using A)
  have : a * a ≤ a := le_trans this (sqrt_spec_le a)
  exact not_lt.mpr this (lt_mul_self h)


-- @@ L522-528 expanded
lemma sqrt_le_of_le_sq {a b : V} : a ≤ b ^ 2 → sqrt a ≤ b :=
  by
  intro h; by_contra A
  have : a < a :=
    calc
      a ≤ b ^ 2 := h
      _ < (sqrt a) ^ 2 := (sq_lt_sq.mpr (by simpa using A))
      _ ≤ a := by simp
  simp_all


-- @@ L530-532 expanded
lemma sq_lt_of_lt_sqrt {a b : V} : a < sqrt b → a ^ 2 < b :=
  by
  intro h; by_contra A
  exact not_le.mpr h (sqrt_le_of_le_sq <| show b ≤ a ^ 2 from by simpa using A)


-- @@ L534-534 verbatim
end «lp_section_4»


-- @@ L536-540 verbatim
section «lp_section_5»

-- Source:
-- https://github.com/leanprover-community/mathlib4/blob/
-- b075cdd0e6ad8b5a3295e7484b2ae59e9b2ec2a7/Mathlib/Data/Nat/Pairing.lean#L37

-- @@ L541-544 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def pair (a b : V) : V := if a < b then b * b + a else a * a + a + b

--notation "⟪" a ", " b "⟫" => pair a b


-- @@ L546-547 verbatim
/-- `!⟪x, y, z, ...⟫` notation for `Seq` -/
syntax "⟪" term,* "⟫" : term


-- @@ L549-551 unexpanded
macro_rules
  | `(⟪$term:term, $terms:term,*⟫) => `(pair $term ⟪$terms,*⟫)
  | `(⟪$term:term⟫) => `($term)


-- @@ L553-557 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander pair]
meta def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term $term2) => `(⟪$term, $term2⟫)
  | _ => throw ()


-- @@ L559-564 expanded
lemma pair_graph {a b c : V} :
    c = pair a b ↔ (a < b ∧ c = b * b + a) ∨ (b ≤ a ∧ c = a * a + a + b) :=
  by
  simp [pair]
  by_cases h : a < b
  · simp [h, show ¬b ≤ a from by simpa using h]
  · simp [h, show b ≤ a from by simpa using h]


-- @@ L566-568 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pairDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Vee.vee
      (Wedge.wedge (Semiformula.Operator.operator Operator.LT.lt ![#1, #2])
        (Semiformula.Operator.operator Operator.Eq.eq
          ![#0,
            Semiterm.Operator.Add.add.operator
              ![Semiterm.Operator.Mul.mul.operator ![#2, #2], #1]]))
      (Wedge.wedge (Semiformula.Operator.operator Operator.LE.le ![#2, #1])
        (Semiformula.Operator.operator Operator.Eq.eq
          ![#0,
            Semiterm.Operator.Add.add.operator
              ![Semiterm.Operator.Add.add.operator
                  ![Semiterm.Operator.Mul.mul.operator ![#1, #1], #1],
                #2]])))
    (by simp)


-- @@ L570-571 expanded
lemma pair_defined : DefinedFunction₂ Sg0 (fun a b : V ↦ pair a b) pairDef := by intro v;
  simp [pair_graph, pairDef]


-- @@ L573-574 expanded
@[simp]
lemma pair_defined_iff (v) : Semiformula.Evalbm V v pairDef.val ↔ v 0 = pair (v 1) (v 2) :=
  pair_defined.df.iff v


-- @@ L576-576 expanded
instance pair_definable : BoldfaceFunction₂ Sg0 (pair : V → V → V) :=
  pair_defined.to_definable


-- @@ L578-579 expanded
instance : Bounded₂ (pair : V → V → V) :=
  ⟨Semiterm.Operator.Add.add.operator
      ![Semiterm.Operator.Add.add.operator ![Semiterm.Operator.Mul.mul.operator ![#1, #1], #0],
        Semiterm.Operator.Add.add.operator
          ![Semiterm.Operator.Add.add.operator ![Semiterm.Operator.Mul.mul.operator ![#0, #0], #0],
            #1]],
    by intro v; simp [pair]; split_ifs <;> try simp [*]⟩


-- @@ L581-582 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def unpair (a : V) : V × V :=
  if a - sqrt a * sqrt a < sqrt a then (a - sqrt a * sqrt a, sqrt a)
  else (sqrt a, a - sqrt a * sqrt a - sqrt a)


-- @@ L584-585 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev pi₁ (a : V) : V := (unpair a).1


-- @@ L587-588 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev pi₂ (a : V) : V := (unpair a).2


-- @@ L590-591 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix: 80 "π₁" => pi₁


-- @@ L593-594 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix: 80 "π₂" => pi₂


-- @@ L596-603 expanded
@[simp]
lemma pair_unpair (a : V) : pair (pi₁ a) (pi₂ a) = a :=
  by
  simp only [pi₁, unpair, pi₂]
  split_ifs with h
  · simp [pair, h]
  · change pair (sqrt a) (a - sqrt a * sqrt a - sqrt a) = a
    rw [pair]
    have : a - sqrt a * sqrt a - sqrt a ≤ sqrt a := by simp [add_comm (2 * sqrt a), ← two_mul]
    simp_all


-- @@ L605-614 expanded
@[simp]
lemma unpair_pair (a b : V) : unpair (pair a b) = (a, b) :=
  by
  simp only [pair]; split_ifs with h
  · have : sqrt (b * b + a) = b :=
      sqrt_eq_of_le_of_le (by simp)
        (by
          simp only [add_le_add_iff_left]
          exact le_trans (le_of_lt h) (by simp only [le_two_mul_left]))
    simp [unpair, this, show ¬b ≤ a from by simpa using h]
  · have : sqrt (a * a + (a + b)) = a :=
      sqrt_eq_of_le_of_le (by simp) (by simp [two_mul, show b ≤ a from by simpa using h])
    simp [unpair, this, add_assoc]


-- @@ L616-616 expanded
@[simp]
lemma pi₁_pair (a b : V) : pi₁ (pair a b) = a := by simp [pi₁]


-- @@ L618-618 expanded
@[simp]
lemma pi₂_pair (a b : V) : pi₂ (pair a b) = b := by simp [pi₂]


-- @@ L620-622 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def pairEquiv : V × V ≃ V :=
  ⟨Function.uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩


-- @@ L624-624 expanded
@[simp]
lemma pi₁_le_self (a : V) : pi₁ a ≤ a := by simp [pi₁, unpair]; split_ifs <;> simp


-- @@ L626-627 expanded
@[simp]
lemma pi₂_le_self (a : V) : pi₂ a ≤ a := by simp [pi₂, unpair]; split_ifs <;> simp [add_assoc]


-- @@ L629-629 expanded
@[simp]
lemma le_pair_left (a b : V) : a ≤ pair a b := by simpa using pi₁_le_self (pair a b)


-- @@ L631-631 expanded
@[simp]
lemma le_pair_right (a b : V) : b ≤ pair a b := by simpa using pi₂_le_self (pair a b)


-- @@ L633-639 expanded
@[simp]
lemma lt_pair_left_of_pos {a} (pos : 0 < a) (b : V) : a < pair a b :=
  by
  simp only [pair]; split_ifs
  · simp only [lt_add_iff_pos_left, mul_self_pos, ne_eq]
    exact pos_iff_ne_zero.mp <| pos_of_gt (by assumption)
  ·
    calc
      a < a * a + a := lt_add_of_pos_left a (by simpa using (pos_iff_ne_zero.mp pos))
      _ ≤ a * a + a + b := by simp


-- @@ L641-641 verbatim
instance : Bounded₁ (pi₁ : V → V) := ⟨#0, by intro v; simp⟩


-- @@ L643-643 verbatim
instance : Bounded₁ (pi₂ : V → V) := ⟨#0, by intro v; simp⟩


-- @@ L645-647 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pi₁Def : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#2) (vecCons (#1) (vecCons #0 ![])))))
    (by simp)


-- @@ L649-651 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pi₂Def : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#2) (vecCons (#0) (vecCons #1 ![])))))
    (by simp)


-- @@ L653-661 expanded
lemma pi₁_defined : DefinedFunction₁ Sg0 (pi₁ : V → V) pi₁Def :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, pi₁Def, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_app_two, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.vecCons_zero, Matrix.constant_eq_singleton, pair_defined_iff]
  constructor
  · intro h; exact ⟨pi₂ (v 1), by simp, by simp [h]⟩
  · rintro ⟨a, _, e⟩; simp [show v 1 = pair (v 0) a from e]


-- @@ L663-664 expanded
@[simp]
lemma pi₁_defined_iff (v) : Semiformula.Evalbm V v pi₁Def.val ↔ v 0 = pi₁ (v 1) :=
  pi₁_defined.df.iff v


-- @@ L666-666 expanded
instance pi₁_definable : BoldfaceFunction₁ Sg0 (pi₁ : V → V) :=
  pi₁_defined.to_definable₀


-- @@ L668-676 expanded
lemma pi₂_defined : DefinedFunction₁ Sg0 (pi₂ : V → V) pi₂Def :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, pi₂Def, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_app_two, Matrix.vecCons_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.constant_eq_singleton, pair_defined_iff]
  constructor
  · intro h; exact ⟨pi₁ (v 1), by simp, by simp [h]⟩
  · rintro ⟨a, _, e⟩; simp [show v 1 = pair a (v 0) from e]


-- @@ L678-679 expanded
@[simp]
lemma pi₂_defined_iff (v) : Semiformula.Evalbm V v pi₂Def.val ↔ v 0 = pi₂ (v 1) :=
  pi₂_defined.df.iff v


-- @@ L681-681 expanded
instance pi₂_definable : BoldfaceFunction₁ Sg0 (pi₂ : V → V) :=
  pi₂_defined.to_definable₀


-- @@ L683-698 expanded
lemma pair_lt_pair_left {a₁ a₂ : V} (h : a₁ < a₂) (b) : pair a₁ b < pair a₂ b :=
  by
  by_cases h₁ : a₁ < b <;> simp only [pair, h₁, ↓reduceIte]
  · by_cases h₂ : a₂ < b
    · simp only [h₂, ↓reduceIte, add_lt_add_iff_left, h]
    · simp only [h₂, ↓reduceIte]
      calc
        b * b + a₁ < b * b + b := by simpa using h₁
        _ ≤ a₂ * a₂ + a₂ :=
          (add_le_add (mul_le_mul (by simpa using h₂) (by simpa using h₂) (by simp) (by simp))
            (by simpa using h₂))
        _ ≤ a₂ * a₂ + a₂ + b := by simp
  · have h₂ : ¬a₂ < b := not_lt.mpr (le_trans (not_lt.mp h₁) (le_of_lt h))
    simp only [h₂, ↓reduceIte]
    have hs : a₁ * a₁ + a₁ < a₂ * a₂ + a₂ :=
      _root_.add_lt_add (mul_self_lt_mul_self (zero_le a₁) h) h
    simpa [add_comm] using add_lt_add_right hs b


-- @@ L700-703 expanded
lemma pair_le_pair_left {a₁ a₂ : V} (h : a₁ ≤ a₂) (b) : pair a₁ b ≤ pair a₂ b :=
  by
  rcases h with (rfl | lt)
  · simp
  · exact le_of_lt (pair_lt_pair_left lt b)


-- @@ L705-717 expanded
lemma pair_lt_pair_right (a : V) {b₁ b₂} (h : b₁ < b₂) : pair a b₁ < pair a b₂ :=
  by
  by_cases h₁ : a < b₁ <;> simp only [pair, h₁, ↓reduceIte]
  · simpa [lt_trans h₁ h, ← sq] using h
  · by_cases h₂ : a < b₂
    · simp only [h₂, ↓reduceIte]
      calc
        a * a + a + b₁ < (a + 1) * (a + 1) + b₁ :=
          by
          simp only [add_mul_self_eq, mul_one, add_lt_add_iff_right]
          exact lt_succ_iff_le.mpr (by simp only [add_le_add_iff_left, le_two_mul_left])
        _ ≤ b₂ * b₂ + b₁ := by simpa [← sq, succ_le_iff_lt] using h₂
        _ ≤ b₂ * b₂ + a := by simpa using h₁
    · simp only [h₂, ↓reduceIte]
      simpa [add_comm] using add_lt_add_left h (a * a + a)


-- @@ L719-722 expanded
lemma pair_le_pair_right (a : V) {b₁ b₂} (h : b₁ ≤ b₂) : pair a b₁ ≤ pair a b₂ :=
  by
  rcases h with (rfl | lt)
  · simp
  · exact le_of_lt (pair_lt_pair_right a lt)


-- @@ L724-727 expanded
lemma pair_le_pair {a₁ a₂ b₁ b₂ : V} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : pair a₁ b₁ ≤ pair a₂ b₂ :=
  calc
    pair a₁ b₁ ≤ pair a₂ b₁ := pair_le_pair_left ha b₁
    _ ≤ pair a₂ b₂ := pair_le_pair_right a₂ hb


-- @@ L729-732 expanded
lemma pair_lt_pair {a₁ a₂ b₁ b₂ : V} (ha : a₁ < a₂) (hb : b₁ < b₂) : pair a₁ b₁ < pair a₂ b₂ :=
  calc
    pair a₁ b₁ < pair a₂ b₁ := pair_lt_pair_left ha b₁
    _ < pair a₂ b₂ := pair_lt_pair_right a₂ hb


-- @@ L734-737 expanded
@[simp]
lemma pair_polybound (a b : V) : pair a b ≤ (a + b + 1) ^ 2 :=
  by
  by_cases h : a < b <;> simp [pair, h, sq, add_mul_self_eq, two_mul]
  · simp [← add_assoc, add_right_comm _ a]; simp [add_right_comm _ (b * b)]
  · simp [← add_assoc, add_right_comm _ b]; simp [add_right_comm _ a]; simp [add_assoc]


-- @@ L739-741 expanded
@[simp]
lemma pair_ext_iff {a₁ a₂ b₁ b₂ : V} : pair a₁ b₁ = pair a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun e ↦ ⟨by simpa using congr_arg (pi₁ ·) e, by simpa using congr_arg (pi₂ ·) e⟩, by
    rintro ⟨rfl, rfl⟩; simp⟩


-- @@ L743-743 verbatim
section «lp_section_6»


-- @@ L745-747 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pair₃Def : Sg0.Semisentence 4 :=
  .mkSigma
    (Semiformula.bexLTSucc (#0)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#1) (vecCons (#2) (vecCons #0 ![]))))
        (LO.FirstOrder.Rewriting.substitute pairDef
          (vecCons (#0) (vecCons (#3) (vecCons #4 ![]))))))
    (by simp)


-- @@ L749-752 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pair₄Def : Sg0.Semisentence 5 :=
  .mkSigma
    (Semiformula.bexLTSucc (#0)
      (Semiformula.bexLTSucc (#0)
        (Wedge.wedge
          (LO.FirstOrder.Rewriting.substitute pairDef
            (vecCons (#2) (vecCons (#3) (vecCons #1 ![]))))
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#1) (vecCons (#4) (vecCons #0 ![]))))
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#0) (vecCons (#5) (vecCons #6 ![]))))))))
    (by simp)


-- @@ L754-757 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pair₅Def : Sg0.Semisentence 6 :=
  .mkSigma
    (Semiformula.bexLTSucc (#0)
      (Semiformula.bexLTSucc (#0)
        (Semiformula.bexLTSucc (#0)
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#3) (vecCons (#4) (vecCons #2 ![]))))
            (Wedge.wedge
              (LO.FirstOrder.Rewriting.substitute pairDef
                (vecCons (#2) (vecCons (#5) (vecCons #1 ![]))))
              (Wedge.wedge
                (LO.FirstOrder.Rewriting.substitute pairDef
                  (vecCons (#1) (vecCons (#6) (vecCons #0 ![]))))
                (LO.FirstOrder.Rewriting.substitute pairDef
                  (vecCons (#0) (vecCons (#7) (vecCons #8 ![]))))))))))
    (by simp)


-- @@ L759-761 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pair₆Def : Sg0.Semisentence 7 :=
  .mkSigma
    (Semiformula.bexLTSucc (#0)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pair₅Def
          (vecCons (#0)
            (vecCons (#3) (vecCons (#4) (vecCons (#5) (vecCons (#6) (vecCons #7 ![])))))))
        (LO.FirstOrder.Rewriting.substitute pairDef
          (vecCons (#1) (vecCons (#2) (vecCons #0 ![]))))))
    (by simp)


-- @@ L763-765 verbatim
theorem fegergreg (v : Fin 4 → ℕ) : v (0 : Fin (Nat.succ 1)).succ.succ = v 2 := by
  { simp only [Nat.succ_eq_add_one,
  Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] }


-- @@ L767-767 verbatim
theorem fin4 {n} : (2 : Fin (n + 3)).succ = 3 := rfl


-- @@ L769-769 verbatim
@[simp] theorem _root_.LO.Arith.Fin.succ_zero_eq_one'' {n} : (0 : Fin (n + 1)).succ = 1 := rfl


-- @@ L771-771 verbatim
@[simp] theorem _root_.LO.Arith.Fin.succ_two_eq_three {n} : (2 : Fin (n + 3)).succ = 3 := fin4


-- @@ L773-775 verbatim
theorem ss (v : Fin 4 → ℕ) : v (Fin.succ (0 : Fin (Nat.succ 1))).succ = v 2 := by
  { simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two] }


-- @@ L777-786 expanded
lemma pair₃_defined : DefinedFunction₃ Sg0 ((pair · (pair · ·)) : V → V → V → V) pair₃Def :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.succ_two_eq_three,
    Nat.reduceAdd, pair₃Def, Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_bexLTSucc', Semiterm.val_bvar, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_one, Matrix.cons_app_two,
    Matrix.cons_val_fin_one, Matrix.vecCons_zero, Matrix.constant_eq_singleton, pair_defined_iff,
    Matrix.cons_app_three, Matrix.cons_app_four, LogicalConnective.Prop.and_eq,
    exists_eq_right_right, iff_and_self]
  rintro h; simp [h]


-- @@ L788-789 expanded
@[simp]
lemma eval_pair₃Def (v) :
    Semiformula.Evalbm V v pair₃Def.val ↔ v 0 = pair (v 1) (pair (v 2) (v 3)) :=
  pair₃_defined.df.iff v


-- @@ L791-801 expanded
lemma pair₄_defined :
    DefinedFunction₄ Sg0 ((pair · (pair · (pair · ·))) : V → V → V → V → V) pair₄Def :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.succ_two_eq_three,
    Fin.reduceSucc, Nat.reduceAdd, pair₄Def, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
    Matrix.vecCons_zero, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.cons_app_two, Matrix.cons_val_one, Matrix.cons_app_three,
    Matrix.cons_val_fin_one, Matrix.constant_eq_singleton, pair_defined_iff, Matrix.cons_app_four,
    Matrix.cons_app_five, Matrix.cons_app_six, LogicalConnective.Prop.and_eq, ↓existsAndEq,
    and_true, le_pair_right, true_and, iff_and_self]
  simp_all


-- @@ L803-804 expanded
@[simp]
lemma eval_pair₄Def (v) :
    Semiformula.Evalbm V v pair₄Def.val ↔ v 0 = pair (v 1) (pair (v 2) (pair (v 3) (v 4))) :=
  pair₄_defined.df.iff v


-- @@ L806-817 expanded
lemma pair₅_defined :
    Sg0.DefinedFunction
      (fun v : Fin 5 → V ↦ (pair (v 0) (pair (v 1) (pair (v 2) (pair (v 3) (v 4)))))) pair₅Def :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.succ_two_eq_three,
    Fin.reduceSucc, Nat.reduceAdd, pair₅Def, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
    Matrix.vecCons_zero, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.cons_app_three, Matrix.cons_app_two, Matrix.cons_val_one,
    Matrix.cons_app_four, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton, pair_defined_iff,
    Matrix.cons_app_five, Matrix.cons_app_six, Matrix.cons_app_seven, Matrix.cons_app_eight,
    LogicalConnective.Prop.and_eq, ↓existsAndEq, and_true, le_pair_right, true_and, iff_and_self]
  simp_all


-- @@ L819-820 expanded
@[simp]
lemma eval_pair₅Def (v) :
    Semiformula.Evalbm V v pair₅Def.val ↔
      v 0 = pair (v 1) (pair (v 2) (pair (v 3) (pair (v 4) (v 5)))) :=
  pair₅_defined.df.iff v


-- @@ L822-833 expanded
lemma pair₆_defined :
    Sg0.DefinedFunction
      (fun v : Fin 6 → V ↦ (pair (v 0) (pair (v 1) (pair (v 2) (pair (v 3) (pair (v 4) (v 5)))))))
      pair₆Def :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.succ_two_eq_three,
    Fin.reduceSucc, Nat.reduceAdd, pair₆Def, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.vecCons_zero, Matrix.cons_app_three, Matrix.cons_app_four, Matrix.cons_app_five,
    Matrix.cons_app_six, Matrix.cons_val_fin_one, Matrix.cons_app_seven,
    Matrix.constant_eq_singleton, eval_pair₅Def, Matrix.cons_val_one, Matrix.cons_app_two,
    pair_defined_iff, LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and, iff_and_self]
  simp_all


-- @@ L835-837 expanded
@[simp]
lemma eval_pair₆Def (v) :
    Semiformula.Evalbm V v pair₆Def.val ↔
      v 0 = pair (v 1) (pair (v 2) (pair (v 3) (pair (v 4) (pair (v 5) (v 6))))) :=
  pair₆_defined.df.iff v


-- @@ L839-839 verbatim
end «lp_section_6»


-- @@ L841-844 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def npair : {n : ℕ} → (v : Fin n → V) → V
  | 0, _ => 0
  | _ + 1, v => pair (v 0) (npair (v ·.succ))


-- @@ L846-846 verbatim
@[simp] lemma npair_zero (v : Fin 0 → V) : npair v = 0 := by simp [npair]


-- @@ L848-848 expanded
lemma npair_succ (x) (v : Fin n → V) : npair (vecCons x v) = pair x (npair v) := by simp [npair]


-- @@ L850-853 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def unNpair : {n : ℕ} → Fin n → V → V
  | 0, i, _ => i.elim0
  | _ + 1, i, x => Fin.cases (pi₁ x) (fun i ↦ unNpair i (pi₂ x)) i


-- @@ L855-860 verbatim
@[simp] lemma unNpair_npair {n} (i : Fin n) (v : Fin n → V) : unNpair i (npair v) = v i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp [npair, unNpair, *]
    cases i using Fin.cases <;> simp


-- @@ L862-862 verbatim
section «lp_section_7»


-- @@ L864-869 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.unNpairDef : {n : ℕ} → (i : Fin n) → Sg0.Semisentence 2
  | 0, i => i.elim0
  | n + 1, i =>
    Fin.cases pi₁Def
      (fun i ↦
        .mkSigma
          (Semiformula.bexLTSucc (#1)
            (Wedge.wedge (LO.FirstOrder.Rewriting.substitute pi₂Def (vecCons (#0) (vecCons #2 ![])))
              (LO.FirstOrder.Rewriting.substitute (unNpairDef i) (vecCons (#1) (vecCons #0 ![])))))
          (by simp))
      i


-- @@ L871-878 expanded
lemma unNpair_defined {n} (i : Fin n) : DefinedFunction₁ Sg0 (unNpair i : V → V) (unNpairDef i) :=
  by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    intro v
    cases i using Fin.cases with
    | zero => simp [unNpairDef, unNpair]
    | succ i => simp [unNpairDef, unNpair, (ih i).df.iff]


-- @@ L880-882 verbatim
@[simp 1100] lemma eval_unNpairDef {n} (i : Fin n) (v) :
    Semiformula.Evalbm V v (unNpairDef i).val ↔ v 0 = unNpair i (v 1) :=
      (unNpair_defined i).df.iff v


-- @@ L884-885 expanded
@[aesop 10 (rule_sets := [Definability]) safe]
instance unNpair_definable {n} (i : Fin n) (Γ) : BoldfaceFunction₁ Γ (unNpair i : V → V) :=
  (unNpair_defined i).to_definable₀


-- @@ L887-887 verbatim
end «lp_section_7»


-- @@ L889-889 verbatim
end «lp_section_5»


-- @@ L891-891 verbatim
end «lp_section_1»


-- @@ L893-893 verbatim
section «lp_section_8»


-- @@ L895-895 expanded
variable [ModelsTheory V iOpen]


-- @@ L897-913 expanded
@[elab_as_elim]
lemma hierarchy_polynomial_induction (Γ m)
    [ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy Γ m))] {P : V → Prop}
    (hP : BoldfacePred Γ-[m] P) (zero : P 0) (even : ∀ x > 0, P x → P (2 * x))
    (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  by
  intro x; induction x using order_induction_h
  · exact Γ
  · exact m
  · exact hP
  case inst => exact inferInstance
  case ind x IH =>
    rcases zero_le x with (rfl | pos)
    · exact zero
    · have : x / 2 < x := div_lt_of_pos_of_one_lt pos one_lt_two
      rcases even_or_odd' x with (hx | hx)
      ·
        simpa [← hx] using
          even (x / 2)
            (by by_contra A; simp at A; simp [show x = 0 from by simpa [A] using hx] at pos)
            (IH (x / 2) this)
      · simpa [← hx] using odd (x / 2) (IH (x / 2) this)


-- @@ L915-915 verbatim
end «lp_section_8»


-- @@ L917-920 expanded
@[elab_as_elim]
lemma hierarchy_polynomial_induction_oRing_sigma₀ [ModelsTheory V (iSigma 0)] {P : V → Prop}
    (hP : BoldfacePred Sg0 P) (zero : P 0) (even : ∀ x > 0, P x → P (2 * x))
    (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction SigmaSymbol.sigma 0 (P := P) hP zero even odd


-- @@ L922-925 expanded
@[elab_as_elim]
lemma hierarchy_polynomial_induction_oRing_sigma₁ [ModelsTheory V (iSigma 1)] {P : V → Prop}
    (hP : BoldfacePred Sg1 P) (zero : P 0) (even : ∀ x > 0, P x → P (2 * x))
    (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction SigmaSymbol.sigma 1 (P := P) hP zero even odd


-- @@ L927-930 expanded
@[elab_as_elim]
lemma hierarchy_polynomial_induction_oRing_pi₁ [ModelsTheory V (iPi 1)] {P : V → Prop}
    (hP : BoldfacePred Pg1 P) (zero : P 0) (even : ∀ x > 0, P x → P (2 * x))
    (odd : ∀ x, P x → P (2 * x + 1)) : ∀ x, P x :=
  hierarchy_polynomial_induction PiSymbol.pi 1 (P := P) hP zero even odd


-- @@ L932-932 expanded
variable [ModelsTheory V iOpen]


-- @@ L934-934 expanded
lemma nat_cast_pair (n m : ℕ) : (pair n m : ℕ) = pair (↑n : V) (↑m : V) := by simp [pair]


-- @@ L936-936 expanded
lemma nat_pair_eq (m n : ℕ) : pair n m = Nat.pair n m := by simp [Arith.pair, Nat.pair]


-- @@ L938-938 expanded
lemma pair_coe_eq_coe_pair (m n : ℕ) : pair n m = (Nat.pair n m : V) := by simp [nat_pair_eq]


-- @@ L940-940 verbatim
end «lp_nc_section_1»


-- @@ L942-942 verbatim
end Arith

-- @@ L943-943 verbatim
end LO
