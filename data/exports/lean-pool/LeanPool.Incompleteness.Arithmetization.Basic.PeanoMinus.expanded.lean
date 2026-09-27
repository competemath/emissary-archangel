/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Definability.BoundedBoldface
public import LeanPool.Incompleteness.Foundation.Vorspiel.ExistsUnique
public import Mathlib.Algebra.Prime.Defs
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Prime.Lemmas


-- @@ L15-15 verbatim
/-! # PeanoMinus -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Arith


-- @@ L23-23 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L25-25 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L27-27 expanded
variable {V : Type*} [ORingStruc V] [ModelsTheory V PeanoMinus]


-- @@ L29-29 verbatim
variable {a b c : V}


-- @@ L31-31 verbatim
section «lp_section_1»


-- @@ L33-41 verbatim
lemma sub_existsUnique (a b : V) : ∃! c, (a ≥ b → a = b + c) ∧ (a < b → c = 0) := by
  have : b ≤ a ∨ a < b := le_or_gt b a
  rcases this with hxy | hxy
  · simp only [ge_iff_le, hxy, forall_const, isEmpty_Prop, not_lt, IsEmpty.forall_iff,
      and_true]
    have : ∃ c, a = b + c := exists_add_of_le hxy
    rcases this with ⟨c, rfl⟩
    exact ExistsUnique.intro c rfl (fun a h => (add_left_cancel h).symm)
  · simp_all


-- @@ L43-44 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sub (a b : V) : V := Classical.choose! (sub_existsUnique a b)


-- @@ L46-46 verbatim
instance instSubV : Sub V := ⟨sub⟩


-- @@ L48-49 verbatim
lemma sub_spec_of_ge (h : a ≥ b) : a = b + (a - b) :=
  (Classical.choose!_spec (sub_existsUnique a b)).1 h


-- @@ L51-51 verbatim
lemma sub_spec_of_lt (h : a < b) : a - b = 0 := (Classical.choose!_spec (sub_existsUnique a b)).2 h


-- @@ L53-54 verbatim
lemma sub_eq_iff : c = a - b ↔ ((a ≥ b → a = b + c) ∧ (a < b → c = 0)) :=
  Classical.choose!_eq_iff (sub_existsUnique a b)


-- @@ L56-60 verbatim
@[simp 1100] lemma sub_le_self (a b : V) : a - b ≤ a := by
  have : b ≤ a ∨ a < b := le_or_gt b a
  rcases this with (hxy | hxy) <;> simp[]
  · simpa [← sub_spec_of_ge hxy] using show a - b ≤ b + (a - b) from le_add_self
  · simp[sub_spec_of_lt hxy]


-- @@ L62-62 verbatim
open FirstOrder.Arith.HierarchySymbol.Boldface


-- @@ L64-67 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.subDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#2, #1])
        (Semiformula.Operator.operator Operator.Eq.eq
          ![#1, Semiterm.Operator.Add.add.operator ![#2, #0]]))
      (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![#1, #2])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])))
    (by simp [])


-- @@ L69-70 expanded
lemma sub_defined : DefinedFunction₂ Sg0 ((· - ·) : V → V → V) subDef := by intro v;
  simp [FirstOrder.Arith.subDef, sub_eq_iff]


-- @@ L72-73 verbatim
@[simp] lemma sub_defined_iff (v) :
    Semiformula.Evalbm V v subDef.val ↔ v 0 = v 1 - v 2 := sub_defined.df.iff v


-- @@ L75-77 verbatim
instance sub_definable (ℌ : HierarchySymbol) : ℌ.BoldfaceFunction₂ ((· - ·) :
    V → V → V) :=
  sub_defined.to_definable₀


-- @@ L79-79 verbatim
instance sub_polybounded : Bounded₂ ((· - ·) : V → V → V) := ⟨#0, fun _ ↦ by simp⟩


-- @@ L81-83 verbatim
@[simp] lemma sub_self (a : V) : a - a = 0 :=
  add_left_cancel (a := a) (by
    simpa using (sub_spec_of_ge (a := a) (b := a) (by rfl)).symm)


-- @@ L85-86 verbatim
lemma sub_spec_of_le (h : a ≤ b) : a - b = 0 := by
  rcases lt_or_eq_of_le h with (lt | rfl) <;> simp [sub_spec_of_lt, *]


-- @@ L88-89 verbatim
lemma sub_add_self_of_le (h : b ≤ a) :
    a - b + b = a := by symm; rw [add_comm]; exact sub_spec_of_ge h


-- @@ L91-91 verbatim
lemma add_tsub_self_of_le (h : b ≤ a) : b + (a - b) = a := by symm; exact sub_spec_of_ge h


-- @@ L93-94 verbatim
@[simp] lemma add_sub_self : (a + b) - b = a := by
  symm; simpa [add_comm b] using sub_spec_of_ge (show b ≤ a + b from le_add_self)


-- @@ L96-96 verbatim
@[simp] lemma add_sub_self' : (b + a) - b = a := by simp [add_comm]


-- @@ L98-98 verbatim
@[simp] lemma zero_sub (a : V) : 0 - a = 0 := sub_spec_of_le (by simp)


-- @@ L100-101 verbatim
@[simp] lemma sub_zero (a : V) : a - 0 = a := by
  simpa using sub_add_self_of_le (show 0 ≤ a from zero_le a)


-- @@ L103-103 verbatim
lemma sub_remove_left (e : a = b + c) : a - c = b := by simp[e]


-- @@ L105-118 verbatim
lemma sub_sub : a - b - c = a - (b + c) := by
  by_cases ha : b + c ≤ a
  · exact sub_remove_left <| sub_remove_left <| by
      simp [add_assoc, show c + b = b + c from add_comm _ _, sub_add_self_of_le, ha]
  · simp only [sub_spec_of_lt (show a < b + c from not_le.mp ha)]
    by_cases hc : c ≤ a - b
    · by_cases hb : b ≤ a
      · have : a < a := calc
          a < b + c       := not_le.mp ha
          _ ≤ b + (a - b) := by simp[hc]
          _ = a           := add_tsub_self_of_le hb
        simp at this
      · simp [show a - b = 0 from sub_spec_of_lt (not_le.mp hb)]
    · exact sub_spec_of_lt (not_le.mp hc)


-- @@ L120-125 verbatim
@[simp] lemma pos_sub_iff_lt : 0 < a - b ↔ b < a :=
  ⟨by contrapose; simp only [not_lt, nonpos_iff_eq_zero]; exact sub_spec_of_le,
   by intro h; by_contra hs
      simp only [not_lt, nonpos_iff_eq_zero] at hs
      have : a = b := by simpa [hs] using sub_spec_of_ge (show b ≤ a from LT.lt.le h)
      simp [this] at h⟩


-- @@ L127-127 verbatim
@[simp] lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := not_iff_not.mp (by simp [←pos_iff_ne_zero])


-- @@ L129-137 verbatim
instance : OrderedSub V where
  tsub_le_iff_right := by
    intro a b c
    by_cases h : b ≤ a
    · calc
        a - b ≤ c ↔ (a - b) + b ≤ c + b := by simp
        _         ↔ a ≤ c + b           := by rw [sub_add_self_of_le h]
    · simp only [sub_spec_of_lt (show a < b from by simpa using h), _root_.zero_le, true_iff]
      exact le_trans (le_of_lt <| show a < b from by simpa using h) (by simp)


-- @@ L139-142 verbatim
lemma zero_or_succ (a : V) : a = 0 ∨ ∃ a', a = a' + 1 := by
  rcases zero_le a with (rfl | pos)
  · simp
  · right; exact ⟨a - 1, by rw [sub_add_self_of_le]; exact pos_iff_one_le.mp pos⟩


-- @@ L144-145 verbatim
lemma pred_lt_self_of_pos (h : 0 < a) : a - 1 < a := by
  simp_all


-- @@ L147-148 verbatim
lemma tsub_lt_iff_left (h : b ≤ a) : a - b < c ↔ a < c + b :=
  AddLECancellable.tsub_lt_iff_right (add_le_cancel b) h


-- @@ L150-155 verbatim
lemma sub_mul (h : b ≤ a) : (a - b) * c = a * c - b * c := by
  have : a = (a - b) + b := (tsub_eq_iff_eq_add_of_le h).mp rfl
  calc
    (a - b) * c = (a - b) * c + b * c - b * c := by simp
    _           = (a - b + b) * c - b * c     := by simp [add_mul]
    _           = a * c - b * c               := by simp [sub_add_self_of_le h]


-- @@ L157-157 verbatim
lemma mul_sub (h : b ≤ a) : c * (a - b) = c * a - c * b := by simp [mul_comm c, sub_mul, h]


-- @@ L159-159 verbatim
lemma add_sub_of_le (h : c ≤ b) (a : V) : a + b - c = a + (b - c) := add_tsub_assoc_of_le h a


-- @@ L161-165 verbatim
lemma sub_succ_add_succ {x y : V} (h : y < x) (z) : x - (y + 1) + (z + 1) = x - y + z := calc
  x - (y + 1) + (z + 1) = x - (y + 1) + 1 + z := by simp [add_assoc, add_comm]
  _                     = x - y - 1 + 1 + z   := by simp [sub_sub]
  _                     = x - y + z           := by
    simp only [add_left_inj]; rw [sub_add_self_of_le (one_le_of_zero_lt _ (pos_sub_iff_lt.mpr h))]


-- @@ L167-169 verbatim
lemma le_sub_one_of_lt {a b : V} (h : a < b) : a ≤ b - 1 := by
  have : 1 ≤ b := one_le_of_zero_lt _ (pos_of_gt h)
  simp [le_iff_lt_succ, sub_add_self_of_le this, h]


-- @@ L171-171 verbatim
end «lp_section_1»


-- @@ L173-173 verbatim
section «lp_section_2»


-- @@ L175-177 verbatim
lemma le_mul_self_of_pos_left (hy : 0 < b) : a ≤ b * a := by
  have : 1 * a ≤ b * a := mul_le_mul_of_nonneg_right (one_le_of_zero_lt b hy) (by simp)
  simpa using this


-- @@ L179-180 verbatim
lemma le_mul_self_of_pos_right (hy : 0 < b) : a ≤ a * b := by
  simpa [mul_comm a b] using le_mul_self_of_pos_left hy


-- @@ L182-187 verbatim
lemma dvd_iff_bounded {a b : V} : a ∣ b ↔ ∃ c ≤ b, b = a * c := by
  by_cases hx : a = 0
  · simp_all
  · constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, le_mul_self_of_pos_left (pos_iff_ne_zero.mpr hx), rfl⟩
    · rintro ⟨c, hz, rfl⟩; exact dvd_mul_right a c


-- @@ L189-191 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.dvd : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Semiformula.Operator.operator Operator.Eq.eq
        ![#2, Semiterm.Operator.Mul.mul.operator ![#1, #0]]))
    (by simp)


-- @@ L193-194 expanded
lemma dvd_defined : DefinedRel Sg0 (fun a b : V ↦ a ∣ b) dvd := fun v ↦ by
  simp [dvd_iff_bounded, dvd]


-- @@ L196-197 verbatim
@[simp] lemma dvd_defined_iff (v) :
    Semiformula.Evalbm V v dvd.val ↔ v 0 ∣ v 1 := dvd_defined.df.iff v


-- @@ L199-201 verbatim
instance dvd_definable (ℌ : HierarchySymbol) : ℌ.BoldfaceRel ((· ∣ ·) :
    V → V → Prop) :=
  dvd_defined.to_definable₀


-- @@ L203-203 verbatim
section «lp_section_3»


-- @@ L205-206 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∣ " firstOrderTerm:0 : firstOrderFormula


-- @@ L208-210 expanded
macro_rules
  |
  `(LO.FirstOrder.Rewriting.substitute dvd.val
        (vecCons foTerm[$binders* | $fbinders* | $t:firstOrderTerm]
          (vecCons foTerm[$binders* | $fbinders* | $u:firstOrderTerm] ![]))) =>
    `(LO.FirstOrder.Rewriting.substitute dvd.val
        (vecCons foTerm[$binders* | $fbinders* | $t]
          (vecCons foTerm[$binders* | $fbinders* | $u] ![])))


-- @@ L212-212 verbatim
end «lp_section_3»


-- @@ L214-214 verbatim
end «lp_section_2»


-- @@ L216-219 verbatim
lemma le_of_dvd (h : 0 < b) : a ∣ b → a ≤ b := by
  rintro ⟨c, rfl⟩
  exact le_mul_self_of_pos_right
    (pos_iff_ne_zero.mpr (show c ≠ 0 from by rintro rfl; simp at h))


-- @@ L221-222 verbatim
lemma not_dvd_of_lt (pos : 0 < b) : b < a → ¬a ∣ b := by
  intro hb h; exact not_le.mpr hb (le_of_dvd pos h)


-- @@ L224-230 verbatim
lemma dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  intro hx hy
  rcases show a = 0 ∨ 0 < a from eq_zero_or_pos a with (rfl | ltx)
  · simp [show b = 0 from by simpa using hx]
  · rcases show b = 0 ∨ 0 < b from eq_zero_or_pos b with (rfl | lty)
    · simp [show a = 0 from by simpa using hy]
    · exact le_antisymm (le_of_dvd lty hx) (le_of_dvd ltx hy)


-- @@ L232-233 verbatim
lemma dvd_one_iff : a ∣ 1 ↔ a = 1 :=
  ⟨by { intro hx; exact dvd_antisymm hx (by simp) }, by rintro rfl; simp⟩


-- @@ L235-235 verbatim
theorem units_eq_one (u : Vˣ) : u = 1 := Units.ext <| dvd_one_iff.mp ⟨u.inv, u.val_inv.symm⟩


-- @@ L237-238 verbatim
@[simp] lemma unit_iff_eq_one {a : V} : IsUnit a ↔ a = 1 :=
  ⟨by rintro ⟨u, rfl⟩; simp [units_eq_one u], by rintro rfl; simp⟩


-- @@ L240-240 verbatim
section «lp_section_4»


-- @@ L242-247 verbatim
lemma eq_one_or_eq_of_dvd_of_prime {p a : V} (pp : Prime p) (hxp : a ∣ p) : a = 1 ∨ a = p := by
  have : p ∣ a ∨ a ∣ 1 :=
    pp.left_dvd_or_dvd_right_of_dvd_mul (show a ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one_iff.mp hx


-- @@ L249-251 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def IsPrime (a : V) : Prop := 1 < a ∧ ∀ b ≤ a, b ∣ a → b = 1 ∨ b = a
-- TODO: prove IsPrime a ↔ Prime a


-- @@ L253-256 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.isPrime : Sg0.Semisentence 1 :=
  .mkSigma
    (Wedge.wedge (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 1, #0])
      (Semiformula.ballLTSucc (#0)
        (Arrow.arrow (LO.FirstOrder.Rewriting.substitute dvd.val (vecCons (#0) (vecCons #1 ![])))
          (Vee.vee (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 1])
            (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])))))
    (by simp [])


-- @@ L258-261 expanded
lemma isPrime_defined : DefinedPred Sg0 (fun a : V ↦ IsPrime a) isPrime :=
  by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, IsPrime,
    isPrime]


-- @@ L263-263 verbatim
end «lp_section_4»


-- @@ L265-265 verbatim
section «lp_section_5»


-- @@ L267-269 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.min : Sg0.Semisentence 3 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#1, #2])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]))
      (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#2, #1])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])))
    (by simp)


-- @@ L271-283 expanded
lemma min_defined : DefinedFunction₂ Sg0 (min : V → V → V) min :=
  by
  intro v
  suffices h : v 0 = min (v 1) (v 2) ↔ (v 1 ≤ v 2 → v 0 = v 1) ∧ (v 1 ≥ v 2 → v 0 = v 2) by
    simpa [FirstOrder.Arith.min] using h
  rcases le_total (v 1) (v 2) with h | h
  · simp only [Fin.isValue, h, inf_of_le_left, forall_const, ge_iff_le, iff_self_and]
    intro h₀₁ h₂₁
    exact le_antisymm (by simpa [h₀₁] using h) (by simpa [h₀₁] using h₂₁)
  · simp only [Fin.isValue, h, inf_of_le_right, forall_const, iff_and_self]
    intro h₀₂ h₁₂
    exact le_antisymm (by simpa [h₀₂] using h) (by simpa [h₀₂] using h₁₂)


-- @@ L285-286 verbatim
@[simp] lemma eval_minDef (v) :
    Semiformula.Evalbm V v min.val ↔ v 0 = min (v 1) (v 2) := min_defined.df.iff v


-- @@ L288-290 expanded
instance min_definable (ℌ) : BoldfaceFunction₂ ℌ (min : V → V → V) :=
  HierarchySymbol.Defined.to_definable₀ min_defined


-- @@ L292-292 verbatim
instance min_polybounded : Bounded₂ (min : V → V → V) := ⟨#0, fun _ ↦ by simp⟩


-- @@ L294-294 verbatim
end «lp_section_5»


-- @@ L296-296 verbatim
section «lp_section_6»


-- @@ L298-300 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.max : Sg0.Semisentence 3 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#2, #1])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]))
      (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#1, #2])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])))
    (by simp)


-- @@ L302-314 expanded
lemma max_defined : DefinedFunction₂ Sg0 (max : V → V → V) max :=
  by
  intro v
  suffices h : v 0 = max (v 1) (v 2) ↔ (v 1 ≥ v 2 → v 0 = v 1) ∧ (v 1 ≤ v 2 → v 0 = v 2) by
    simpa [Arith.max] using h
  rcases le_total (v 1) (v 2) with h | h
  · simp only [Fin.isValue, h, sup_of_le_right, ge_iff_le, forall_const, iff_and_self]
    intro h₀₂ h₂₁
    exact le_antisymm (by simpa [h₀₂] using h₂₁) (by simpa [h₀₂] using h)
  · simp only [Fin.isValue, h, sup_of_le_left, forall_const, iff_self_and]
    intro h₀₁ h₁₂
    exact le_antisymm (by simpa [h₀₁] using h₁₂) (by simpa [h₀₁] using h)


-- @@ L316-317 verbatim
@[simp] lemma eval_maxDef (v) :
    Semiformula.Evalbm V v max.val ↔ v 0 = max (v 1) (v 2) := max_defined.df.iff v


-- @@ L319-321 expanded
instance max_definable (Γ) : BoldfaceFunction₂ Γ (max : V → V → V) :=
  HierarchySymbol.Defined.to_definable₀ max_defined


-- @@ L323-323 expanded
instance max_polybounded : Bounded₂ (max : V → V → V) :=
  ⟨Semiterm.Operator.Add.add.operator ![#0, #1], fun v ↦ by simp⟩


-- @@ L325-325 verbatim
end «lp_section_6»


-- @@ L327-327 verbatim
end «lp_nc_section_1»


-- @@ L329-329 verbatim
end Arith

-- @@ L330-330 verbatim
end LO
