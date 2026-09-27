/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.CobhamR0
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L12-12 verbatim
/-! # PeanoMinus -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L19-19 verbatim
namespace LO


-- @@ L21-21 verbatim
namespace Arith


-- @@ L23-23 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L25-25 verbatim
variable {M : Type*} [ORingStruc M]


-- @@ L27-27 verbatim
open Language


-- @@ L29-30 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instLEofPeanoMinus : LE M := ⟨fun x y => x = y ∨ x < y⟩


-- @@ L32-32 verbatim
lemma le_def {x y : M} : x ≤ y ↔ x = y ∨ x < y := iff_of_eq rfl


-- @@ L34-34 expanded
variable [ModelsTheory M PeanoMinus]


-- @@ L36-37 verbatim
protected lemma add_zero (x : M) : x + 0 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.addZero (fun _ ↦ x)


-- @@ L39-40 expanded
protected lemma add_assoc (x y z : M) : (x + y) + z = x + (y + z) := by
  simpa [models_iff] using
    ModelsTheory.models M Theory.PeanoMinus.addAssoc (cases x (cases y fun _ ↦ z))


-- @@ L42-43 expanded
protected lemma add_comm (x y : M) : x + y = y + x := by
  simpa [models_iff] using ModelsTheory.models M Theory.PeanoMinus.addComm (cases x fun _ ↦ y)


-- @@ L45-46 expanded
lemma add_eq_of_lt (x y : M) : x < y → ∃ z, x + z = y := by
  simpa [models_iff] using ModelsTheory.models M Theory.PeanoMinus.addEqOfLt (cases x fun _ ↦ y)


-- @@ L48-51 verbatim
@[simp] lemma zero_le (x : M) : 0 ≤ x := by
  rw [le_def]
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M
    Theory.PeanoMinus.zeroLe (fun _ ↦ x)


-- @@ L53-54 verbatim
lemma zero_lt_one : (0 : M) < 1 := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.zeroLtOne


-- @@ L56-59 verbatim
lemma one_le_of_zero_lt (x : M) : 0 < x → 1 ≤ x := by
  rw [le_def]
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M
    Theory.PeanoMinus.oneLeOfZeroLt (fun _ ↦ x)


-- @@ L61-62 expanded
lemma add_lt_add (x y z : M) : x < y → x + z < y + z := by
  simpa [models_iff] using
    ModelsTheory.models M Theory.PeanoMinus.addLtAdd (cases x (cases y fun _ ↦ z))


-- @@ L64-65 verbatim
protected lemma mul_zero (x : M) : x * 0 = 0 := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulZero (fun _ ↦ x)


-- @@ L67-68 verbatim
protected lemma mul_one (x : M) : x * 1 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulOne (fun _ ↦ x)


-- @@ L70-71 expanded
protected lemma mul_assoc (x y z : M) : (x * y) * z = x * (y * z) := by
  simpa [models_iff] using
    ModelsTheory.models M Theory.PeanoMinus.mulAssoc (cases x (cases y fun _ ↦ z))


-- @@ L73-74 expanded
protected lemma mul_comm (x y : M) : x * y = y * x := by
  simpa [models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulComm (cases x fun _ ↦ y)


-- @@ L76-77 expanded
lemma mul_lt_mul (x y z : M) : x < y → 0 < z → x * z < y * z := by
  simpa [models_iff] using
    ModelsTheory.models M Theory.PeanoMinus.mulLtMul (cases x (cases y fun _ ↦ z))


-- @@ L79-80 expanded
lemma distr (x y z : M) : x * (y + z) = x * y + x * z := by
  simpa [models_iff] using
    ModelsTheory.models M Theory.PeanoMinus.distr (cases x (cases y fun _ ↦ z))


-- @@ L82-83 verbatim
lemma lt_irrefl (x : M) : ¬x < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.ltIrrefl (fun _ ↦ x)


-- @@ L85-86 expanded
protected lemma lt_trans (x y z : M) : x < y → y < z → x < z := by
  simpa [models_iff] using
    ModelsTheory.models M Theory.PeanoMinus.ltTrans (cases x (cases y fun _ ↦ z))


-- @@ L88-89 expanded
lemma lt_tri (x y : M) : x < y ∨ x = y ∨ y < x := by
  simpa [models_iff] using ModelsTheory.models M Theory.PeanoMinus.ltTri (cases x fun _ ↦ y)


-- @@ L91-97 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instAddCommMonoidOfPeanoMinus : AddCommMonoid M where
  add_assoc := Arith.add_assoc
  zero_add  := fun x => Arith.add_comm x 0 ▸ Arith.add_zero x
  add_zero  := Arith.add_zero
  add_comm  := Arith.add_comm
  nsmul := nsmulRec


-- @@ L99-104 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instCommMonoidOfPeanoMinus : CommMonoid M where
  mul_assoc := Arith.mul_assoc
  one_mul   := fun x => Arith.mul_comm x 1 ▸ Arith.mul_one x
  mul_one   := Arith.mul_one
  mul_comm  := Arith.mul_comm


-- @@ L106-134 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instLinearOrderOfPeanoMinus : LinearOrder M where
  le_refl := fun x => Or.inl (by simp)
  le_trans := by
    rintro x y z (rfl | hx) (rfl | hy)
    · exact Or.inl rfl
    · exact Or.inr hy
    · exact Or.inr hx
    · exact Or.inr (Arith.lt_trans _ _ _ hx hy)
  le_antisymm := by
    rintro x y (rfl | hx) hyx
    · rfl
    · rcases hyx with (rfl | hy)
      · rfl
      · exact False.elim <| Arith.lt_irrefl _ (Arith.lt_trans _ _ _ hx hy)
  le_total := by
    intro x y
    rcases Arith.lt_tri x y with (h | rfl | h) <;> simp[*, le_def]
  lt_iff_le_not_ge := fun x y =>
    ⟨fun h => ⟨Or.inr h, by
      simp only [le_def]
      rintro (rfl | h')
      · exact lt_irrefl y h
      · exact lt_irrefl _ (Arith.lt_trans _ _ _ h h')⟩,
     by
      rintro ⟨(rfl | h), hyx⟩
      · exact False.elim (hyx (Or.inl rfl))
      · exact h ⟩
  toDecidableLE := fun _ _ => Classical.dec _


-- @@ L136-136 verbatim
protected lemma zero_mul : ∀ x : M, 0 * x = 0 := fun x => by simpa[mul_comm] using Arith.mul_zero x


-- @@ L138-154 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instCommSemiringOfPeanoMinus : CommSemiring M where
  add_assoc := Arith.add_assoc
  zero_add  := fun x => Arith.add_comm x 0 ▸ Arith.add_zero x
  add_zero  := Arith.add_zero
  add_comm  := Arith.add_comm
  nsmul := nsmulRec
  left_distrib := distr
  right_distrib := fun x y z => by
    rw [mul_comm (x + y) z, mul_comm x z, mul_comm y z]
    exact distr z x y
  zero_mul := Arith.zero_mul
  mul_zero := Arith.mul_zero
  mul_assoc := Arith.mul_assoc
  mul_comm := mul_comm
  one_mul   := fun x => Arith.mul_comm x 1 ▸ Arith.mul_one x
  mul_one   := Arith.mul_one


-- @@ L156-167 verbatim
scoped instance : IsOrderedCancelAddMonoid M where
  add_le_add_left := by
    rintro x y (rfl | h) z
    · exact Or.inl rfl
    · exact Or.inr (by simpa [add_comm z] using add_lt_add x y z h)
  le_of_add_le_add_left := by
    rintro x y z h
    have : y ≤ z ∨ z < y := le_or_gt y z
    rcases this with (hyz | hyz)
    · exact hyz
    · have : x + z < x + y := by simpa[add_comm] using add_lt_add z y x hyz
      exact False.elim (lt_iff_not_ge.mp this h)


-- @@ L169-170 verbatim
scoped instance : ZeroLEOneClass M where
  zero_le_one := Or.inr zero_lt_one


-- @@ L172-173 verbatim
scoped instance : Nontrivial M where
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩


-- @@ L175-178 verbatim
scoped instance : PosMulStrictMono M where
  mul_lt_mul_of_pos_left := by
    intro z hz x y h
    simpa[mul_comm z] using mul_lt_mul x y z h hz


-- @@ L180-183 verbatim
scoped instance : MulPosStrictMono M where
  mul_lt_mul_of_pos_right := by
    intro z hz x y h
    exact mul_lt_mul x y z h hz


-- @@ L185-185 verbatim
scoped instance : IsStrictOrderedRing M where


-- @@ L187-195 verbatim
scoped instance : CanonicallyOrderedAdd M where
  exists_add_of_le := by
    rintro x y (rfl | h)
    · exact ⟨0, by simp⟩
    · simpa[eq_comm] using add_eq_of_lt x y h
  le_add_self := by
    simp_all
  le_self_add := by
    simp_all


-- @@ L197-200 verbatim
lemma numeral_eq_natCast : (n : ℕ) → (ORingStruc.numeral n : M) = n
  | 0     => rfl
  | 1     => by simp
  | n + 2 => by simp[ORingStruc.numeral, numeral_eq_natCast (n + 1), add_assoc, one_add_one_eq_two]


-- @@ L202-202 verbatim
lemma not_neg (x : M) : ¬x < 0 := by simp


-- @@ L204-206 verbatim
lemma eq_succ_of_pos {x : M} (h : 0 < x) : ∃ y, x = y + 1 := by
  rcases le_iff_exists_add.mp (one_le_of_zero_lt x h) with ⟨y, rfl⟩
  exact ⟨y, add_comm 1 y⟩


-- @@ L208-214 verbatim
lemma le_iff_lt_succ {x y : M} : x ≤ y ↔ x < y + 1 :=
  ⟨by intro h; exact lt_of_le_of_lt h (lt_add_one y),
   fun h => by
    rcases lt_iff_exists_add.mp h with ⟨z, hz, h⟩
    rcases eq_succ_of_pos hz with ⟨z', rfl⟩
    have : y = x + z' := by simpa[←add_assoc] using h
    simp[this]⟩


-- @@ L216-222 verbatim
lemma eq_nat_of_lt_nat : ∀ {n : ℕ} {x : M}, x < n → ∃ m : ℕ, x = m
  | 0,     x, hx => by simp[] at hx
  | n + 1, x, hx => by
    have : x ≤ n := by simpa[le_iff_lt_succ] using hx
    rcases this with (rfl | hx)
    · exact ⟨n, rfl⟩
    · exact eq_nat_of_lt_nat hx


-- @@ L224-242 expanded
instance qq : ModelsTheory M CobhamR0 :=
  modelsTheory_iff.mpr <| by
    intro φ h
    rcases h
    case equal h =>
      have : ModelsTheory M (eqAxiom : Theory oRing) := inferInstance
      exact modelsTheory_iff.mp this h
    case Ω₁ n m => simp [models_iff, numeral_eq_natCast]
    case Ω₂ n m => simp [models_iff, numeral_eq_natCast]
    case Ω₃ n m h => simp [models_iff, numeral_eq_natCast, h]
    case Ω₄
      n =>
      simp only [Nat.reduceAdd, Fin.isValue, models_iff, Semiformula.eval_all, Nat.succ_eq_add_one,
        LogicalConnective.HomClass.map_iff, Semiformula.eval_operator₂, Semiterm.val_bvar,
        Matrix.vecCons_zero, Semiterm.val_const, Structure.numeral_eq_numeral, numeral_eq_natCast,
        Structure.LT.lt, hom_disj_prop, Structure.Eq.eq, LogicalConnective.Prop.iff_eq,
        forall_const]
      intro x
      constructor
      · intro hx; rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩; exact ⟨x, by simpa using hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩; simp [hi]


-- @@ L244-244 verbatim
end Arith


-- @@ L246-246 verbatim
namespace FirstOrder

-- @@ L247-247 verbatim
namespace Arith


-- @@ L249-249 verbatim
open LO.Arith


-- @@ L251-251 expanded
variable {T : Theory oRing} [WeakerThan PeanoMinus T]


-- @@ L253-253 expanded
instance : WeakerThan CobhamR0 PeanoMinus :=
  oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance


-- @@ L255-258 expanded
instance : StrictlyWeakerThan CobhamR0 PeanoMinus :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable R₀_unprovable_add_zero
    (Entailment.by_axm _ Theory.PeanoMinus.addZero)


-- @@ L260-260 verbatim
end Arith

-- @@ L261-261 verbatim
end FirstOrder


-- @@ L263-263 verbatim
end LO


-- @@ L265-265 verbatim
end «lp_nc_section_1»
