/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Ring.Defs
import LeanPool.Duality.Common
import Mathlib.Algebra.Order.Field.Basic


-- @@ L14-17 verbatim
/-!
This entire file is inspired by:
https://github.com/leanprover-community/mathlib4/blob/333e2d79fdaee86489af73dee919bc4b66957a52/Mathlib/Data/Real/EReal.lean
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-23 verbatim
/-- `Extend F` is the type of values in `F ∪ {⊥, ⊤}` where, informally speaking,
    `⊥` (negative infinity) is stronger than `⊤` (positive infinity). -/
def Extend (F : Type*) := WithBot (WithTop F)



-- @@ L26-26 verbatim
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]


-- @@ L28-29 verbatim
instance : AddCommMonoid (Extend F) :=
  inferInstanceAs (AddCommMonoid (WithBot (WithTop F)))


-- @@ L31-32 verbatim
instance : LinearOrder (Extend F) :=
  inferInstanceAs (LinearOrder (WithBot (WithTop F)))


-- @@ L34-35 verbatim
instance : IsOrderedAddMonoid (Extend F) :=
  inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop F)))


-- @@ L37-38 verbatim
instance : AddCommMonoidWithOne (Extend F) :=
  inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop F)))



-- @@ L41-41 verbatim
instance : ZeroLEOneClass (Extend F) := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop F)))


-- @@ L43-43 verbatim
instance : CharZero (Extend F) := inferInstanceAs (CharZero (WithBot (WithTop F)))


-- @@ L45-45 verbatim
instance : BoundedOrder (Extend F) := inferInstanceAs (BoundedOrder (WithBot (WithTop F)))


-- @@ L47-47 verbatim
instance : DenselyOrdered (Extend F) := inferInstanceAs (DenselyOrdered (WithBot (WithTop F)))


-- @@ L49-49 verbatim
instance : DecidableRel ((· < ·) : Extend F → Extend F → Prop) := WithBot.decidableLT



-- @@ L52-53 verbatim
/-- The canonical inclusion from `F` to `Extend F` is registered as a coercion. -/
@[coe] def toE : F → Extend F := some ∘ some


-- @@ L55-55 verbatim
instance : Coe F (Extend F) := ⟨toE⟩



-- @@ L58-58 verbatim
namespace EF


-- @@ L60-60 verbatim
/-! ### Coercion -/


-- @@ L62-64 verbatim
omit [Field F] [IsStrictOrderedRing F] in
lemma coe_strictMono : StrictMono (toE (F := F)) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono


-- @@ L66-68 verbatim
omit [Field F] [IsStrictOrderedRing F] in
lemma coe_injective : Function.Injective (toE (F := F)) :=
  coe_strictMono.injective


-- @@ L70-73 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_le_coe_iff {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y :=
  coe_strictMono.le_iff_le


-- @@ L75-76 verbatim
lemma coe_le_coe_iff_F (F : Type) [LinearOrder F]
    {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y := coe_strictMono.le_iff_le


-- @@ L78-81 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_lt_coe_iff {x y : F} : (x : Extend F) < (y : Extend F) ↔ x < y :=
  coe_strictMono.lt_iff_lt


-- @@ L83-86 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_eq_coe_iff {x y : F} : (x : Extend F) = (y : Extend F) ↔ x = y :=
  coe_injective.eq_iff


-- @@ L88-90 verbatim
omit [Field F] [IsStrictOrderedRing F] in
lemma coe_neq_coe_iff {x y : F} : (x : Extend F) ≠ (y : Extend F) ↔ x ≠ y :=
  coe_injective.ne_iff


-- @@ L92-94 verbatim
omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_zero : ((0 : F) : Extend F) = 0 := rfl


-- @@ L96-98 verbatim
omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_one : ((1 : F) : Extend F) = 1 := rfl


-- @@ L100-103 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp]
lemma bot_lt_coe (x : F) : (⊥ : Extend F) < x :=
  WithBot.bot_lt_coe _


-- @@ L105-108 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp]
lemma coe_neq_bot (x : F) : (x : Extend F) ≠ ⊥ :=
  (bot_lt_coe x).ne'


-- @@ L110-113 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp]
lemma bot_neq_coe (x : F) : (⊥ : Extend F) ≠ x :=
  (bot_lt_coe x).ne


-- @@ L115-118 expanded
omit [Field F] [IsStrictOrderedRing F] in
@[simp]
lemma coe_lt_top (x : F) : (x : Extend F) < ⊤ :=
  Iff.mpr WithBot.coe_lt_coe <| WithTop.coe_lt_top _


-- @@ L120-123 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp]
lemma coe_neq_top (x : F) : (x : Extend F) ≠ ⊤ :=
  (coe_lt_top x).ne


-- @@ L125-128 verbatim
omit [Field F] [IsStrictOrderedRing F] in
@[simp]
lemma top_neq_coe (x : F) : (⊤ : Extend F) ≠ x :=
  (coe_lt_top x).ne'


-- @@ L130-133 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma bot_lt_zero : (⊥ : Extend F) < 0 :=
  bot_lt_coe 0


-- @@ L135-138 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma bot_neq_zero : (⊥ : Extend F) ≠ 0 :=
  (coe_neq_bot 0).symm


-- @@ L140-143 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma zero_neq_bot : (0 : Extend F) ≠ ⊥ :=
  coe_neq_bot 0


-- @@ L145-148 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma zero_lt_top : (0 : Extend F) < ⊤ :=
  coe_lt_top 0


-- @@ L150-153 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma zero_neq_top : (0 : Extend F) ≠ ⊤ :=
  coe_neq_top 0


-- @@ L155-158 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma top_neq_zero : (⊤ : Extend F) ≠ 0 :=
  zero_neq_top.symm


-- @@ L160-163 verbatim
omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_add (x y : F) : toE (x + y) = toE x + toE y :=
  rfl


-- @@ L165-168 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_eq_zero {x : F} : (x : Extend F) = 0 ↔ x = 0 :=
  coe_eq_coe_iff


-- @@ L170-173 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_eq_one {x : F} : (x : Extend F) = 1 ↔ x = 1 :=
  coe_eq_coe_iff


-- @@ L175-177 verbatim
omit [IsStrictOrderedRing F] in
lemma coe_neq_zero {x : F} : (x : Extend F) ≠ 0 ↔ x ≠ 0 :=
  coe_neq_coe_iff


-- @@ L179-181 verbatim
omit [IsStrictOrderedRing F] in
lemma coe_neq_one {x : F} : (x : Extend F) ≠ 1 ↔ x ≠ 1 :=
  coe_neq_coe_iff


-- @@ L183-186 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_nonneg {x : F} : (0 : Extend F) ≤ x ↔ 0 ≤ x :=
  coe_le_coe_iff


-- @@ L188-191 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_nonpos {x : F} : x ≤ (0 : Extend F) ↔ x ≤ 0 :=
  coe_le_coe_iff


-- @@ L193-196 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_pos {x : F} : (0 : Extend F) < x ↔ 0 < x :=
  coe_lt_coe_iff


-- @@ L198-201 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_neg' {x : F} : x < (0 : Extend F) ↔ x < 0 :=
  coe_lt_coe_iff


-- @@ L203-203 verbatim
/-! ### Addition -/


-- @@ L205-208 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma add_bot (x : Extend F) : x + ⊥ = ⊥ :=
  WithBot.add_bot x


-- @@ L210-213 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma bot_add (x : Extend F) : ⊥ + x = ⊥ :=
  WithBot.bot_add x


-- @@ L215-218 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma add_eq_bot_iff {x y : Extend F} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot


-- @@ L220-223 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma top_add_top : (⊤ : Extend F) + ⊤ = ⊤ :=
  rfl


-- @@ L225-228 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma top_add_coe (x : F) : (⊤ : Extend F) + x = ⊤ :=
  rfl


-- @@ L230-233 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma coe_add_top (x : F) : (x : Extend F) + ⊤ = ⊤ :=
  rfl


-- @@ L235-235 verbatim
/-! ### Negation -/


-- @@ L237-241 verbatim
/-- Negation on `Extend F`. -/
def neg : Extend F → Extend F
| ⊥ => ⊤
| ⊤ => ⊥
| (x : F) => toE (-x)


-- @@ L243-243 verbatim
instance : Neg (Extend F) := ⟨EF.neg⟩


-- @@ L245-247 verbatim
instance : SubNegZeroMonoid (Extend F) where
  neg_zero := congr_arg toE neg_zero
  zsmul := zsmulRec


-- @@ L249-252 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma neg_top : -(⊤ : Extend F) = ⊥ :=
  rfl


-- @@ L254-257 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma neg_bot : -(⊥ : Extend F) = ⊤ :=
  rfl


-- @@ L259-261 verbatim
omit [IsStrictOrderedRing F] in
@[simp, norm_cast]
lemma coe_neg (x : F) : toE (-x) = -(toE x) := rfl


-- @@ L263-268 verbatim
instance : InvolutiveNeg (Extend F) where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : F) => congr_arg toE (neg_neg a)


-- @@ L270-273 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma neg_eq_top_iff {x : Extend F} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl


-- @@ L275-278 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma neg_eq_bot_iff {x : Extend F} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl


-- @@ L280-283 verbatim
omit [IsStrictOrderedRing F] in
@[simp]
lemma neg_eq_zero_iff {x : Extend F} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero


-- @@ L285-285 verbatim
end EF
