/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Tactic.NormNum.Basic


-- @@ L12-14 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L16-16 verbatim
namespace MisereGames


-- @@ L18-42 verbatim
/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a + b` is recursively defined as the least ordinal greater than `a' + b` and `a + b'` for `a' < a`
and `b' < b`. The natural multiplication `a * b` is likewise recursively defined as the least
ordinal such that `a * b + a' * b'` is greater than `a' * b + a * b'` for any `a' < a` and
`b' < b`.

These operations give the ordinals a `CommSemiring` + `IsStrictOrderedRing` structure. To make the
best use of it, we define them on a type alias `NatOrdinal`.

An equivalent characterization explains the relevance of these operations to game theory: they are
the restrictions of surreal addition and multiplication to the ordinals.

## Implementation notes

To reduce API duplication, we opt not to implement operations on `NatOrdinal` on `Ordinal`. The
order isomorphisms `NatOrdinal.of` and `NatOrdinal.val` allow us to cast between them whenever
needed.

For similar reasons, most results about ordinals and games are written using `NatOrdinal` rather
than `Ordinal` (except when `Nimber` would make more sense).
-/


-- @@ L44-44 verbatim
universe u v


-- @@ L46-46 verbatim
open Order Set Lean


-- @@ L48-48 verbatim
@[expose] public noncomputable section


-- @@ L50-52 verbatim
/-- Ordinals equipped with natural arithmetic. -/
def NatOrdinal : Type _ :=
  Ordinal deriving Nontrivial, Inhabited


-- @@ L54-54 verbatim
namespace NatOrdinal


-- @@ L56-76 verbatim
instance : PartialOrder NatOrdinal where
  le a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (InitialSeg r s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
        ⟨fun ⟨h⟩ => ⟨f.symm.toInitialSeg.trans <| h.trans g.toInitialSeg⟩, fun ⟨h⟩ =>
          ⟨f.toInitialSeg.trans <| h.trans g.symm.toInitialSeg⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (PrincipalSeg r s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
        ⟨fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f.symm <| h.transRelIso g⟩,
          fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f <| h.transRelIso g.symm⟩⟩
  le_refl := Quot.ind fun ⟨_, _, _⟩ => ⟨InitialSeg.refl _⟩
  le_trans a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  lt_iff_le_not_ge a b :=
    Quotient.inductionOn₂ a b fun _ _ =>
      ⟨fun ⟨f⟩ => ⟨⟨f⟩, fun ⟨g⟩ => (f.transInitial g).irrefl⟩, fun ⟨⟨f⟩, h⟩ =>
        f.principalSumRelIso.recOn (fun g => ⟨g⟩) fun g => (h ⟨g.symm.toInitialSeg⟩).elim⟩
  le_antisymm a b :=
    Quotient.inductionOn₂ a b fun _ _ ⟨h₁⟩ ⟨h₂⟩ =>
      Quot.sound ⟨InitialSeg.antisymm h₁ h₂⟩


-- @@ L78-80 verbatim
/-- The natural ordinal represented by a well-order. -/
def type {α : Type u} (r : α → α → Prop) [wo : IsWellOrder α r] : NatOrdinal :=
  ⟦⟨α, r, wo⟩⟧


-- @@ L82-84 verbatim
theorem _root_.PrincipalSeg.nat_ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : PrincipalSeg r s) : type r < type s :=
  ⟨h⟩


-- @@ L86-89 verbatim
@[elab_as_elim]
theorem inductionOn {C : NatOrdinal → Prop} (o : NatOrdinal)
    (H : ∀ (α r) [IsWellOrder α r], C (type r)) : C o :=
  Quot.inductionOn o fun ⟨α, r, wo⟩ => @H α r wo


-- @@ L91-104 verbatim
/-- The initial segment of `NatOrdinal` below the order type of `r`. -/
def typein {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    @PrincipalSeg α NatOrdinal.{u} r (· < ·) := by
  refine ⟨RelEmbedding.ofMonotone _ fun a b ha ↦
    ((PrincipalSeg.ofElement r a).codRestrict _ ?_ ?_).nat_ordinal_type_lt, type r, fun a ↦ ⟨?_,
      ?_⟩⟩
  · rintro ⟨c, hc⟩
    exact trans hc ha
  · exact ha
  · rintro ⟨b, rfl⟩
    exact (PrincipalSeg.ofElement _ _).nat_ordinal_type_lt
  · refine inductionOn a ?_
    rintro β s wo ⟨g⟩
    exact ⟨_, g.subrelIso.ordinalType_congr⟩


-- @@ L106-110 verbatim
/-- Enumerate the ordinals below a given order type by the original well-order. -/
@[simps! symm_apply_coe]
def enum {α : Type u} (r : α → α → Prop) [IsWellOrder α r] : (· < · :
    Iio (type r) → Iio (type r) → Prop) ≃r r :=
  (typein r).subrelIso


-- @@ L112-114 verbatim
theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ ↦
    RelHomClass.wellFounded (enum _) wo.wf)


-- @@ L116-116 verbatim
instance : WellFoundedLT NatOrdinal := lt_wf


-- @@ L118-119 verbatim
instance wellFoundedRelation : WellFoundedRelation NatOrdinal :=
  ⟨(· < ·), lt_wf⟩


-- @@ L121-122 verbatim
instance zero : Zero NatOrdinal :=
  ⟨type <| @emptyRelation PEmpty⟩


-- @@ L124-125 verbatim
instance one : One NatOrdinal :=
  ⟨type <| @emptyRelation PUnit⟩


-- @@ L127-129 verbatim
instance : OrderBot NatOrdinal where
  bot := 0
  bot_le o := inductionOn o fun _ r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le


-- @@ L131-131 verbatim
instance : NoMaxOrder NatOrdinal := inferInstanceAs (NoMaxOrder Ordinal)

-- @@ L132-132 verbatim
instance : ZeroLEOneClass NatOrdinal := inferInstanceAs (ZeroLEOneClass Ordinal)


-- @@ L134-136 verbatim
theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'


-- @@ L138-141 verbatim
theorem _root_.RelIso.nat_ordinal_type_eq {α β} {r : α → α → Prop} {s :
    β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩


-- @@ L143-144 verbatim
theorem type_eq_zero_of_empty {α} (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinalType_congr


-- @@ L146-152 verbatim
@[simp]
theorem type_eq_zero_iff_isEmpty {α : Type u} {r : α → α → Prop} [IsWellOrder α r] :
    type r = 0 ↔ IsEmpty α :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero_of_empty α r _⟩


-- @@ L154-156 verbatim
theorem type_ne_zero_iff_nonempty {α : Type u} {r : α → α → Prop} [IsWellOrder α r] :
    type r ≠ 0 ↔ Nonempty α := by
  simp [ne_eq, type_eq_zero_iff_isEmpty, not_isEmpty_iff]


-- @@ L158-159 verbatim
theorem type_ne_zero_of_nonempty {α : Type u} (r) [IsWellOrder α r] [h : Nonempty α] : type r ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h


-- @@ L161-161 verbatim
instance : NeZero (1 : NatOrdinal) := inferInstanceAs (NeZero (1 : Ordinal))


-- @@ L163-165 verbatim
/-- The order isomorphism from ordinals to `NatOrdinal`. -/
@[match_pattern]
def of : Ordinal ≃o NatOrdinal := .refl _


-- @@ L167-169 verbatim
/-- The order isomorphism from `NatOrdinal` to ordinals. -/
@[match_pattern]
def val : NatOrdinal ≃o Ordinal := .refl _


-- @@ L171-171 verbatim
@[simp] theorem of_symm : .symm of = val := rfl

-- @@ L172-172 verbatim
@[simp] theorem val_symm : .symm val = of := rfl


-- @@ L174-174 verbatim
@[simp] theorem of_val (a) : of (val a) = a := rfl

-- @@ L175-175 verbatim
@[simp] theorem val_of (a) : val (of a) = a := rfl


-- @@ L177-177 verbatim
theorem val_le_iff {a b} : val a ≤ b ↔ a ≤ of b := .rfl

-- @@ L178-178 verbatim
theorem val_lt_iff {a b} : val a < b ↔ a < of b := .rfl

-- @@ L179-179 verbatim
theorem val_eq_iff {a b} : val a = b ↔ a = of b := .rfl


-- @@ L181-181 verbatim
theorem of_le_iff {a b} : of a ≤ b ↔ a ≤ val b := .rfl

-- @@ L182-182 verbatim
theorem of_lt_iff {a b} : of a < b ↔ a < val b := .rfl

-- @@ L183-183 verbatim
theorem of_eq_iff {a b} : of a = b ↔ a = val b := .rfl


-- @@ L185-186 verbatim
theorem of_image_Iio (a) : of '' Set.Iio a = Set.Iio (of a) :=
  Set.image_id _


-- @@ L188-189 verbatim
theorem val_image_Iio (a) : val '' Set.Iio a = Set.Iio (val a) :=
  Set.image_id _


-- @@ L191-191 verbatim
@[simp] theorem bot_eq_zero : (⊥ : NatOrdinal) = 0 := rfl


-- @@ L193-193 verbatim
@[simp] theorem of_zero : of 0 = 0 := rfl

-- @@ L194-194 verbatim
@[simp] theorem val_zero : val 0 = 0 := rfl


-- @@ L196-196 verbatim
@[simp] theorem of_one : of 1 = 1 := rfl

-- @@ L197-197 verbatim
@[simp] theorem val_one : val 1 = 1 := rfl


-- @@ L199-199 verbatim
@[simp] theorem of_eq_zero {a} : of a = 0 ↔ a = 0 := .rfl

-- @@ L200-200 verbatim
@[simp] theorem val_eq_zero {a} : val a = 0 ↔ a = 0 := .rfl


-- @@ L202-202 verbatim
@[simp] theorem of_eq_one {a} : of a = 1 ↔ a = 1 := .rfl

-- @@ L203-203 verbatim
@[simp] theorem val_eq_one {a} : val a = 1 ↔ a = 1 := .rfl


-- @@ L205-205 verbatim
instance : SuccOrder NatOrdinal := inferInstanceAs (SuccOrder Ordinal)


-- @@ L207-208 verbatim
theorem succ_def (a : NatOrdinal) : Order.succ a = of (val a + 1) :=
  rfl


-- @@ L210-212 verbatim
@[simp]
theorem succ_of (a : Ordinal) : Order.succ (of a) = of (a + 1) :=
  rfl


-- @@ L214-214 verbatim
theorem succ_ne_zero (a : NatOrdinal) : Order.succ a ≠ 0 := Order.succ_ne_bot a

-- @@ L215-217 verbatim
theorem succ_zero : Order.succ (0 : NatOrdinal) = 1 := by
  change Order.succ (0 : Ordinal) = 1
  simp


-- @@ L219-223 verbatim
/-- Recursor through the underlying ordinal representation. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def ind {motive : NatOrdinal → Sort*}
    (mk : ∀ a, motive (of a)) (a) : motive a :=
  mk (val a)


-- @@ L225-226 verbatim
theorem induction {p : NatOrdinal → Prop} : ∀ i (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  WellFoundedLT.induction


-- @@ L228-228 verbatim
@[simp] theorem zero_le (a : NatOrdinal) : 0 ≤ a := bot_le

-- @@ L229-229 verbatim
@[simp] theorem le_zero {a : NatOrdinal} : a ≤ 0 ↔ a = 0 := le_bot_iff

-- @@ L230-230 verbatim
@[simp] theorem not_lt_zero (a : NatOrdinal) : ¬ a < 0 := not_lt_bot

-- @@ L231-231 verbatim
theorem pos_iff_ne_zero {a : NatOrdinal} : 0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot

-- @@ L232-232 verbatim
theorem eq_zero_or_pos (a : NatOrdinal) : a = 0 ∨ 0 < a := eq_bot_or_bot_lt a


-- @@ L234-238 verbatim
noncomputable instance : LinearOrder NatOrdinal where
  __ := (inferInstance : PartialOrder NatOrdinal)
  le_total := fun a b => Quotient.inductionOn₂ a b fun ⟨_, r, _⟩ ⟨_, s, _⟩ =>
      (InitialSeg.total r s).recOn (fun f => Or.inl ⟨f⟩) fun f => Or.inr ⟨f⟩
  toDecidableLE := Classical.decRel _


-- @@ L240-241 verbatim
noncomputable instance : ConditionallyCompleteLinearOrderBot NatOrdinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _


-- @@ L243-243 verbatim
instance : Uncountable NatOrdinal := Ordinal.uncountable


-- @@ L245-246 verbatim
@[simp] theorem lt_one_iff_zero {a : NatOrdinal} : a < 1 ↔ a = 0 :=
  (show val a < (1 : Ordinal) ↔ val a = 0 from Order.lt_one_iff)

-- @@ L247-248 verbatim
@[simp] theorem one_le_iff_ne_zero {a : NatOrdinal} : 1 ≤ a ↔ a ≠ 0 :=
  (show (1 : Ordinal) ≤ val a ↔ val a ≠ 0 from Order.one_le_iff_ne_zero)

-- @@ L249-252 verbatim
theorem le_one_iff {a : NatOrdinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 :=
  (show val a ≤ (1 : Ordinal) ↔ val a = 0 ∨ val a = 1 from Order.le_one_iff)

-- TODO: upstream to Mathlib for Ordinal

-- @@ L253-255 verbatim
theorem eq_natCast_of_le_natCast {a : NatOrdinal} {b : ℕ} (h : a ≤ of b) :
    ∃ c : ℕ, a = of c :=
  Ordinal.lt_omega0.1 (h.trans_lt (Ordinal.natCast_lt_omega0 b))


-- @@ L257-257 verbatim
instance (a : NatOrdinal.{u}) : Small.{u} (Set.Iio a) := Ordinal.small_Iio a

-- @@ L258-258 verbatim
instance (a : NatOrdinal.{u}) : Small.{u} (Set.Iic a) := Ordinal.small_Iic a

-- @@ L259-259 verbatim
instance (a b : NatOrdinal.{u}) : Small.{u} (Set.Ico a b) := Ordinal.small_Ico a b

-- @@ L260-260 verbatim
instance (a b : NatOrdinal.{u}) : Small.{u} (Set.Icc a b) := Ordinal.small_Icc a b

-- @@ L261-261 verbatim
instance (a b : NatOrdinal.{u}) : Small.{u} (Set.Ioo a b) := Ordinal.small_Ioo a b

-- @@ L262-262 verbatim
instance (a b : NatOrdinal.{u}) : Small.{u} (Set.Ioc a b) := Ordinal.small_Ioc a b


-- @@ L264-265 verbatim
instance : IsEmpty (Set.Iio (0 : NatOrdinal)) where
  false x := (not_lt_zero x.1) x.2

-- @@ L266-266 verbatim
instance : Unique (Set.Iio (1 : NatOrdinal)) := Ordinal.uniqueIioOne


-- @@ L268-270 verbatim
@[simp]
theorem Iio_one_default_eq : (default : Set.Iio (1 : NatOrdinal)) = ⟨0, zero_lt_one' NatOrdinal⟩ :=
  rfl


-- @@ L272-273 verbatim
theorem bddAbove_iff_small {s : Set NatOrdinal.{u}} : BddAbove s ↔ Small.{u} s :=
  Ordinal.bddAbove_iff_small


-- @@ L275-276 verbatim
theorem bddAbove_of_small (s : Set NatOrdinal.{u}) [h : Small.{u} s] : BddAbove s :=
  @Ordinal.bddAbove_of_small s h


-- @@ L278-279 verbatim
theorem not_bddAbove_compl_of_small (s : Set NatOrdinal.{u}) [h : Small.{u} s] : ¬ BddAbove sᶜ :=
  @Ordinal.not_bddAbove_compl_of_small s h


-- @@ L281-282 verbatim
theorem le_iSup {ι : Type*} (f : ι → NatOrdinal.{u}) [Small.{u} ι] (i : ι) : f i ≤ iSup f :=
  Ordinal.le_iSup f i


-- @@ L284-286 verbatim
theorem iSup_le_iff {ι : Type*} {f : ι → NatOrdinal.{u}} {a : NatOrdinal.{u}} [Small.{u} ι] :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  Ordinal.iSup_le_iff


-- @@ L288-290 verbatim
theorem lt_iSup_iff {ι : Type*} [Small.{u} ι] (f : ι → NatOrdinal.{u}) {x} :
    x < ⨆ i, f i ↔ ∃ i, x < f i :=
  Ordinal.lt_iSup_iff


-- @@ L292-294 verbatim
theorem iSup_eq_zero_iff {ι : Type*} [Small.{u} ι] {f : ι → NatOrdinal.{u}} :
    ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  Ordinal.iSup_eq_zero_iff


-- @@ L296-296 verbatim
variable {a b c d a' b' c' : NatOrdinal.{u}}


-- @@ L298-298 verbatim
/-! ### Natural addition -/


-- @@ L300-303 verbatim
private def add (a b : NatOrdinal.{u}) : NatOrdinal.{u} :=
  max (⨆ x : Iio a, succ (add x.1 b)) (⨆ x : Iio b, succ (add a x.1))
termination_by (a, b)
decreasing_by all_goals cases x; decreasing_tactic


-- @@ L305-311 verbatim
/-- Natural addition on ordinals `a + b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' + b` and `a + b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
@[no_expose] instance : Add NatOrdinal := ⟨add⟩


-- @@ L313-314 verbatim
/-- Add two `NatOrdinal`s as ordinal numbers. -/
scoped notation:65 x:65 "+ₒ" y:66 => of (val x + val y)


-- @@ L316-320 verbatim
theorem add_def (a b : NatOrdinal) :
    a + b = max (⨆ x : Iio a, succ (x.1 + b)) (⨆ x : Iio b, succ (a + x.1)) := by
  change add .. = _
  rw [add]
  rfl


-- @@ L322-324 verbatim
theorem lt_add_iff : a < b + c ↔ (∃ b' < b, a ≤ b' + c) ∨ ∃ c' < c, a ≤ b + c' := by
  rw [add_def]
  simp [NatOrdinal.lt_iSup_iff]


-- @@ L326-328 verbatim
theorem add_le_iff : b + c ≤ a ↔ (∀ b' < b, b' + c < a) ∧ ∀ c' < c, b + c' < a := by
  rw [← not_lt, lt_add_iff]
  simp


-- @@ L330-331 verbatim
instance : AddLeftStrictMono NatOrdinal where
  elim _a _b _c h := lt_add_iff.2 (.inr ⟨_, h, le_rfl⟩)


-- @@ L333-334 verbatim
instance : AddRightStrictMono NatOrdinal where
  elim _a _b _c h := lt_add_iff.2 (.inl ⟨_, h, le_rfl⟩)


-- @@ L336-337 verbatim
instance : AddLeftMono NatOrdinal :=
  addLeftMono_of_addLeftStrictMono _


-- @@ L339-340 verbatim
instance : AddRightMono NatOrdinal :=
  addRightMono_of_addRightStrictMono _


-- @@ L342-345 verbatim
private theorem add_comm' (a b : NatOrdinal) : a + b = b + a := by
  rw [add_def, add_def, sup_comm]
  congr with x <;> cases x <;> exact congrArg _ (add_comm' ..)
termination_by (a, b)


-- @@ L347-352 verbatim
private theorem add_zero' (a : NatOrdinal) : a + 0 = a := by
  rw [add_def, ciSup_of_empty fun _ : Iio 0 ↦ _, max_bot_right]
  convert iSup_succ a with x
  cases x
  exact add_zero' _
termination_by a


-- @@ L354-364 verbatim
private theorem iSup_add_of_monotone (f : NatOrdinal.{u} → NatOrdinal.{u}) (h : Monotone f) :
    ⨆ x : Iio (a + b), f x = max (⨆ a' : Iio a, f (a'.1 + b)) (⨆ b' : Iio b, f (a + b'.1)) := by
  apply (max_le _ _).antisymm'
  · rw [iSup_le_iff]
    rintro ⟨i, hi⟩
    obtain ⟨x, hx, hi⟩ | ⟨x, hx, hi⟩ := lt_add_iff.1 hi
    · exact le_max_of_le_left ((h hi).trans <| le_iSup (fun x : Iio a ↦ _) ⟨x, hx⟩)
    · exact le_max_of_le_right ((h hi).trans <| le_iSup (fun x : Iio b ↦ _) ⟨x, hx⟩)
  all_goals
    refine csSup_le_csSup' (bddAbove_of_small _) fun _ ↦ ?_
    aesop


-- @@ L366-371 verbatim
private theorem add_assoc' (a b c : NatOrdinal) : a + b + c = a + (b + c) := by
  rw [add_def, add_def a (b + c)]
  rw [iSup_add_of_monotone (fun _ ↦ succ _) (succ_mono.comp add_right_mono),
    iSup_add_of_monotone (fun _ ↦ succ _) (succ_mono.comp add_left_mono), sup_assoc]
  congr with x <;> cases x <;> exact congrArg _ (add_assoc' ..)
termination_by (a, b, c)


-- @@ L373-378 verbatim
instance : AddCommMonoid NatOrdinal where
  add_zero := private add_zero'
  zero_add x := by rw [add_comm', add_zero']
  add_comm := private add_comm'
  add_assoc := private add_assoc'
  nsmul := nsmulRec


-- @@ L380-384 verbatim
instance : IsOrderedCancelAddMonoid NatOrdinal where
  add_le_add_left _ _ := add_le_add_left
  le_of_add_le_add_left a b c h := by
    by_contra! h'
    exact h.not_gt (add_lt_add_right h' a)


-- @@ L386-386 verbatim
theorem le_add_left : a ≤ b + a := by simp

-- @@ L387-387 verbatim
theorem le_add_right : a ≤ a + b := by simp


-- @@ L389-394 verbatim
@[simp]
theorem add_eq_zero_iff : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · repeat rw [← NatOrdinal.le_zero]
    exact ⟨le_add_right.trans_eq h, le_add_left.trans_eq h⟩
  · simp +contextual


-- @@ L396-401 verbatim
private theorem succ_eq_add_one' (a : NatOrdinal) : succ a = a + 1 := by
  rw [add_def, ciSup_unique (s := fun _ : Iio 1 ↦ _), Iio_one_default_eq, add_zero,
    eq_comm, max_eq_right_iff, iSup_le_iff]
  rintro ⟨i, hi⟩
  rwa [← succ_eq_add_one', succ_le_succ_iff, succ_le_iff]
termination_by a


-- @@ L403-403 verbatim
instance : SuccAddOrder NatOrdinal := ⟨by exact succ_eq_add_one'⟩


-- @@ L405-405 verbatim
@[simp] theorem of_add_one (a : Ordinal) : of (a + 1) = of a + 1 := succ_eq_add_one _

-- @@ L406-406 verbatim
@[simp] theorem val_add_one (a : NatOrdinal) : val (a + 1) = val a + 1 := (succ_eq_add_one a).symm


-- @@ L408-409 verbatim
theorem add_one_ne_zero (a : NatOrdinal) : a + 1 ≠ 0 := by
  simpa [← succ_eq_add_one] using succ_ne_zero a


-- @@ L411-411 verbatim
attribute [simp] Order.succ_eq_add_one


-- @@ L413-415 verbatim
instance : AddMonoidWithOne NatOrdinal where
  natCast n := of n
  natCast_succ n := by simp


-- @@ L417-417 verbatim
@[simp] theorem of_natCast (n : ℕ) : of n = n := rfl

-- @@ L418-418 verbatim
@[simp] theorem val_natCast (n : ℕ) : val n = n := rfl


-- @@ L420-422 verbatim
protected theorem succ_one : succ (1 : NatOrdinal) = 2 := by
  rw [succ_eq_add_one]
  exact one_add_one_eq_two


-- @@ L424-425 verbatim
theorem natCast_image_Iio' (n : ℕ) : Nat.cast '' Iio n = Iio (n : Ordinal) := by
  simp_all


-- @@ L427-429 verbatim
@[simp]
theorem natCast_image_Iio (n : ℕ) : Nat.cast '' Iio n = Iio (n : NatOrdinal) :=
  natCast_image_Iio' n


-- @@ L431-434 verbatim
@[simp]
theorem forall_lt_natCast {P : NatOrdinal → Prop} {n : ℕ} : (∀ a < ↑n, P a) ↔ ∀ a < n, P a := by
  change (∀ a ∈ Iio _, _) ↔ ∀ a ∈ Iio _, _
  simp [← natCast_image_Iio]


-- @@ L436-439 verbatim
@[simp]
theorem exists_lt_natCast {P : NatOrdinal → Prop} {n : ℕ} : (∃ a < ↑n, P a) ↔ ∃ a < n, P a := by
  change (∃ a ∈ Iio _, _) ↔ ∃ a ∈ Iio _, _
  simp [← natCast_image_Iio]


-- @@ L441-442 verbatim
theorem lt_omega0 {o : NatOrdinal} : o < of .omega0 ↔ ∃ n : ℕ, o = n :=
  Ordinal.lt_omega0


-- @@ L444-445 verbatim
theorem nat_lt_omega0 (n : ℕ) : n < of .omega0 :=
  Ordinal.natCast_lt_omega0 n


-- @@ L447-450 verbatim
instance : CharZero NatOrdinal where
  cast_injective m n h := by
    apply_fun val at h
    simpa using h


-- @@ L452-456 verbatim
@[simp]
theorem of_add_natCast (a : Ordinal) (n : ℕ) : of (a + n) = of a + n := by
  induction n with
  | zero => simp
  | succ n IH => simp [← add_assoc, IH]


-- @@ L458-460 verbatim
@[simp]
theorem val_add_natCast (a : NatOrdinal) (n : ℕ) : val (a + n) = val a + n :=
  (of_add_natCast _ n).symm


-- @@ L462-470 verbatim
/-- A version of `oadd_le_add` stated in terms of `Ordinal`. -/
theorem oadd_le_add' (a b : Ordinal) : a + b ≤ val (of a + of b) := by
  induction b using Ordinal.limitRecOn with
  | zero => simp
  | add_one c IH => simpa [← add_assoc] using add_le_add_left IH 1
  | limit c hc IH =>
    rw [(Ordinal.isNormal_add_right a).apply_of_isSuccLimit hc, Ordinal.iSup_le_iff]
    rintro ⟨i, hi⟩
    exact (IH i hi).trans (add_le_add_right hi.le (of a))


-- @@ L472-473 verbatim
theorem oadd_le_add (a b : NatOrdinal) : a +ₒ b ≤ a + b :=
  oadd_le_add' ..


-- @@ L475-476 verbatim
theorem lt_omega0' {o : NatOrdinal} : o < NatOrdinal.of Ordinal.omega0 ↔ ∃ n : ℕ, o = n :=
  Ordinal.lt_omega0


-- @@ L478-479 verbatim
theorem nat_lt_omega0' (n : ℕ) : n < NatOrdinal.of Ordinal.omega0 :=
  Ordinal.natCast_lt_omega0 n


-- @@ L481-483 verbatim
@[simp]
theorem add_lt_add_iff_left_right {a b c : NatOrdinal} :
    a + b < c + a ↔ b < c := by rw [add_comm]; exact add_lt_add_iff_right a


-- @@ L485-487 verbatim
@[simp]
theorem add_lt_add_iff_right_left {a b c : NatOrdinal} :
    b + a < a + c ↔ b < c := by rw [add_comm]; exact add_lt_add_iff_left a


-- @@ L489-489 verbatim
end NatOrdinal


-- @@ L491-491 verbatim
end


-- @@ L493-493 verbatim
end MisereGames
