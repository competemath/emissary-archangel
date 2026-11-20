/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/


import Mathlib
import Tnorms.Basic.ContinuousAlgebra


-- @@ L11-26 verbatim
/-!
In this file, we define the following basic T-norms:
  * the product T-norm
  * some trivial T-norms
  * the Minimum (or Godel) T-norm
  * the Łukasiewicz T-norm
  * the drastic T-norm
We also prove when various properties hold.  Each of the t-norms (except the product t-norm) is
  defined on an arbitrary type (with appropriate typeclasses) instead of just the unit interval.
  The trivial t-norms are defined in case we want a concrete counterexample for something.

TODO:
  * This is a slow file, and anything that imports this will probably only need one or two examples,
    so we should make this file into a folder with a file for each example.  This should help with
    build speed.
-/


-- @@ L28-28 verbatim
section ProdTnorm


-- @@ L30-30 verbatim
abbrev ProdTnorm := unitInterval


-- @@ L32-33 verbatim
@[implicit_reducible]
def prodTnorm : Tnorm unitInterval where


-- @@ L35-37 verbatim
noncomputable
instance instProdFuzzyLogic : @IsFuzzyLogic unitInterval _ _ prodTnorm :=
  @IsFuzzyLogic.mk unitInterval _ _ prodTnorm _ _


-- @@ L39-39 verbatim
#synth PosMulStrictMono unitInterval

-- @@ L40-40 verbatim
#synth IsCancelMulZero unitInterval

-- @@ L41-41 verbatim
#synth ConditionalCancellative unitInterval

-- @@ L42-42 verbatim
#synth MulArchimedeanDualWithZero unitInterval

-- @@ L43-43 verbatim
#synth NoNontrivialIdempotents unitInterval

-- @@ L44-44 verbatim
#synth NoZeroDivisors unitInterval

-- @@ L45-45 verbatim
#synth IsReduced unitInterval

-- @@ L46-46 verbatim
#synth ContinuousMul unitInterval

-- @@ L47-47 verbatim
#synth Strict unitInterval

-- @@ L48-50 verbatim
example : ¬ Nilpotent unitInterval := by
  rw [nilpt_iff, not_not]
  infer_instance


-- @@ L52-55 verbatim
end ProdTnorm


-- T-norm on a single element

-- @@ L56-56 verbatim
section TrivialTnorm


-- @@ L58-61 verbatim
instance : OrderTopology PUnit where
  topology_eq_generate_intervals := by
    ext s
    simp


-- @@ L63-64 verbatim
instance : IsOrderedMonoid PUnit where
  mul_le_mul_left := by simp


-- @@ L66-67 verbatim
instance : IsTopOneClass PUnit where
  isTop_one := by simp


-- @@ L69-69 verbatim
instance : Tnorm PUnit where


-- @@ L71-71 verbatim
#synth IsFuzzyLogic PUnit

-- @@ L72-72 verbatim
#synth PosMulStrictMono PUnit

-- @@ L73-73 verbatim
#synth IsCancelMulZero PUnit

-- @@ L74-74 verbatim
#synth ConditionalCancellative PUnit

-- @@ L75-75 verbatim
#synth MulArchimedeanDualWithZero PUnit

-- @@ L76-76 verbatim
#synth NoNontrivialIdempotents PUnit

-- @@ L77-77 verbatim
#synth NoZeroDivisors PUnit

-- @@ L78-78 verbatim
#synth IsReduced PUnit

-- @@ L79-79 verbatim
#synth ContinuousMul PUnit

-- @@ L80-80 verbatim
#synth Strict PUnit

-- @@ L81-81 verbatim
#synth Nilpotent PUnit

-- @@ L82-82 verbatim
#synth SubsingletonZeroOne PUnit


-- @@ L84-84 verbatim
abbrev TrivialTnorm := PUnit


-- @@ L86-89 verbatim
end TrivialTnorm


-- T-norm on two elements

-- @@ L90-90 verbatim
section TrivialZeroOneTnorm


-- @@ L92-93 verbatim
instance : SubsingletonZeroOne Bool where
  allEq_zero_or_one := by grind [Bool.zero_eq_false, Bool.one_eq_true]


-- @@ L95-96 verbatim
instance : IsOrderedMonoid Bool where
  mul_le_mul_left := by simp [Bool.mul_eq_and]


-- @@ L98-99 verbatim
instance : IsTopOneClass Bool where
  isTop_one := by simp [Bool.one_eq_true]


-- @@ L101-103 verbatim
instance : OrderTopology Bool := by
  have : LocallyFiniteOrder Bool := Fintype.toLocallyFiniteOrder
  exact OrderTopology.of_linearLocallyFinite


-- @@ L105-105 verbatim
instance : Tnorm Bool where


-- @@ L107-107 verbatim
#synth IsFuzzyLogic Bool

-- @@ L108-108 verbatim
#synth PosMulStrictMono Bool

-- @@ L109-109 verbatim
#synth IsCancelMulZero Bool

-- @@ L110-110 verbatim
#synth ConditionalCancellative Bool

-- @@ L111-111 verbatim
#synth MulArchimedeanDualWithZero Bool

-- @@ L112-112 verbatim
#synth NoNontrivialIdempotents Bool

-- @@ L113-113 verbatim
#synth NoZeroDivisors Bool

-- @@ L114-114 verbatim
#synth IsReduced Bool

-- @@ L115-115 verbatim
#synth ContinuousMul Bool

-- @@ L116-116 verbatim
#synth Strict Bool

-- @@ L117-117 verbatim
#synth Nilpotent Bool

-- @@ L118-118 verbatim
#synth SubsingletonZeroOne Bool


-- @@ L120-120 verbatim
abbrev TrivialZeroOneTnorm := Bool


-- @@ L122-122 verbatim
end TrivialZeroOneTnorm



-- @@ L125-125 verbatim
namespace MinTnorm


-- @@ L127-127 verbatim
variable (M : Type*)


-- @@ L129-131 verbatim
@[reducible]
def minMul [Min M] : Mul M where
  mul := min


-- @@ L133-144 verbatim
@[reducible]
def minMonoid [SemilatticeInf M] [BoundedOrder M] :
    CommMonoidWithZero M where
  toMul := minMul M
  mul_assoc := inf_assoc
  mul_comm := inf_comm
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  zero := ⊥
  zero_mul := bot_inf_eq
  mul_zero := inf_bot_eq


-- @@ L146-147 verbatim
local instance minMul_continuousMul [LinearOrder M] [TopologicalSpace M] [OrderClosedTopology M] :
  @ContinuousMul M _ (minMul M) := @ContinuousMul.mk M _ (minMul M) continuous_min


-- @@ L149-152 verbatim
local instance [SemilatticeInf M] [BoundedOrder M] : @IsTopOneClass M _ (minMonoid M).toOne := by
  refine @IsTopOneClass.mk M _ (minMonoid M).toOne ?_
  intro a
  exact le_top


-- @@ L154-158 verbatim
@[reducible]
def minTnorm [CompleteLinearOrder M] [TopologicalSpace M] [OrderTopology M] : Tnorm M where
  toCommMonoidWithZero := minMonoid M
  toIsTopOneClass := inferInstance
  mul_le_mul_left := fun _ _ h _ ↦ inf_le_inf_right _ h


-- @@ L160-162 verbatim
instance minTnorm_isFuzzyLogic [CompleteLinearOrder M] [TopologicalSpace M] [OrderTopology M]
    [FirstCountableTopology M] : @IsFuzzyLogic M _ _ (minTnorm M) :=
  @IsFuzzyLogic.mk M _ _ (minTnorm M) _ _


-- @@ L164-164 verbatim
section SemilatticeInf


-- @@ L166-166 verbatim
variable {M} [SemilatticeInf M] [BoundedOrder M]


-- @@ L168-168 verbatim
local instance : CommMonoidWithZero M := minMonoid M


-- @@ L170-171 verbatim
@[simp, grind =]
lemma minMul_mul {a b : M} : a * b = a ⊓ b := rfl


-- @@ L173-174 verbatim
@[simp, grind =]
lemma minMonoid_zero : (0 : M) = ⊥ := rfl


-- @@ L176-177 verbatim
@[simp, grind =]
lemma minMonoid_one : (1 : M) = ⊤ := rfl


-- @@ L179-188 verbatim
@[simp, grind =]
lemma minMonoid_pow {a : M} {n : ℕ} (hn : n ≠ 0) : a ^ n = a := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp at ih
      simp [pow_succ, ih]


-- @@ L190-190 verbatim
theorem isIdempotentElem (a : M) : IsIdempotentElem a := by simp [IsIdempotentElem]


-- @@ L192-193 verbatim
instance : IsReduced M where
  eq_zero x := IsIdempotentElem.eq_zero_of_isNilpotent (isIdempotentElem x)


-- @@ L195-197 verbatim
theorem nontrivialZeroOne_iff_nontrivialIdempotents :
    NontrivialZeroOne M ↔ ¬ NoNontrivialIdempotents M := by
  simp [nontrivialZeroOne_iff, noNontrivialIdempotents_iff, isIdempotentElem]


-- @@ L199-212 verbatim
theorem nontrivialZeroOne_iff_not_posMulStrictMono :
    NontrivialZeroOne M ↔ ¬ PosMulStrictMono M := by
  constructor
  · simp only [nontrivialZeroOne_iff, minMonoid_zero, ne_eq, minMonoid_one, posMulStrictMono_iff,
      minMul_mul, not_forall, forall_exists_index, and_imp]
    intro a ha0 ha1
    use a, by rwa [bot_lt_iff_ne_bot], a, ⊤
    constructor
    · simp
    · rwa [lt_top_iff_ne_top]
  · contrapose!
    rw [← subsingletonZeroOne_iff_not_nontrivialZeroOne]
    intro h
    infer_instance


-- @@ L214-223 verbatim
theorem nontrivialZeroOne_iff_not_isCancelMulZero :
    NontrivialZeroOne M ↔ ¬ IsCancelMulZero M := by
  contrapose!
  constructor
  · rw [← subsingletonZeroOne_iff_not_nontrivialZeroOne]
    intro h
    infer_instance
  · rw [nontrivialZeroOne_iff_nontrivialIdempotents, not_not]
    intro h
    infer_instance


-- @@ L225-234 verbatim
theorem nontrivialZeroOne_iff_not_conditionalCancellative :
    NontrivialZeroOne M ↔ ¬ ConditionalCancellative M := by
  contrapose!
  constructor
  · rw [← subsingletonZeroOne_iff_not_nontrivialZeroOne]
    intro h
    infer_instance
  · rw [nontrivialZeroOne_iff_nontrivialIdempotents, not_not]
    intro h
    infer_instance


-- @@ L236-253 verbatim
theorem not_arch_of_infinite [Infinite M] : ¬ MulArchimedeanDualWithZero M := by
  have : NontrivialZeroOne M := inferInstance
  obtain ⟨x, hx0, hx1⟩ := this.exists_ne
  classical obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1, x})
  simp only [minMonoid_zero, minMonoid_one, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy0, hy1, hyx⟩ := hy
  simp only [mulArchimedeanDualWithZero_iff, minMonoid_zero, minMonoid_one, not_forall, not_exists]
  wlog hxy : ¬y < x
  · push Not at hxy
    rename_i hnzo
    specialize this hnzo y hy0 hy1 x hx0 hx1
    rw [eq_comm] at hyx
    exact this hyx <| Std.not_gt_of_lt hxy
  · use x, y, by rwa [bot_lt_iff_ne_bot], by rwa [lt_top_iff_ne_top]
    intro n
    cases n with
    | zero => simp
    | succ n => simp [hxy]


-- @@ L255-257 verbatim
variable [TopologicalSpace M]

-- these are clearly equivalent

-- @@ L258-259 verbatim
instance [h : ContinuousInf M] : ContinuousMul M where
  continuous_mul := by simp [continuous_inf]


-- @@ L261-261 verbatim
variable [ContinuousInf M]


-- @@ L263-271 verbatim
theorem nilpt_iff_subsingletonZeroOne : Nilpotent M ↔ SubsingletonZeroOne M := by
  constructor
  · rw [subsingletonZeroOne_iff_not_nontrivialZeroOne]
    intro h
    have hr : IsReduced M := inferInstance
    contrapose! hr
    exact not_isReduced_of_nilpotent M
  · intro _
    infer_instance


-- @@ L273-276 verbatim
theorem strict_iff_subsingletonZeroOne : Strict M ↔ SubsingletonZeroOne M := by
  have : ContinuousMul M := inferInstance
  simp [strict_iff, this, subsingletonZeroOne_iff_not_nontrivialZeroOne,
    nontrivialZeroOne_iff_not_posMulStrictMono]


-- @@ L278-278 verbatim
end SemilatticeInf


-- @@ L280-280 verbatim
section LinearOrder


-- @@ L282-282 verbatim
variable [LinearOrder M] [BoundedOrder M]


-- @@ L284-284 verbatim
local instance : CommMonoidWithZero M := minMonoid M


-- @@ L286-287 verbatim
local instance : NoZeroDivisors M where
  eq_zero_or_eq_zero_of_mul_eq_zero := by simp


-- @@ L289-289 verbatim
end LinearOrder


-- @@ L291-294 verbatim
end MinTnorm


-- the Łukasiewicz T-norm


-- @@ L296-296 verbatim
namespace LukTnorm


-- @@ L298-298 verbatim
variable (R : Type*) [Ring R]


-- @@ L300-300 verbatim
section SemilatticeSup


-- @@ L302-302 verbatim
variable [SemilatticeSup R] [IsOrderedRing R]


-- @@ L304-306 verbatim
@[implicit_reducible]
def lukMul : Mul (Set.Icc (0 : R) 1) where mul p q :=
  ⟨(max 0 (p.1 + q - 1)), by simp; grind [add_le_add]⟩


-- @@ L308-311 verbatim
@[simp, grind =]
lemma lukMul_mul (a b : Set.Icc (0 : R) 1) :
  @HMul.hMul _ _ _ (@instHMul _ (lukMul R)) a b =
  ⟨(max 0 (a.1 + b - 1)), by simp; grind [add_le_add]⟩ := rfl


-- @@ L313-315 verbatim
instance [TopologicalSpace R] [IsTopologicalAddGroup R] [ContinuousSup R] :
  @ContinuousMul (Set.Icc (0 : R) 1) _ (lukMul R) :=
  @ContinuousMul.mk _ _ (lukMul R) <| Continuous.subtype_mk (by fun_prop) _


-- @@ L317-318 verbatim
instance : IsBotZeroClass (Set.Icc (0 : R) 1) where
  isBot_zero a := a.2.1


-- @@ L320-321 verbatim
instance : IsTopOneClass (Set.Icc (0 : R) 1) where
  isTop_one a := a.2.2


-- @@ L323-323 verbatim
end SemilatticeSup


-- @@ L325-325 verbatim
section LinearOrder


-- @@ L327-327 verbatim
variable [LinearOrder R] [IsOrderedRing R]


-- @@ L329-335 verbatim
@[implicit_reducible]
def lukSemigroup : Semigroup (Set.Icc (0 : R) 1) where
  mul p q := ⟨(max 0 (p.1 + q - 1)), by grind⟩
  mul_assoc := by
    intro ⟨a, ha0, ha1⟩ ⟨b, hb0, hb1⟩ ⟨c, hc0, hc1⟩
    simp [sup_eq_sup_iff_left]
    grind


-- @@ L337-358 verbatim
@[implicit_reducible]
def lukMonoid : CommMonoidWithZero (Set.Icc (0 : R) 1) where
  toMul := lukMul R
  npow := @npowRecAuto _ (lukSemigroup R) _
  mul_assoc := @mul_assoc _ (lukSemigroup R)
  mul_comm := by
    simp
    grind
  one_mul := by
    simp
    grind
  mul_one := by
    simp
    grind
  zero_mul := by
    intro a
    rw [lukMul_mul, ← Subtype.coe_inj, Subtype.coe_mk, Set.Icc.coe_zero]
    grind
  mul_zero := by
    intro a
    rw [lukMul_mul, ← Subtype.coe_inj, Subtype.coe_mk, Set.Icc.coe_zero]
    grind


-- @@ L360-360 verbatim
local instance : MonoidWithZero (Set.Icc (0 : R) 1) := (lukMonoid R).toMonoidWithZero


-- @@ L362-362 verbatim
local instance : CommMonoidWithZero (Set.Icc (0 : R) 1) := lukMonoid R


-- @@ L364-367 verbatim
instance : IsOrderedMonoid (Set.Icc (0 : R) 1) where
  mul_le_mul_left := by
    simp [HMul.hMul, Mul.mul]
    grind


-- @@ L369-386 verbatim
lemma luk_pow_le_max (q : Set.Icc (0 : R) 1) (n : ℕ) (hn : n > 1) :
    ((lukMonoid R).npow n q : Set.Icc (0 : R) 1) ≤ max 0 (n * (q.1 - 1) + 1) := by
  induction n with
  | zero => grind
  | succ n ih =>
    have hn0 : n ≠ 0 := by grind
    by_cases! hn1 : n = 1
    · subst hn1
      simp only [Nat.reduceAdd, @npow_eq_pow _ (lukMonoid R).toMonoid,
        @pow_two _ (lukMonoid R).toMonoid, Nat.cast_ofNat, two_mul, le_sup_iff]
      simp only [HMul.hMul, Mul.mul, sup_le_iff, le_refl, tsub_le_iff_right, zero_add, true_and]
      grind
    specialize ih (by grind)
    rw [@npow_eq_pow _ (lukMonoid R).toMonoid] at ih
    push_cast
    rw [@npow_eq_pow _ (lukMonoid R).toMonoid, @pow_succ _ (lukMonoid R).toMonoid, add_mul, one_mul]
    conv => lhs; simp only [HMul.hMul, Mul.mul]
    grind


-- @@ L388-404 verbatim
lemma luk_isNilpotent [Archimedean R] (p : Set.Icc (0 : R) 1) (hp : p ≠ 1) :
    @IsNilpotent (Set.Icc (0 : R) 1) (lukMonoid R).toZero (lukMonoid R).toPow p := by
  rw [← lt_one_iff_ne_one, ← Subtype.coe_lt_coe, Set.Icc.coe_one] at hp
  have hp : 0 < 1 - p.1 := by grind
  obtain ⟨n, hn⟩ := Archimedean.arch (1 : R) hp
  simp only [nsmul_eq_mul] at hn
  use (n + 2)
  suffices (n + 2) * (p.1 - 1) + 1 ≤ 0 by
    have hp := luk_pow_le_max R p (n + 2) (by grind)
    simp only [npow_eq_pow, Nat.cast_add, Nat.cast_ofNat, this, sup_of_le_left] at hp
    exact le_antisymm hp zero_le
  have hn2 : 1 ≤ (n + 2) * (1 - p.1) := by
    rw [add_mul]
    refine le_trans hn ?_
    rw [le_add_iff_nonneg_right]
    exact mul_nonneg zero_le_two hp.le
  rwa [← neg_le_neg_iff, neg_mul_eq_mul_neg, neg_sub, le_neg_iff_add_nonpos_right] at hn2


-- @@ L406-410 verbatim
instance instLukNilpotent [TopologicalSpace R] [IsTopologicalAddGroup R] [ContinuousSup R]
    [Archimedean R] :
    Nilpotent (Set.Icc (0 : R) 1) where
  toContinuousMul := inferInstance
  nilpt p hp := luk_isNilpotent R p hp


-- @@ L412-423 verbatim
instance : @NoNontrivialIdempotents (Set.Icc (0 : R) 1) (lukMul R) _ _ := by
  rw [noNontrivialIdempotents_iff]
  intro ⟨x, hx⟩
  unfold IsIdempotentElem
  simp only [lukMul_mul, Subtype.mk.injEq, not_and, ne_eq, Decidable.not_not]
  intro h
  have := Std.max_eq_or (a := 0) (b := x + x - 1)
  rw [h] at this
  rcases this with this | this
  · simp [this]
  · have hx1 : x = 1 := by grind
    simp [hx1]


-- @@ L425-430 verbatim
instance [Archimedean R] : MulArchimedeanDualWithZero (Set.Icc (0 : R) 1) := by
  rw [mulArchimedeanDualWithZero_iff]
  intro a b ha0 hb1
  obtain ⟨n, hn⟩ := luk_isNilpotent R b hb1.ne
  use n
  rwa [hn]


-- @@ L432-436 verbatim
instance [DenselyOrdered R] [Nontrivial R] : NontrivialZeroOne (Set.Icc (0 : R) 1) where
  exists_ne := by
    obtain ⟨a, ha0, ha1⟩ := exists_between (zero_lt_one' R)
    use ⟨a, by grind⟩
    simp [← Subtype.coe_inj, ha0.ne', ha1.ne]


-- @@ L438-457 verbatim
theorem luk_not_strict [TopologicalSpace R] [IsTopologicalAddGroup R]
    [Archimedean R] [ContinuousSup R] [OrderTopology R] [Nontrivial R]
    [PreconnectedSpace (Set.Icc (0 : R) 1)] :
    ¬ @Strict (Set.Icc (0 : R) 1) _ (lukMul R) _ _ := by
  have : DenselyOrdered (Set.Icc (0 : R) 1) := denselyOrdered_of_preconnectedSpace
  have : Nontrivial (Set.Icc (0 : R) 1) := by
    refine Nontrivial.mk ?_
    use 0, 1
    rw [ne_eq, ← Subtype.coe_inj, Set.Icc.coe_zero, Set.Icc.coe_one]
    exact zero_ne_one' R
  rw [← nilpt_iff]
  infer_instance

/-
PosMulStrictMono
IsCancelMulZero
ConditionalCancellative
NoZeroDivisors
IsReduced
-/


-- @@ L459-459 verbatim
end LinearOrder


-- @@ L461-461 verbatim
section CompleteLinearOrder


-- @@ L463-463 verbatim
variable [CompleteLinearOrder R] [IsOrderedRing R] [TopologicalSpace R] [OrderTopology R]


-- @@ L465-465 verbatim
#synth @MulArchimedeanDualWithZero (Set.Icc (0 : R) 1) _ (lukMonoid R).toMonoidWithZero


-- @@ L467-472 verbatim
@[implicit_reducible]
def lukTnorm : Tnorm (Set.Icc (0 : R) 1)  where
  toCommMonoidWithZero := lukMonoid R
  toIsTopOneClass := inferInstance
  toOrderTopology := inferInstance
  toIsOrderedMonoid := inferInstance


-- @@ L474-474 verbatim
variable [FirstCountableTopology R]


-- @@ L476-478 verbatim
noncomputable instance instLukFuzzyLogic : @IsFuzzyLogic (Set.Icc (0 : R) 1) _ _ (lukTnorm R) := by
  refine @IsFuzzyLogic.mk _ _ _ (lukTnorm R) ?_ _
  exact @instLeftContinuousMulOfContinuousMul _ (lukMul R) _ _ _


-- @@ L480-480 verbatim
local instance : MonoidWithZero (Set.Icc (0 : R) 1) := (lukMonoid R).toMonoidWithZero


-- @@ L482-482 verbatim
local instance : Tnorm (Set.Icc (0 : R) 1) := lukTnorm R


-- @@ L484-491 expanded
lemma luk_LImp_eq_min (p q : (Set.Icc (0 : R) 1)) : LImp p q = ⟨min 1 (1 - p.1 + q), by grind⟩ :=
  by
  refine le_antisymm ?_ ?_
  · simp [LImp_def, ← Subtype.coe_le_coe]
    grind
  · rw [le_LImp_iff_mul_le]
    simp [← Subtype.coe_le_coe]
    grind


-- @@ L493-493 verbatim
end CompleteLinearOrder


-- @@ L495-498 verbatim
end LukTnorm


-- the drastic T-norm


-- @@ L500-500 verbatim
namespace DrasticTnorm


-- @@ L502-502 verbatim
variable (M : Type*)


-- @@ L504-506 verbatim
@[implicit_reducible]
def drasticMul [Bot M] [Top M] [DecidableEq M] : Mul M where
  mul := fun p q ↦ if p = ⊤ then q else if q = ⊤ then p else ⊥


-- @@ L508-508 verbatim
local instance [Bot M] [Top M] [DecidableEq M] : Mul M := drasticMul M


-- @@ L510-512 verbatim
@[simp, grind =]
lemma drasticMul_mul [Bot M] [Top M] [DecidableEq M] (a b : M) :
  a * b = if a = ⊤ then b else if b = ⊤ then a else ⊥ := rfl


-- @@ L514-514 verbatim
section PartialOrder


-- @@ L516-516 verbatim
variable [PartialOrder M] [BoundedOrder M] [DecidableEq M]


-- @@ L518-538 verbatim
@[implicit_reducible]
def drasticMonoid : CommMonoidWithZero M where
  toMul := drasticMul M
  zero := ⊥
  one := ⊤
  mul_assoc a b c := by
    by_cases! h : (⊤ : M) = ⊥
    · rw [subsingleton_iff_top_eq_bot] at h
      exact Subsingleton.allEq _ _
    grind
  mul_comm := by grind
  one_mul := by simp [OfNat.ofNat]
  mul_one := by simp [OfNat.ofNat]
  zero_mul a := by
    simp only [OfNat.ofNat, Zero.zero, drasticMul_mul, ite_self, ite_eq_right_iff]
    intro h
    exact eq_bot_of_top_eq_bot h.symm a
  mul_zero a := by
    simp only [OfNat.ofNat, Zero.zero, drasticMul_mul, ite_eq_left_iff, ite_eq_right_iff]
    intro ha h
    exact eq_bot_of_top_eq_bot h.symm a


-- @@ L540-540 verbatim
local instance : CommMonoidWithZero M := drasticMonoid M


-- @@ L542-543 verbatim
instance : IsBotZeroClass M where
  isBot_zero a := by simp [OfNat.ofNat, Zero.zero]


-- @@ L545-546 verbatim
instance : IsTopOneClass M where
  isTop_one a := by simp [OfNat.ofNat, One.one]


-- @@ L548-549 verbatim
instance : IsOrderedMonoid M where
  mul_le_mul_left := by grind [bot_le]


-- @@ L551-566 verbatim
theorem posMulStrictMono_iff_subsingletonZeroOne :
    PosMulStrictMono M ↔ SubsingletonZeroOne M := by
  constructor
  · simp only [posMulStrictMono_iff, drasticMul_mul, subsingletonZeroOne_iff_not_nontrivialZeroOne]
    contrapose!
    intro h
    obtain ⟨a, ha0, ha1⟩ := h.exists_ne
    use a
    constructor
    · rwa [zero_lt_iff]
    use ⊥, a
    constructor
    · rwa [bot_lt_iff_ne_bot, bot_eq_zero]
    simp [ha1, bot_eq_zero, top_eq_one]
  · intro h
    infer_instance


-- @@ L568-583 verbatim
theorem isCancelMulZero_iff_subsingletonZeroOne :
    IsCancelMulZero M ↔ SubsingletonZeroOne M := by
  constructor
  · rw [subsingletonZeroOne_iff_not_nontrivialZeroOne, isCancelMulZero_iff]
    contrapose!
    intro h hc
    obtain ⟨a, ha0, ha1⟩ := h.exists_ne
    simp only [isRightCancelMulZero_iff, ne_eq, isRightRegular_iff_isRegular, not_forall]
    use a, ha0
    suffices ¬ IsLeftRegular a by simpa using this
    rw [IsLeftRegular, Function.Injective]
    push Not
    use a, 0
    simp [top_eq_one, ha1, ha0]
  · intro h
    infer_instance


-- @@ L585-599 verbatim
instance : ConditionalCancellative M where
  right_cancel_of_mul_ne_zero := by
    intro a b c
    by_cases! h : (⊤ : M) = ⊥
    · intro _ _
      rw [subsingleton_iff_top_eq_bot] at h
      exact Subsingleton.allEq _ _
    grind [← bot_eq_zero]
  left_cancel_of_mul_ne_zero := by
    intro a b c
    by_cases! h : (⊤ : M) = ⊥
    · intro _ _
      rw [subsingleton_iff_top_eq_bot] at h
      exact Subsingleton.allEq _ _
    grind [← bot_eq_zero]


-- @@ L601-601 verbatim
lemma sq_eq_bot (a : M) (ha : a ≠ ⊤) : a ^ 2 = 0 := by simp [pow_two, ha, bot_eq_zero]


-- @@ L603-607 verbatim
instance : MulArchimedeanDualWithZero M where
  arch := by
    intro a b ha0 hb1
    use 2
    rwa [sq_eq_bot M b hb1.ne]


-- @@ L609-614 verbatim
instance : NoNontrivialIdempotents M where
  no_idem p hp := by
    simp [IsIdempotentElem] at hp
    simp only [not_and, ne_eq, Decidable.not_not]
    contrapose!
    rwa [eq_comm]


-- @@ L616-625 verbatim
theorem noZeroDivisors_iff_subsingletonZeroOne :
    NoZeroDivisors M ↔ SubsingletonZeroOne M := by
  constructor
  · rw [subsingletonZeroOne_iff, noZeroDivisors_iff]
    contrapose!
    intro ⟨a, ha0, ha1⟩
    use a, a
    simp [ha0, ha1, top_eq_one, bot_eq_zero]
  · intro h
    infer_instance


-- @@ L627-640 verbatim
theorem isReduced_iff_subsingletonZeroOne :
    IsReduced M ↔ SubsingletonZeroOne M := by
  constructor
  · rw [subsingletonZeroOne_iff, isReduced_iff]
    contrapose!
    intro ⟨a, ha0, ha1⟩
    use a
    unfold IsNilpotent
    constructor
    · use 2
      exact sq_eq_bot M a ha1
    · exact ha0
  · intro h
    infer_instance


-- @@ L642-642 verbatim
variable [TopologicalSpace M] [OrderTopology M]


-- @@ L644-678 verbatim
theorem continuousMul_of_isOpen_top (ht : IsOpen {(⊤ : M)}) : ContinuousMul M := by
  by_cases hS : Subsingleton M
  · infer_instance
  rw [← subsingleton_iff_top_eq_bot] at hS
  refine ContinuousMul.mk ?_
  rw [OrderTopology.continuous_iff]
  intro x
  constructor
  · by_cases! hx : x = ⊤
    · simp [hx]
    have h : (fun p : M × M ↦ p.1 * p.2) ⁻¹' Set.Ioi x = {⊤} ×ˢ Set.Ioi x ∪ Set.Ioi x ×ˢ {⊤} := by
      grind [not_lt_bot]
    rw [h]
    refine IsOpen.union ?_ ?_
    · exact IsOpen.prod ht (isOpen_Ioi' _)
    · exact IsOpen.prod (isOpen_Ioi' _) ht
  · by_cases! hx : x = ⊤
    · have h : (fun p : M × M ↦ p.1 * p.2) ⁻¹' Set.Iio x =
          Set.univ ×ˢ Set.Iio ⊤ ∪ Set.Iio ⊤ ×ˢ Set.univ := by
        grind [lt_top_iff_ne_top]
      rw [h]
      refine IsOpen.union ?_ ?_
      · exact IsOpen.prod isOpen_univ (isOpen_Iio' _)
      · exact IsOpen.prod (isOpen_Iio' _) isOpen_univ
    by_cases! hx : x = ⊥
    · simp [hx]
    suffices (fun p : M × M ↦ p.1 * p.2) ⁻¹' Set.Iio x =
        (Set.Iio (⊤ : M) ×ˢ Set.Iio (⊤ : M) ∪ Set.univ ×ˢ Set.Iio x ∪ Set.Iio x ×ˢ Set.univ) by
      rw [this]
      refine IsOpen.union ?_ ?_
      · refine IsOpen.union ?_ ?_
        · exact IsOpen.prod (isOpen_Iio' _) (isOpen_Iio' _)
        · exact IsOpen.prod isOpen_univ (isOpen_Iio' _)
      · exact IsOpen.prod (isOpen_Iio' _) isOpen_univ
    grind [lt_top_iff_ne_top, bot_lt_iff_ne_bot]


-- @@ L680-686 verbatim
theorem nilpotent_of_isOpen_top (ht : IsOpen {(⊤ : M)}) : Nilpotent M := by
  have : ContinuousMul M := continuousMul_of_isOpen_top M ht
  refine Nilpotent.mk ?_
  intro p hp
  unfold IsNilpotent
  use 2
  exact sq_eq_bot M p hp


-- @@ L688-702 verbatim
theorem strict_iff_subsingletonZeroOne : Strict M ↔ SubsingletonZeroOne M := by
  constructor
  · rw [subsingletonZeroOne_iff_not_nontrivialZeroOne, strict_iff, posMulStrictMono_iff]
    contrapose!
    intro h hcm
    obtain ⟨a, ha0, ha1⟩ := h.exists_ne
    use a
    constructor
    · rwa [← bot_eq_zero, bot_lt_iff_ne_bot]
    use 0, a
    constructor
    · rwa [← bot_eq_zero, bot_lt_iff_ne_bot]
    simp [ha1, bot_eq_zero, top_eq_one]
  · intro h
    infer_instance


-- @@ L704-704 verbatim
end PartialOrder


-- @@ L706-711 verbatim
@[implicit_reducible]
def drasticTnorm [CompleteLinearOrder M] [TopologicalSpace M] [OrderTopology M] :
    Tnorm M where
  toCommMonoidWithZero := drasticMonoid M
  toIsTopOneClass := inferInstance
  toIsOrderedMonoid := inferInstance


-- @@ L713-719 verbatim
end DrasticTnorm



-- Half product Tnorm
-- this is just what I call it and it is not a Tnorm under the usual definition
--   since it's an operation on [0.5,1] not [0,1]


-- @@ L721-721 verbatim
section HalfProdTnorm


-- @@ L723-723 verbatim
def HalfProdTnorm := Set.Icc (1 / 2 : ℝ) 1


-- @@ L725-728 verbatim
noncomputable
instance : CompleteLinearOrder HalfProdTnorm := by
  have hf : Fact (1 / 2 ≤ (1 : ℝ)) := by grind only [fact_iff]
  exact instCompleteLinearOrderElemIccOfFactLe

-- @@ L729-731 verbatim
instance : OrderTopology HalfProdTnorm := by
  unfold HalfProdTnorm
  exact orderTopology_of_ordConnected


-- @@ L733-741 verbatim
noncomputable
def halfProd (p q : HalfProdTnorm) : HalfProdTnorm := ⟨(p * q ⊔ 1 / 2), by
  simp only [HalfProdTnorm, Set.mem_Icc, le_sup_right, sup_le_iff, true_and] at ⊢ p q
  constructor
  · have h := mul_le_mul_of_nonneg p.2.2 q.2.2 (by grind) (by grind)
    rw [mul_one] at h
    exact h
  · grind
  ⟩


-- @@ L743-743 verbatim
noncomputable instance instHalfProdMul : Mul HalfProdTnorm where mul := halfProd

-- @@ L744-744 verbatim
noncomputable instance instHalfProdZero : Zero HalfProdTnorm := ⟨1 / 2, by grind [= HalfProdTnorm]⟩

-- @@ L745-745 verbatim
noncomputable instance instHalfProdOne : One HalfProdTnorm := ⟨1, by grind [= HalfProdTnorm]⟩


-- @@ L747-747 verbatim
@[grind =] lemma halfProd_zero : (0 : HalfProdTnorm) = (1 / 2 : ℝ) := rfl

-- @@ L748-748 verbatim
@[grind =] lemma halfProd_one : (1 : HalfProdTnorm) = (1 : ℝ) := rfl

-- @@ L749-749 verbatim
@[grind =] lemma halfProd_mul {p q : HalfProdTnorm} : (p * q).1 = (p.1 * q.1 ⊔ 1 / 2) := rfl


-- @@ L751-790 verbatim
noncomputable
def lukHalfProdEquiv : @OrderMonoidIso unitInterval HalfProdTnorm _ _ (LukTnorm.lukMul ℝ) _ := by
  refine @OrderMonoidIso.mk unitInterval HalfProdTnorm _ _ (LukTnorm.lukMul ℝ) _ ?_ ?_
  · refine @MulEquiv.mk unitInterval HalfProdTnorm (LukTnorm.lukMul ℝ) _ ?_ ?_
    · refine Equiv.mk ?_ ?_ ?_ ?_
      · use fun ⟨p, hp⟩ ↦ ⟨2 ^ (p - 1), by
          grind [Real.rpow_le_rpow_left_iff, Real.rpow_neg_one 2, Real.rpow_zero 2,
            = HalfProdTnorm]⟩
      · use fun ⟨p, hp⟩ ↦ ⟨(Real.logb 2 p) + 1, by
          simp only [HalfProdTnorm, one_div, Set.mem_Icc, add_le_iff_nonpos_left] at hp ⊢
          constructor
          · suffices -1 ≤ Real.logb 2 p by grind
            grind [Real.le_logb_iff_rpow_le, Real.rpow_neg_one 2]
          · grind [Real.logb_nonpos]⟩
      · intro ⟨p, hp⟩
        simp
      · intro ⟨p, hp⟩
        simp only [add_sub_cancel_right, Subtype.mk.injEq]
        rw [Real.rpow_logb (by grind) (by grind) (by grind [= HalfProdTnorm])]
    · simp only [Std.max_eq_if, tsub_le_iff_right, zero_add, ← Subtype.val_inj, halfProd_mul,
        one_div, Subtype.forall, Set.mem_Icc, and_imp]
      intro p hp0 hp1 q hq0 hq1
      split_ifs
      · rename_i h1 h2
        refine le_antisymm ?_ ?_
        · rw [zero_sub, Real.rpow_neg_one 2]
          exact h2
        · rw [← Real.rpow_add zero_lt_two, Real.rpow_le_rpow_left_iff one_lt_two]
          grind
      · norm_num
      · rw [← Real.rpow_add zero_lt_two]
        ring_nf
      · rename_i h1 h2
        refine le_antisymm ?_ ?_
        · push Not at h2
          rw [← Real.rpow_add zero_lt_two] at h2
          grind
        · rw [← Real.rpow_neg_one 2, Real.rpow_le_rpow_left_iff one_lt_two]
          grind
  · simp


-- @@ L792-792 verbatim
end HalfProdTnorm
