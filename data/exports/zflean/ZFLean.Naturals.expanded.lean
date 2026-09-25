/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import ZFLean.Def
public import ZFLean.TransferAlgebra
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Divisibility.Basic


-- @@ L14-28 verbatim
/-! # ZFC Natural numbers

This file defines the natural numbers in ZF set theory. The definition is based on the construction
of the Von Neumann ordinals, where each natural number is represented as the set of all smaller
natural numbers.

The set of all natural numbers is defined as the smallest inductive set. Because of the axiom of
separation, the definition relies on the existence of an infinite set, which is provided by the
`some_inf` constant. It can be shown that the choice of `some_inf` does not affect the definition of
the natural numbers and leads to isomorphic definitions.

The file also includes the definition of the `ZFNat` type for ZF natural numbers, and provides
various properties and usual arithmetic operations on natural numbers.

-/


-- @@ L30-30 verbatim
public noncomputable section


-- @@ L32-32 verbatim
namespace ZFSet


-- @@ L34-34 verbatim
/-! ## Preliminary definitions -/


-- @@ L36-36 verbatim
section Preamble


-- @@ L38-39 verbatim
/-- Witness for an infinite set, meant to be used for definitional purpose only. -/
private abbrev some_inf := @Classical.choose _ inductive_set ⟨_, omega_inductive⟩


-- @@ L41-42 verbatim
/-- The set `some_inf` is inductive. -/
private lemma inductive_some_inf : inductive_set some_inf := Classical.choose_spec _


-- @@ L44-48 verbatim
private lemma some_inf_nonempty : some_inf ≠ ∅ := by
  intro h
  let h' := inductive_some_inf.left
  rw [h] at h'
  exact (ZFSet.notMem_empty ∅) h'


-- @@ L50-52 verbatim
private lemma some_inf_mem_sep_inductive_set : some_inf ∈ some_inf.powerset.sep inductive_set := by
  simp only [mem_sep, mem_powerset, subset_refl, true_and]
  exact inductive_some_inf


-- @@ L54-54 verbatim
end Preamble


-- @@ L56-56 verbatim
/-! ## Natural numbers -/


-- @@ L58-58 verbatim
section Naturals


-- @@ L60-64 verbatim
/--
The set of natural numbers `Nat` is defined as the smallest inductive set.
This definition avoids the use of `ω`, even though `ω` may be thought of as `ℕ`.
-/
def Nat : ZFSet := ⋂₀ ((powerset some_inf).sep inductive_set)


-- @@ L66-67 verbatim
/-- The type of natural numbers `ZFNat` is defined as the subtype of `Nat`. -/
abbrev ZFNat := {x // x ∈ Nat}


-- @@ L69-69 verbatim
namespace ZFNat


-- @@ L71-77 verbatim
/--
`some_inf` is an inductive subset of `some_inf`:
`some_inf ∈ { a ⊆ some_inf | inductive_set a }`.
-/
private theorem some_inf_mem_powerset_some_inf_ind :
  some_inf ∈ some_inf.powerset.sep inductive_set :=
  mem_sep.mpr ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩


-- @@ L79-97 verbatim
/-- `Nat` is an infinite inductive set. -/
private theorem Nat_subset_some_inf : Nat ⊆ some_inf := by
  intro n hn
  unfold Nat at hn
  rw [mem_sInter] at hn
  · have aux :
      n ∈ (⋃₀ (powerset some_inf).sep inductive_set : ZFSet) ∧
      (fun b => ∀ c, c ∈ (powerset some_inf).sep inductive_set → b ∈ c) n := by
        simp only [mem_sUnion, mem_sep, and_imp] at *
        exact ⟨
          ⟨some_inf,
            ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩,
            hn some_inf (mem_powerset.mpr fun _ => id) (inductive_some_inf)⟩,
          fun _ _ _ => hn _ ‹_› ‹_›⟩
    simp only [mem_sep, mem_powerset, and_imp, mem_sUnion] at aux
    obtain ⟨⟨_, ⟨left, _⟩, _⟩, _⟩ := aux
    apply left
    assumption
  · exact ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩


-- @@ L99-105 verbatim
theorem zero_in_Nat : ∅ ∈ Nat := by
  unfold Nat
  rw [mem_sInter]
  · intro x hx
    rw [mem_sep] at hx
    exact hx.right.left
  · exact ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩


-- @@ L107-107 verbatim
instance nat_zero : Zero ZFNat := ⟨∅, zero_in_Nat⟩

-- @@ L108-108 verbatim
lemma nat_zero_eq : (0 : ZFNat) = ⟨∅, zero_in_Nat⟩ := rfl


-- @@ L110-110 verbatim
instance nat_lt : LT ZFNat := ⟨fun x y => x.val ∈ y.val⟩

-- @@ L111-111 verbatim
instance nat_le : LE ZFNat := ⟨fun x y => x < y ∨ x = y⟩


-- @@ L113-113 verbatim
theorem not_lt_zero {n : ZFNat} : ¬ n < 0 := fun _ => notMem_empty _ ‹_›

-- @@ L114-118 verbatim
theorem zero_lt_ne_zero {n : ZFNat} : 0 < n → n ≠ 0 := by
  intro h h'
  subst h'
  absurd not_lt_zero h
  trivial


-- @@ L120-121 verbatim
/-- Any inductive set contains zero. -/
lemma zero_mem_inductive {a} (h : inductive_set a) : ↑(0 : ZFNat).val ∈ a := h.left


-- @@ L123-125 verbatim
/-- Any inductive set containing an element also contains its successor. -/
theorem insert_mem_inductive {a n} (h : inductive_set a) (h' : n ∈ a) : insert n n ∈ a :=
  h.right n h'


-- @@ L127-128 verbatim
private theorem some_inf_powerset_sep_inductive_nonempty : (some_inf.powerset.sep inductive_set).Nonempty :=
  ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩


-- @@ L130-147 verbatim
/-- Any inductive set is a subset of `some_inf`. -/
private theorem inductive_subset_some_inf_contains_Nat {a} (h : inductive_set a) (h' : a ⊆ some_inf) :
  Nat ⊆ a := by
  intro n hn
  unfold Nat at hn
  rw [mem_sInter] at hn
  · have aux :
      n ∈ (⋃₀ (powerset some_inf).sep inductive_set : ZFSet) ∧
      (fun b => ∀ c, c ∈ (powerset some_inf).sep inductive_set → b ∈ c) n := by
        simp only [mem_sUnion, mem_sep, and_imp] at *
        exact ⟨
          ⟨some_inf,
            ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩,
            hn some_inf (mem_powerset.mpr fun _ => id) (inductive_some_inf)⟩,
            fun _ _ _ => hn _ ‹_› ‹_›⟩
    simp only [mem_sep, mem_powerset, and_imp, mem_sUnion] at aux
    exact aux.2 _ h' h
  · exact some_inf_powerset_sep_inductive_nonempty


-- @@ L149-157 verbatim
theorem succ_mem_Nat' {n} (h : n ∈ Nat) : insert n n ∈ Nat := by
  have all_sub_ind : ∀ a, a ∈ some_inf.powerset.sep inductive_set → insert n n ∈ a := by
    intro a ha
    rw [mem_sep] at ha
    exact ha.2.2 n (inductive_subset_some_inf_contains_Nat ha.2 (mem_powerset.mp ha.1) h)
  unfold Nat
  rw [mem_sInter]
  · exact (all_sub_ind · ·)
  · exact some_inf_powerset_sep_inductive_nonempty


-- @@ L159-170 verbatim
/--
`Nat` is the least inductive set: it is contained in *every* inductive set, with no
restriction to subsets of `some_inf`.

This is the unrestricted form of `inductive_subset_some_inf_contains_Nat`; the extra
hypothesis `a ⊆ some_inf` is eliminated by intersecting `a` with `some_inf` first.
-/
theorem Nat_subset_of_inductive {a : ZFSet} (h : inductive_set a) : Nat ⊆ a := by
  have hb : inductive_set (some_inf.sep (· ∈ a)) :=
    inductive_sep _ inductive_some_inf h.left fun n _ hn => h.right n hn
  intro n hn
  exact mem_sep.mp (inductive_subset_some_inf_contains_Nat hb sep_subset_self hn) |>.right


-- @@ L172-192 verbatim
/--
The definition of `Nat` is independent of the witness granted by the axiom of infinity:
intersecting the inductive subsets of *any* inductive set `T` yields the same set `Nat`.

In particular `Nat = ⋂₀ ((powerset ω).sep inductive_set)`, so seeding the construction with
`some_inf` rather than `ω` is a choice without observable consequence.
-/
theorem Nat_eq_of_inductive {T : ZFSet} (hT : inductive_set T) :
    Nat = ⋂₀ ((powerset T).sep inductive_set) := by
  have Nat_ind : inductive_set Nat := ⟨zero_in_Nat, fun _ _ => succ_mem_Nat' ‹_›⟩
  have hne : ((powerset T).sep inductive_set).Nonempty :=
    ⟨T, mem_sep.mpr ⟨mem_powerset.mpr fun _ => id, hT⟩⟩
  ext n
  constructor
  · intro hn
    rw [mem_sInter hne]
    intro y hy
    exact Nat_subset_of_inductive (mem_sep.mp hy).right hn
  · intro hn
    rw [mem_sInter hne] at hn
    exact hn Nat <| mem_sep.mpr ⟨mem_powerset.mpr (Nat_subset_of_inductive hT), Nat_ind⟩


-- @@ L194-196 verbatim
private theorem mk_ofNat_mem_Nat : ∀ n : ℕ, mk (PSet.ofNat n) ∈ Nat
  | 0 => zero_in_Nat
  | n + 1 => succ_mem_Nat' (mk_ofNat_mem_Nat n)


-- @@ L198-209 expanded
/-- The least inductive set is Mathlib's `ω`: `Nat ⊆ ω` because `ω` is inductive, and every element
of `ω` is a finite von Neumann ordinal, reached from `∅` by successors, hence in `Nat`.
-/
theorem Nat_eq_omega : Nat = omega :=
  by
  refine ZFSet.ext fun x => ⟨fun hx => Nat_subset_of_inductive omega_inductive hx, fun hx => ?_⟩
  induction x using Quotient.inductionOn with
  | h x =>
    obtain ⟨⟨n⟩, h⟩ := hx
    change mk x ∈ Nat
    rw [ZFSet.sound h]
    exact mk_ofNat_mem_Nat n


-- @@ L211-218 verbatim
/--
The successor function `succ` is build from the insertion of a set into itself embedded into the
`ZFNat` type.
-/
@[expose] def succ (n : ZFNat) : ZFNat :=
  let ⟨n, h⟩ := n
  have p : insert n n ∈ Nat := succ_mem_Nat' h
  ⟨insert n n, p⟩


-- @@ L220-220 verbatim
instance nat_one : One ZFNat := ⟨succ 0⟩


-- @@ L222-222 verbatim
theorem nat_one_eq : 1 = succ 0 := rfl


-- @@ L224-228 verbatim
theorem succ_ne_zero : ∀ n, succ n ≠ 0 := by
  rintro ⟨n, hn⟩ h
  rw [succ, nat_zero_eq, Subtype.mk.injEq, ZFSet.ext_iff] at h
  simp only [mem_insert_iff, notMem_empty, iff_false, not_or] at h
  exact h n |>.1 rfl


-- @@ L230-245 verbatim
theorem succ_inj_aux {m n a : ZFSet} (h : insert m m = insert n n) (h' : a ∈ m) : a ∈ n := by
  have d' : a ∈ m ∨ a = m ↔ a ∈ n ∨ a = n := by
    have : a ∈ insert m m ↔ a ∈ n ∨ a = n := by
      rw [h, mem_insert_iff]
      exact Or.comm
    rw [mem_insert_iff, _root_.or_comm] at this
    assumption
  let h'' := mem_insert m m
  rw [h] at h''
  simp only [mem_insert_iff] at h''
  rcases h'' with rfl | h''
  · assumption
  · rcases d'.mp (Or.inl h') with _ | rfl
    · assumption
    · absurd mem_asymm h''
      assumption


-- @@ L247-248 verbatim
theorem succ_inj_aux' {m n : ZFSet} (h : insert m m = insert n n) : m = n :=
  ext fun _ => ⟨succ_inj_aux h, succ_inj_aux <| Eq.symm h⟩


-- @@ L250-255 verbatim
theorem succ_inj {m n} (h : succ m = succ n) : m = n := by
  let ⟨m, hm⟩ := m
  let ⟨n, hn⟩ := n
  simp only [succ, Subtype.mk.injEq] at *
  ext1
  exact ⟨succ_inj_aux h, succ_inj_aux (Eq.symm h)⟩


-- @@ L257-265 verbatim
/-- Any inductive set `a` separated by an inductive predicate `P` is inductive. -/
theorem sep_of_ind_is_ind (P : ZFSet → Prop) {a} (h : inductive_set a)
  (h₀ : P ∅) (ih : ∀ n, n ∈ a → P n → P (insert n n)) : inductive_set (a.sep P) := by
  unfold inductive_set at *
  apply And.intro
  · exact mem_sep.mpr ⟨h.left, h₀⟩
  · simp only [mem_sep, and_imp]
    intros
    exact ⟨h.right _ ‹_›, ih _ ‹_› ‹_›⟩


-- @@ L267-267 verbatim
/-! ## Recursion on natural numbers -/


-- @@ L269-269 verbatim
section Recursion


-- @@ L271-277 verbatim
theorem succ_subrelation_mem' :
  Subrelation (fun x y => insert x x = y) (fun x y : ZFSet => x ∈ y) := by
  intro _ _ _
  subst_eqs
  rw [mem_insert_iff]
  left
  rfl


-- @@ L279-282 verbatim
theorem succ_wf' : @WellFounded ZFSet (fun x y => insert x x = y) := by
  apply Subrelation.wf
  · exact succ_subrelation_mem'
  · exact mem_wf


-- @@ L284-289 verbatim
open Function in
theorem mem_wf' : @WellFounded ZFNat (·.1 ∈ ·.1) := by
  have : (fun x y : ZFNat => x.1 ∈ y.1) = ((fun x y : ZFSet => x ∈ y) on Subtype.val) := rfl
  rw [this]
  apply WellFounded.onFun
  exact mem_wf


-- @@ L291-298 verbatim
/-- The relation built over the successor function is a subrelation of the membership relation. -/
theorem succ_subrelation_mem : Subrelation (succ · = ·) (·.1 ∈ ·.1) := by
  intro _ _ _
  simp only [succ] at *
  subst_eqs
  rw [mem_insert_iff]
  left
  rfl


-- @@ L300-303 verbatim
theorem succ_wf : @WellFounded ZFNat (succ · = ·) := by
  apply Subrelation.wf
  · exact succ_subrelation_mem
  · exact mem_wf'


-- @@ L305-322 verbatim
/--
The induction principle for sets in `Nat`. This principle is meant to be used for definitional
purposes only.
-/
lemma ind {P : ZFSet → Prop} (n : ZFSet)
  (h : n ∈ Nat) (zero : P ∅) (succ : ∀ n ∈ Nat, P n → P (insert n n)) : P n := by
  have : Nat.sep P |>.inductive_set := by
    unfold inductive_set
    apply And.intro
    · exact mem_sep.mpr ⟨zero_in_Nat, ‹_›⟩
    · simp only [mem_sep, and_imp]
      intros
      exact ⟨succ_mem_Nat' ‹_›, succ _ ‹_› ‹_›⟩
  let p := inductive_subset_some_inf_contains_Nat this
  let p' := fun x (_ : x ∈ Nat.sep P) => Nat_subset_some_inf (ZFSet.sep_subset_self ‹_›)
  simp_rw [subset_def, mem_sep] at p
  simp only [mem_sep] at p'
  exact p p' h |>.right


-- @@ L324-338 verbatim
/-- The (weak) induction principle for natural numbers. -/
theorem induction {P : ZFNat → Prop} (n : ZFNat)
  (zero : P 0) (succ : ∀ n, P n → P (succ n)) : P n := by classical
  let ⟨n, hn⟩ := n
  let P' x := if hx : x ∈ Nat then P ⟨x, hx⟩ else PUnit
  have : P' n = P ⟨n, hn⟩ := dif_pos hn
  rw [← this]
  apply @ind P' n hn
  · unfold P'
    simpa [hn, zero_in_Nat, nat_zero_eq] using zero
  · intro m hm hm'
    unfold P' at *
    rw [dif_pos hm] at hm'
    rw [dif_pos <| succ_mem_Nat' hm]
    exact succ ⟨m, hm⟩ hm'


-- @@ L340-342 verbatim
@[cases_eliminator]
theorem cases {P : ZFNat → Prop} (n : ZFNat) (zero : P 0) (succ : ∀ n, P (succ n)) : P n :=
  induction n zero fun n _ => succ n


-- @@ L344-353 verbatim
theorem every_nat_transitive {n : ZFSet} (h : n ∈ Nat) : transitive n := by
  unfold transitive
  apply ind _ h
  · intros _ _
    exact False.elim (notMem_empty _ ‹_›)
  · intros _ _ ih _ hy _ _
    rw [mem_insert_iff] at hy ⊢
    rcases hy with rfl | _
    · exact Or.inr ‹_›
    · exact Or.inr (ih _ ‹_› ‹_›)


-- @@ L355-355 verbatim
theorem lt_succ {n : ZFNat} : n < succ n := mem_insert _ _

-- @@ L356-356 verbatim
theorem le_succ {n : ZFNat} : n ≤ succ n := Or.inl lt_succ


-- @@ L358-359 verbatim
theorem lt_trans {x y z : ZFNat} : x < y → y < z → x < z :=
  fun _ _ => every_nat_transitive z.2 _ ‹_› ‹_›


-- @@ L361-361 verbatim
theorem lt_irrefl {n : ZFNat} : ¬ n < n := fun _ => mem_irrefl _ ‹_›

-- @@ L362-365 verbatim
theorem lt_imp_ne {n m : ZFNat} : n < m → n ≠ m := fun _ _ => by
  subst_eqs
  absurd lt_irrefl ‹_›
  trivial


-- @@ L367-372 verbatim
theorem le_trans {x y z : ZFNat} : x ≤ y → y ≤ z → x ≤ z := by
  rintro (_ | rfl)  (_ | rfl)
  · left; exact lt_trans ‹_› ‹_›
  · left; assumption
  · left; assumption
  · right; rfl


-- @@ L374-380 verbatim
theorem le_antisymm {x y : ZFNat} : x ≤ y → y ≤ x → x = y := by
  rintro (h | rfl) (_ | _)
  · absurd lt_irrefl <| lt_trans ‹_› ‹_›
    trivial
  · symm; assumption
  · trivial
  · trivial


-- @@ L382-394 verbatim
theorem lt_le_iff {n m} : n ≤ m ↔ n < succ m := by
  apply Iff.intro
  · rintro (_ | rfl)
    · exact lt_trans ‹_› lt_succ
    · exact lt_succ
  · intro h
    let ⟨n, hn⟩ := n
    let ⟨m, hm⟩ := m
    dsimp [LT.lt, nat_lt, succ] at *
    rw [mem_insert_iff] at h
    rcases h with rfl | _
    · right; rfl
    · left; assumption


-- @@ L396-405 verbatim
theorem lt_mono {x y : ZFNat} : x < y → x.succ < y.succ := by
  intro h
  induction y using induction with
  | zero =>
    absurd not_lt_zero h
    trivial
  | succ y ih =>
    rcases lt_le_iff.mpr h with (h | rfl)
    · exact lt_trans (ih h) lt_succ
    · exact lt_succ


-- @@ L407-419 verbatim
theorem succ_lt_mono {x y : ZFNat} : succ x < succ y → x < y := by
  intro h
  induction y using induction with
  | zero =>
    rcases lt_le_iff.mpr h with (h | h)
    · absurd not_lt_zero h; trivial
    · absurd succ_ne_zero x h; trivial
  | succ y ih =>
    rcases lt_le_iff.mpr h with (h | h)
    · exact lt_trans (ih h) lt_succ
    · replace h := succ_inj h
      subst h
      exact lt_succ


-- @@ L421-432 verbatim
theorem le_mono {x y : ZFNat} : x ≤ y → x.succ ≤ y.succ := by
  rintro (h | rfl)
  · left
    induction y using induction with
    | zero =>
      absurd not_lt_zero h
      trivial
    | succ y ih =>
      rcases lt_le_iff.mpr h with (h | rfl)
      · exact lt_trans (ih h) lt_succ
      · exact lt_succ
  · right; rfl


-- @@ L434-446 verbatim
theorem succ_le_mono {x y : ZFNat} : x.succ ≤ y.succ → x ≤ y := by
  rintro (h | h)
  · left
    induction y using induction with
    | zero =>
      rcases lt_le_iff.mpr h with (h | h)
      · absurd not_lt_zero h; trivial
      · absurd succ_ne_zero x h; trivial
    | succ y ih =>
      rcases lt_le_iff.mpr h with (h | h)
      · exact lt_trans (ih h) lt_succ
      · rw [← h]; exact lt_succ
  · replace h := succ_inj h; subst h; right; rfl


-- @@ L448-452 verbatim
theorem le_lt_iff {n m} : succ n ≤ m ↔ n < m := by
  rw [lt_le_iff]
  apply Iff.intro
  · intro; exact succ_lt_mono ‹_›
  · exact lt_mono


-- @@ L454-484 verbatim
theorem le_total {x y : ZFNat} : x ≤ y ∨ y ≤ x := by
  induction x using induction with
  | zero =>
    left
    induction y using induction with
    | zero => right; rfl
    | succ _ ih => exact le_trans ih (le_succ)
  | succ x ih =>
    induction y using induction with
    | zero =>
      rcases ih with ((h | _) | (_ | _))
      · absurd not_lt_zero h; trivial
      · subst_eqs; right; exact le_succ
      · right; left; exact lt_trans ‹_› lt_succ
      · subst_eqs; right; left; exact lt_succ
    | succ y ih' =>
      rcases ih with (h | _) | (h | _)
      · rcases ih' (Or.inl <| lt_le_iff.mpr h) with l | (r | rfl)
        · left; left; exact lt_le_iff.mp l
        · right; right; congr; exact le_antisymm (lt_le_iff.mpr r) (lt_le_iff.mpr h)
        · replace h := lt_le_iff.mpr h
          left
          apply le_mono
          exact h
      · subst_eqs; right; exact le_succ
      · right
        simp only [lt_le_iff]
        exact lt_trans (lt_trans h lt_succ) lt_succ
      · subst_eqs
        right
        exact le_succ


-- @@ L486-498 verbatim
theorem lt_iff_le_not_ge {x y : ZFNat} : x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  apply Iff.intro
  · intro
    apply And.intro
    · left
      assumption
    · rintro (_ | rfl)
      · exact lt_irrefl (lt_trans ‹_› ‹_›)
      · exact lt_irrefl ‹_›
  · rintro ⟨h | rfl, h'⟩
    · assumption
    · simp only [LE.le, or_true] at h'
      contradiction


-- @@ L500-520 verbatim
/-- The (strong) induction principle for natural numbers. -/
theorem strong_induction {P : ZFNat → Prop} (n : ZFNat)
  (ind : ∀ n, (∀ m, m < n → P m) → P n) : P n := by
  let Q x := ∀ m < x, P m
  have aux {x} : Q x := by
    induction x using induction with
    | zero =>
      intros _ _
      exact False.elim (not_lt_zero ‹_›)
    | succ n ih =>
      intros m hm
      unfold Q at ih
      by_cases h : m = n
      · subst h
        exact ind _ ih
      · have h' : m < n := by
          rcases lt_le_iff.mpr hm with (_ | rfl)
          · assumption
          · contradiction
        exact ih m h'
  exact ind _ aux


-- @@ L522-530 verbatim
theorem mem_Nat_of_mem_mem_Nat {n m : ZFSet} (hn : n ∈ Nat) : m ∈ n → m ∈ Nat := by
  apply ZFNat.ind n hn
  · intro h
    nomatch notMem_empty m h
  · intro n hn ih hm
    rw [mem_insert_iff] at hm
    rcases hm with rfl | hm
    · exact hn
    · exact ih hm


-- @@ L532-537 verbatim
theorem not_zero_imp_succ {n : ZFNat} : n ≠ 0 → ∃ m, n = succ m := by
  induction n using induction with
  | zero => intro h; contradiction
  | succ n _ =>
    intro
    exact exists_apply_eq_apply' succ n


-- @@ L539-547 verbatim
lemma sUnion_insert_nat {x : ZFSet} (h : x ∈ Nat) : (⋃₀ (insert x x) : ZFSet) = x := by
  apply ind _ h
  · rw [sUnion_insert, sUnion_empty]
    ext1
    simp only [mem_union, notMem_empty, or_self]
  · intros n _ ih
    rw [sUnion_insert, ih]
    ext1
    simp only [mem_union, mem_insert_iff, or_self_right]


-- @@ L549-554 verbatim
theorem pred_in_Nat' ⦃x : ZFSet⦄ (h : x ∈ Nat) : (⋃₀ x : ZFSet) ∈ Nat := by
  apply ind _ h
  · rw [sUnion_empty]
    exact zero_in_Nat
  · intros
    rw [sUnion_insert_nat] <;> assumption


-- @@ L556-557 verbatim
/-- The predecessor function on natural numbers, defined directly as the union of a set. -/
@[expose] def pred (x : ZFNat) : ZFNat := x.map sUnion pred_in_Nat'


-- @@ L559-559 verbatim
theorem pred_eq (n : ZFNat) : pred n = ⟨⋃₀ n.val, pred_in_Nat' n.property⟩ := rfl


-- @@ L561-564 verbatim
@[simp]
theorem pred_zero : pred 0 = 0 := by
  unfold pred
  rw [nat_zero_eq, Subtype.map, Subtype.mk.injEq, sUnion_empty]


-- @@ L566-571 verbatim
@[simp]
theorem pred_one : pred 1 = 0 := by
  unfold pred
  rw [nat_one_eq, nat_zero_eq, Subtype.map, Subtype.mk.injEq]
  dsimp [succ]
  rw [LawfulSingleton.insert_empty_eq, sUnion_singleton]


-- @@ L573-578 verbatim
@[simp]
theorem pred_succ {n : ZFNat} : pred (succ n) = n := by
  let ⟨_, _⟩ := n
  simp only [pred, succ, Subtype.map]
  congr
  exact sUnion_insert_nat ‹_›


-- @@ L580-586 verbatim
@[simp]
theorem succ_pred {n : ZFNat} (h : n ≠ 0) : succ (pred n) = n := by
  induction n using strong_induction with
  | ind n ih =>
    obtain ⟨m, hm⟩ := not_zero_imp_succ h
    subst hm
    by_cases h' : m = 0 <;> subst_eqs <;> rw [pred_succ]


-- @@ L588-588 verbatim
private theorem succ_lift_eq {x : ZFNat} : ↑(succ x) = insert x.val x.val := by rfl


-- @@ L590-591 verbatim
private theorem succ_eq (n : ZFSet) (n_Nat : n ∈ Nat) :
  ⟨insert n n, succ_mem_Nat' n_Nat⟩ = succ ⟨n, n_Nat⟩ := by rfl


-- @@ L593-609 verbatim
/--
The recursion principle for sets in `Nat`. This principle is meant to be used for definitional
purposes only.
-/
def rec'.{u} {motive : ZFSet → Sort u} (n : ZFSet) (h : n ∈ Nat)
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) : motive n := by
  apply succ_wf.fix (C := fun x => motive x.val) (x := ⟨n, h⟩)
  intro x ih
  by_cases x_eq_0 : x = 0
  · subst x_eq_0
    exact zero
  · specialize ih _ (succ_pred x_eq_0)
    specialize succ (pred x) (pred x).2 ih
    conv at succ =>
      arg 1
      rw [← succ_lift_eq, succ_pred x_eq_0]
    assumption


-- @@ L611-618 verbatim
/-- Provides the base case of the recursion principle for sets in `Nat`. -/
theorem rec'_zero.{u} {motive : ZFSet → Sort u}
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) :
  ZFNat.rec' ∅ zero_in_Nat zero succ = zero := by
    unfold ZFNat.rec' WellFounded.fix
    beta_reduce
    rw [WellFounded.fixF_eq, dite_cond_eq_true]
    exact eq_self _



-- @@ L621-643 verbatim
/-- Provides the inductive step of the recursion principle for sets in `Nat`. -/
theorem rec'_succ.{u} {motive : ZFSet → Sort u} (n : ZFSet) (n_Nat : n ∈ Nat)
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) :
  rec' (insert n n) (succ_mem_Nat' n_Nat) zero succ = succ n n_Nat (rec' n n_Nat zero succ) := by
    unfold ZFNat.rec' WellFounded.fix
    beta_reduce
    rw [WellFounded.fixF_eq, dite_cond_eq_false]
    · apply cast_eq_iff_heq.mpr
      · congr
        · conv => enter [1, 1]; rw [succ_eq _ n_Nat, pred_succ]
        · exact proof_irrel_heq ..
        · conv =>
            left
            conv => arg 1; rw [succ_eq _ n_Nat]
            rw [pred_succ]
        · exact proof_irrel_heq ..
        · apply succ_pred
          rw [succ_eq _ n_Nat]
          exact succ_ne_zero _
      · apply eq_false
        intro h
        rw [succ_eq _ n_Nat] at h
        exact succ_ne_zero _ h


-- @@ L645-662 verbatim
/--
The recursion principle for natural numbers. This recursor allows inductive
definitions over natural numbers to be defined in a more natural way.
-/
@[induction_eliminator, expose] def rec.{u} {motive : ZFNat → Sort u} (n : ZFNat)
  (zero : motive 0) (succ : Π x, motive x → motive (succ x)) : motive n := by classical
  let ⟨n, hn⟩ := n
  let motive' (x : ZFSet) := if hx : x ∈ Nat then motive ⟨x, hx⟩ else PUnit
  have : motive' n = motive ⟨n, hn⟩ := dif_pos hn
  rw [← this]
  apply @ZFNat.rec' motive' n hn
  · unfold motive'
    simpa [hn, zero_in_Nat, nat_zero_eq] using zero
  · intro m hm hm'
    unfold motive' at *
    rw [dif_pos hm] at hm'
    rw [dif_pos <| succ_mem_Nat' hm]
    exact succ ⟨m, hm⟩ hm'


-- @@ L664-669 verbatim
/--
The induction principle of `ZFNat` is a universe-specialized version of the recursion principle.
-/
@[simp]
theorem induction_is_rec_into_Prop {motive : ZFNat → Prop} :
  induction = ZFNat.rec (motive := motive) := rfl


-- @@ L671-673 verbatim
theorem rec_zero.{u} {motive : ZFNat → Sort u}
  (zero : motive 0) (succ : Π x, motive x → motive (succ x)) :
  rec 0 zero succ = zero := by conv => arg 1; simp [ZFNat.rec, ZFNat.rec'_zero]


-- @@ L675-680 verbatim
theorem rec_succ.{u} {motive : ZFNat → Sort u} (n : ZFNat)
  (zero : motive 0) (succ' : Π x, motive x → motive (succ x)) :
  rec (succ n) zero succ' = succ' n (ZFNat.rec n zero succ') := by
    simp only [succ, rec, eq_mpr_eq_cast, id_eq, eq_mp_eq_cast, ZFNat.rec'_succ _ n.property,
      SetLike.eta, dite_eq_ite]
    exact eq_of_heq (HEq.trans (cast_heq _ _) (cast_heq _ _))


-- @@ L682-695 verbatim
/--
Uniqueness half of the universal property of `ZFNat`: `ZFNat.rec` is the *only* family
satisfying the two computation rules `rec_zero` and `rec_succ`.

Together with `rec_zero`/`rec_succ` this says that `(ZFNat, 0, succ)` is initial among
sets equipped with a point and an endomorphism.
-/
theorem rec_unique.{u} {motive : ZFNat → Sort u} (zero : motive 0)
  (succ' : Π x, motive x → motive (succ x)) (f : Π x, motive x)
  (h₀ : f 0 = zero) (hs : ∀ x, f (succ x) = succ' x (f x)) (n : ZFNat) :
    f n = ZFNat.rec n zero succ' := by
  induction n using ZFNat.rec with
  | zero => rw [h₀, rec_zero]
  | succ n ih => rw [hs, rec_succ, ih]


-- @@ L697-697 verbatim
end Recursion


-- @@ L699-703 verbatim
/--
The predecessor function `pred'` on natural numbers, defined inductively.
This definition is equivalent to `pred`, as proven by `pred'_eq_pred`.
-/
protected abbrev pred' (m : ZFNat) : ZFNat := ZFNat.rec m 0 (fun x _ : ZFNat => x)


-- @@ L705-710 verbatim
/-- The definitions of `pred` and `pred'` are equivalent. -/
lemma pred'_eq_pred : pred = ZFNat.pred' := by
  ext1 n
  induction n with
  | zero => rw [pred_zero, ZFNat.pred', ZFNat.rec_zero]
  | succ _ _ => rw [pred_succ, ZFNat.pred', ZFNat.rec_succ]


-- @@ L712-712 verbatim
/-! ## Arithmetic -/


-- @@ L714-714 verbatim
section Inequalities


-- @@ L716-719 verbatim
theorem zero_lt_succ {n : ZFNat} : 0 < n.succ := by
  induction n with
  | zero => exact lt_succ
  | succ n ih => exact lt_trans ih lt_succ


-- @@ L721-726 verbatim
theorem pos_of_ne_zero {n : ZFNat} : 0 ≠ n → 0 < n := by
  induction n with
  | zero => intro h; nomatch h
  | succ x ih =>
    intro
    exact zero_lt_succ


-- @@ L728-732 verbatim
instance : Preorder ZFNat where
  le := nat_le.le
  le_trans _ _ _ := le_trans
  le_refl _ := Or.inr rfl
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge


-- @@ L734-740 verbatim
instance : LinearOrder ZFNat where
  le_refl _ := Or.inr rfl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total _ _ := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable ((· ≤ ·) _ _)
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge


-- @@ L742-750 verbatim
instance : IsStrictTotalOrder ZFNat (·<·) where
  trichotomous x y := by
    intros h₁ h₂
    rcases @le_total x y with (h | rfl) | h | rfl <;>
    first
    | contradiction
    | rfl
  irrefl _ := lt_irrefl
  trans _ _ _ := lt_trans


-- @@ L752-752 verbatim
end Inequalities


-- @@ L754-754 verbatim
section Arithmetic


-- @@ L756-757 verbatim
/-- The addition function on natural numbers, defined inductively. -/
protected abbrev add (n m : ZFNat) : ZFNat := ZFNat.rec n m (fun _ : ZFNat => succ)


-- @@ L759-759 verbatim
instance add_inst : Add ZFNat := ⟨ZFNat.add⟩

-- @@ L760-760 verbatim
lemma add_inst_eq {n m : ZFNat} : n + m = n.add m := rfl


-- @@ L762-766 verbatim
lemma add_one_eq_succ {n : ZFNat} : n + 1 = succ n := by
  dsimp [add_inst_eq]
  induction n with
  | zero => rw [ZFNat.add, ZFNat.rec_zero, nat_one_eq]
  | succ _ ih => rw [ZFNat.add, ZFNat.rec_succ, ← ZFNat.add, ih]


-- @@ L768-769 verbatim
lemma add_one_eq_succ' {n : ZFNat} : 1 + n = succ n := by
  rw [add_inst_eq, ZFNat.add, nat_one_eq, rec_succ, rec_zero]


-- @@ L771-776 verbatim
@[simp]
lemma add_zero {n : ZFNat} : n + 0 = n := by
  dsimp [add_inst_eq]
  induction n with
  | zero => rw [ZFNat.add, rec_zero]
  | succ _ ih => rw [ZFNat.add, rec_succ, ← ZFNat.add, ih]


-- @@ L778-780 verbatim
@[simp]
lemma zero_add {n : ZFNat} : 0 + n = n := by
  rw [add_inst_eq, ZFNat.add, rec_zero]


-- @@ L782-782 verbatim
lemma add_succ {n m : ZFNat} : succ n + m = succ (n + m) := rec_succ n m fun _ => succ


-- @@ L784-790 verbatim
lemma succ_add {n m : ZFNat} : succ (n + m) = n + succ m := by
  induction n with
  | zero => rw [add_inst_eq, add_inst_eq, ZFNat.add, rec_zero, ZFNat.add, rec_zero]
  | succ n ih =>
    rw [add_succ, ih]
    dsimp [add_inst_eq]
    conv => rhs; rw [ZFNat.add, rec_succ]


-- @@ L792-795 verbatim
lemma add_comm (n m : ZFNat) : n + m = m + n := by
  induction n with
  | zero => rw [add_zero, add_inst_eq, ZFNat.add, rec_zero]
  | succ n ih => rw [← succ_add, add_succ, ih]


-- @@ L797-801 verbatim
@[simp]
lemma add_assoc (n m k : ZFNat) : n + (m + k) = n + m + k := by
  induction n with
  | zero => rw [zero_add, zero_add]
  | succ _ ih => rw [add_succ, add_succ, add_succ, ih]


-- @@ L803-804 verbatim
lemma add_left_comm (n m k : ZFNat) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]


-- @@ L806-807 verbatim
lemma add_right_comm (n m k : ZFNat) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]


-- @@ L809-818 verbatim
theorem add_left_cancel {n m k : ZFNat} : n + m = n + k ↔ m = k := by
  induction n with
  | zero => simp only [zero_add]
  | succ n ih =>
    simp_rw [add_succ]
    apply Iff.intro
    · intro h
      exact ih.mp (succ_inj h)
    · intro h
      rw [h]


-- @@ L820-822 verbatim
theorem add_right_cancel {n m k : ZFNat} : n + m = k + m ↔ n = k := by
  rw [add_comm n, add_comm k]
  exact add_left_cancel


-- @@ L824-832 verbatim
theorem eq_zero_of_add_eq_zero : ∀ {n m : ZFNat}, n + m = 0 → n = 0 ∧ m = 0 := by
  intro n m
  induction n generalizing m with
  | zero => simp only [zero_add, true_and, imp_self]
  | succ n ih =>
    intro h
    rw [add_succ, succ_add] at h
    absurd succ_ne_zero m (ih h).right
    trivial


-- @@ L834-835 verbatim
theorem eq_zero_of_add_eq_zero_left {n m : ZFNat} (h : n + m = 0) : m = 0 :=
  eq_zero_of_add_eq_zero h |>.right


-- @@ L837-839 verbatim
@[simp] theorem add_left_eq_self {a b : ZFNat} : a + b = b ↔ a = 0 := by
  conv => lhs; rhs; rw [← @zero_add b]
  rw [add_right_cancel]

-- @@ L840-842 verbatim
@[simp] theorem add_right_eq_self {a b : ZFNat} : a + b = a ↔ b = 0 := by
  conv => lhs; rhs; rw [← @add_zero a]
  rw [add_left_cancel]

-- @@ L843-846 verbatim
@[simp] theorem self_eq_add_right {a b : ZFNat} : a = a + b ↔ b = 0 := by
  conv => lhs; lhs; rw [← @add_zero a]
  rw [add_left_cancel]
  exact eq_comm

-- @@ L847-850 verbatim
@[simp] theorem self_eq_add_left {a b : ZFNat} : a = b + a ↔ b = 0 := by
  conv => lhs; lhs; rw [← @zero_add a]
  rw [add_right_cancel]
  exact eq_comm


-- @@ L852-852 verbatim
theorem lt_of_succ_le {n m : ZFNat} (h : succ n ≤ m) : n < m := le_lt_iff.mp ‹_›

-- @@ L853-853 verbatim
theorem succ_le_of_lt {n m : ZFNat} (h : n < m) : succ n ≤ m := le_lt_iff.mpr ‹_›


-- @@ L855-871 verbatim
theorem le.dest {n m : ZFNat} : n ≤ m → ∃ k, n + k = m := by
  intro h
  induction n with
  | zero => exact ⟨m, zero_add⟩
  | succ n ih =>
    rcases h with h | rfl
    · have : n < m := by
        apply lt_trans (lt_succ)
        assumption
      let ⟨k, hk⟩ := ih (Or.inl this)
      exact ⟨pred k, by
        rwa [← add_one_eq_succ, ← add_assoc, add_one_eq_succ', ZFNat.succ_pred]
        intro
        subst_eqs
        rw [add_zero] at this
        exact lt_irrefl this⟩
    · exact ⟨0, add_zero⟩


-- @@ L873-873 verbatim
theorem le_succ_of_le {n m : ZFNat} (h : n ≤ m) : n ≤ succ m := le_trans h le_succ


-- @@ L875-880 verbatim
@[simp] theorem le_add_right (n k : ZFNat) : n ≤ n + k := by
  induction k with
  | zero => rw [add_zero]
  | succ _ ih =>
    rw [add_comm, add_succ, ← add_comm]
    exact le_succ_of_le ih


-- @@ L882-882 verbatim
@[simp] theorem le_add_left (n m : ZFNat) : n ≤ m + n := add_comm .. ▸ le_add_right ..


-- @@ L884-884 verbatim
theorem le.intro {n m k : ZFNat} (h : n + k = m) : n ≤ m := h ▸ le_add_right n k


-- @@ L886-889 verbatim
theorem zero_le {n : ZFNat} : 0 ≤ n := by
  induction n with
  | zero => right; rfl
  | succ n ih => exact le_trans ih le_succ


-- @@ L891-896 verbatim
theorem le_of_add_le_add_left {a b c : ZFNat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [← add_assoc] at hd
    exact add_left_cancel.mp hd


-- @@ L898-902 verbatim
theorem add_le_add_left {n m : ZFNat} (h : n ≤ m) (k : ZFNat) : k + n ≤ k + m :=
  match le.dest h with
  | ⟨w, hw⟩ =>
    have : k + (n + w) = k + m     := congrArg _ hw
    le.intro <| (Eq.symm <| add_assoc k n w).trans this


-- @@ L904-905 verbatim
@[simp] theorem add_le_add_iff_left {n m k : ZFNat} : n + m ≤ n + k ↔ m ≤ k :=
  ⟨le_of_add_le_add_left, fun h => add_le_add_left h _⟩


-- @@ L907-914 verbatim
theorem lt_of_add_lt_add_right {n m k : ZFNat} : k + n < m + n → k < m := by
  induction n with
  | zero => simp_rw [add_zero]; exact id
  | succ n ih =>
    simp_rw [← succ_add]
    intro h
    apply succ_lt_mono at h
    exact ih h


-- @@ L916-917 verbatim
theorem add_lt_add_left {n m : ZFNat} (h : n < m) (k : ZFNat) : k + n < k + m :=
  lt_of_succ_le <| succ_add ▸ add_le_add_left (succ_le_of_lt h) k


-- @@ L919-920 verbatim
theorem add_lt_add_right {n m : ZFNat} (h : n < m) (k : ZFNat) : n + k < m + k :=
  add_comm k m ▸ add_comm k n ▸ add_lt_add_left h k


-- @@ L922-924 verbatim
theorem lt_add_of_pos_right {n k : ZFNat} (h : 0 < k) : n < n + k := by
  let this := add_zero ▸ add_lt_add_left h n;
  exact this


-- @@ L926-927 verbatim
theorem lt_of_add_lt_add_left {n m k : ZFNat} : n + k < n + m → k < m := by
  rw [add_comm n, add_comm n]; exact lt_of_add_lt_add_right


-- @@ L929-930 verbatim
@[simp] theorem add_lt_add_iff_left {k n m : ZFNat} : k + n < k + m ↔ n < m :=
  ⟨lt_of_add_lt_add_left, fun _ => add_lt_add_left ‹_› _⟩


-- @@ L932-933 verbatim
@[simp] theorem add_lt_add_iff_right {k n m : ZFNat} : n + k < m + k ↔ n < m :=
  ⟨lt_of_add_lt_add_right, fun _ => add_lt_add_right ‹_› _⟩


-- @@ L935-936 verbatim
theorem add_le_add_right {n m : ZFNat} (h : n ≤ m) (k : ZFNat) : n + k ≤ m + k :=
  add_comm .. ▸ add_comm m k ▸ add_le_add_left h k


-- @@ L938-939 verbatim
theorem add_lt_add_of_le_of_lt {a b c d : ZFNat} (hle : a ≤ b) (hlt : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right hle _) (add_lt_add_left hlt _)


-- @@ L941-942 verbatim
theorem add_lt_add_of_lt_of_le {a b c d : ZFNat} (hlt : a < b) (hle : c ≤ d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_left hle _) (add_lt_add_right hlt _)


-- @@ L944-945 verbatim
theorem lt_add_of_pos_left {k n : ZFNat} : 0 < k → n < k + n :=
  add_comm .. ▸ lt_add_of_pos_right


-- @@ L947-950 verbatim
theorem pos_of_lt_add_right {n k : ZFNat} (h : n < n + k) : 0 < k := by
  apply lt_of_add_lt_add_left
  rw [add_zero]
  assumption


-- @@ L952-953 verbatim
theorem pos_of_lt_add_left {n k : ZFNat} : n < k + n → 0 < k := by
  rw [add_comm]; exact pos_of_lt_add_right


-- @@ L955-956 verbatim
@[simp] theorem lt_add_right_iff_pos {n k : ZFNat} : n < n + k ↔ 0 < k :=
  ⟨pos_of_lt_add_right, lt_add_of_pos_right⟩


-- @@ L958-959 verbatim
@[simp] theorem lt_add_left_iff_pos {n k : ZFNat} : n < k + n ↔ 0 < k :=
  ⟨pos_of_lt_add_left, lt_add_of_pos_left⟩


-- @@ L961-962 verbatim
theorem add_pos_left {m : ZFNat} (h : 0 < m) (n : ZFNat) : 0 < m + n :=
  lt_of_lt_of_le h (le_add_right ..)


-- @@ L964-965 verbatim
theorem add_pos_right {n : ZFNat} (m : ZFNat) (h : 0 < n) : 0 < m + n :=
  lt_of_lt_of_le h (le_add_left ..)


-- @@ L967-981 verbatim
theorem pred_le_pred {n m : ZFNat} : n ≤ m → (pred n) ≤ (pred m) := by
  intro h
  induction n <;> induction m
  · right; rfl
  · simp only [pred_zero, pred_succ]
    rcases h with (_ | _)
    · exact lt_le_iff.mpr ‹_›
    · absurd (succ_ne_zero _ (Eq.symm ‹_›))
      trivial
  · rcases h with (h | h)
    · absurd not_lt_zero h
      trivial
    · rw [h]
  · simp only [pred_succ]
    exact succ_le_mono h


-- @@ L983-987 verbatim
theorem le_of_succ_le_succ {n m : ZFNat} : (succ n) ≤ (succ m) → n ≤ m := by
  intro h
  replace h := pred_le_pred h
  simp only [pred_succ] at h
  assumption


-- @@ L989-994 verbatim
theorem lt_of_succ_lt_succ {n m : ZFNat} : succ n < succ m → n < m := by
  intro h
  rcases le_of_succ_le_succ (Or.inl h) with (h | rfl)
  · assumption
  · absurd lt_irrefl h
    trivial


-- @@ L996-1006 verbatim
theorem add_self_ne_one {n : ZFNat} : n + n ≠ 1 := by
  intro h
  induction n with
  | zero =>
    simp only [zero_add, nat_one_eq] at h
    absurd succ_ne_zero _ (Eq.symm h)
    trivial
  | succ n _ =>
    rw [add_succ, ← succ_add, nat_one_eq] at h
    absurd succ_ne_zero _ (succ_inj h)
    trivial


-- @@ L1008-1008 verbatim
protected abbrev sub (n m : ZFNat) : ZFNat := ZFNat.rec m n (fun _ => pred)

-- @@ L1009-1009 verbatim
instance sub_inst : Sub ZFNat := ⟨ZFNat.sub⟩

-- @@ L1010-1010 verbatim
lemma sub_inst_eq {n m : ZFNat} : n - m = n.sub m := rfl


-- @@ L1012-1014 verbatim
@[simp]
theorem sub_zero {n : ZFNat} : n - 0 = n := by
  rw [sub_inst_eq, ZFNat.sub, ZFNat.rec_zero]


-- @@ L1016-1017 verbatim
theorem sub_one_eq_pred {n : ZFNat} : n - 1 = pred n := by
  rw [sub_inst_eq, ZFNat.sub, nat_one_eq, ZFNat.rec_succ, ZFNat.rec_zero]


-- @@ L1019-1020 verbatim
theorem succ_mono {n m : ZFNat} : n < m ↔ succ n < succ m :=
  ⟨lt_mono, lt_of_succ_lt_succ⟩


-- @@ L1022-1024 verbatim
theorem sub_succ (n m : ZFNat) : n - succ m = pred (n - m) := by
  rw [sub_inst_eq, ZFNat.sub, ZFNat.rec_succ, ← ZFNat.sub]
  rfl


-- @@ L1026-1030 verbatim
@[simp]
theorem zero_sub {n : ZFNat} : 0 - n = 0 := by
  induction n with
  | zero => rw [sub_zero]
  | succ n ih => rw [sub_succ, ih, pred_zero]


-- @@ L1032-1035 verbatim
theorem succ_sub_succ (n m : ZFNat) : succ n - succ m = n - m := by
  induction m with
  | zero      => rw [← nat_one_eq, sub_one_eq_pred, pred_succ, sub_zero]
  | succ m ih => rw [sub_succ, ih, ← sub_succ]


-- @@ L1037-1040 verbatim
theorem succ_sub_self (n : ZFNat) : succ n - n = 1 := by
  induction n with
  | zero => rw [sub_zero, nat_one_eq]
  | succ n ih => rw [succ_sub_succ, ih]


-- @@ L1042-1045 verbatim
theorem sub_self {n : ZFNat} : n - n = 0 := by
  induction n with
  | zero => rw [sub_zero]
  | succ n _ => rw [sub_succ, succ_sub_self, pred_one]


-- @@ L1047-1050 verbatim
theorem sub_add_distrib {n m k : ZFNat} : n - (m + k) = n - m - k := by
  induction k with
  | zero => rw [add_zero, sub_zero]
  | succ k ih => rw [← succ_add, sub_succ, ih, ← sub_succ]


-- @@ L1052-1059 verbatim
theorem sub_ne_zero_of_lt {a b : ZFNat} : a < b → b - a ≠ 0 := by
  intro h
  induction a generalizing b with
  | zero => rw [sub_zero]; exact zero_lt_ne_zero h
  | succ a ih =>
    induction b with
    | zero => exact absurd h not_lt_zero
    | succ b _ => rw [succ_sub_succ]; exact ih <| succ_mono.mpr h


-- @@ L1061-1061 verbatim
theorem le_of_succ_le {n m : ZFNat} (_ : succ n ≤ m) : n ≤ m := le_trans le_succ ‹_›

-- @@ L1062-1065 verbatim
theorem lt_of_succ_lt {n m : ZFNat} (h : succ n < m) : n < m := by
  rcases le_of_succ_le (.inl h) with (h | rfl)
  · assumption
  · absurd lt_irrefl (lt_trans lt_succ h); trivial

-- @@ L1066-1066 verbatim
theorem le_of_lt {n m : ZFNat} : n < m → n ≤ m := Or.inl


-- @@ L1068-1076 verbatim
theorem add_sub_of_le {a b : ZFNat} (h : a ≤ b) : a + (b - a) = b := by
  induction a with
  | zero => rw [sub_zero, zero_add]
  | succ a ih =>
    have hne : b - a ≠ 0 := by
      apply sub_ne_zero_of_lt
      exact lt_of_succ_le ‹_›
    have : a ≤ b := le_of_succ_le ‹_›
    rw [sub_succ, add_succ, succ_add, succ_pred hne, ih this]


-- @@ L1078-1081 verbatim
theorem sub_one_cancel {a b : ZFNat} : 0 < a → 0 < b → a - 1 = b - 1 → a = b := by
  intro ha hb h
  rw [← succ_pred (zero_lt_ne_zero ha), ← succ_pred (zero_lt_ne_zero hb)]
  simpa only [← sub_one_eq_pred, ← add_one_eq_succ, add_right_cancel]


-- @@ L1083-1085 verbatim
@[simp]
theorem sub_add_cancel {n m : ZFNat} (h : m ≤ n) : n - m + m = n := by
  rw [add_comm, add_sub_of_le h]


-- @@ L1087-1090 verbatim
theorem add_sub_add_right (n k m : ZFNat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => simp_rw [add_zero]
  | succ k ih => rwa [← succ_add, ← succ_add, succ_sub_succ]


-- @@ L1092-1093 verbatim
theorem add_sub_add_left (k n m : ZFNat) : (k + n) - (k + m) = n - m := by
  rw [add_comm k n, add_comm k m, add_sub_add_right]


-- @@ L1095-1097 verbatim
@[simp] theorem add_sub_cancel (n m : ZFNat) : n + m - m = n :=
  suffices n + m - (0 + m) = n by rw [zero_add] at this; assumption
  by rw [add_sub_add_right, sub_zero]


-- @@ L1099-1101 verbatim
theorem add_sub_cancel_left (n m : ZFNat) : n + m - n = m := by
  have : n + m - (n + 0) = m := by rw [add_sub_add_left, sub_zero]
  rwa [add_zero] at this


-- @@ L1103-1105 verbatim
theorem add_sub_assoc {m k : ZFNat} (h : k ≤ m) (n : ZFNat) : n + m - k = n + (m - k) := by
 rcases le.dest h with ⟨l, rfl⟩
 rw [add_assoc, add_comm n, ← add_assoc, add_sub_cancel_left k, add_comm k, add_sub_cancel]


-- @@ L1107-1108 verbatim
theorem eq_add_of_sub_eq {a b c : ZFNat} (hle : b ≤ a) (h : a - b = c) : a = c + b := by
  rw [h.symm, sub_add_cancel hle]


-- @@ L1110-1111 verbatim
theorem sub_eq_of_eq_add {a b c : ZFNat} (h : a = c + b) : a - b = c := by
  rw [h, add_sub_cancel]


-- @@ L1113-1117 verbatim
theorem add_eq_add_sub_eq_sub {a b c d : ZFNat} : a + b = c + d → a - c = d - b := by
  intro h
  have : a = c + d - b := ZFNat.sub_eq_of_eq_add h.symm |>.symm
  subst this
  rw [←ZFNat.sub_add_distrib, ZFNat.add_comm b c, ZFNat.add_sub_add_left c d b]


-- @@ L1119-1127 verbatim
theorem sub_factor {m k n : ZFNat} (_ : k ≤ m) (_ : m ≤ n) : n - m + k = n - (m - k) := by
  symm
  apply sub_eq_of_eq_add
  rw [← add_assoc, ← add_sub_assoc, add_comm k, add_sub_assoc, sub_self, add_zero, add_comm,
    ← add_sub_assoc, add_comm, add_sub_assoc, sub_self, add_zero]
  · trivial
  · assumption
  · trivial
  · assumption


-- @@ L1129-1130 verbatim
theorem sub_add_comm {m n k : ZFNat} (h : m ≤ n) : n - m + k = n + k - m := by
  rw [add_comm, add_comm n k, add_sub_assoc h k]


-- @@ L1132-1134 verbatim
theorem succ_le_succ {n m : ZFNat} : n ≤ m → succ n ≤ succ m
  | .inl _ => .inl <| succ_mono.mp ‹_›
  | .inr _ => .inr <| congrArg succ ‹_›


-- @@ L1136-1138 verbatim
theorem succ_le_succ_iff {a b : ZFNat} : succ a ≤ succ b ↔ a ≤ b where
  mp := le_of_succ_le_succ
  mpr := succ_le_succ


-- @@ L1140-1143 verbatim
theorem le_zero_imp_eq {n : ZFNat} : n ≤ 0 → n = 0 := by
  rintro (h | rfl)
  · exact absurd h not_lt_zero
  · rfl


-- @@ L1145-1146 verbatim
/-- The multiplication function on natural numbers, defined inductively. -/
protected abbrev mul (n m : ZFNat) : ZFNat := ZFNat.rec n 0 (fun _ => (· + m))

-- @@ L1147-1147 verbatim
instance mul_inst : Mul ZFNat := ⟨ZFNat.mul⟩

-- @@ L1148-1148 verbatim
lemma mul_inst_eq {n m : ZFNat} : n * m = n.mul m := rfl


-- @@ L1150-1155 verbatim
@[simp]
lemma mul_zero {n : ZFNat} : n * 0 = 0 := by
  dsimp [mul_inst_eq]
  induction n using induction with
  | zero => rw [ZFNat.mul, rec_zero]
  | succ _ ih => rw [ZFNat.mul, rec_succ, ← ZFNat.mul, ih, add_zero]


-- @@ L1157-1159 verbatim
@[simp]
lemma zero_mul {n : ZFNat} : 0 * n = 0 := by
  rw [mul_inst_eq, ZFNat.mul, rec_zero]


-- @@ L1161-1166 verbatim
@[simp]
lemma mul_one {n : ZFNat} : n * 1 = n := by
  dsimp [mul_inst_eq]
  induction n using induction with
  | zero => rw [ZFNat.mul, rec_zero]
  | succ _ ih => rw [ZFNat.mul, rec_succ, ← ZFNat.mul, ih, add_one_eq_succ]


-- @@ L1168-1170 verbatim
@[simp]
lemma one_mul {n : ZFNat} : 1 * n = n := by
  rw [mul_inst_eq, ZFNat.mul, nat_one_eq, rec_succ, rec_zero, zero_add]


-- @@ L1172-1176 verbatim
lemma mul_succ {n m : ZFNat} : (n + 1) * m = n * m + m := by
  induction n with
  | zero => rw [zero_add, one_mul, zero_mul, zero_add]
  | succ n ih => rw [add_one_eq_succ, mul_inst_eq, ZFNat.mul, rec_succ, rec_succ, ← ZFNat.mul,
    ← mul_inst_eq, ← ih, add_one_eq_succ]


-- @@ L1178-1179 verbatim
lemma succ_mul {n m : ZFNat} : (succ n) * m = n * m + m := by
  rw [← add_one_eq_succ, mul_succ]


-- @@ L1181-1187 verbatim
lemma left_distrib {n m k : ZFNat} : n * (m + k) = n * m + n * k := by
  induction n with
  | zero => rw [zero_mul, zero_mul, zero_add, zero_mul]
  | succ n ih =>
    rw [← add_one_eq_succ]
    conv_rhs => rw [mul_succ, mul_succ, add_assoc, ← add_assoc, ← add_assoc, add_comm m, add_assoc,
      add_assoc, ← ih, ← add_assoc, add_comm k m, ← mul_succ]


-- @@ L1189-1192 verbatim
lemma mul_comm (n m : ZFNat) : n * m = m * n := by
  induction n using induction with
  | zero => rw [zero_mul, mul_zero]
  | succ n ih => rw [← add_one_eq_succ, mul_succ, ih, left_distrib, mul_one]


-- @@ L1194-1195 verbatim
lemma succ_mul' {n m : ZFNat} : m * (succ n) = m * n + m := by
  rw [mul_comm, succ_mul, mul_comm]


-- @@ L1197-1198 verbatim
lemma right_distrib {n m k : ZFNat} : (n + m) * k = n * k + m * k := by
  rw [mul_comm, left_distrib, mul_comm m, mul_comm k]


-- @@ L1200-1207 verbatim
lemma mul_assoc (n m k : ZFNat) : n * m * k = n * (m * k) := by
  induction n using induction with
  | zero => rw [zero_mul, zero_mul, zero_mul]
  | succ n ih =>
    rw [← add_one_eq_succ]
    conv =>
      rhs
      rw [right_distrib, one_mul, ← ih, ← right_distrib, ← mul_succ]


-- @@ L1209-1210 verbatim
lemma mul_left_comm (n m k : ZFNat) : n * (m * k) = m * (n * k) := by
  rw [← mul_assoc, mul_comm n m, mul_assoc]


-- @@ L1212-1212 verbatim
lemma two_mul (n : ZFNat) : (1 + 1) * n = n + n := by rw [mul_succ, one_mul]

-- @@ L1213-1213 verbatim
lemma mul_two (n : ZFNat) : n * (1 + 1) = n + n := by rw [mul_comm, two_mul]


-- @@ L1215-1223 verbatim
lemma sub_lt_eq_zero {n m : ZFNat} (h : n ≤ m) : n - m = 0 := by
  induction m using induction with
  | zero => rw [le_zero_imp_eq h, sub_zero]
  | succ _ ih =>
    rcases h with _ | rfl
    · rw [sub_succ, ih]
      · exact pred_zero
      · exact lt_le_iff.mpr ‹_›
    · rw [sub_self]


-- @@ L1225-1227 verbatim
theorem add_lt_trans {n m p q : ZFNat} : n < m → p < q → n + p < m + q := by
  intros h h'
  exact lt_trans (add_lt_add_left h' n) (add_lt_add_right h q)


-- @@ L1229-1241 verbatim
theorem pos_mul_pos {k n : ZFNat} (h : 0 < k) : 0 < k*n → 0 < n := by
  intro h'
  induction n with
  | zero => rwa [mul_zero] at h'
  | succ m ih =>
    obtain ⟨l, rfl⟩ := not_zero_imp_succ (zero_lt_ne_zero h)
    rcases lt_le_iff.mpr h with (_ | rfl)
    · by_contra contr
      rw [not_lt] at contr
      replace contr := le_zero_imp_eq contr
      nomatch succ_ne_zero m contr
    · rw [← nat_one_eq, one_mul] at h'
      assumption


-- @@ L1243-1253 verbatim
theorem mul_lt_mono {n m k : ZFNat} (h : 0 < k) : n < m → k*n < k*m := by
  intro h'
  induction m using induction with
  | zero => nomatch not_lt_zero h'
  | succ m ih =>
    rw [← add_one_eq_succ, left_distrib, mul_one]
    rcases lt_le_iff.mpr h' with (h' | rfl)
    · let this := add_lt_add_of_le_of_lt (@zero_le k) (ih h')
      rwa [zero_add, add_comm] at this
    · conv => lhs; rw [← @zero_add (k*n), add_comm]
      exact add_lt_add_left h (k*n)


-- @@ L1255-1268 verbatim
theorem mul_le_mono {k m n : ZFNat} : n ≤ m → k*n ≤ k*m := by
  intro h
  induction k using induction with
  | zero => rw [zero_mul, zero_mul]
  | succ k ih =>
    rw [succ_mul, succ_mul]
    by_contra contr
    rw [not_le, add_comm, add_comm _ n] at contr
    rcases ih with _ | l
    · nomatch lt_irrefl <| lt_trans (add_lt_add_of_le_of_lt h ‹_›) contr
    · rcases h with _ | rfl
      · rw [l] at contr
        nomatch lt_irrefl <| lt_trans (lt_of_add_lt_add_right contr) ‹_›
      · nomatch lt_irrefl ‹_›


-- @@ L1270-1273 verbatim
theorem mul_lt_cancel {k m n : ZFNat} : k*n < k*m → n < m := by
  contrapose
  rw [not_lt, not_lt]
  exact mul_le_mono


-- @@ L1275-1283 verbatim
lemma lt_mul_iff {n m k : ZFNat} : n < m ↔ (k+1)*n < (k+1)*m := by
  apply Iff.intro
  · induction k using induction with
    | zero => rw [zero_add, one_mul, one_mul]; exact id
    | succ k ih =>
      intro
      rw [← add_one_eq_succ, mul_succ, mul_succ (m:=m)]
      exact add_lt_trans (ih ‹_›) ‹_›
  · exact mul_lt_cancel


-- @@ L1285-1291 verbatim
lemma left_distrib_mul_sub_one {n m : ZFNat} : n * (m - 1) = n * m - n := by
  induction m using induction with
  | zero => rw [zero_sub, mul_zero, zero_sub]
  | succ _ _ =>
    rw [nat_one_eq, succ_sub_succ, sub_zero, succ_mul', add_sub_assoc, sub_self, add_zero]
    right
    rfl


-- @@ L1293-1299 verbatim
lemma left_distrib_mul_sub_aux {n m k : ZFNat} (h : k < m) : n * (m - k) = n * m - n * k := by
  induction k with
  | zero => rw [sub_zero, mul_zero, sub_zero]
  | succ k ih =>
    rw [mul_comm n k.succ, succ_mul, mul_comm k n, sub_add_distrib]
    specialize ih (lt_trans lt_succ h)
    rw [← ih, ← left_distrib_mul_sub_one, ← sub_add_distrib, add_one_eq_succ]


-- @@ L1301-1317 verbatim
lemma sub_eq_zero_imp_le {a b : ZFNat} : a - b = 0 ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    induction b with
    | zero => rw [sub_zero] at h; right; assumption
    | succ b ih =>
      induction a with
      | zero => exact zero_le
      | succ a _ =>
        apply le_mono
        rw [succ_sub_succ] at h
        by_contra contr
        rw [not_le] at contr
        absurd sub_ne_zero_of_lt contr
        assumption
  · intro
    exact sub_lt_eq_zero ‹_›


-- @@ L1319-1323 verbatim
lemma sub_eq_zero_mul {n a b : ZFNat} : a - b = 0 → n * a - n * b = 0 := by
  intro
  induction n with
  | zero => rw [zero_mul, zero_mul, sub_zero]
  | succ _ _ => exact sub_eq_zero_imp_le.mpr (mul_le_mono (sub_eq_zero_imp_le.mp ‹_›))


-- @@ L1325-1331 verbatim
lemma left_distrib_mul_sub {n m k : ZFNat} : n * (m - k) = n * m - n * k := by
  rcases @le_total m k with (h | rfl) | _ | rfl
  · replace h := sub_lt_eq_zero (Or.inl h)
    rw [h, mul_zero, sub_eq_zero_mul h]
  · rw [sub_self, sub_self, mul_zero]
  · exact left_distrib_mul_sub_aux ‹_›
  · rw [sub_self, sub_self, mul_zero]


-- @@ L1333-1334 verbatim
lemma right_distrib_mul_sub {n m k : ZFNat} : (m - k)*n = m*n - k*n := by
  rw [mul_comm, left_distrib_mul_sub, mul_comm, mul_comm k]


-- @@ L1336-1352 verbatim
lemma add_eq_zero_iff {n m : ZFNat} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    induction n with
    | zero =>
      rw [zero_add] at h
      exact ⟨rfl, h⟩
    | succ n ih =>
      induction m with
      | zero =>
        rw [add_zero] at h
        exact ⟨h, rfl⟩
      | succ m ih' =>
        rw [add_succ] at h
        nomatch succ_ne_zero _ h
  · rintro ⟨rfl, rfl⟩
    rw [zero_add]


-- @@ L1354-1367 verbatim
lemma mul_eq_zero_iff {n m : ZFNat} : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h
    induction n with
    | zero => left; rfl
    | succ n ih =>
      induction m with
      | zero => right; rfl
      | succ m ih' =>
        rw [←add_one_eq_succ, mul_succ, add_eq_zero_iff] at h
        nomatch succ_ne_zero _ h.2
  · rintro (rfl | rfl)
    · rw [zero_mul]
    · rw [mul_zero]


-- @@ L1369-1378 verbatim
lemma eq_le_le_iff {n m : ZFNat} : n = m ↔ n ≤ m ∧ m ≤ n := by
  constructor
  · rintro rfl
    exact ⟨le_refl _, le_refl _⟩
  · rintro ⟨n_le_m, m_le_n⟩
    rcases n_le_m with n_le_m | rfl
    · rcases m_le_n with m_le_n | rfl
      · nomatch lt_irrefl <| lt_trans n_le_m m_le_n
      · rfl
    · rfl


-- @@ L1380-1413 verbatim
lemma mul_left_cancel_iff {n m k : ZFNat} (k_pos : k ≠ 0) : k * m = k * n ↔ m = n := by
  constructor
  · induction n generalizing m with
    | zero =>
      intro hm
      rw [mul_zero, mul_eq_zero_iff] at hm
      rcases hm with rfl | rfl
      · contradiction
      · rfl
    | succ n ih =>
      intro eq
      cases m with
      | zero =>
        symm at eq
        rw [mul_zero, mul_eq_zero_iff] at eq
        rcases eq with rfl | eq
        · contradiction
        · nomatch succ_ne_zero _ eq
      | succ m =>
        congr
        rw [eq_le_le_iff]
        and_intros
        · have := zero_add ▸ @ZFNat.sub_eq_of_eq_add (k * m.succ) (k * n.succ) 0 <| eq
          rw [←left_distrib_mul_sub, mul_eq_zero_iff] at this
          rcases this with rfl | this
          · contradiction
          · rwa [ZFNat.succ_sub_succ, ZFNat.sub_eq_zero_imp_le] at this
        · have := zero_add ▸ @ZFNat.sub_eq_of_eq_add (k * n.succ) (k * m.succ) 0 <| eq.symm
          rw [←left_distrib_mul_sub, mul_eq_zero_iff] at this
          rcases this with rfl | this
          · contradiction
          · rwa [ZFNat.succ_sub_succ, ZFNat.sub_eq_zero_imp_le] at this
  · rintro rfl
    rfl


-- @@ L1415-1417 verbatim
lemma mul_right_cancel_iff {n m k : ZFNat} (k_pos : k ≠ 0) : m * k = n * k ↔ m = n := by
  rw [mul_comm m k, mul_comm n k]
  exact mul_left_cancel_iff k_pos


-- @@ L1419-1420 verbatim
/-- The power function on natural numbers, defined inductively. -/
protected abbrev pow (n p : ZFNat) : ZFNat := ZFNat.rec p 1 (fun _  => (· * n))

-- @@ L1421-1421 verbatim
instance pow_inst : HomogeneousPow ZFNat := ⟨ZFNat.pow⟩

-- @@ L1422-1422 verbatim
lemma pow_inst_eq {n p : ZFNat} : n ^ p = n.pow p := rfl


-- @@ L1424-1426 verbatim
lemma pow_zero {n : ZFNat} : n ^ 0 = 1 := by
  dsimp [pow_inst_eq]
  rw [ZFNat.pow, rec_zero]


-- @@ L1428-1429 verbatim
lemma pow_one {n : ZFNat} : n ^ 1 = n := by
  rw [pow_inst_eq, ZFNat.pow, nat_one_eq, rec_succ, rec_zero, ← nat_one_eq, one_mul]


-- @@ L1431-1432 verbatim
lemma pow_succ {n p : ZFNat} : n ^ succ p = n ^ p * n := by
  rw [pow_inst_eq, ZFNat.pow, ZFNat.rec_succ, ← ZFNat.pow, ← pow_inst_eq]


-- @@ L1434-1434 verbatim
end Arithmetic


-- @@ L1436-1448 verbatim
/--
Induction principle for `ZFNat`, using natural notations.

Declared as an induction eliminator.
-/
@[induction_eliminator]
theorem induction' {P : ZFNat → Prop} (n : ZFNat)
  (zero : P 0) (succ : ∀ n, P n → P (n + 1)) : P n := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [← add_one_eq_succ]
    exact succ n ih


-- @@ L1450-1452 verbatim
abbrev nsmul : ℕ → ZFNat → ZFNat
  | 0, _ => 0
  | n+1, m => m + nsmul n m


-- @@ L1454-1472 verbatim
instance : Semiring ZFNat where
  add := .add
  add_assoc _ _ _ := by rw [add_assoc]
  zero := 0
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFNat.nsmul
  nsmul_zero _ := rfl
  nsmul_succ _ _ := add_comm _ _
  add_comm := add_comm
  mul := .mul
  left_distrib _ _ _ := left_distrib
  right_distrib _ _ _:= right_distrib
  zero_mul _ := zero_mul
  mul_zero _ := mul_zero
  mul_assoc _ _ _ := by rw [mul_assoc]
  one := 1
  one_mul _ := one_mul
  mul_one _ := mul_one


-- @@ L1474-1475 verbatim
instance : CommSemiring ZFNat where
  mul_comm := mul_comm


-- @@ L1477-1482 verbatim
/--
The `CommSemiring` instance makes Mathlib's `ring` normalisation available on `ZFNat`.
Here `^` is the monoid power with exponent in `ℕ`, while the coefficient `2` is the
`ZFNat` numeral obtained from `Nat.cast`.
-/
example (a b : ZFNat) : (a+b)^2 = a^2 + 2*a*b + b^2 := by ring


-- @@ L1484-1484 verbatim
instance : Std.Associative (α := ZFNat) (· + ·) := ⟨(ZFNat.add_assoc · · · |>.symm)⟩

-- @@ L1485-1485 verbatim
instance : Std.Commutative (α := ZFNat) (· + ·) := ⟨ZFNat.add_comm⟩


-- @@ L1487-1487 verbatim
instance : Std.Associative (α := ZFNat) (· * ·) := ⟨ZFNat.mul_assoc⟩

-- @@ L1488-1488 verbatim
instance : Std.Commutative (α := ZFNat) (· * ·) := ⟨ZFNat.mul_comm⟩



-- @@ L1491-1492 verbatim
instance : IsLeftCancelAdd ZFNat where
  add_left_cancel x y z := by rw [ZFNat.add_left_cancel]; intro; trivial


-- @@ L1494-1494 verbatim
def toNat (n : ZFNat) : ℕ := ZFNat.rec n 0 (fun _ => Nat.succ)

-- @@ L1495-1495 verbatim
def ofNat (n : ℕ) : ZFNat := nsmul n 1


-- @@ L1497-1501 verbatim
theorem toNat_is_id {n : ℕ} : (n : ZFNat).toNat = n := by
  induction n with
  | zero => apply ZFNat.rec_zero
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, ZFNat.add_one_eq_succ, ZFNat.toNat,
    ZFNat.rec_succ, ← ZFNat.toNat, ih]


-- @@ L1503-1503 verbatim
end ZFNat


-- @@ L1505-1514 verbatim
theorem Nat.is_transitive : transitive Nat := by
  intro n hn
  apply ZFNat.rec' n hn
  case zero => exact empty_subset Nat
  case succ =>
    intros x hx hx' z hz
    rw [mem_insert_iff] at hz
    rcases hz with rfl | hz
    · assumption
    · exact hx' hz


-- @@ L1516-1519 verbatim
/-- `Nat` is an inductive set. -/
theorem Nat.is_inductive : inductive_set Nat where
  left := ZFNat.zero_in_Nat
  right := fun _ _ => ZFNat.succ_mem_Nat' ‹_›


-- @@ L1521-1547 verbatim
theorem ZFNat.ofNat_inj {n m : ℕ} : (n : ZFNat) = (m : ZFNat) ↔ n = m where
  mp := by
    intro h
    induction n generalizing m with
    | zero =>
      conv_rhs at h =>
        unfold Nat.cast NatCast.natCast
      unfold_projs at h
      unfold Nat.unaryCast at h
      split at h
      · rfl
      · rw [ZFNat.add_one_eq_succ] at h
        nomatch ZFNat.succ_ne_zero _ h.symm
    | succ n ih =>
      cases m with
      | zero =>
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
        rw [ZFNat.add_one_eq_succ] at h
        nomatch ZFNat.succ_ne_zero _ h
      | succ m =>
        simp only [Nat.cast_add, Nat.cast_one] at h
        rw [ZFNat.add_one_eq_succ, ZFNat.add_one_eq_succ] at h
        obtain rfl := ih <| ZFNat.succ_inj h
        rfl
  mpr := by
    rintro rfl
    rfl


-- @@ L1549-1558 verbatim
theorem ZFNat.toNat_eq (n : ZFNat) : ZFNat.toNat n = n := by
  induction n with
  | zero =>
    rw [ZFNat.toNat, ZFNat.rec_zero]
    rfl
  | succ n ih =>
    rw [ZFNat.add_one_eq_succ, ZFNat.toNat, ZFNat.rec_succ, ←ZFNat.toNat]
    unfold Nat.cast
    simp only [Nat.succ_eq_add_one, Nat.cast_add, ih, Nat.cast_one, Nat.succ_eq_add_one]
    rw [ZFNat.add_one_eq_succ]


-- @@ L1560-1583 verbatim
theorem ZFNat.toNat_iff {n m : ZFNat} : n = m ↔ n.toNat = m.toNat where
  mp := by
    rintro rfl
    rfl
  mpr := by
    intro h
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => rfl
      | succ m =>
        rw [toNat, ZFNat.rec_zero, toNat, ZFNat.rec_succ] at h
        nomatch Nat.succ_ne_zero _ h.symm
    | succ n ih =>
      rw [add_one_eq_succ, ZFNat.toNat, ZFNat.rec_succ] at h
      cases m with
      | zero =>
        rw [ZFNat.toNat, ZFNat.rec_zero] at h
        nomatch Nat.succ_ne_zero _ h
      | succ m =>
        rw [ZFNat.toNat, ZFNat.rec_succ, _root_.Nat.succ_inj, ←toNat, ←toNat] at h
        rw [add_one_eq_succ]
        obtain rfl := ih h
        rfl


-- @@ L1585-1603 verbatim
def ZFNat.equivZFNat_Nat : ZFNat ≃ ℕ where
  toFun := toNat
  invFun := ofNat
  left_inv := by
    intro n
    induction n with
    | zero =>
      rw [toNat, ZFNat.rec_zero]
      rfl
    | succ n ih =>
      rw [toNat, ZFNat.add_one_eq_succ, ZFNat.rec_succ,
        ←toNat, ofNat, nsmul, ←ofNat, ih, add_one_eq_succ']
  right_inv := by
    intro n
    induction n with
    | zero =>
      rw [ofNat, toNat, ZFNat.rec_zero]
    | succ n ih =>
      rw [ofNat, nsmul, add_one_eq_succ', ←ofNat, toNat, ZFNat.rec_succ, ←toNat, ih]



-- @@ L1606-1621 verbatim
/-! ## Transfer to `ℕ`

`equivZFNat_Nat` says that `ZFNat` and `ℕ` are the same type. Upgraded to a ring isomorphism and
registered as a `TransferEquiv`, it lets the `transfer` tactic read a goal about `ZFNat` in `ℕ`:

```
example (n m : ZFNat) : n + m = m + n := by
  transfer ZFNat → ℕ =>
    rw [Nat.add_comm]
```

The block is proved in `ℕ`, and closing it closes the goal about `ZFNat`. The ring operations,
the numerals and the casts travel through the generic `map_…` lemmas of the `transfer_simps`
simp set; what those lemmas do not cover is stated here: `succ`, the truncated subtraction, the
homogeneous power, and the two order relations.
-/


-- @@ L1623-1623 verbatim
section Transfer


-- @@ L1625-1625 verbatim
namespace ZFNat


-- @@ L1627-1627 verbatim
theorem toNat_zero : (0 : ZFNat).toNat = 0 := by rw [toNat, rec_zero]


-- @@ L1629-1631 verbatim
theorem toNat_succ (a : ZFNat) : (succ a).toNat = a.toNat.succ := by
  rw [toNat, ZFNat.rec_succ]
  rfl


-- @@ L1633-1633 verbatim
theorem toNat_one : (1 : ZFNat).toNat = 1 := by rw [nat_one_eq, toNat_succ, toNat_zero]


-- @@ L1635-1641 verbatim
theorem toNat_pred (a : ZFNat) : (pred a).toNat = a.toNat.pred := by
  by_cases h : a = 0
  · subst h
    rw [pred_zero, toNat_zero]
    rfl
  · obtain ⟨b, rfl⟩ := not_zero_imp_succ h
    rw [pred_succ, toNat_succ, Nat.pred_succ]


-- @@ L1643-1644 verbatim
theorem toNat_add (a b : ZFNat) : (a + b).toNat = a.toNat + b.toNat :=
  ofNat_inj.mp (by rw [Nat.cast_add, toNat_eq, toNat_eq, toNat_eq])


-- @@ L1646-1647 verbatim
theorem toNat_mul (a b : ZFNat) : (a * b).toNat = a.toNat * b.toNat :=
  ofNat_inj.mp (by rw [Nat.cast_mul, toNat_eq, toNat_eq, toNat_eq])


-- @@ L1649-1652 verbatim
theorem toNat_sub (a b : ZFNat) : (a - b).toNat = a.toNat - b.toNat := by
  induction b with
  | zero => rw [sub_zero, toNat_zero, Nat.sub_zero]
  | succ b ih => rw [add_one_eq_succ, sub_succ, toNat_pred, ih, toNat_succ, Nat.sub_succ]


-- @@ L1654-1657 verbatim
theorem toNat_pow (a b : ZFNat) : (a ^ b).toNat = a.toNat ^ b.toNat := by
  induction b with
  | zero => rw [pow_zero, toNat_one, toNat_zero, Nat.pow_zero]
  | succ b ih => rw [add_one_eq_succ, pow_succ, toNat_mul, ih, toNat_succ, Nat.pow_succ]


-- @@ L1659-1667 verbatim
theorem toNat_le (a b : ZFNat) : a ≤ b ↔ a.toNat ≤ b.toNat where
  mp h := by
    obtain ⟨k, rfl⟩ := le.dest h
    rw [toNat_add]
    exact Nat.le_add_right _ _
  mpr h := by
    obtain ⟨j, hj⟩ := Nat.le.dest h
    refine le.intro (k := (j : ZFNat)) (toNat_iff.mpr ?_)
    rw [toNat_add, toNat_is_id, hj]


-- @@ L1669-1670 verbatim
theorem toNat_lt (a b : ZFNat) : a < b ↔ a.toNat < b.toNat := by
  rw [← le_lt_iff, toNat_le, toNat_succ, Nat.succ_le_iff]


-- @@ L1672-1674 verbatim
/-- `equivZFNat_Nat` as a ring isomorphism. -/
def ringEquivNat : ZFNat ≃+* ℕ :=
  { equivZFNat_Nat with map_add' := toNat_add, map_mul' := toNat_mul }


-- @@ L1676-1677 verbatim
/-- Equivalence used by the `transfer` tactic to move goals between `ZFNat` and `ℕ`. -/
instance : TransferEquiv ZFNat ℕ := ⟨ringEquivNat.toEquiv⟩


-- @@ L1679-1680 verbatim
@[transfer_simps] theorem ringEquivNat_succ (a : ZFNat) :
    ringEquivNat (succ a) = (ringEquivNat a).succ := toNat_succ a


-- @@ L1682-1683 verbatim
@[transfer_simps] theorem ringEquivNat_sub (a b : ZFNat) :
    ringEquivNat (a - b) = ringEquivNat a - ringEquivNat b := toNat_sub a b


-- @@ L1685-1686 verbatim
@[transfer_simps] theorem ringEquivNat_pow (a b : ZFNat) :
    ringEquivNat (a ^ b) = ringEquivNat a ^ ringEquivNat b := toNat_pow a b


-- @@ L1688-1689 verbatim
@[transfer_simps] theorem ringEquivNat_dvd (a b : ZFNat) :
    a ∣ b ↔ ringEquivNat a ∣ ringEquivNat b := (map_dvd_iff ringEquivNat).symm


-- @@ L1691-1692 verbatim
@[transfer_simps] theorem ringEquivNat_le (a b : ZFNat) :
    a ≤ b ↔ ringEquivNat a ≤ ringEquivNat b := toNat_le a b


-- @@ L1694-1695 verbatim
@[transfer_simps] theorem ringEquivNat_lt (a b : ZFNat) :
    a < b ↔ ringEquivNat a < ringEquivNat b := toNat_lt a b

-- @@ L1696-1696 verbatim
end ZFNat


-- @@ L1698-1698 verbatim
end Transfer


-- @@ L1700-1700 verbatim
end Naturals

-- @@ L1701-1701 verbatim
end ZFSet

-- @@ L1702-1702 verbatim
end
