/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaOne.HFS.Basic
import LeanPool.Incompleteness.Arithmetization.Definability.Absoluteness
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Algebra.Order.Sub.Basic


-- @@ L13-17 verbatim
/-!

# Sequence

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L23-23 verbatim
namespace LO

-- @@ L24-24 verbatim
namespace Arith


-- @@ L26-26 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L28-28 expanded
variable {V : Type*} [ORingStruc V] [ModelsTheory V (iSigma 1)]


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Seq (s : V) : Prop := IsMapping s ∧ ∃ l, domain s = under l


-- @@ L33-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Arith.Seq.isMapping {s : V} (h : Seq s) : IsMapping s := h.1


-- @@ L36-43 verbatim
private lemma seq_iff (s : V) :
    Seq s ↔ IsMapping s ∧ ∃ l ≤ 2 * s, ∃ d ≤ 2 * s, d = domain s ∧ d = under l :=
  ⟨by rintro ⟨hs, l, h⟩
      exact ⟨hs, l, (by
      calc
        l ≤ domain s := by simp [h]
        _ ≤ 2 * s    := by simp), ⟨domain s , by simp,  rfl, h⟩⟩,
   by rintro ⟨hs, l, _, _, _, rfl, h⟩; exact ⟨hs, l, h⟩⟩


-- @@ L45-47 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.seqDef : Sg0.Semisentence 1 :=
  .mkSigma
    (Wedge.wedge (LO.FirstOrder.Rewriting.substitute isMappingDef (vecCons #0 ![]))
      (Semiformula.bexLTSucc (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0])
        (Semiformula.bexLTSucc (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #1])
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute domainDef (vecCons (#0) (vecCons #2 ![])))
            (LO.FirstOrder.Rewriting.substitute underDef (vecCons (#0) (vecCons #1 ![])))))))
    (by simp)


-- @@ L49-66 expanded
lemma seq_defined : DefinedPred Sg0 (Seq : V → Prop) seqDef :=
  by
  intro v
  simp only [Fin.isValue, seq_iff, ↓existsAndEq, domain_bound, true_and, seqDef,
    Nat.succ_eq_add_one, Nat.reduceAdd, HierarchySymbol.Semiformula.val_mkSigma,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.cons_val_fin_one,
    Semiterm.val_bvar, Matrix.constant_eq_singleton, isMapping_defined_iff, Matrix.vecCons_zero,
    Semiformula.eval_bexLTSucc', Semiterm.val_operator₂, Semiterm.val_const,
    Structure.numeral_eq_numeral, numeral_two_eq_two, Structure.Mul.mul, Matrix.cons_val_one,
    Matrix.comp_vecCons', Matrix.cons_app_two, domain_defined_iff, under_defined_iff,
    LogicalConnective.Prop.and_eq, exists_eq_right_right, and_congr_right_iff]
  intro hs
  constructor
  · rintro ⟨l, hl, hdom⟩
    exact
      ⟨l, hl, by
        rw [← hdom]
        simp, hdom.symm⟩
  · rintro ⟨l, hl, _, hdom⟩
    exact ⟨l, hl, hdom.symm⟩


-- @@ L68-69 verbatim
@[simp] lemma seq_defined_iff (v) :
    Semiformula.Evalbm V v seqDef.val ↔ Seq (v 0) := seq_defined.df.iff v


-- @@ L71-71 expanded
instance seq_definable : BoldfacePred Sg0 (Seq : V → Prop) :=
  seq_defined.to_definable


-- @@ L73-73 expanded
instance seq_definable' (ℌ) : BoldfacePred ℌ (Seq : V → Prop) :=
  seq_definable.of_zero


-- @@ L75-75 verbatim
section «lp_section_1»


-- @@ L77-77 verbatim
open Lean PrettyPrinter Delaborator


-- @@ L79-80 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax ":Seq " firstOrderTerm : firstOrderFormula


-- @@ L82-84 expanded
scoped macro_rules
  | `(foFormula[$binders* | $fbinders* | :Seq $t:firstOrderTerm]) =>
    `(LO.FirstOrder.Rewriting.substitute seqDef.val
        (vecCons foTerm[$binders* | $fbinders* | $t] ![]))


-- @@ L86-86 verbatim
end «lp_section_1»


-- @@ L88-94 verbatim
lemma lh_exists_uniq (s : V) : ∃! l, (Seq s → domain s = under l) ∧ (¬Seq s → l = 0) := by
  by_cases h : Seq s
  · rcases h with ⟨h, l, hl⟩
    exact ExistsUnique.intro l
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
  · simp [h]


-- @@ L96-97 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def lh (s : V) : V := Classical.choose! (lh_exists_uniq s)


-- @@ L99-100 verbatim
lemma lh_prop (s : V) : (Seq s → domain s = under (lh s)) ∧ (¬Seq s → lh s = 0) :=
  Classical.choose!_spec (lh_exists_uniq s)


-- @@ L102-102 verbatim
lemma lh_prop_of_not_seq {s : V} (h : ¬Seq s) : lh s = 0 := (lh_prop s).2 h


-- @@ L104-104 verbatim
lemma _root_.LO.Arith.Seq.domain_eq {s : V} (h : Seq s) : domain s = under (lh s) := (lh_prop s).1 h


-- @@ L106-111 verbatim
@[simp] lemma lh_bound (s : V) : lh s ≤ 2 * s := by
  by_cases hs : Seq s
  · calc
      lh s ≤ under (lh s) := le_under _
      _    ≤ 2 * s        := by simp [←hs.domain_eq]
  · simp [lh_prop_of_not_seq hs]


-- @@ L113-121 verbatim
private lemma lh_graph (l s : V) :
    l = lh s ↔ (Seq s → ∃ d ≤ 2 * s, d = domain s ∧ d = under l) ∧ (¬Seq s → l = 0) :=
  ⟨by
    rintro rfl
    by_cases Hs : Seq s <;> simp [Hs, ←Seq.domain_eq, lh_prop_of_not_seq], by
    rintro ⟨h, hn⟩
    by_cases Hs : Seq s
    · rcases h Hs with ⟨_, _, rfl, h⟩; simpa [h] using Hs.domain_eq
    · simp [lh_prop_of_not_seq Hs, hn Hs]⟩


-- @@ L123-125 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.lhDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Wedge.wedge
      (Arrow.arrow (LO.FirstOrder.Rewriting.substitute seqDef (vecCons #1 ![]))
        (Semiformula.bexLTSucc (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #1])
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute domainDef (vecCons (#0) (vecCons #2 ![])))
            (LO.FirstOrder.Rewriting.substitute underDef (vecCons (#0) (vecCons #1 ![]))))))
      (Arrow.arrow (Tilde.tilde (LO.FirstOrder.Rewriting.substitute seqDef (vecCons #1 ![])))
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])))
    (by simp)


-- @@ L127-128 expanded
lemma lh_defined : DefinedFunction₁ Sg0 (lh : V → V) lhDef := by intro v;
  simp [lhDef, -exists_eq_right_right, lh_graph]


-- @@ L130-131 verbatim
@[simp] lemma lh_defined_iff (v) :
    Semiformula.Evalbm V v lhDef.val ↔ v 0 = lh (v 1) := lh_defined.df.iff v


-- @@ L133-133 expanded
instance lh_definable : BoldfaceFunction₁ Sg0 (lh : V → V) :=
  lh_defined.to_definable


-- @@ L135-135 expanded
instance lh_definable' (ℌ) : BoldfaceFunction₁ ℌ (lh : V → V) :=
  lh_definable.of_zero


-- @@ L137-137 expanded
instance : Bounded₁ (lh : V → V) :=
  ⟨Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0], fun _ ↦ by simp⟩


-- @@ L139-140 expanded
lemma _root_.LO.Arith.Seq.exists {s : V} (h : Seq s) {x : V} (hx : x < lh s) : ∃ y, pair x y ∈ s :=
  h.isMapping x (by simpa [h.domain_eq] using hx) |>.exists


-- @@ L142-143 expanded
lemma _root_.LO.Arith.Seq.nth_exists_uniq {s : V} (h : Seq s) {x : V} (hx : x < lh s) :
    ∃! y, pair x y ∈ s :=
  h.isMapping x (by simpa [h.domain_eq] using hx)


-- @@ L145-147 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Seq.nth {s : V} (h : Seq s) {x : V} (hx : x < lh s) : V :=
  Classical.choose! (h.nth_exists_uniq hx)


-- @@ L149-150 expanded
@[simp]
lemma _root_.LO.Arith.Seq.nth_mem {s : V} (h : Seq s) {x : V} (hx : x < lh s) :
    pair x (h.nth hx) ∈ s :=
  Classical.choose!_spec (h.nth_exists_uniq hx)


-- @@ L152-154 expanded
lemma _root_.LO.Arith.Seq.nth_uniq {s : V} (h : Seq s) {x y : V} (hx : x < lh s)
    (hy : pair x y ∈ s) : y = h.nth hx :=
  (h.nth_exists_uniq hx).unique hy (by simp)


-- @@ L156-157 verbatim
@[simp] lemma _root_.LO.Arith.Seq.nth_lt {s : V} (h : Seq s) {x} (hx : x < lh s) : h.nth hx < s :=
  lt_of_mem_rng (h.nth_mem hx)


-- @@ L159-160 verbatim
lemma _root_.LO.Arith.Seq.lh_eq_of {s : V} (H : Seq s) {l} (h : domain s = under l) : lh s = l := by
  simpa [H.domain_eq] using h


-- @@ L162-163 verbatim
lemma _root_.LO.Arith.Seq.lt_lh_iff {s : V} (h : Seq s) {i} : i < lh s ↔ i ∈ domain s :=
  by simp [h.domain_eq]


-- @@ L165-166 expanded
lemma _root_.LO.Arith.Seq.lt_lh_of_mem {s : V} (h : Seq s) {i x} (hix : pair i x ∈ s) : i < lh s :=
  h.lt_lh_iff.mpr (mem_domain_iff.mpr ⟨x, hix⟩)


-- @@ L168-169 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def seqCons (s x : V) : V :=
  insert (pair (lh s) x) s


-- @@ L171-171 verbatim
section «lp_section_2»


-- @@ L173-179 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma znth_existsUnique (s i : V) :
    ∃! x, (Seq s ∧ i < lh s → pair i x ∈ s) ∧ (¬(Seq s ∧ i < lh s) → x = 0) :=
  by
  by_cases h : Seq s ∧ i < lh s
  · simp only [h, and_self, forall_const, not_true_eq_false, IsEmpty.forall_iff, and_true]
    exact h.1.nth_exists_uniq h.2
  · simp_all


-- @@ L181-182 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def znth (s i : V) : V := Classical.choose! (znth_existsUnique s i)


-- @@ L184-186 expanded
protected lemma _root_.LO.Arith.Seq.znth {s i : V} (h : Seq s) (hi : i < lh s) :
    pair i (znth s i) ∈ s :=
  Classical.choose!_spec (znth_existsUnique s i) |>.1 ⟨h, hi⟩


-- @@ L188-189 expanded
lemma _root_.LO.Arith.Seq.znth_eq_of_mem {s i : V} (h : Seq s) (hi : pair i x ∈ s) : znth s i = x :=
  h.isMapping.uniq (h.znth (h.lt_lh_of_mem hi)) hi


-- @@ L191-192 verbatim
lemma znth_prop_not {s i : V} (h : ¬Seq s ∨ lh s ≤ i) : znth s i = 0 :=
  Classical.choose!_spec (znth_existsUnique s i) |>.2 (by simpa [-not_and, not_and_or] using h)


-- @@ L194-197 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.znthDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #1])
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute lhDef (vecCons (#0) (vecCons #2 ![])))
        (Wedge.wedge
          (Arrow.arrow
            (Wedge.wedge (foFormula[l x s i | | :Seq s])
              (Semiformula.Operator.operator Operator.LT.lt ![#3, #0]))
            (memRelOpr.operator ![#2, #3, #1]))
          (Arrow.arrow
            (Tilde.tilde
              (Wedge.wedge (foFormula[l x s i | | :Seq s])
                (Semiformula.Operator.operator Operator.LT.lt ![#3, #0])))
            (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0])))))
    (by simp)


-- @@ L199-201 expanded
private lemma znth_graph {x s i : V} :
    x = znth s i ↔
      ∃ l ≤ 2 * s, l = lh s ∧ (Seq s ∧ i < l → pair i x ∈ s) ∧ (¬(Seq s ∧ i < l) → x = 0) :=
  by simp [znth, Classical.choose!_eq_iff]


-- @@ L203-205 expanded
lemma znth_defined : DefinedFunction₂ Sg0 (znth : V → V → V) znthDef := by intro v;
  simpa [znthDef, -not_and, not_and_or] using znth_graph (V := V)


-- @@ L207-208 verbatim
@[simp] lemma eval_znthDef (v) :
    Semiformula.Evalbm V v znthDef.val ↔ v 0 = znth (v 1) (v 2) := znth_defined.df.iff v


-- @@ L210-210 expanded
instance znth_definable : BoldfaceFunction₂ Sg0 (znth : V → V → V) :=
  znth_defined.to_definable


-- @@ L212-212 expanded
instance znth_definable' (ℌ) : BoldfaceFunction₂ ℌ (znth : V → V → V) :=
  znth_definable.of_zero


-- @@ L214-216 verbatim
end «lp_section_2»

-- infixr:67 " ::ˢ " => seqCons


-- @@ L218-219 verbatim
/-- Imported notation from the Incompleteness formalization. -/
infixr:67 " ⁀' " => seqCons


-- @@ L221-221 verbatim
@[simp] lemma seq_empty : Seq (∅ : V) := ⟨by simp, 0, by simp⟩


-- @@ L223-227 verbatim
@[simp] lemma lh_empty : lh (∅ : V) = 0 := by
  have :
      under (lh ∅ : V) = under 0 := by
    simpa using (Eq.symm (Seq.domain_eq (V := V) (s := ∅) (by simp)))
  exact under_inj.mp this


-- @@ L229-231 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Arith.Seq.isempty_of_lh_eq_zero {s : V} (Hs : Seq s) (h : lh s = 0) : s = ∅ :=
  by simpa [h] using Hs.domain_eq


-- @@ L233-233 expanded
@[simp]
lemma _root_.LO.Arith.Seq.subset_seqCons (s x : V) : s ⊆ seqCons s x := by simp [seqCons]


-- @@ L235-239 expanded
lemma _root_.LO.Arith.Seq.lt_seqCons {s} (hs : Seq s) (x : V) : s < seqCons s x :=
  lt_iff_le_and_ne.mpr <|
    ⟨le_of_subset <| by simp, by
      simp only [seqCons, ne_eq]; intro A
      have : pair (lh s) x ∈ s := by simpa [← A] using mem_insert (pair (lh s) x) s
      simpa using hs.lt_lh_of_mem this⟩


-- @@ L241-241 expanded
lemma _root_.LO.Arith.Seq.mem_seqCons (s x : V) : pair (lh s) x ∈ seqCons s x := by simp [seqCons]


-- @@ L243-244 expanded
protected lemma _root_.LO.Arith.Seq.seqCons {s : V} (h : Seq s) (x : V) : Seq (seqCons s x) :=
  ⟨h.isMapping.insert (by simp [h.domain_eq]), lh s + 1, by simp [seqCons, h.domain_eq]⟩


-- @@ L246-249 expanded
@[simp]
lemma _root_.LO.Arith.Seq.lh_seqCons (x : V) {s} (h : Seq s) : lh (seqCons s x) = lh s + 1 :=
  by
  have : under (lh s + 1) = under (lh (seqCons s x)) := by
    simpa [seqCons, h.domain_eq] using (h.seqCons x).domain_eq
  exact Eq.symm <| under_inj.mp this


-- @@ L251-252 expanded
lemma mem_seqCons_iff {i x z s : V} : pair i x ∈ seqCons s z ↔ (i = lh s ∧ x = z) ∨ pair i x ∈ s :=
  by simp [seqCons]


-- @@ L254-254 expanded
@[simp]
lemma lh_mem_seqCons (s z : V) : pair (lh s) z ∈ seqCons s z := by simp [seqCons]


-- @@ L256-258 expanded
@[simp]
lemma lh_mem_seqCons_iff {s x z : V} (H : Seq s) : pair (lh s) x ∈ seqCons s z ↔ x = z :=
  by
  simp only [seqCons, mem_bitInsert_iff, pair_ext_iff, true_and, or_iff_left_iff_imp]
  intro h; have := H.lt_lh_of_mem h; simp at this


-- @@ L260-263 expanded
lemma _root_.LO.Arith.Seq.mem_seqCons_iff_of_lt {s x z : V} (hi : i < lh s) :
    pair i x ∈ seqCons s z ↔ pair i x ∈ s :=
  by
  simp only [seqCons, mem_bitInsert_iff, pair_ext_iff, or_iff_right_iff_imp, and_imp]
  rintro rfl; simp at hi


-- @@ L265-266 expanded
@[simp]
lemma lh_not_mem {s} (Ss : Seq s) (x : V) : pair (lh s) x ∉ s := fun h ↦ by
  have := Ss.lt_lh_of_mem h; simp at this


-- @@ L268-268 verbatim
section «lp_section_3»


-- @@ L270-275 expanded
lemma seqCons_graph (t x s : V) :
    t = seqCons s x ↔
      ∃ l ≤ 2 * s, l = lh s ∧ ∃ p ≤ (2 * s + x + 1) ^ 2, p = pair l x ∧ t = insert p s :=
  ⟨by
    rintro rfl
    exact
      ⟨lh s, by simp [], rfl, pair (lh s) x,
        le_trans (pair_le_pair_left (by simp) x) (pair_polybound (2 * s) x), rfl, by rfl⟩,
    by rintro ⟨l, _, rfl, p, _, rfl, rfl⟩; rfl⟩


-- @@ L277-280 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.seqConsDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #1])
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute lhDef (vecCons (#0) (vecCons #2 ![])))
        (Semiformula.bexLTSucc
          ((Semiterm.Operator.npow _ 2).operator
            ![Semiterm.Operator.Add.add.operator
                ![Semiterm.Operator.Add.add.operator
                    ![Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #2], #3],
                  Semiterm.numeral 1]])
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#0) (vecCons (#1) (vecCons #4 ![]))))
            (LO.FirstOrder.Rewriting.substitute insertDef
              (vecCons (#2) (vecCons (#0) (vecCons #3 ![]))))))))
    (by simp)


-- @@ L282-283 expanded
lemma seqCons_defined : DefinedFunction₂ Sg0 (seqCons : V → V → V) seqConsDef := by intro v;
  simp [seqConsDef, seqCons_graph]


-- @@ L285-286 expanded
@[simp]
lemma seqCons_defined_iff (v) : Semiformula.Evalbm V v seqConsDef.val ↔ v 0 = seqCons (v 1) (v 2) :=
  seqCons_defined.df.iff v


-- @@ L288-288 expanded
instance seqCons_definable : BoldfaceFunction₂ Sg0 (seqCons : V → V → V) :=
  seqCons_defined.to_definable


-- @@ L290-290 expanded
instance seqCons_definable' (ℌ) : BoldfaceFunction₂ ℌ (seqCons : V → V → V) :=
  seqCons_definable.of_zero


-- @@ L292-292 verbatim
@[simp] lemma natCast_empty : ((∅ : ℕ) : V) = ∅ := by simp [emptyset_def]


-- @@ L294-295 expanded
lemma seqCons_absolute (s a : ℕ) : ((seqCons s a : ℕ) : V) = seqCons (s : V) (a : V) := by
  simpa using DefinedFunction.shigmaZero_absolute_func V seqCons_defined seqCons_defined ![s, a]


-- @@ L297-297 verbatim
end «lp_section_3»


-- @@ L299-300 verbatim
lemma _root_.LO.Arith.Seq.restr {s : V} (H : Seq s) {i : V} (hi : i ≤ lh s) : Seq (s ↾ under i) :=
  ⟨H.isMapping.restr (under i), i, domain_restr_of_subset_domain (by simp [H.domain_eq, hi])⟩


-- @@ L302-304 verbatim
lemma _root_.LO.Arith.Seq.restr_lh {s : V} (H : Seq s) {i : V} (hi : i ≤ lh s) :
    lh (s ↾ under i) = i :=
  (H.restr hi).lh_eq_of (domain_restr_of_subset_domain <| by simp [H.domain_eq, hi])


-- @@ L306-313 expanded
lemma domain_bitRemove_of_isMapping_of_mem {x y s : V} (hs : IsMapping s) (hxy : pair x y ∈ s) :
    domain (bitRemove (pair x y) s) = bitRemove x (domain s) :=
  by
  apply mem_ext
  simp only [mem_domain_iff, mem_bitRemove_iff, ne_eq, pair_ext_iff, not_and]
  intro x₁
  constructor
  · rintro ⟨y₁, hy₁, hx₁y₁⟩; exact ⟨by rintro rfl; exact hy₁ rfl (hs.uniq hx₁y₁ hxy), y₁, hx₁y₁⟩
  · simp_all


-- @@ L315-328 expanded
lemma _root_.LO.Arith.Seq.eq_of_eq_of_subset {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂)
    (hl : lh s₁ = lh s₂) (h : s₁ ⊆ s₂) : s₁ = s₂ :=
  by
  apply mem_ext; intro u
  constructor
  · intro hu; exact h hu
  · intro hu
    have : pi₁ u < lh s₁ := by
      simpa [hl] using H₂.lt_lh_of_mem (show pair (pi₁ u) (pi₂ u) ∈ s₂ from by simpa using hu)
    have : ∃ y, pair (pi₁ u) y ∈ s₁ := H₁.exists this
    rcases this with ⟨y, hy⟩
    have : y = pi₂ u :=
      H₂.isMapping.uniq (h hy) (show pair (pi₁ u) (pi₂ u) ∈ s₂ from by simpa using hu)
    simp_all


-- @@ L330-332 expanded
lemma subset_pair {s t : V} (h : ∀ i x, pair i x ∈ s → pair i x ∈ t) : s ⊆ t :=
  by
  intro u hu
  simpa using h (pi₁ u) (pi₂ u) (by simpa using hu)


-- @@ L334-340 expanded
lemma _root_.LO.Arith.Seq.lh_ext {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) (h : lh s₁ = lh s₂)
    (H : ∀ i x₁ x₂, pair i x₁ ∈ s₁ → pair i x₂ ∈ s₂ → x₁ = x₂) : s₁ = s₂ :=
  H₁.eq_of_eq_of_subset H₂ h <|
    subset_pair <| by
      intro i x hx
      have hi : i < lh s₂ := by simpa [← h] using H₁.lt_lh_of_mem hx
      rcases H i _ _ hx (H₂.nth_mem hi)
      simp


-- @@ L342-358 expanded
@[simp]
lemma _root_.LO.Arith.Seq.seqCons_ext {a₁ a₂ s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) :
    seqCons s₁ a₁ = seqCons s₂ a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by
    intro h
    have hs₁s₂ : lh s₁ = lh s₂ := by simpa [H₁, H₂] using congr_arg lh h
    have hs₁ : pair (lh s₁) a₁ ∈ seqCons s₂ a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
    have hs₂ : pair (lh s₁) a₂ ∈ seqCons s₂ a₂ := by simp [hs₁s₂]
    have ha₁a₂ : a₁ = a₂ := (H₂.seqCons a₂).isMapping.uniq hs₁ hs₂
    have : s₁ ⊆ s₂ :=
      subset_pair <| by
        intro i x hix
        have : i = lh s₂ ∧ x = a₂ ∨ pair i x ∈ s₂ := by
          simpa [mem_seqCons_iff, h] using Seq.subset_seqCons s₁ a₁ hix
        rcases this with (⟨rfl, rfl⟩ | hix₂)
        · have := H₁.lt_lh_of_mem hix; simp [hs₁s₂] at this
        · assumption
    exact ⟨ha₁a₂, H₁.eq_of_eq_of_subset H₂ hs₁s₂ this⟩, by rintro ⟨rfl, rfl⟩; rfl⟩


-- @@ L360-362 verbatim
/-- TODO: move to Lemmata.lean -/
lemma ne_zero_iff_one_le {a : V} : a ≠ 0 ↔ 1 ≤ a :=
  Iff.trans pos_iff_ne_zero.symm (pos_iff_one_le (a := a))


-- @@ L364-389 expanded
lemma _root_.LO.Arith.Seq.cases_iff {s : V} : Seq s ↔ s = ∅ ∨ ∃ x s', Seq s' ∧ s = seqCons s' x :=
  ⟨fun h ↦ by
    by_cases hs : lh s = 0
    · left
      simpa [hs] using h.domain_eq
    · right
      let i := lh s - 1
      have hi : i < lh s := pred_lt_self_of_pos (pos_iff_ne_zero.mpr hs)
      have lhs_eq : lh s = i + 1 := Eq.symm <| tsub_add_cancel_of_le <| ne_zero_iff_one_le.mp hs
      let s' := bitRemove (pair i (h.nth hi)) s
      have his : pair i (h.nth hi) ∈ s := h.nth_mem hi
      have hdoms' : domain s' = under i :=
        by
        simp only [domain_bitRemove_of_isMapping_of_mem h.isMapping his, h.domain_eq, s']
        apply mem_ext
        simp only [lhs_eq, under_succ, mem_bitRemove_iff, ne_eq, mem_bitInsert_iff, mem_under_iff,
          and_or_left, not_and_self, false_or, and_iff_right_iff_imp]
        intro j hj; exact ne_of_lt hj
      have hs' : Seq s' := ⟨h.isMapping.of_subset (by simp [s']), i, hdoms'⟩
      have hs'i : lh s' = i := by simpa [hs'.domain_eq] using hdoms'
      exact
        ⟨h.nth hi, s', hs',
          mem_ext <| fun v ↦ by
            simp only [seqCons, hs'i, mem_bitInsert_iff]
            simp [s']
            by_cases hv : v = pair i (h.nth hi) <;> simp [hv]⟩,
    by
    rintro (rfl | ⟨x, s', hs', rfl⟩)
    · simp
    · exact hs'.seqCons x⟩


-- @@ L391-391 verbatim
alias ⟨Seq.cases, _⟩ := Seq.cases_iff


-- @@ L393-405 expanded
@[elab_as_elim]
theorem seq_induction (Γ) {P : V → Prop} (hP : BoldfacePred Γ-[1] P) (hnil : P ∅)
    (hcons : ∀ s x, Seq s → P s → P (seqCons s x)) : ∀ {s : V}, Seq s → P s :=
  by
  intro s sseq
  induction s using order_induction_h_sigma1
  · exact Γ
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind s ih =>
    have : s = ∅ ∨ ∃ x s', Seq s' ∧ s = seqCons s' x := sseq.cases
    rcases this with (rfl | ⟨x, s, hs, rfl⟩)
    · exact hnil
    · exact hcons s x hs (ih s (hs.lt_seqCons x) hs)


-- @@ L407-408 verbatim
/-- `!⟦x, y, z, ...⟧` notation for `Seq` -/
syntax "!⟦" term,* "⟧" : term


-- @@ L410-413 unexpanded
macro_rules
  | `(!⟦$terms:term,*, $term:term⟧) => `(seqCons !⟦$terms,*⟧ $term)
  | `(!⟦$term:term⟧) => `(seqCons ∅ $term)
  | `(!⟦⟧) => `(∅)


-- @@ L415-421 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander seqCons]
meta def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ !⟦$term2, $terms,*⟧ $term) => `(!⟦$term2, $terms,*, $term⟧)
  | `($_ !⟦$term2⟧ $term) => `(!⟦$term2, $term⟧)
  | `($_ ∅ $term) => `(!⟦$term⟧)
  | _ => throw ()


-- @@ L423-423 expanded
@[simp]
lemma singleton_seq (x : V) : Seq (seqCons ∅ x) := by apply Seq.seqCons; simp


-- @@ L425-425 expanded
@[simp]
lemma doubleton_seq (x y : V) : Seq (seqCons (seqCons ∅ x) y) := by apply Seq.seqCons; simp


-- @@ L427-427 expanded
@[simp]
lemma mem_singleton_seq_iff (x y : V) : pair 0 x ∈ seqCons ∅ y ↔ x = y := by simp [mem_seqCons_iff]


-- @@ L429-429 verbatim
section «lp_section_4»


-- @@ L431-433 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.mkSeq₁Def : Sg0.Semisentence 2 :=
  .mkSigma
    (LO.FirstOrder.Rewriting.substitute seqConsDef
      (vecCons (#0) (vecCons (Semiterm.numeral 0) (vecCons #1 ![]))))
    (by simp)


-- @@ L435-436 expanded
lemma mkSeq₁_defined : DefinedFunction₁ Sg0 (fun x : V ↦ seqCons ∅ x) mkSeq₁Def := by intro v;
  simp [mkSeq₁Def]; rfl


-- @@ L438-439 expanded
@[simp]
lemma eval_mkSeq₁Def (v) : Semiformula.Evalbm V v mkSeq₁Def.val ↔ v 0 = seqCons ∅ (v 1) :=
  mkSeq₁_defined.df.iff v


-- @@ L441-441 expanded
instance mkSeq₁_definable : BoldfaceFunction₁ Sg0 (fun x : V ↦ seqCons ∅ x) :=
  mkSeq₁_defined.to_definable


-- @@ L443-443 expanded
instance mkSeq₁_definable' (Γ) : BoldfaceFunction₁ Γ (fun x : V ↦ seqCons ∅ x) :=
  mkSeq₁_definable.of_zero


-- @@ L445-447 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.mkSeq₂Def : Sg1.Semisentence 3 :=
  .mkSigma
    (ExQuantifier.ex
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute mkSeq₁Def (vecCons (#0) (vecCons #2 ![])))
        (LO.FirstOrder.Rewriting.substitute seqConsDef
          (vecCons (#1) (vecCons (#0) (vecCons #3 ![]))))))
    (by simp)


-- @@ L449-450 expanded
lemma mkSeq₂_defined : DefinedFunction₂ Sg1 (fun x y : V ↦ seqCons (seqCons ∅ x) y) mkSeq₂Def := by
  intro v; simp [mkSeq₂Def]


-- @@ L452-453 expanded
@[simp]
lemma eval_mkSeq₂Def (v) :
    Semiformula.Evalbm V v mkSeq₂Def.val ↔ v 0 = seqCons (seqCons ∅ (v 1)) (v 2) :=
  mkSeq₂_defined.df.iff v


-- @@ L455-455 expanded
instance mkSeq₂_definable : BoldfaceFunction₂ Sg1 (fun x y : V ↦ seqCons (seqCons ∅ x) y) :=
  mkSeq₂_defined.to_definable


-- @@ L457-458 expanded
instance mkSeq₂_definable' (Γ m) :
    BoldfaceFunction₂ Γ-[m + 1] (fun x y : V ↦ seqCons (seqCons ∅ x) y) :=
  mkSeq₂_definable.of_sigmaOne


-- @@ L460-460 verbatim
end «lp_section_4»


-- @@ L462-466 expanded
theorem sigmaOne_skolem_seq {R : V → V → Prop} (hP : BoldfaceRel Sg1 R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ s, Seq s ∧ lh s = l ∧ ∀ i x, pair i x ∈ s → R i x :=
  by
  rcases sigmaOne_skolem hP (show ∀ x ∈ under l, ∃ y, R x y by simpa using H) with ⟨s, ms, sdom, h⟩
  have : Seq s := ⟨ms, l, sdom⟩
  exact ⟨s, this, by simpa [this.domain_eq] using sdom, h⟩


-- @@ L468-475 expanded
theorem sigmaOne_skolem_seq! {R : V → V → Prop} (hP : BoldfaceRel Sg1 R) {l}
    (H : ∀ x < l, ∃! y, R x y) : ∃! s, Seq s ∧ lh s = l ∧ ∀ i x, pair i x ∈ s → R i x :=
  by
  have : ∀ x < l, ∃ y, R x y := fun x hx ↦ (H x hx).exists
  rcases sigmaOne_skolem_seq hP this with ⟨s, Ss, rfl, hs⟩
  exact
    ExistsUnique.intro s ⟨Ss, rfl, hs⟩
      (by
        rintro s' ⟨Ss', hss', hs'⟩
        exact
          Seq.lh_ext Ss' Ss hss'
            (fun i x₁ x₂ h₁ h₂ ↦ H i (Ss.lt_lh_of_mem h₂) |>.unique (hs' i x₁ h₁) (hs i x₂ h₂)))


-- @@ L477-477 verbatim
section «lp_section_5»


-- @@ L479-482 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def vecToSeq : {n : ℕ} → (Fin n → V) → V
  | 0, _ => ∅
  | n + 1, v => seqCons (vecToSeq (v ·.castSucc)) (v (Fin.last n))


-- @@ L484-484 verbatim
@[simp] lemma vecToSeq_nil : vecToSeq ![] = (∅ : V) := by simp [vecToSeq]


-- @@ L486-487 expanded
@[simp]
lemma vecToSeq_vecCons {n} (v : Fin n → V) (a : V) :
    vecToSeq (vecConsLast v a) = seqCons (vecToSeq v) a := by simp [vecToSeq]


-- @@ L489-493 verbatim
@[simp] lemma vecToSeq_seq {n} (v : Fin n → V) : Seq (vecToSeq v) := by
  induction n with
  | zero => simp [vecToSeq]
  | succ n ih =>
    simpa only [vecToSeq] using (ih _).seqCons _


-- @@ L495-498 verbatim
@[simp] lemma lh_vecToSeq {n} (v : Fin n → V) : lh (vecToSeq v) = n := by
  induction n with
  | zero => simp [vecToSeq]
  | succ n ih => simp [vecToSeq, *]


-- @@ L500-509 expanded
lemma mem_vectoSeq {n : ℕ} (v : Fin n → V) (i : Fin n) : pair (i : V) (v i) ∈ vecToSeq v := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [vecToSeq]
    cases i using Fin.lastCases with
    | last => simp [mem_seqCons_iff]
    | cast i =>
      simp only [Fin.val_castSucc, mem_seqCons_iff, lh_vecToSeq, Nat.cast_inj]
      right; exact ih (v ·.castSucc) i


-- @@ L511-511 verbatim
end «lp_section_5»


-- @@ L513-513 verbatim
open HierarchySymbol


-- @@ L515-605 expanded
lemma order_ball_induction_sigma1 {f : V → V → V} (hf : BoldfaceFunction₂ Sg1 f) {P : V → V → Prop}
    (hP : BoldfaceRel Sg1 P) (ind : ∀ x y, (∀ x' < x, ∀ y' ≤ f x y, P x' y') → P x y) :
    ∀ x y, P x y :=
  by
  have maxf : ∀ x y, ∃ m, ∀ x' ≤ x, ∀ y' ≤ y, f x' y' ≤ m :=
    by
    intro x y; rcases sigma₁_replacement₂ hf (under (x + 1)) (under (y + 1)) |>.exists with ⟨m, hm⟩
    exact
      ⟨m, fun x' hx' y' hy' ↦
        le_of_lt <|
          lt_of_mem <|
            hm (f x' y') |>.mpr
              ⟨x', by simpa [lt_succ_iff_le, le_def] using hx', y', by
                simpa [lt_succ_iff_le, le_def] using hy', rfl⟩⟩
  intro x y
  have :
    ∀ k ≤ x,
      ∃ W,
        Seq W ∧
          k + 1 = lh W ∧
            pair 0 y ∈ W ∧
              ∀ l < k,
                ∀ m < W,
                  ∀ m' < W,
                    pair l m ∈ W → pair (l + 1) m' ∈ W → ∀ x' ≤ x - l, ∀ y' ≤ m, f x' y' ≤ m' :=
    by
    intro k hk
    induction k using induction_sigma1
    · apply
        Boldface.imp
          (Boldface.comp₂
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability])))
      apply Boldface.ex
      apply
        Boldface.and
          (Boldface.comp₁
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability])))
      apply
        Boldface.and
          (Boldface.comp₂ (BoldfaceFunction.comp₂ (.var _) (.const _))
            (BoldfaceFunction.comp₁ (.var _)))
      apply
        Boldface.and
          (Boldface.comp₂ (.var 0)
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability])))
      iterate 3 apply Boldface.ball_lt (.var _)
      apply Boldface.imp (Boldface.comp₂ (.var _) (BoldfaceFunction.comp₂ (.var _) (.var _)))
      apply
        Boldface.imp
          (Boldface.comp₂ (.var _)
            (BoldfaceFunction.comp₂ (BoldfaceFunction.comp₂ (.var _) (.const _)) (.var _)))
      apply Boldface.ball_le (Boldface.comp₂ (.var _) (BoldfaceFunction.comp₂ (.const _) (.var _)))
      apply Boldface.ball_le (.var _)
      apply Boldface.comp₂ (BoldfaceFunction.comp₂ (.var _) (.var _)) (.var _)
    case zero => exact ⟨seqCons ∅ y, by simp⟩
    case succ k ih =>
      rcases ih (le_trans le_self_add hk) with ⟨W, SW, hkW, hW₀, hWₛ⟩
      let m₀ := SW.nth (show k < lh W by simp [← hkW])
      have : ∃ m₁, ∀ x' ≤ x - k, ∀ y' ≤ m₀, f x' y' ≤ m₁ := maxf (x - k) m₀
      rcases this with ⟨m₁, hm₁⟩
      exact
        ⟨seqCons W m₁, SW.seqCons m₁, by simp [SW, hkW], Seq.subset_seqCons _ _ hW₀,
          by
          intro l hl m _ m' _ hm hm' x' hx' y' hy'
          rcases show l ≤ k from lt_succ_iff_le.mp hl with (rfl | hl)
          · have hmm₀ : m = m₀ :=
              by
              simp only [mem_seqCons_iff, ← hkW, left_eq_add, one_ne_zero, false_and,
                false_or] at hm
              exact SW.isMapping.uniq hm (by simp [m₀])
            simp_all
          · have Hm : pair l m ∈ W := Seq.mem_seqCons_iff_of_lt (by simpa [← hkW]) |>.mp hm
            have Hm' : pair (l + 1) m' ∈ W := Seq.mem_seqCons_iff_of_lt (by simpa [← hkW]) |>.mp hm'
            exact hWₛ l hl m (lt_of_mem_rng Hm) m' (lt_of_mem_rng Hm') Hm Hm' x' hx' y' hy'⟩
  rcases this x (by rfl) with ⟨W, SW, hxW, hW₀, hWₛ⟩
  have : ∀ i ≤ x, ∀ m < W, pair (x - i) m ∈ W → ∀ x' ≤ i, ∀ y' ≤ m, P x' y' :=
    by
    intro i
    induction i using induction_sigma1
    · apply Boldface.imp (Boldface.comp₂ (.var _) (.const _))
      apply Boldface.ball_lt (.const _)
      apply
        Boldface.imp
          (Boldface.comp₂ (.const _)
            (BoldfaceFunction.comp₂ (BoldfaceFunction.comp₂ (.const _) (.var _)) (.var _)))
      apply Boldface.ball_le (.var _)
      apply Boldface.ball_le (.var _)
      apply Boldface.comp₂ (.var _) (.var _)
    case zero => simp_all
    case succ i ih' =>
      intro hi m _ hm x' hx' y' hy'
      have ih : ∀ m < W, pair (x - i) m ∈ W → ∀ x' ≤ i, ∀ y' ≤ m, P x' y' :=
        ih' (le_trans le_self_add hi)
      refine ind x' y' ?_
      intro x'' hx'' y'' hy''
      let m₁ := SW.nth (show x - i < lh W by simp [← hxW, lt_succ_iff_le])
      have : f x' y' ≤ m₁ :=
        hWₛ (x - (i + 1)) (tsub_lt_iff_left hi |>.mpr (by simp)) m (lt_of_mem_rng hm) m₁
          (by simp [m₁]) hm
          (by rw [← sub_sub, sub_add_self_of_le (show 1 ≤ x - i from le_tsub_of_add_le_left hi)];
            simp [m₁])
          x' (by simp [tsub_tsub_cancel_of_le hi, hx']) y' hy'
      exact
        ih m₁ (by simp [m₁]) (by simp [m₁]) x'' (lt_succ_iff_le.mp (lt_of_lt_of_le hx'' hx')) y''
          (le_trans hy'' this)
  exact this x (by rfl) y (lt_of_mem_rng hW₀) (by simpa using hW₀) x (by rfl) y (by rfl)


-- @@ L607-611 expanded
lemma order_ball_induction_sigma1' {f : V → V} (hf : BoldfaceFunction₁ Sg1 f) {P : V → V → Prop}
    (hP : BoldfaceRel Sg1 P) (ind : ∀ x y, (∀ x' < x, ∀ y' ≤ f y, P x' y') → P x y) :
    ∀ x y, P x y :=
  have : BoldfaceFunction₂ Sg1 (fun _ ↦ f) := BoldfaceFunction.comp₁ (by simp)
  order_ball_induction_sigma1 this hP ind


-- @@ L613-637 expanded
lemma order_ball_induction₂_sigma1 {fy fz : V → V → V → V} (hfy : BoldfaceFunction₃ Sg1 fy)
    (hfz : BoldfaceFunction₃ Sg1 fz) {P : V → V → V → Prop} (hP : BoldfaceRel₃ Sg1 P)
    (ind : ∀ x y z, (∀ x' < x, ∀ y' ≤ fy x y z, ∀ z' ≤ fz x y z, P x' y' z') → P x y z) :
    ∀ x y z, P x y z :=
  by
  let Q : V → V → Prop := fun x w ↦ P x (pi₁ w) (pi₂ w)
  have hQ : BoldfaceRel Sg1 Q := by
    simp only [Q]
    apply
      Boldface.comp₃ (.var _) (BoldfaceFunction.comp₁ (.var _)) (BoldfaceFunction.comp₁ (.var _))
  let f : V → V → V := fun x w ↦ pair (fy x (pi₁ w) (pi₂ w)) (fz x (pi₁ w) (pi₂ w))
  have hf : BoldfaceFunction₂ Sg1 f := by
    simp only [f]
    apply BoldfaceFunction.comp₂
    · apply BoldfaceFunction.comp₃ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
    · apply BoldfaceFunction.comp₃ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
      · apply BoldfaceFunction.comp₁ (.var _)
  intro x y z
  simpa [Q] using
    order_ball_induction_sigma1 hf hQ
      (fun x w ih ↦
        ind x (pi₁ w) (pi₂ w)
          (fun x' hx' y' hy' z' hz' ↦ by
            simpa [Q] using ih x' hx' (pair y' z') (pair_le_pair hy' hz')))
      x (pair y z)


-- @@ L639-680 expanded
lemma order_ball_induction₃_sigma1 {fy fz fw : V → V → V → V → V} (hfy : BoldfaceFunction₄ Sg1 fy)
    (hfz : BoldfaceFunction₄ Sg1 fz) (hfw : BoldfaceFunction₄ Sg1 fw) {P : V → V → V → V → Prop}
    (hP : BoldfaceRel₄ Sg1 P)
    (ind :
      ∀ x y z w,
        (∀ x' < x, ∀ y' ≤ fy x y z w, ∀ z' ≤ fz x y z w, ∀ w' ≤ fw x y z w, P x' y' z' w') →
          P x y z w) :
    ∀ x y z w, P x y z w :=
  by
  let Q : V → V → Prop := fun x v ↦ P x (pi₁ v) (pi₁ (pi₂ v)) (pi₂ (pi₂ v))
  have hQ : BoldfaceRel Sg1 Q := by
    simp only [Q]
    apply
      Boldface.comp₄ (.var _) (BoldfaceFunction.comp₁ <| .var _)
        (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
        (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
  let f : V → V → V := fun x v ↦
    pair (fy x (pi₁ v) (pi₁ (pi₂ v)) (pi₂ (pi₂ v)))
      (pair (fz x (pi₁ v) (pi₁ (pi₂ v)) (pi₂ (pi₂ v))) (fw x (pi₁ v) (pi₁ (pi₂ v)) (pi₂ (pi₂ v))))
  have hf : BoldfaceFunction₂ Sg1 f := by
    simp only [f]
    apply BoldfaceFunction.comp₂
    ·
      apply
        BoldfaceFunction.comp₄ (.var _) (BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
          (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
    · apply BoldfaceFunction.comp₂
      ·
        apply
          BoldfaceFunction.comp₄ (.var _) (BoldfaceFunction.comp₁ <| .var _)
            (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
            (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
      ·
        apply
          BoldfaceFunction.comp₄ (.var _) (BoldfaceFunction.comp₁ <| .var _)
            (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
            (BoldfaceFunction.comp₁ <| BoldfaceFunction.comp₁ <| .var _)
  intro x y z w
  have :=
    order_ball_induction_sigma1 hf hQ
      (fun x v ih ↦
        ind x (pi₁ v) (pi₁ (pi₂ v)) (pi₂ (pi₂ v))
          (fun x' hx' y' hy' z' hz' w' hw' ↦ by
            simpa [Q] using
              ih x' hx' (pair y' (pair z' w')) (pair_le_pair hy' <| pair_le_pair hz' hw')))
      x (pair y (pair z w))
  simpa [Q] using this


-- @@ L682-682 verbatim
end Arith

-- @@ L683-683 verbatim
end LO


-- @@ L685-685 verbatim
end «lp_nc_section_1»
