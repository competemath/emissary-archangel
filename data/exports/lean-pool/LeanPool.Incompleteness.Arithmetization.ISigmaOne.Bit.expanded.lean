/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaZero.Exponential.Log
import LeanPool.Incompleteness.Arithmetization.Definability.Absoluteness
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L13-13 verbatim
/-! # Bit -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L20-20 verbatim
open scoped Length


-- @@ L22-22 verbatim
namespace LO

-- @@ L23-23 verbatim
namespace Arith


-- @@ L25-25 verbatim
open scoped Length


-- @@ L27-27 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L29-29 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L31-31 expanded
variable [ModelsTheory V (iSigma 1)]


-- @@ L33-34 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Bit (i a : V) : Prop :=
  LenBit (Exp.exp i) a


-- @@ L36-36 verbatim
instance instMembershipVV : Membership V V := ⟨fun a i ↦ Bit i a⟩


-- @@ L38-40 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.bitDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute expDef (vecCons (#0) (vecCons #1 ![])))
        (LO.FirstOrder.Rewriting.substitute lenbitDef (vecCons (#0) (vecCons #2 ![])))))
    (by simp)


-- @@ L42-52 expanded
lemma bit_defined : DefinedRel Sg0 ((· ∈ ·) : V → V → Prop) bitDef :=
  by
  intro v
  simp only [Fin.isValue, bitDef, Nat.reduceAdd, Nat.succ_eq_add_one,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.vecCons_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.constant_eq_singleton,
    exp_defined_iff, Matrix.cons_app_two, lenbit_defined_iff, LogicalConnective.Prop.and_eq,
    ↓existsAndEq, true_and]
  constructor
  · intro h; exact ⟨h.le, h⟩
  · exact And.right


-- @@ L54-55 verbatim
@[simp] lemma bit_defined_iff (v) :
    Semiformula.Evalbm V v bitDef.val ↔ v 0 ∈ v 1 := bit_defined.df.iff v


-- @@ L57-57 expanded
instance mem_definable : BoldfaceRel Sg0 ((· ∈ ·) : V → V → Prop) :=
  bit_defined.to_definable


-- @@ L59-61 expanded
instance mem_definable' (ℌ : HierarchySymbol) : BoldfaceRel ℌ ((· ∈ ·) : V → V → Prop) :=
  mem_definable.of_zero


-- @@ L63-64 expanded
instance mem_definable'' (ℌ : HierarchySymbol) : BoldfaceRel ℌ (Membership.mem : V → V → Prop) := by
  simpa using (mem_definable' ℌ).retraction (n := 2) ![1, 0]


-- @@ L66-67 verbatim
lemma mem_absolute (i a : ℕ) : i ∈ a ↔ (i : V) ∈ (a : V) := by
  simpa using Defined.shigmaZero_absolute V bit_defined bit_defined ![i, a]


-- @@ L69-69 verbatim
lemma mem_iff_bit {i a : V} : i ∈ a ↔ Bit i a := iff_of_eq rfl


-- @@ L71-71 expanded
lemma exp_le_of_mem {i a : V} (h : i ∈ a) : Exp.exp i ≤ a :=
  LenBit.le h


-- @@ L73-73 verbatim
lemma lt_of_mem {i a : V} (h : i ∈ a) : i < a := lt_of_lt_of_le (lt_exp i) (exp_le_of_mem h)


-- @@ L75-76 expanded
lemma not_mem_of_lt_exp {i a : V} (h : a < Exp.exp i) : i ∉ a := fun H ↦ by
  have := lt_of_le_of_lt (exp_le_of_mem H) h; simp at this


-- @@ L78-78 verbatim
section «lp_section_1»


-- @@ L80-89 expanded
@[aesop 10 (rule_sets := [Definability]) safe]
lemma _root_.LO.Arith.HierarchySymbol.Boldface.ball_mem (Γ m) {P : (Fin k → V) → V → Prop}
    {f : (Fin k → V) → V} (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x ∈ f v, P v x) :=
  by
  have : Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v, x ∈ f v → P v x) :=
    .ball_lt hf
      (.imp (HierarchySymbol.Boldface.comp₂ (P := (· ∈ ·)) (.var 0) (hf.retraction Fin.succ)) h)
  exact
    this.of_iff <| by intro v; exact ⟨fun h x _ hxv ↦ h x hxv, fun h x hx ↦ h x (lt_of_mem hx) hx⟩


-- @@ L91-104 expanded
@[aesop 10 (rule_sets := [Definability]) safe]
lemma _root_.LO.Arith.HierarchySymbol.Boldface.bex_mem (Γ m) {P : (Fin k → V) → V → Prop}
    {f : (Fin k → V) → V} (hf : SigmaSymbol.sigma-[m + 1].BoldfaceFunction f)
    (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x ∈ f v, P v x) :=
  by
  have : Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v, x ∈ f v ∧ P v x) :=
    .bex_lt hf (.and (HierarchySymbol.Boldface.comp₂ (P := (· ∈ ·)) (.var 0) (hf.retraction _)) h)
  exact
    this.of_iff <| by
      intro v
      exact
        ⟨by
          rintro ⟨x, hx, hxv⟩
          exact ⟨x, lt_of_mem hx, hx, hxv⟩,
          by
          rintro ⟨x, _, hx, hvx⟩
          exact ⟨x, hx, hvx⟩⟩


-- @@ L106-106 verbatim
end «lp_section_1»


-- @@ L108-108 verbatim
end Arith

-- @@ L109-109 verbatim
end LO


-- @@ L111-111 verbatim
end «lp_nc_section_1»


-- @@ L113-113 verbatim
namespace LO

-- @@ L114-114 verbatim
namespace FirstOrder

-- @@ L115-115 verbatim
namespace Arith


-- @@ L117-117 verbatim
variable {ξ : Type*} {n}


-- @@ L119-119 expanded
instance : Semiformula.Operator.Mem oRing :=
  ⟨⟨bitDef.val⟩⟩


-- @@ L121-122 verbatim
lemma operator_mem_def : Semiformula.Operator.Mem.mem.sentence = bitDef.val := by
  simp [Semiformula.Operator.Mem.mem]


-- @@ L124-126 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ballIn (t : Semiterm oRing ξ n) (p : Semiformula oRing ξ (n + 1)) : Semiformula oRing ξ n :=
  Semiformula.ballLT t
    (Arrow.arrow (Semiformula.Operator.operator Operator.Mem.mem ![#0, (Rew.bShift t)])
      (LO.FirstOrder.Rewriting.substitute p (vecCons #0 fun x ↦ #(finSuccItr x 1))))


-- @@ L128-130 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def bexIn (t : Semiterm oRing ξ n) (p : Semiformula oRing ξ (n + 1)) : Semiformula oRing ξ n :=
  Semiformula.bexLT t
    (Wedge.wedge (Semiformula.Operator.operator Operator.Mem.mem ![#0, (Rew.bShift t)])
      (LO.FirstOrder.Rewriting.substitute p (vecCons #0 fun x ↦ #(finSuccItr x 1))))


-- @@ L132-134 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.Hierarchy.bit {t u : Semiterm oRing μ n} :
    Hierarchy Γ s (Semiformula.Operator.operator Operator.Mem.mem ![t, u]) := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec₂, operator_mem_def]


-- @@ L136-140 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.Hieralchy.ballIn {Γ m} (t : Semiterm oRing ξ n)
    (p : Semiformula oRing ξ (n + 1)) : Hierarchy Γ m (ballIn t p) ↔ Hierarchy Γ m p :=
  by
  simp only [Arith.ballIn]
  simp [Semiformula.Operator.operator, operator_mem_def]


-- @@ L142-146 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.Hieralchy.bexIn {Γ m} (t : Semiterm oRing ξ n)
    (p : Semiformula oRing ξ (n + 1)) : Hierarchy Γ m (bexIn t p) ↔ Hierarchy Γ m p :=
  by
  simp only [Arith.bexIn]
  simp [Semiformula.Operator.operator, operator_mem_def]


-- @@ L148-150 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def memRel : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc
      ((Semiterm.Operator.npow _ 2).operator
        ![Semiterm.Operator.Add.add.operator
            ![Semiterm.Operator.Add.add.operator ![#1, #2], Semiterm.numeral 1]])
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#0) (vecCons (#2) (vecCons #3 ![]))))
        (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])))
    (by simp)


-- @@ L152-155 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def memRel₃ : Sg0.Semisentence 4 :=
  .mkSigma
    (Semiformula.bexLTSucc
      ((Semiterm.Operator.npow _ 2).operator
        ![Semiterm.Operator.Add.add.operator
            ![Semiterm.Operator.Add.add.operator ![#2, #3], Semiterm.numeral 1]])
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#0) (vecCons (#3) (vecCons #4 ![]))))
        (Semiformula.bexLTSucc
          ((Semiterm.Operator.npow _ 2).operator
            ![Semiterm.Operator.Add.add.operator
                ![Semiterm.Operator.Add.add.operator ![#2, #0], Semiterm.numeral 1]])
          (Wedge.wedge
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#0) (vecCons (#3) (vecCons #1 ![]))))
            (Semiformula.Operator.operator Operator.Mem.mem ![#0, #2])))))
    (by simp)


-- @@ L157-158 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def memRelOpr : Semiformula.Operator oRing 3 :=
  ⟨memRel.val⟩


-- @@ L160-161 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def memRel₃Opr : Semiformula.Operator oRing 4 :=
  ⟨memRel₃.val⟩


-- @@ L163-163 verbatim
section «lp_section_2»


-- @@ L165-165 verbatim
open Lean PrettyPrinter Delaborator


-- @@ L167-168 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " ∈' " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L169-170 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " ∈' " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula


-- @@ L172-180 expanded
macro_rules
  | `(ballIn foTerm[$binders* | $fbinders* | $t] foFormula[$x$binders* | $fbinders* | $p]) => do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(ballIn foTerm[$binders* | $fbinders* | $t] foFormula[$binders'* | $fbinders* | $p])
  | `(bexIn foTerm[$binders* | $fbinders* | $t] foFormula[$x$binders* | $fbinders* | $p]) => do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(bexIn foTerm[$binders* | $fbinders* | $t] foFormula[$binders'* | $fbinders* | $p])


-- @@ L182-183 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∼[" firstOrderTerm "]" firstOrderTerm:0 : firstOrderFormula

-- @@ L184-185 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≁[" firstOrderTerm "]" firstOrderTerm:0 : firstOrderFormula

-- @@ L186-188 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 ":⟪" firstOrderTerm ", " firstOrderTerm "⟫:∈ " firstOrderTerm:0 :
    firstOrderFormula

-- @@ L189-191 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 ":⟪" firstOrderTerm ", " firstOrderTerm ", " firstOrderTerm "⟫:∈ "
    firstOrderTerm:0 : firstOrderFormula


-- @@ L193-214 expanded
macro_rules
  |
  `(memRelOpr.operator
        ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₁:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₂:firstOrderTerm]]) =>
    `(memRelOpr.operator
        ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t₁],
          foTerm[$binders* | $fbinders* | $t₂]])
  |
  `(Tilde.tilde
        (memRelOpr.operator
          ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
            foTerm[$binders* | $fbinders* | $t₁:firstOrderTerm],
            foTerm[$binders* | $fbinders* | $t₂:firstOrderTerm]])) =>
    `(Tilde.tilde
        (memRelOpr.operator
          ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t₁],
            foTerm[$binders* | $fbinders* | $t₂]]))
  |
  `(memRelOpr.operator
        ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₁:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₂:firstOrderTerm]]) =>
    `(memRelOpr.operator
        ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t₁],
          foTerm[$binders* | $fbinders* | $t₂]])
  |
  `(memRel₃Opr.operator
        ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₁:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₂:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t₃:firstOrderTerm]]) =>
    `(memRel₃Opr.operator
        ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t₁],
          foTerm[$binders* | $fbinders* | $t₂], foTerm[$binders* | $fbinders* | $t₃]])


-- @@ L215-215 verbatim
end «lp_section_2»


-- @@ L217-219 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.Hierarchy.memRel {t₁ t₂ u : Semiterm oRing μ n} :
    Hierarchy Γ s (memRelOpr.operator ![u, t₁, t₂]) := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec₂, memRelOpr]


-- @@ L221-223 expanded
@[simp]
lemma _root_.LO.FirstOrder.Arith.Hierarchy.memRel₃ {t₁ t₂ t₃ u : Semiterm oRing μ n} :
    Hierarchy Γ s (memRel₃Opr.operator ![u, t₁, t₂, t₃]) := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec₂, memRel₃Opr]


-- @@ L225-225 expanded
variable {V : Type*} [ORingStruc V] [ModelsTheory V (iSigma 1)]


-- @@ L227-227 verbatim
open LO.Arith


-- @@ L229-230 expanded
scoped instance : Structure.Mem oRing V :=
  ⟨by intro a b; simp [Semiformula.Operator.val, operator_mem_def, bit_defined.df.iff]⟩


-- @@ L232-241 expanded
@[simp]
lemma eval_ballIn {t : Semiterm oRing ξ n} {p : Semiformula oRing ξ (n + 1)} {e ε} :
    Semiformula.Evalm V e ε (ballIn t p) ↔
      ∀ x ∈ t.valm V e ε, Semiformula.Evalm V (vecCons x e) ε p :=
  by
  simp only [ballIn, Matrix.zero_cons_succ_eq_self, Semiformula.eval_ballLT, Nat.succ_eq_add_one,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂, Semiterm.val_bvar,
    Matrix.vecCons_zero, Semiterm.val_bShift, Structure.Mem.mem, Semiformula.eval_substs,
    LogicalConnective.Prop.arrow_eq]
  constructor
  · intro h x hx; exact h x (lt_of_mem hx) hx
  · intro h x _ hx; exact h x hx


-- @@ L243-251 expanded
@[simp]
lemma eval_bexIn {t : Semiterm oRing ξ n} {p : Semiformula oRing ξ (n + 1)} {e ε} :
    Semiformula.Evalm V e ε (bexIn t p) ↔
      ∃ x ∈ t.valm V e ε, Semiformula.Evalm V (vecCons x e) ε p :=
  by
  simp only [bexIn, Matrix.zero_cons_succ_eq_self, Semiformula.eval_bexLT, Nat.succ_eq_add_one,
    LogicalConnective.HomClass.map_and, Semiformula.eval_operator₂, Semiterm.val_bvar,
    Matrix.vecCons_zero, Semiterm.val_bShift, Structure.Mem.mem, Semiformula.eval_substs,
    LogicalConnective.Prop.and_eq]
  constructor
  · rintro ⟨x, _, hx, h⟩; exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨x, lt_of_mem hx, hx, h⟩


-- @@ L253-254 expanded
lemma memRel_defined : DefinedRel₃ Sg0 (fun r x y : V ↦ pair x y ∈ r) memRel := by intro v;
  simp [memRel, pair_defined.df.iff]


-- @@ L256-257 expanded
lemma memRel₃_defined : DefinedRel₄ Sg0 (fun r x y z : V ↦ pair x (pair y z) ∈ r) memRel₃ := by
  intro v; simp [memRel₃, pair_defined.df.iff]


-- @@ L259-262 expanded
@[simp]
lemma eval_memRel {x y r : V} : memRelOpr.val ![r, x, y] ↔ pair x y ∈ r :=
  by
  unfold Semiformula.Operator.val
  simp [memRelOpr, memRel_defined.df.iff]


-- @@ L264-267 expanded
@[simp]
lemma eval_memRel₃ {x y z r : V} : memRel₃Opr.val ![r, x, y, z] ↔ pair x (pair y z) ∈ r :=
  by
  unfold Semiformula.Operator.val
  simp [memRel₃Opr, memRel₃_defined.df.iff]


-- @@ L269-269 verbatim
end Arith

-- @@ L270-270 verbatim
end FirstOrder

-- @@ L271-271 verbatim
end LO


-- @@ L273-273 verbatim
noncomputable section «lp_nc_section_2»


-- @@ L275-275 verbatim
namespace LO

-- @@ L276-276 verbatim
namespace Arith


-- @@ L278-278 verbatim
open scoped Length


-- @@ L280-280 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L282-282 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L284-284 expanded
variable [ModelsTheory V (iSigma 1)]


-- @@ L286-289 expanded
lemma mem_iff_mul_exp_add_exp_add {i a : V} :
    i ∈ a ↔ ∃ k, ∃ r < Exp.exp i, a = k * Exp.exp (i + 1) + Exp.exp i + r :=
  by
  rw [mem_iff_bit, exp_succ]
  exact lenbit_iff_add_mul (exp_pow2 i) (a := a)


-- @@ L291-293 expanded
lemma not_mem_iff_mul_exp_add {i a : V} :
    i ∉ a ↔ ∃ k, ∃ r < Exp.exp i, a = k * Exp.exp (i + 1) + r :=
  by
  rw [mem_iff_bit, exp_succ]
  exact not_lenbit_iff_add_mul (exp_pow2 i) (a := a)


-- @@ L295-295 verbatim
section «lp_section_3»


-- @@ L297-298 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instEmptyCollectionV : EmptyCollection V := ⟨0⟩


-- @@ L300-301 expanded
omit [ModelsTheory V (iSigma 1)] in
lemma emptyset_def : (∅ : V) = 0 :=
  rfl


-- @@ L303-303 verbatim
@[simp] lemma not_mem_empty (i : V) : i ∉ (∅ : V) := by simp [emptyset_def, mem_iff_bit, Bit]


-- @@ L305-305 verbatim
@[simp] lemma not_mem_zero (i : V) : i ∉ (0 : V) := by simp [mem_iff_bit, Bit]


-- @@ L307-307 verbatim
end «lp_section_3»


-- @@ L309-309 verbatim
section «lp_section_4»


-- @@ L311-312 expanded
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instSingletonVV : Singleton V V :=
  ⟨fun a ↦ Exp.exp a⟩


-- @@ L314-314 expanded
lemma singleton_def (a : V) : { a } = Exp.exp a :=
  rfl


-- @@ L316-316 verbatim
end «lp_section_4»


-- @@ L318-318 verbatim
section «lp_section_5»


-- @@ L320-322 expanded
open Classical in
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def bitInsert (i a : V) : V :=
  if i ∈ a then a else a + Exp.exp i


-- @@ L324-326 expanded
open Classical in
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def bitRemove (i a : V) : V :=
  if i ∈ a then a - Exp.exp i else a


-- @@ L328-329 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instInsertVV : Insert V V := ⟨bitInsert⟩


-- @@ L331-331 verbatim
lemma insert_eq {i a : V} : insert i a = bitInsert i a := rfl


-- @@ L333-335 verbatim
lemma singleton_eq_insert (i : V) : ({i} :
    V) = insert i ∅ := by
  simp [singleton_def, insert, bitInsert, emptyset_def]


-- @@ L337-338 verbatim
instance : LawfulSingleton V V where
  insert_empty_eq := fun x ↦ Eq.symm <| singleton_eq_insert x


-- @@ L340-349 verbatim
@[simp] lemma mem_bitInsert_iff {i j a : V} :
    i ∈ insert j a ↔ i = j ∨ i ∈ a := by
  by_cases h : j ∈ a <;> simp only [h, insert_eq, bitInsert, ↓reduceIte, mem_iff_bit, Bit]
  · constructor
    · exact fun hi => Or.inr hi
    · rintro (rfl | hi)
      · exact h
      · exact hi
  · have h2 := lenbit_add_pow2_iff_of_not_lenbit (exp_pow2 i) (exp_pow2 j) h
    rw [exp_inj.eq_iff] at h2; exact h2


-- @@ L351-362 verbatim
@[simp] lemma mem_bitRemove_iff {i j a : V} :
    i ∈ bitRemove j a ↔ i ≠ j ∧ i ∈ a := by
  by_cases h : j ∈ a
  · simp only [bitRemove, h, ↓reduceIte, mem_iff_bit]
    simp only [Bit]
    have h2 := lenbit_sub_pow2_iff_of_lenbit (exp_pow2 i) (exp_pow2 j) h
    rw [exp_inj.ne_iff] at h2; exact h2
  · simp only [bitRemove, h, ↓reduceIte]
    constructor
    · intro hi
      exact ⟨by rintro rfl; exact h hi, hi⟩
    · exact And.right


-- @@ L364-364 verbatim
@[simp 1100] lemma not_mem_bitRemove_self (i a : V) : i ∉ bitRemove i a := by simp


-- @@ L366-372 expanded
lemma insert_graph (b i a : V) :
    b = insert i a ↔ (i ∈ a ∧ b = a) ∨ (i ∉ a ∧ ∃ e ≤ b, e = Exp.exp i ∧ b = a + e) :=
  ⟨by rintro rfl; by_cases hi : i ∈ a <;> simp [hi, insert, bitInsert],
    by
    by_cases hi : i ∈ a <;>
      simp only [hi, true_and, not_true_eq_false, false_and, or_false, insert, bitInsert,
        ↓reduceIte, imp_self, not_false_eq_true, true_and, false_or, forall_exists_index, and_imp]
    rintro x _ rfl rfl; rfl⟩


-- @@ L374-376 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.insertDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Vee.vee
      (Wedge.wedge (Semiformula.Operator.operator Operator.Mem.mem ![#1, #2])
        (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2]))
      (Wedge.wedge (Tilde.tilde (Semiformula.Operator.operator Operator.Mem.mem ![#1, #2]))
        (Semiformula.bexLTSucc (#0)
          (Wedge.wedge (LO.FirstOrder.Rewriting.substitute expDef (vecCons (#0) (vecCons #2 ![])))
            (Semiformula.Operator.operator Operator.Eq.eq
              ![#1, Semiterm.Operator.Add.add.operator ![#3, #0]])))))
    (by simp)


-- @@ L378-379 expanded
lemma insert_defined : DefinedFunction₂ Sg0 (insert : V → V → V) insertDef := by intro v;
  simp [insertDef, insert_graph]


-- @@ L381-382 verbatim
@[simp] lemma insert_defined_iff (v) :
    Semiformula.Evalbm V v insertDef.val ↔ v 0 = insert (v 1) (v 2) := insert_defined.df.iff v


-- @@ L384-384 expanded
instance insert_definable : BoldfaceFunction₂ Sg0 (insert : V → V → V) :=
  insert_defined.to_definable


-- @@ L386-386 expanded
instance insert_definable' (Γ) : BoldfaceFunction₂ Γ (insert : V → V → V) :=
  insert_definable.of_zero


-- @@ L388-393 expanded
lemma insert_le_of_le_of_le {i j a b : V} (hij : i ≤ j) (hab : a ≤ b) :
    insert i a ≤ b + Exp.exp j := by
  by_cases hi : i ∈ a
  · simp only [insert, bitInsert, hi, ↓reduceIte]
    exact le_trans hab (by simp)
  · simp only [insert, bitInsert, hi, ↓reduceIte]
    exact add_le_add hab (exp_monotone_le.mpr hij)


-- @@ L395-395 verbatim
end «lp_section_5»


-- @@ L397-399 verbatim
lemma one_eq_singleton : (1 :
    V) = {∅} := by
  simp [singleton_eq_insert, insert, bitInsert, emptyset_def]


-- @@ L401-402 verbatim
@[simp] lemma mem_singleton_iff {i j : V} :
    i ∈ ({j} : V) ↔ i = j := by simp [singleton_eq_insert, -insert_empty_eq]


-- @@ L404-405 verbatim
lemma bitRemove_lt_of_mem {i a : V} (h : i ∈ a) : bitRemove i a < a := by
  simp [h, bitRemove, tsub_lt_iff_left (exp_le_of_mem h)]


-- @@ L407-409 verbatim
lemma pos_of_nonempty {i a : V} (h : i ∈ a) : 0 < a := by
  exact pos_iff_ne_zero.mpr (fun ha ↦ by
    simp_all)


-- @@ L411-411 verbatim
@[simp 1100] lemma mem_insert (i a : V) : i ∈ insert i a := by simp


-- @@ L413-414 verbatim
lemma insert_eq_self_of_mem {i a : V} (h : i ∈ a) : insert i a = a := by
  simp [insert_eq, bitInsert, h]


-- @@ L416-422 expanded
lemma log_mem_of_pos {a : V} (h : 0 < a) : log a ∈ a :=
  mem_iff_mul_exp_add_exp_add.mpr
    ⟨0, a - Exp.exp (log a),
      (tsub_lt_iff_left (exp_log_le_self h)).mpr
        (by rw [← two_mul]; exact lt_two_mul_exponential_log h),
      by
      simp only [zero_mul, zero_add]
      exact Eq.symm <| add_tsub_self_of_le (exp_log_le_self h)⟩


-- @@ L424-425 verbatim
lemma le_log_of_mem {i a : V} (h : i ∈ a) : i ≤ log a :=
  (exp_le_iff_le_log (pos_of_nonempty h)).mp (exp_le_of_mem h)


-- @@ L427-429 verbatim
lemma succ_mem_iff_mem_div_two {i a : V} :
    i + 1 ∈ a ↔ i ∈ a / 2 := by
  simp [mem_iff_bit, Bit, LenBit.iff_rem, exp_succ, div_mul]


-- @@ L431-432 verbatim
lemma lt_length_of_mem {i a : V} (h : i ∈ a) : i < ‖a‖ := by
  simpa [length_of_pos (pos_of_nonempty h), ←le_iff_lt_succ] using le_log_of_mem h


-- @@ L434-441 expanded
lemma lt_exp_iff {a i : V} : a < Exp.exp i ↔ ∀ j ∈ a, j < i :=
  ⟨fun h j hj ↦ exp_monotone.mp <| lt_of_le_of_lt (exp_le_of_mem hj) h,
    by
    contrapose
    simp only [not_lt, not_forall, exists_prop]
    intro (h : Exp.exp i ≤ a)
    have pos : 0 < a := lt_of_lt_of_le (by simp) h
    exact ⟨log a, log_mem_of_pos pos, (exp_le_iff_le_log pos).mp h⟩⟩


-- @@ L443-443 verbatim
instance instHasSubsetV : HasSubset V := ⟨fun a b ↦ ∀ ⦃i⦄, i ∈ a → i ∈ b⟩


-- @@ L445-447 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.bitSubsetDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.ballLT (#0)
      (Arrow.arrow (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
        (Semiformula.Operator.operator Operator.Mem.mem ![#0, #2])))
    (by simp)


-- @@ L449-455 expanded
lemma bitSubset_defined : DefinedRel Sg0 ((· ⊆ ·) : V → V → Prop) bitSubsetDef :=
  by
  intro v
  simp only [Fin.isValue, bitSubsetDef, Nat.reduceAdd, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_ballLT, Semiterm.val_bvar, Nat.succ_eq_add_one,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂, Matrix.vecCons_zero,
    Matrix.cons_val_one, Structure.Mem.mem, Matrix.cons_app_two, LogicalConnective.Prop.arrow_eq]
  exact ⟨by intro h x _ hx; exact h hx, by intro h x hx; exact h x (lt_of_mem hx) hx⟩


-- @@ L457-458 verbatim
@[simp] lemma bitSubset_defined_iff (v) :
    Semiformula.Evalbm V v bitSubsetDef.val ↔ v 0 ⊆ v 1 := bitSubset_defined.df.iff v


-- @@ L460-462 expanded
instance bitSubset_definable : BoldfaceRel Sg0 ((· ⊆ ·) : V → V → Prop) :=
  bitSubset_defined.to_definable₀


-- @@ L464-466 expanded
@[simp, aesop 10 (rule_sets := [Definability]) safe]
instance bitSubset_definable' (ℌ : HierarchySymbol) : BoldfaceRel ℌ ((· ⊆ ·) : V → V → Prop) :=
  bitSubset_defined.to_definable₀


-- @@ L468-468 verbatim
lemma subset_iff {a b : V} : a ⊆ b ↔ (∀ x ∈ a, x ∈ b) := by simp [HasSubset.Subset]


-- @@ L470-470 verbatim
@[refl, simp] lemma subset_refl (a : V) : a ⊆ a := by intro x; simp


-- @@ L472-473 verbatim
@[trans] lemma subset_trans {a b c : V} (hab : a ⊆ b) (hbc : b ⊆ c) : a ⊆ c := by
  intro x hx; exact hbc (hab hx)


-- @@ L475-489 expanded
lemma mem_exp_add_succ_sub_one (i j : V) : i ∈ Exp.exp (i + j + 1) - 1 :=
  by
  have :
    Exp.exp (i + j + 1) - 1 = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp i + (Exp.exp i - 1) :=
    calc
      Exp.exp (i + j + 1) - 1 = Exp.exp j * Exp.exp (i + 1) - 1 := by
        simp [exp_add, ← mul_assoc, mul_comm]
      _ = Exp.exp j * Exp.exp (i + 1) - Exp.exp (i + 1) + Exp.exp (i + 1) - 1 := by
        rw [sub_add_self_of_le]; exact le_mul_of_pos_left (exp_pos j)
      _ = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp (i + 1) - 1 := by simp [sub_mul]
      _ = (Exp.exp j - 1) * Exp.exp (i + 1) + (Exp.exp i + Exp.exp i) - 1 := by
        simp [← two_mul, ← exp_succ i]
      _ = (Exp.exp j - 1) * Exp.exp (i + 1) + (Exp.exp i + Exp.exp i - 1) := by
        rw [add_tsub_assoc_of_le]; simp [← two_mul, ← pos_iff_one_le]
      _ = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp i + (Exp.exp i - 1) := by
        simp [add_assoc, add_tsub_assoc_of_le]
  exact
    mem_iff_mul_exp_add_exp_add.mpr
      ⟨Exp.exp j - 1, Exp.exp i - 1, (tsub_lt_iff_left (by simp)).mpr <| by simp, this⟩


-- @@ L491-492 expanded
/-- under a = {0, 1, 2, ..., a - 1} -/
def under (a : V) : V :=
  Exp.exp a - 1


-- @@ L494-495 expanded
@[simp]
lemma le_under (a : V) : a ≤ under a :=
  le_iff_lt_succ.mpr
    (by simp [under, show Exp.exp a - 1 + 1 = Exp.exp a from sub_add_self_of_le (by simp)])


-- @@ L497-510 expanded
@[simp]
lemma mem_under_iff {i j : V} : i ∈ under j ↔ i < j :=
  by
  constructor
  · intro h
    have : Exp.exp i < Exp.exp j :=
      calc
        Exp.exp i ≤ Exp.exp j - 1 := exp_le_of_mem h
        _ < Exp.exp j := pred_lt_self_of_pos (exp_pos j)
    exact exp_monotone.mp this
  · intro lt
    have := lt_iff_succ_le.mp lt
    let k := j - (i + 1)
    have : j = i + k + 1 := by
      rw [add_assoc, add_comm k 1, ← add_assoc]
      simpa only [k] using (add_tsub_self_of_le this).symm
    rw [this]; exact mem_exp_add_succ_sub_one i k


-- @@ L512-512 verbatim
@[simp 1100] lemma not_mem_under_self (i : V) : i ∉ under i := by simp


-- @@ L514-520 expanded
private lemma under_graph (x y : V) : y = under x ↔ y + 1 = Exp.exp x :=
  ⟨by
    rintro rfl
    simp [under, sub_add_self_of_le], by
    intro h
    have := congr_arg (· - 1) h
    simpa [under] using this⟩


-- @@ L522-524 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.underDef : Sg0.Semisentence 2 :=
  .mkSigma
    (LO.FirstOrder.Rewriting.substitute expDef.val
      (vecCons (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]) (vecCons #1 ![])))
    (by simp)


-- @@ L526-527 expanded
lemma under_defined : DefinedFunction₁ Sg0 (under : V → V) underDef := by intro v;
  simp [underDef, under_graph]


-- @@ L529-530 verbatim
@[simp] lemma under_defined_iff (v) :
    Semiformula.Evalbm V v underDef.val ↔ v 0 = under (v 1) := under_defined.df.iff v


-- @@ L532-532 expanded
instance under_definable : BoldfaceFunction₁ Sg0 (under : V → V) :=
  under_defined.to_definable


-- @@ L534-534 expanded
instance under_definable' (Γ) : BoldfaceFunction₁ Γ (under : V → V) :=
  under_definable.of_zero


-- @@ L536-539 verbatim
lemma eq_zero_of_subset_zero {a : V} : a ⊆ 0 → a = 0 := by
  intro h; by_contra A
  have : log a ∈ (0 : V) := h (log_mem_of_pos (pos_iff_ne_zero.mpr A))
  simp_all


-- @@ L541-544 verbatim
lemma subset_div_two {a b : V} : a ⊆ b → a / 2 ⊆ b / 2 := by
  intro ss i hi
  have : i + 1 ∈ a := succ_mem_iff_mem_div_two.mpr hi
  exact succ_mem_iff_mem_div_two.mp <| ss this


-- @@ L546-546 verbatim
lemma zero_mem_iff {a : V} : 0 ∉ a ↔ 2 ∣ a := by simp [mem_iff_bit, Bit, LenBit]


-- @@ L548-548 verbatim
@[simp] lemma zero_not_mem (a : V) : 0 ∉ 2 * a := by simp [mem_iff_bit, Bit, LenBit]


-- @@ L550-552 verbatim
@[simp] lemma zero_mem_double_add_one (a : V) :
    0 ∈ 2 * a + 1 := by
  simp [mem_iff_bit, Bit, LenBit, ←mod_eq_zero_iff_dvd]


-- @@ L554-555 verbatim
@[simp] lemma succ_mem_two_mul_iff {i a : V} : i + 1 ∈ 2 * a ↔ i ∈ a := by
  simp [mem_iff_bit, Bit, LenBit, exp_succ, div_cancel_left]


-- @@ L557-558 verbatim
@[simp] lemma succ_mem_two_mul_succ_iff {i a : V} : i + 1 ∈ 2 * a + 1 ↔ i ∈ a := by
  simp [mem_iff_bit, Bit, LenBit, exp_succ, div_mul]


-- @@ L560-572 expanded
lemma le_of_subset {a b : V} (h : a ⊆ b) : a ≤ b :=
  by
  induction b using hierarchy_polynomial_induction_oRing_pi₁ generalizing a
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp [eq_zero_of_subset_zero h]
  case even b _ IH =>
    have IH : a / 2 ≤ b := IH (by simpa using subset_div_two h)
    have : 2 * (a / 2) = a :=
      mul_div_self_of_dvd.mpr (zero_mem_iff.mp <| by intro ha; have : 0 ∈ 2 * b := h ha; simp_all)
    simpa [this] using mul_le_mul_left (a := 2) IH
  case odd b
    IH =>
    have IH : a / 2 ≤ b := IH (by simpa [div_mul_add' b 2 one_lt_two] using subset_div_two h)
    exact le_trans (le_two_mul_div_two_add_one a) (by simpa using IH)


-- @@ L574-575 verbatim
lemma mem_ext {a b : V} (h : ∀ i, i ∈ a ↔ i ∈ b) : a = b :=
  le_antisymm (le_of_subset fun i hi ↦ (h i).mp hi) (le_of_subset fun i hi ↦ (h i).mpr hi)


-- @@ L577-577 verbatim
lemma pos_iff_nonempty {s : V} : 0 < s ↔ s ≠ ∅ := pos_iff_ne_zero


-- @@ L579-582 verbatim
lemma nonempty_of_pos {a : V} (h : 0 < a) : ∃ i, i ∈ a := by
  by_contra A
  have : a = 0 := mem_ext (by simpa using A)
  simp [this] at h


-- @@ L584-587 verbatim
lemma eq_empty_or_nonempty (a : V) : a = ∅ ∨ ∃ i, i ∈ a := by
  rcases zero_le a with (rfl | pos)
  · simp [emptyset_def]
  · right; exact nonempty_of_pos pos


-- @@ L589-596 verbatim
lemma nonempty_iff {s : V} : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp_all
  · exact iff_of_true
      (by
        rintro rfl
        simp_all)
      hs


-- @@ L598-599 verbatim
lemma isempty_iff {s : V} : s = ∅ ↔ ∀ x, x ∉ s := by
  simpa using not_iff_not.mpr (nonempty_iff (s := s))


-- @@ L601-601 verbatim
@[simp] lemma empty_subset (s : V) : ∅ ⊆ s := by intro x; simp


-- @@ L603-608 verbatim
lemma lt_of_lt_log {a b : V} (pos : 0 < b) (h : ∀ i ∈ a, i < log b) : a < b := by
  rcases zero_le a with (rfl | apos)
  · exact pos
  by_contra A
  exact (not_lt.mpr (log_monotone <| show b ≤ a by simpa using A))
    (h (log a) (log_mem_of_pos apos))


-- @@ L610-615 verbatim
@[simp] lemma under_inj {i j : V} : under i = under j ↔ i = j := ⟨fun h ↦ by
  by_contra ne
  wlog lt : i < j
  · exact this (Eq.symm h) (Ne.symm ne) (lt_of_le_of_ne (by simpa using lt) (Ne.symm ne))
  have : i ∉ under i := by simp
  simp_all, by rintro rfl; simp⟩


-- @@ L617-617 verbatim
@[simp] lemma under_zero : under (0 : V) = ∅ := mem_ext (by simp [mem_under_iff])


-- @@ L619-620 verbatim
@[simp] lemma under_succ (i : V) : under (i + 1) = insert i (under i) :=
  mem_ext (by simp [mem_under_iff, lt_succ_iff_le, le_iff_eq_or_lt])


-- @@ L622-627 verbatim
lemma insert_remove {i a : V} (h : i ∈ a) : insert i (bitRemove i a) = a := mem_ext <| by
  intro j
  simp only [mem_bitInsert_iff, mem_bitRemove_iff]
  constructor
  · rintro (rfl | ⟨_, hj⟩) <;> assumption
  · intro hj; simp [hj, eq_or_ne j i]


-- @@ L629-629 verbatim
section «lp_section_6»


-- @@ L631-631 expanded
variable {m : ℕ} [Fact (1 ≤ m)] [ModelsTheory V ((indH SigmaSymbol.sigma) m)]


-- @@ L633-633 expanded
omit [ModelsTheory V (iSigma 1)]


-- @@ L635-663 expanded
private lemma finset_comprehension_aux (Γ : Polarity) {P : V → Prop} (hP : BoldfacePred Γ-[m] P)
    (a : V) :
    haveI : ModelsTheory V (iSigma 1) := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i :=
  by
  have : ModelsTheory V (iSigma 1) := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  have : ∃ s < Exp.exp a, ∀ i < a, P i → i ∈ s :=
    ⟨under a, pred_lt_self_of_pos (by simp), fun i hi _ ↦ by simpa [mem_under_iff] using hi⟩
  rcases this with ⟨s, hsn, hs⟩
  have : BoldfacePred Γ.alt-[m] (fun s : V ↦ ∀ i < a, P i → i ∈ s) :=
    by
    apply HierarchySymbol.Boldface.ball_blt
    · simp
    · apply HierarchySymbol.Boldface.imp
      ·
        simpa using
          HierarchySymbol.Boldface.bcomp₁
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
      ·
        simpa using
          HierarchySymbol.Boldface.bcomp₂
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
  have : ∃ t, (∀ i < a, P i → i ∈ t) ∧ ∀ t' < t, ∃ x < a, P x ∧ x ∉ (t' : V) := by
    simpa using least_number_h Γ.alt m this hs
  rcases this with ⟨t, ht, t_minimal⟩
  have t_le_s : t ≤ s :=
    not_lt.mp
      (by
        intro lt
        rcases t_minimal s lt with ⟨i, hin, hi, his⟩
        exact his (hs i hin hi))
  have : ∀ i < a, i ∈ t → P i := by
    intro i _ hit
    by_contra Hi
    have : ∃ j < a, P j ∧ (j ∈ t → j = i) := by
      simpa [not_imp_not] using t_minimal (bitRemove i t) (bitRemove_lt_of_mem hit)
    rcases this with ⟨j, hjn, Hj, hm⟩
    rcases hm (ht j hjn Hj); contradiction
  exact ⟨t, lt_of_le_of_lt t_le_s hsn, fun i hi ↦ ⟨this i hi, ht i hi⟩⟩


-- @@ L665-671 expanded
theorem finset_comprehension {Γ} {P : V → Prop} (hP : BoldfacePred Γ-[m] P) (a : V) :
    haveI : ModelsTheory V (iSigma 1) := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i :=
  match Γ with
  | SigmaSymbol.sigma => finset_comprehension_aux SigmaSymbol.sigma hP a
  | PiSymbol.pi => finset_comprehension_aux PiSymbol.pi hP a
  | DeltaSymbol.delta => finset_comprehension_aux SigmaSymbol.sigma hP.of_delta a


-- @@ L673-688 expanded
theorem finset_comprehension_exists_unique {P : V → Prop} (hP : BoldfacePred Γ-[m] P) (a : V) :
    haveI : ModelsTheory V (iSigma 1) := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
    ∃! s, s < Exp.exp a ∧ ∀ i < a, i ∈ s ↔ P i :=
  by
  have : ModelsTheory V (iSigma 1) := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  rcases finset_comprehension hP a with ⟨s, hs, Hs⟩
  exact
    ExistsUnique.intro s ⟨hs, Hs⟩
      (by
        intro t ⟨ht, Ht⟩
        apply mem_ext
        intro i
        constructor
        · intro hi
          have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) ht)
          exact (Hs i hin).mpr ((Ht i hin).mp hi)
        · intro hi
          have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) hs)
          exact (Ht i hin).mpr ((Hs i hin).mp hi))


-- @@ L690-690 verbatim
end «lp_section_6»


-- @@ L692-692 verbatim
section «lp_section_7»


-- @@ L694-694 verbatim
instance : Fact (1 ≤ 1) := ⟨by rfl⟩


-- @@ L696-698 expanded
theorem finset_comprehension₁ {P : V → Prop} (hP : BoldfacePred Γ-[1] P) (a : V) :
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i :=
  finset_comprehension hP a


-- @@ L700-714 expanded
theorem finset_comprehension₁! {P : V → Prop} (hP : BoldfacePred Γ-[1] P) (a : V) :
    ∃! s, s < Exp.exp a ∧ (∀ i < a, i ∈ s ↔ P i) :=
  by
  rcases finset_comprehension₁ hP a with ⟨s, hs, Ha⟩
  exact
    ExistsUnique.intro s ⟨hs, Ha⟩
      (by
        rintro b ⟨hb, Hb⟩
        apply mem_ext
        intro x
        constructor
        · intro hx
          have : x < a := exp_monotone.mp <| LE.le.trans_lt (exp_le_of_mem hx) hb
          exact (Ha x this).mpr <| (Hb x this).mp hx
        · intro hx
          have : x < a := exp_monotone.mp <| LE.le.trans_lt (exp_le_of_mem hx) hs
          exact (Hb x this).mpr <| (Ha x this).mp hx)


-- @@ L716-725 expanded
theorem finite_comprehension₁! {P : V → Prop} (hP : BoldfacePred Γ-[1] P)
    (fin : ∃ m, ∀ i, P i → i < m) : ∃! s : V, ∀ i, i ∈ s ↔ P i :=
  by
  rcases fin with ⟨m, mh⟩
  rcases finset_comprehension₁ hP m with ⟨s, hs, Hs⟩
  have H : ∀ i, i ∈ s ↔ P i := fun i ↦
    ⟨fun h ↦ (Hs i (exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem h) hs))).mp h, fun h ↦
      (Hs i (mh i h)).mpr h⟩
  exact ExistsUnique.intro s H (fun s' H' ↦ mem_ext <| fun i ↦ by simp [H, H'])


-- @@ L728-728 verbatim
end «lp_section_7»


-- @@ L730-730 verbatim
end Arith

-- @@ L731-731 verbatim
end LO


-- @@ L733-733 verbatim
end «lp_nc_section_2»
