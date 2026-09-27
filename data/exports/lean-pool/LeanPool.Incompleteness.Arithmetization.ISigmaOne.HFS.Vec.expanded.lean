/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaOne.HFS.Fixpoint
import LeanPool.Incompleteness.Arithmetization.Definability.Absoluteness
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Algebra.Order.Sub.Basic


-- @@ L13-17 verbatim
/-!

# Vec

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


-- @@ L30-30 verbatim
section «lp_section_1»


-- @@ L32-32 expanded
instance : Cons V V :=
  ⟨(pair · · + 1)⟩


-- @@ L34-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infixr:67 " ∷ " => cons


-- @@ L37-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "?[" term,* "]" : term


-- @@ L40-43 unexpanded
macro_rules
  | `(?[$term:term, $terms:term,*]) => `(cons $term ?[$terms,*])
  | `(?[$term:term]) => `(cons $term 0)
  | `(?[]) => `(0)


-- @@ L45-50 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Cons.cons]
meta def consUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ?[$terms,*]) => `(?[$term, $terms,*])
  | `($_ $term 0) => `(?[$term])
  | _ => throw ()


-- @@ L52-52 expanded
lemma cons_def (x v : V) : x ∷ v = pair x v + 1 :=
  rfl


-- @@ L54-54 verbatim
@[simp] lemma fstIdx_cons (x v : V) : fstIdx (x ∷ v) = x := by simp [cons_def, fstIdx]


-- @@ L56-56 verbatim
@[simp] lemma sndIdx_cons (x v : V) : sndIdx (x ∷ v) = v := by simp [cons_def, sndIdx]


-- @@ L58-58 expanded
lemma succ_eq_cons (x : V) : x + 1 = pi₁ x ∷ pi₂ x := by simp [cons_def]


-- @@ L60-60 verbatim
@[simp] lemma lt_cons (x v : V) : x < x ∷ v := by simp [cons_def, lt_succ_iff_le]


-- @@ L62-62 verbatim
@[simp] lemma lt_cons' (x v : V) : v < x ∷ v := by simp [cons_def, lt_succ_iff_le]


-- @@ L64-64 verbatim
@[simp] lemma zero_lt_cons (x v : V) : 0 < x ∷ v := by simp [cons_def]


-- @@ L66-66 verbatim
@[simp] lemma cons_ne_zero (x v : V) : x ∷ v ≠ 0 := by simp [cons_def]


-- @@ L68-68 verbatim
@[simp] lemma zero_ne_cons (x v : V) : 0 ≠ x ∷ v := by symm; simp [cons_def]


-- @@ L70-73 expanded
lemma nil_or_cons (z : V) : z = 0 ∨ ∃ x v, z = x ∷ v :=
  by
  rcases zero_or_succ z with (rfl | ⟨z, rfl⟩)
  · left; rfl
  · right; exact ⟨pi₁ z, pi₂ z, by simp [succ_eq_cons]⟩


-- @@ L75-76 verbatim
@[simp] lemma cons_inj (x₁ x₂ v₁ v₂ : V) :
    x₁ ∷ v₁ = x₂ ∷ v₂ ↔ x₁ = x₂ ∧ v₁ = v₂ := by simp [cons_def]


-- @@ L78-79 verbatim
lemma cons_le_cons {x₁ x₂ v₁ v₂ : V} (hx : x₁ ≤ x₂) (hv : v₁ ≤ v₂) :
    x₁ ∷ v₁ ≤ x₂ ∷ v₂ := by simpa [cons_def] using pair_le_pair hx hv


-- @@ L81-81 verbatim
section «lp_section_2»


-- @@ L83-85 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.consDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLT (#0)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#0) (vecCons (#2) (vecCons #3 ![]))))
        (Semiformula.Operator.operator Operator.Eq.eq
          ![#1, Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]])))
    (by simp)


-- @@ L87-97 expanded
lemma cons_defined : DefinedFunction₂ Sg0 (cons : V → V → V) consDef :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.reduceAdd, consDef,
    Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT,
    Semiterm.val_bvar, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.vecCons_zero, Matrix.cons_app_two, Matrix.cons_val_fin_one,
    Matrix.cons_app_three, Matrix.constant_eq_singleton, pair_defined_iff, Matrix.cons_val_one,
    Semiformula.eval_operator₂, Semiterm.val_operator₂, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.one_eq_one, Structure.Add.add, Structure.Eq.eq,
    LogicalConnective.Prop.and_eq, ↓existsAndEq, true_and]
  exact ⟨fun h ↦ ⟨by simp [h, cons_def], h⟩, fun h ↦ h.2⟩


-- @@ L99-100 verbatim
@[simp] lemma eval_cons (v) :
    Semiformula.Evalbm V v consDef.val ↔ v 0 = v 1 ∷ v 2 := cons_defined.df.iff v


-- @@ L102-102 expanded
instance cons_definable : BoldfaceFunction₂ Sg0 (cons : V → V → V) :=
  cons_defined.to_definable


-- @@ L104-104 expanded
instance cons_definable' (ℌ) : BoldfaceFunction₂ ℌ (cons : V → V → V) :=
  cons_definable.of_zero


-- @@ L106-108 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.mkVec₁Def : Sg0.Semisentence 2 :=
  .mkSigma
    (LO.FirstOrder.Rewriting.substitute consDef
      (vecCons (#0) (vecCons (#1) (vecCons (Semiterm.numeral 0) ![]))))
    (by simp)


-- @@ L110-111 expanded
lemma mkVec₁_defined : DefinedFunction₁ Sg0 (fun x : V ↦ cons x 0) mkVec₁Def := by intro v;
  simp [mkVec₁Def]


-- @@ L113-114 expanded
@[simp]
lemma eval_mkVec₁Def (v) : Semiformula.Evalbm V v mkVec₁Def.val ↔ v 0 = cons (v 1) 0 :=
  mkVec₁_defined.df.iff v


-- @@ L116-116 expanded
instance mkVec₁_definable : BoldfaceFunction₁ Sg0 (fun x : V ↦ cons x 0) :=
  mkVec₁_defined.to_definable


-- @@ L118-118 expanded
instance mkVec₁_definable' (ℌ) : BoldfaceFunction₁ ℌ (fun x : V ↦ cons x 0) :=
  mkVec₁_definable.of_zero


-- @@ L120-122 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.mkVec₂Def : Sg1.Semisentence 3 :=
  .mkSigma
    (ExQuantifier.ex
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute mkVec₁Def (vecCons (#0) (vecCons #3 ![])))
        (LO.FirstOrder.Rewriting.substitute consDef
          (vecCons (#1) (vecCons (#2) (vecCons #0 ![]))))))
    (by simp)


-- @@ L124-125 expanded
lemma mkVec₂_defined : DefinedFunction₂ Sg1 (fun x y : V ↦ cons x (cons y 0)) mkVec₂Def := by
  intro v; simp [mkVec₂Def]


-- @@ L127-128 expanded
@[simp]
lemma eval_mkVec₂Def (v) : Semiformula.Evalbm V v mkVec₂Def.val ↔ v 0 = cons (v 1) (cons (v 2) 0) :=
  mkVec₂_defined.df.iff v


-- @@ L130-130 expanded
instance mkVec₂_definable : BoldfaceFunction₂ Sg1 (fun x y : V ↦ cons x (cons y 0)) :=
  mkVec₂_defined.to_definable


-- @@ L132-133 expanded
instance mkVec₂_definable' (Γ m) : BoldfaceFunction₂ Γ-[m + 1] (fun x y : V ↦ cons x (cons y 0)) :=
  mkVec₂_definable.of_sigmaOne


-- @@ L135-135 verbatim
end «lp_section_2»


-- @@ L137-137 verbatim
end «lp_section_1»


-- @@ L139-143 verbatim
/-!

### N-th element of List

-/


-- @@ L145-145 verbatim
namespace Nth


-- @@ L147-149 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ v, pr = pair v (pair 0 (fstIdx v))) ∨
    (∃ v i x, pr = pair v (pair (i + 1) x) ∧ pair (sndIdx v) (pair i x) ∈ C)


-- @@ L151-163 expanded
private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
      (∃ v ≤ pr, ∃ fst ≤ v, fst = fstIdx v ∧ pr = pair v (pair 0 fst)) ∨
        (∃ v ≤ pr,
          ∃ i ≤ pr,
            ∃ x ≤ pr,
              pr = pair v (pair (i + 1) x) ∧
                ∃ snd ≤ v, snd = sndIdx v ∧ ∃ six < C, six = pair snd (pair i x) ∧ six ∈ C) :=
  by
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, i, x, rfl, hC⟩)
    · left; exact ⟨v, by simp, _, by simp, rfl, rfl⟩
    · right;
      exact
        ⟨v, by simp, i, le_trans (le_trans (by simp) (le_pair_left _ _)) (le_pair_right _ _), x,
          le_trans (by simp) (le_pair_right _ _), rfl, _, by simp, rfl, _, lt_of_mem hC, rfl, hC⟩
  · rintro (⟨v, _, _, _, rfl, rfl⟩ | ⟨v, _, i, _, x, _, rfl, _, _, rfl, _, _, rfl, hC⟩)
    · left; exact ⟨v, rfl⟩
    · right; exact ⟨v, i, x, rfl, hC⟩


-- @@ L165-173 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : Fixpoint.Blueprint 0 where
  core :=
    .ofZero
      (.mkSigma
        (Vee.vee
          (Semiformula.bexLTSucc (#0)
            (Semiformula.bexLTSucc (#0)
              (Wedge.wedge
                (LO.FirstOrder.Rewriting.substitute fstIdxDef (vecCons (#0) (vecCons #1 ![])))
                (LO.FirstOrder.Rewriting.substitute pair₃Def
                  (vecCons (#2) (vecCons (#1) (vecCons (Semiterm.numeral 0) (vecCons #0 ![]))))))))
          (Semiformula.bexLTSucc (#0)
            (Semiformula.bexLTSucc (#1)
              (Semiformula.bexLTSucc (#2)
                (Wedge.wedge
                  (LO.FirstOrder.Rewriting.substitute pair₃Def
                    (vecCons (#3)
                      (vecCons (#2)
                        (vecCons (Semiterm.Operator.Add.add.operator ![#1, Semiterm.numeral 1])
                          (vecCons #0 ![])))))
                  (Semiformula.bexLTSucc (#2)
                    (Wedge.wedge
                      (LO.FirstOrder.Rewriting.substitute sndIdxDef (vecCons (#0) (vecCons #3 ![])))
                      (Semiformula.bexLT (#5)
                        (Wedge.wedge
                          (LO.FirstOrder.Rewriting.substitute pair₃Def
                            (vecCons (#0) (vecCons (#1) (vecCons (#3) (vecCons #2 ![])))))
                          (Semiformula.Operator.operator Operator.Mem.mem ![#0, #6]))))))))))
        (by simp))
      _


-- @@ L175-182 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .of_zero <| by intro v; simp [phi_iff]
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, x, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, x, rfl, hC h⟩


-- @@ L184-188 expanded
instance : construction.Finite V where
  finite := by
    rintro C v x (h | ⟨v, i, x, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨pair (sndIdx v) (pair i x) + 1, Or.inr ⟨v, i, x, rfl, h, by simp⟩⟩


-- @@ L190-191 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph : V → Prop := construction.fixedPoint ![]


-- @@ L193-193 verbatim
section «lp_section_3»


-- @@ L195-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def graphDef : Sg1.Semisentence 1 := blueprint.fixpointDef


-- @@ L198-198 expanded
lemma graph_defined : DefinedPred Sg1 (Graph : V → Prop) graphDef :=
  construction.fixpoint_defined


-- @@ L200-200 expanded
instance graph_definable : BoldfacePred Sg1 (Graph : V → Prop) :=
  graph_defined.to_definable


-- @@ L202-202 expanded
instance graph_definable' : BoldfacePred SigmaSymbol.sigma-[0 + 1] (Graph : V → Prop) :=
  graph_definable


-- @@ L204-204 verbatim
end «lp_section_3»


-- @@ L206-207 verbatim
/-- TODO: move -/
@[simp 1100] lemma zero_ne_add_one (x : V) : 0 ≠ x + 1 := ne_of_lt (by simp)


-- @@ L209-211 expanded
lemma graph_case {pr : V} :
    Graph pr ↔
      (∃ v, pr = pair v (pair 0 (fstIdx v))) ∨
        (∃ v i x, pr = pair v (pair (i + 1) x) ∧ Graph (pair (sndIdx v) (pair i x))) :=
  construction.case


-- @@ L213-215 expanded
lemma graph_zero {v x : V} : Graph (pair v (pair 0 x)) ↔ x = fstIdx v :=
  by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ graph_case.mpr (Or.inl ⟨v, rfl⟩)⟩
  rcases graph_case.mp h with (⟨v, h⟩ | ⟨v, i, x, h, _⟩) <;> simp_all [pair_ext_iff]


-- @@ L217-220 expanded
lemma graph_succ {v i x : V} :
    Graph (pair v (pair (i + 1) x)) ↔ Graph (pair (sndIdx v) (pair i x)) :=
  by
  refine ⟨fun h ↦ ?_, fun h ↦ graph_case.mpr (Or.inr ⟨v, i, x, rfl, h⟩)⟩
  rcases graph_case.mp h with (⟨v, h⟩ | ⟨v, i, x, h, hv⟩) <;> simp_all [pair_ext_iff, add_left_inj]


-- @@ L222-233 expanded
lemma graph_exists (v i : V) : ∃ x, Graph (pair v (pair i x)) :=
  by
  suffices ∀ i' ≤ i, ∀ v' ≤ v, ∃ x, Graph (pair v' (pair i' x)) from this i (by simp) v (by simp)
  intro i' hi'
  induction i' using induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero =>
    intro v' _
    exact ⟨fstIdx v', graph_case.mpr <| Or.inl ⟨v', rfl⟩⟩
  case succ i' ih =>
    intro v' hv'
    rcases ih (le_trans le_self_add hi') (sndIdx v') (le_trans (by simp) hv') with ⟨x, hx⟩
    exact ⟨x, graph_case.mpr <| Or.inr ⟨v', i', x, rfl, hx⟩⟩


-- @@ L235-243 expanded
lemma graph_unique {v i x₁ x₂ : V} :
    Graph (pair v (pair i x₁)) → Graph (pair v (pair i x₂)) → x₁ = x₂ :=
  by
  induction i using induction_pi1 generalizing v x₁ x₂
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero =>
    rw [graph_zero, graph_zero]
    rintro rfl rfl; rfl
  case succ i ih =>
    rw [graph_succ, graph_succ]
    exact ih


-- @@ L245-247 expanded
lemma graph_existsUnique (v i : V) : ∃! x, Graph (pair v (pair i x)) :=
  by
  rcases graph_exists v i with ⟨x, hx⟩
  exact ExistsUnique.intro x hx (fun y hy ↦ graph_unique hy hx)


-- @@ L249-249 verbatim
end Nth


-- @@ L251-251 verbatim
section «lp_section_4»


-- @@ L253-253 verbatim
open Nth


-- @@ L255-256 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def nth (v i : V) : V := Classical.choose! (graph_existsUnique v i)


-- @@ L258-259 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped notation:max v:max ".[" i "]" => nth v i


-- @@ L261-261 expanded
lemma nth_graph (v i : V) : Graph (pair v (pair i v.[i])) :=
  Classical.choose!_spec (graph_existsUnique v i)


-- @@ L263-264 expanded
lemma nth_eq_of_graph {v i x : V} (h : Graph (pair v (pair i x))) : nth v i = x :=
  graph_unique (nth_graph v i) h


-- @@ L266-266 verbatim
lemma nth_zero (v : V) : v.[0] = fstIdx v := nth_eq_of_graph (graph_zero.mpr rfl)


-- @@ L268-269 verbatim
lemma nth_succ (v i : V) : v.[i + 1] = (sndIdx v).[i] :=
  nth_eq_of_graph (graph_succ.mpr <| nth_graph _ _)


-- @@ L271-271 verbatim
@[simp] lemma nth_cons_zero (x v : V) : (x ∷ v).[0] = x := by simp [nth_zero]


-- @@ L273-273 verbatim
@[simp] lemma nth_cons_succ (x v i : V) : (x ∷ v).[i + 1] = v.[i] := by simp [nth_succ]


-- @@ L275-275 verbatim
@[simp] lemma nth_cons_one (x v : V) : (x ∷ v).[1] = v.[0] := by simpa using nth_cons_succ x v 0


-- @@ L277-278 verbatim
@[simp] lemma nth_cons_two (x v : V) : (x ∷ v).[2] = v.[1] := by
  simpa [-nth_cons_succ, one_add_one_eq_two] using nth_cons_succ x v 1


-- @@ L280-283 expanded
lemma cons_cases (x : V) : x = 0 ∨ ∃ y v, x = y ∷ v :=
  by
  rcases zero_or_succ x with (rfl | ⟨z, rfl⟩)
  · simp
  · right; exact ⟨pi₁ z, pi₂ z, by simp [cons]⟩


-- @@ L285-291 expanded
lemma cons_induction (Γ) {P : V → Prop} (hP : BoldfacePred Γ-[1] P) (nil : P 0)
    (cons : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  order_induction_hh Γ 1 hP
    (by
      intro v ih
      rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩)
      · exact nil
      · exact cons _ _ (ih v (by simp)))


-- @@ L293-296 expanded
@[elab_as_elim]
lemma cons_induction_sigma1 {P : V → Prop} (hP : BoldfacePred Sg1 P) (nil : P 0)
    (cons : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  cons_induction SigmaSymbol.sigma hP nil cons


-- @@ L298-301 expanded
@[elab_as_elim]
lemma cons_induction_pi1 {P : V → Prop} (hP : BoldfacePred Pg1 P) (nil : P 0)
    (cons : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  cons_induction PiSymbol.pi hP nil cons


-- @@ L303-303 verbatim
section «lp_section_5»


-- @@ L305-307 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.nthDef : Sg1.Semisentence 3 :=
  .mkSigma
    (ExQuantifier.ex
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pair₃Def
          (vecCons (#0) (vecCons (#2) (vecCons (#3) (vecCons #1 ![])))))
        (LO.FirstOrder.Rewriting.substitute graphDef (vecCons #0 ![]))))
    (by simp)


-- @@ L309-319 expanded
lemma nth_defined : DefinedFunction₂ Sg1 (nth : V → V → V) nthDef :=
  by
  intro v
  simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.reduceAdd, nthDef,
    Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Semiterm.val_bvar, Matrix.vecCons_zero, Matrix.cons_app_two, Matrix.cons_app_three,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.constant_eq_singleton, eval_pair₃Def,
    graph_defined.df.iff, LogicalConnective.Prop.and_eq, exists_eq_left]
  constructor
  · intro h; rw [h]; exact nth_graph _ _
  · intro h; simp [nth_eq_of_graph h]


-- @@ L321-322 verbatim
@[simp] lemma eval_nthDef (v) :
    Semiformula.Evalbm V v nthDef.val ↔ v 0 = nth (v 1) (v 2) := nth_defined.df.iff v


-- @@ L324-324 expanded
instance nth_definable : BoldfaceFunction₂ Sg1 (nth : V → V → V) :=
  nth_defined.to_definable


-- @@ L326-326 expanded
instance nth_definable' (Γ m) : BoldfaceFunction₂ Γ-[m + 1] (nth : V → V → V) :=
  nth_definable.of_sigmaOne


-- @@ L328-328 verbatim
end «lp_section_5»


-- @@ L330-331 verbatim
lemma cons_absolute (a v : ℕ) : ((a ∷ v : ℕ) : V) = (a : V) ∷ (v : V) := by
  simpa using DefinedFunction.shigmaZero_absolute_func V cons_defined cons_defined ![a, v]


-- @@ L333-334 expanded
/-- TODO: move -/
lemma pi₁_zero : pi₁ (0 : V) = 0 :=
  nonpos_iff_eq_zero.mp (pi₁_le_self 0)


-- @@ L336-336 expanded
lemma pi₂_zero : pi₂ (0 : V) = 0 :=
  nonpos_iff_eq_zero.mp (pi₂_le_self 0)


-- @@ L338-342 expanded
@[simp]
lemma nth_zero_idx (i : V) : (0).[i] = 0 :=
  by
  induction i using induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp [nth_zero, fstIdx, pi₁_zero]
  case succ i ih => simp [nth_succ, sndIdx, pi₂_zero, ih]


-- @@ L344-358 expanded
lemma nth_lt_of_pos {v} (hv : 0 < v) (i : V) : v.[i] < v :=
  by
  induction i using induction_pi1 generalizing v
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero =>
    rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
    · simp at hv
    · simp [succ_eq_cons]
  case succ i ih =>
    rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
    · simp at hv
    · rw [succ_eq_cons v, nth_succ]
      simp only [sndIdx_cons]
      rcases eq_zero_or_pos (pi₂ v) with (h | h)
      · simp [h]
      · exact lt_trans (ih h) (by simp)


-- @@ L360-363 verbatim
@[simp] lemma nth_le (v i : V) : v.[i] ≤ v := by
  rcases eq_zero_or_pos v with (h | h)
  · simp [h]
  · exact le_of_lt <| nth_lt_of_pos h i


-- @@ L365-365 verbatim
end «lp_section_4»



-- @@ L368-372 verbatim
/-!

### Inductivly Construction of Function on List

-/


-- @@ L374-374 verbatim
namespace VecRec


-- @@ L376-381 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Blueprint (arity : ℕ) where
  /-- Imported declaration from the Incompleteness formalization. -/
  nil : Sg1.Semisentence (arity + 1)
  /-- Imported declaration from the Incompleteness formalization. -/
  cons : Sg1.Semisentence (arity + 4)


-- @@ L383-383 verbatim
namespace Blueprint


-- @@ L385-385 verbatim
variable {arity : ℕ} (β : Blueprint arity)


-- @@ L387-403 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : Fixpoint.Blueprint arity where
  core :=
    .mkDelta
      (.mkSigma
        (Vee.vee
          (ExQuantifier.ex
            (Wedge.wedge
              (LO.FirstOrder.Rewriting.substitute β.nil (vecCons #0 fun x ↦ #(finSuccItr x 3)))
              (LO.FirstOrder.Rewriting.substitute pairDef
                (vecCons (#1) (vecCons (Semiterm.numeral 0) (vecCons #0 ![]))))))
          (Semiformula.bexLT (#0)
            (Semiformula.bexLT (#1)
              (Semiformula.bexLT (#3)
                (ExQuantifier.ex
                  (Wedge.wedge
                    (LO.FirstOrder.Rewriting.substitute consDef
                      (vecCons (#0) (vecCons (#3) (vecCons #2 ![]))))
                    (ExQuantifier.ex
                      (Wedge.wedge
                        (LO.FirstOrder.Rewriting.substitute β.cons
                          (vecCons (#0)
                            (vecCons (#4) (vecCons (#3) (vecCons #2 fun x ↦ #(finSuccItr x 7))))))
                        (Wedge.wedge
                          (LO.FirstOrder.Rewriting.substitute pairDef
                            (vecCons (#5) (vecCons (#1) (vecCons #0 ![]))))
                          (memRelOpr.operator ![#6, #3, #2]))))))))))
        (by simp))
      (.mkPi
        (Vee.vee
          (UnivQuantifier.univ
            (Arrow.arrow
              (LO.FirstOrder.Rewriting.substitute β.nil (vecCons #0 fun x ↦ #(finSuccItr x 3)))
              (LO.FirstOrder.Rewriting.substitute pairDef
                (vecCons (#1) (vecCons (Semiterm.numeral 0) (vecCons #0 ![]))))))
          (Semiformula.bexLT (#0)
            (Semiformula.bexLT (#1)
              (Semiformula.bexLT (#3)
                (UnivQuantifier.univ
                  (Arrow.arrow
                    (LO.FirstOrder.Rewriting.substitute consDef
                      (vecCons (#0) (vecCons (#3) (vecCons #2 ![]))))
                    (UnivQuantifier.univ
                      (Arrow.arrow
                        (LO.FirstOrder.Rewriting.substitute β.cons
                          (vecCons (#0)
                            (vecCons (#4) (vecCons (#3) (vecCons #2 fun x ↦ #(finSuccItr x 7))))))
                        (Wedge.wedge
                          (LO.FirstOrder.Rewriting.substitute pairDef
                            (vecCons (#5) (vecCons (#1) (vecCons #0 ![]))))
                          (memRelOpr.operator ![#6, #3, #2]))))))))))
        (by simp))


-- @@ L405-406 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def graphDef : Sg1.Semisentence (arity + 1) := β.blueprint.fixpointDef


-- @@ L408-410 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def resultDef : Sg1.Semisentence (arity + 2) :=
  .mkSigma
    (ExQuantifier.ex
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute pairDef (vecCons (#0) (vecCons (#2) (vecCons #1 ![]))))
        (LO.FirstOrder.Rewriting.substitute β.graphDef (vecCons #0 fun x ↦ #(finSuccItr x 3)))))
    (by simp)


-- @@ L412-412 verbatim
end Blueprint


-- @@ L414-414 verbatim
variable (V)


-- @@ L416-423 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Construction {arity : ℕ} (β : Blueprint arity) where
  /-- Imported declaration from the Incompleteness formalization. -/
  nil (param : Fin arity → V) : V
  /-- Imported declaration from the Incompleteness formalization. -/
  cons (param : Fin arity → V) (x xs ih) : V
  nil_defined : Sg1.DefinedFunction nil β.nil
  cons_defined : Sg1.DefinedFunction (fun v ↦ cons (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) β.cons


-- @@ L425-425 verbatim
variable {V}


-- @@ L427-427 verbatim
namespace Construction


-- @@ L429-429 verbatim
variable {arity : ℕ} {β : Blueprint arity} (c : Construction V β)


-- @@ L431-433 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  pr = pair 0 (c.nil param) ∨
    (∃ x xs ih, pr = pair (x ∷ xs) (c.cons param x xs ih) ∧ pair xs ih ∈ C)


-- @@ L435-446 expanded
private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi param {x | x ∈ C} pr ↔
      pr = pair 0 (c.nil param) ∨
        (∃ x < pr,
          ∃ xs < pr, ∃ ih < C, pr = pair (x ∷ xs) (c.cons param x xs ih) ∧ pair xs ih ∈ C) :=
  by
  constructor
  · rintro (h | ⟨x, xs, ih, rfl, hC⟩)
    · left; exact h
    · right
      exact
        ⟨x, lt_of_lt_of_le (by simp) (le_pair_left _ _), xs,
          lt_of_lt_of_le (by simp) (le_pair_left _ _), ih, lt_of_mem_rng hC, rfl, hC⟩
  · rintro (h | ⟨x, _, xs, _, ih, _, rfl, hC⟩)
    · left; exact h
    · right; exact ⟨x, xs, ih, rfl, hC⟩


-- @@ L448-458 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def construction : Fixpoint.Construction V β.blueprint where
  Φ := c.Phi
  defined := ⟨by
    intro v; simp [Blueprint.blueprint, c.nil_defined.df.iff, c.cons_defined.df.iff], by
    intro v; simpa [Blueprint.blueprint, c.nil_defined.df.iff,
      c.cons_defined.df.iff] using c.phi_iff _ _ _⟩
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, hv, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, hv, rfl, hC h⟩


-- @@ L460-464 expanded
instance : c.construction.Finite V where
  finite := by
    rintro C v x (h | ⟨x, xs, ih, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨pair xs ih + 1, Or.inr ⟨x, xs, ih, rfl, h, by simp⟩⟩


-- @@ L466-466 verbatim
variable (param : Fin arity → V)


-- @@ L468-469 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph : V → Prop := c.construction.fixedPoint param


-- @@ L471-471 verbatim
section «lp_section_6»


-- @@ L473-474 verbatim
lemma graph_defined : Sg1.Defined (fun v ↦ c.Graph (v ·.succ) (v 0)) β.graphDef :=
  c.construction.fixpoint_defined


-- @@ L476-477 verbatim
instance graph_definable : Sg1.Boldface (fun v ↦ c.Graph (v ·.succ) (v 0)) :=
  c.graph_defined.to_definable


-- @@ L479-481 expanded
instance graph_definable' (param) : BoldfacePred Sg1 (c.Graph param) := by
  simpa using
    HierarchySymbol.Boldface.retractiont (n := 1) c.graph_definable (vecCons #0 fun i ↦ &(param i))


-- @@ L483-484 expanded
instance graph_definable'' (param) : BoldfacePred SigmaSymbol.sigma-[0 + 1] (c.Graph param) :=
  c.graph_definable' param


-- @@ L486-486 verbatim
end «lp_section_6»


-- @@ L488-488 verbatim
variable {param}


-- @@ L490-492 expanded
lemma graph_case {pr : V} :
    c.Graph param pr ↔
      pr = pair 0 (c.nil param) ∨
        (∃ x xs ih, pr = pair (x ∷ xs) (c.cons param x xs ih) ∧ c.Graph param (pair xs ih)) :=
  c.construction.case


-- @@ L494-496 expanded
lemma graph_nil {l : V} : c.Graph param (pair 0 l) ↔ l = c.nil param :=
  by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ c.graph_case.mpr (Or.inl rfl)⟩
  rcases c.graph_case.mp h with (h | ⟨x, xs, ih, h, _⟩) <;> simp_all [pair_ext_iff]


-- @@ L498-505 expanded
lemma graph_cons {x xs y : V} :
    c.Graph param (pair (x ∷ xs) y) ↔ ∃ y', y = c.cons param x xs y' ∧ c.Graph param (pair xs y') :=
  by
  refine ⟨fun h ↦ ?_, fun ⟨y, hy, hg⟩ ↦ hy ▸ c.graph_case.mpr (Or.inr ⟨x, xs, y, rfl, hg⟩)⟩
  rcases c.graph_case.mp h with (h | ⟨x, xs, y, h, hg⟩)
  · simp at h
  · simp only [pair_ext_iff, cons_inj] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨y, rfl, hg⟩


-- @@ L507-507 verbatim
variable (param)


-- @@ L509-516 expanded
lemma graph_exists (xs : V) : ∃ y, c.Graph param (pair xs y) :=
  by
  induction xs using cons_induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => exact ⟨c.nil param, c.graph_nil.mpr rfl⟩
  case cons x xs ih =>
    · rcases ih with ⟨y, hy⟩
      exact ⟨c.cons param x xs y, c.graph_cons.mpr ⟨y, rfl, hy⟩⟩


-- @@ L518-518 verbatim
variable {param}


-- @@ L520-528 expanded
lemma graph_unique {xs y₁ y₂ : V} :
    c.Graph param (pair xs y₁) → c.Graph param (pair xs y₂) → y₁ = y₂ :=
  by
  induction xs using cons_induction_pi1 generalizing y₁ y₂
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => rw [graph_nil, graph_nil]; rintro rfl rfl; rfl
  case cons x v ih =>
    rw [graph_cons, graph_cons]
    rintro ⟨l₁, rfl, h₁⟩ ⟨l₂, rfl, h₂⟩
    rcases ih h₁ h₂; rfl


-- @@ L530-530 verbatim
variable (param)


-- @@ L532-534 expanded
lemma graph_existsUnique (xs : V) : ∃! y, c.Graph param (pair xs y) :=
  by
  rcases c.graph_exists param xs with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' hy' ↦ c.graph_unique hy' hy)


-- @@ L536-537 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def result (xs : V) : V := Classical.choose! (c.graph_existsUnique param xs)


-- @@ L539-540 expanded
lemma result_graph (xs : V) : c.Graph param (pair xs (c.result param xs)) :=
  Classical.choose!_spec (c.graph_existsUnique param xs)


-- @@ L542-543 expanded
lemma result_eq_of_graph {xs y : V} (h : c.Graph param (pair xs y)) : c.result param xs = y :=
  c.graph_unique (c.result_graph param xs) h


-- @@ L545-546 verbatim
@[simp] lemma result_nil : c.result param (0 : V) = c.nil param :=
  c.result_eq_of_graph param (c.graph_nil.mpr rfl)


-- @@ L548-550 verbatim
@[simp] lemma result_cons (x xs : V) :
    c.result param (x ∷ xs) = c.cons param x xs (c.result param xs) :=
  c.result_eq_of_graph param (c.graph_cons.mpr ⟨_, rfl, c.result_graph param xs⟩)


-- @@ L552-552 verbatim
section «lp_section_7»


-- @@ L554-564 verbatim
lemma result_defined : Sg1.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) β.resultDef := by
  intro v
  simp only [Fin.succ_zero_eq_one, Blueprint.resultDef, Nat.succ_eq_add_one, Nat.reduceAdd,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Semiterm.val_bvar, Matrix.vecCons_zero, Matrix.cons_app_two, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.constant_eq_singleton, pair_defined_iff, Fin.isValue,
    Matrix.vecCons_succ, c.graph_defined.df.iff, LogicalConnective.Prop.and_eq, exists_eq_left]
  constructor
  · intro h; rw [h]; exact c.result_graph _ _
  · intro h; symm; simpa using c.result_eq_of_graph _ h


-- @@ L566-568 verbatim
lemma eval_resultDef (v) :
    Semiformula.Evalbm V v β.resultDef.val ↔ v 0 = c.result (v ·.succ.succ) (v 1) :=
      c.result_defined.df.iff v


-- @@ L570-571 verbatim
instance result_definable : Sg1.BoldfaceFunction (fun v ↦ c.result (v ·.succ) (v 0)) :=
  c.result_defined.to_definable


-- @@ L573-574 verbatim
instance result_definable' (Γ m) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ c.result (v ·.succ) (v 0)) := c.result_definable.of_sigmaOne


-- @@ L576-576 verbatim
end «lp_section_7»


-- @@ L578-578 verbatim
end Construction


-- @@ L580-580 verbatim
end VecRec


-- @@ L582-586 verbatim
/-!

### Length of List

-/


-- @@ L588-588 verbatim
namespace Len


-- @@ L590-593 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : VecRec.Blueprint 0
    where
  nil := .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]) (by simp)
  cons :=
    .mkSigma
      (Semiformula.Operator.operator Operator.Eq.eq
        ![#0, Semiterm.Operator.Add.add.operator ![#3, Semiterm.numeral 1]])
      (by simp)


-- @@ L595-600 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def construction : VecRec.Construction V blueprint where
  nil _ := 0
  cons _ _ _ ih := ih + 1
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]


-- @@ L602-602 verbatim
end Len


-- @@ L604-604 verbatim
section «lp_section_8»


-- @@ L606-606 verbatim
open Len


-- @@ L608-609 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def len (v : V) : V := construction.result ![] v


-- @@ L611-611 verbatim
@[simp] lemma len_nil : len (0 : V) = 0 := by simp [len, construction]


-- @@ L613-613 verbatim
@[simp] lemma len_cons (x v : V) : len (x ∷ v) = len v + 1 := by simp [len, construction]


-- @@ L615-615 verbatim
section «lp_section_9»


-- @@ L617-618 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.lenDef : Sg1.Semisentence 2 := blueprint.resultDef


-- @@ L620-620 expanded
lemma len_defined : DefinedFunction₁ Sg1 (len : V → V) lenDef :=
  construction.result_defined


-- @@ L622-623 verbatim
@[simp] lemma eval_lenDef (v) :
    Semiformula.Evalbm V v lenDef.val ↔ v 0 = len (v 1) := len_defined.df.iff v


-- @@ L625-625 expanded
instance len_definable : BoldfaceFunction₁ Sg1 (len : V → V) :=
  len_defined.to_definable


-- @@ L627-627 expanded
instance len_definable' (Γ m) : BoldfaceFunction₁ Γ-[m + 1] (len : V → V) :=
  len_definable.of_sigmaOne


-- @@ L629-629 verbatim
end «lp_section_9»


-- @@ L631-632 verbatim
@[simp] lemma len_zero_iff_eq_nil {v : V} : len v = 0 ↔ v = 0 := by
  rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩) <;> simp


-- @@ L634-641 expanded
lemma nth_lt_len {v i : V} (hl : len v ≤ i) : v.[i] = 0 :=
  by
  induction v using cons_induction_pi1 generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp at hl
    simpa using ih (by simpa using hl)


-- @@ L643-649 expanded
@[simp]
lemma len_le (v : V) : len v ≤ v :=
  by
  induction v using cons_induction_pi1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih =>
    simp only [len_cons]
    simpa only [cons, add_le_add_iff_right] using le_trans ih (le_pair_right x v)


-- @@ L651-651 verbatim
end «lp_section_8»


-- @@ L653-664 expanded
lemma nth_ext {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] = v₂.[i]) : v₁ = v₂ :=
  by
  induction v₁ using cons_induction_pi1 generalizing v₂
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => exact Eq.symm <| len_zero_iff_eq_nil.mp (by simp [← hl])
  case cons x₁ v₁ ih =>
    rcases nil_or_cons v₂ with (rfl | ⟨x₂, v₂, rfl⟩)
    · simp at hl
    have hx : x₁ = x₂ := by simpa using H 0 (by simp)
    have hv : v₁ = v₂ :=
      ih (by simpa using hl) (by intro i hi; simpa using H (i + 1) (by simpa using hi))
    simp [hx, hv]


-- @@ L666-668 verbatim
lemma nth_ext' (l : V) {v₁ v₂ : V} (hl₁ : len v₁ = l) (hl₂ : len v₂ = l) (H :
    ∀ i < l, v₁.[i] = v₂.[i]) : v₁ = v₂ := by
  rcases hl₂; exact nth_ext hl₁ (by simpa [hl₁] using H)


-- @@ L670-681 expanded
lemma le_of_nth_le_nth {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] ≤ v₂.[i]) :
    v₁ ≤ v₂ := by
  induction v₁ using cons_induction_pi1 generalizing v₂
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x₁ v₁ ih =>
    rcases nil_or_cons v₂ with (rfl | ⟨x₂, v₂, rfl⟩)
    · simp at hl
    have hx : x₁ ≤ x₂ := by simpa using H 0 (by simp)
    have hv : v₁ ≤ v₂ :=
      ih (by simpa using hl) (by intro i hi; simpa using H (i + 1) (by simpa using hi))
    exact cons_le_cons hx hv


-- @@ L683-690 expanded
lemma nth_lt_self {v i : V} (hi : i < len v) : v.[i] < v :=
  by
  induction v using cons_induction_pi1 generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp at hi
  case cons x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simpa using lt_trans (ih (by simpa using hi)) (by simp)


-- @@ L692-707 expanded
theorem sigmaOne_skolem_vec {R : V → V → Prop} (hP : BoldfaceRel Sg1 R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ v, len v = l ∧ ∀ i < l, R i v.[i] :=
  by
  have : ∀ k ≤ l, ∃ v, len v = k ∧ ∀ i < k, R (l - k + i) v.[i] :=
    by
    intro k hk
    induction k using induction_sigma1
    · aesop  (config := { terminal := true })  (rule_sets := [Definability])
    case zero => exact ⟨0, by simp⟩
    case succ k ih =>
      rcases ih (le_trans (by simp) hk) with ⟨v, hvk, hv⟩
      have : ∃ y, R (l - (k + 1)) y := H (l - (k + 1)) (by simp [tsub_lt_iff_left hk])
      rcases this with ⟨y, hy⟩
      exact
        ⟨y ∷ v, by simp [hvk], fun i hi ↦
          by
          rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
          · simpa using hy
          · simpa [sub_succ_add_succ (succ_le_iff_lt.mp hk) i] using hv i (by simpa using hi)⟩
  simpa using this l (by rfl)


-- @@ L709-712 expanded
lemma eq_singleton_iff_len_eq_one {v : V} : len v = 1 ↔ ∃ x, v = cons x 0 :=
  by
  constructor
  · intro h; exact ⟨v.[0], nth_ext (by simp [h]) (by simp [h])⟩
  · rintro ⟨x, rfl⟩; simp


-- @@ L714-719 expanded
lemma eq_doubleton_of_len_eq_two {v : V} : len v = 2 ↔ ∃ x y, v = cons x (cons y 0) :=
  by
  constructor
  · intro h;
    exact
      ⟨v.[0], v.[1],
        nth_ext (by simp [h, one_add_one_eq_two])
          (by simp [lt_two_iff_le_one, le_one_iff_eq_zero_or_one, h])⟩
  · rintro ⟨x, y, rfl⟩; simp [one_add_one_eq_two]


-- @@ L722-726 verbatim
/-!

### Maximum of List

-/


-- @@ L728-728 verbatim
namespace ListMax


-- @@ L730-733 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : VecRec.Blueprint 0
    where
  nil := .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]) (by simp)
  cons :=
    .mkSigma
      (LO.FirstOrder.Rewriting.substitute FirstOrder.Arith.max
        (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))
      (by simp)


-- @@ L735-740 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def construction : VecRec.Construction V blueprint where
  nil _ := 0
  cons _ x _ ih := max x ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]


-- @@ L742-742 verbatim
end ListMax


-- @@ L744-744 verbatim
section «lp_section_10»


-- @@ L746-746 verbatim
open ListMax


-- @@ L748-749 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def listMax (v : V) : V := construction.result ![] v


-- @@ L751-751 verbatim
@[simp] lemma listMax_nil : listMax (0 : V) = 0 := by simp [listMax, construction]


-- @@ L753-754 verbatim
@[simp] lemma listMax_cons (x v : V) : listMax (x ∷ v) = max x (listMax v) := by
  simp [listMax, construction]


-- @@ L756-756 verbatim
section «lp_section_11»


-- @@ L758-759 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.listMaxDef : Sg1.Semisentence 2 := blueprint.resultDef


-- @@ L761-762 expanded
lemma listMax_defined : DefinedFunction₁ Sg1 (listMax : V → V) listMaxDef :=
  construction.result_defined


-- @@ L764-765 verbatim
@[simp] lemma eval_listMaxDef (v) :
    Semiformula.Evalbm V v listMaxDef.val ↔ v 0 = listMax (v 1) := listMax_defined.df.iff v


-- @@ L767-767 expanded
instance listMax_definable : BoldfaceFunction₁ Sg1 (listMax : V → V) :=
  listMax_defined.to_definable


-- @@ L769-770 expanded
instance listMax_definable' (Γ m) : BoldfaceFunction₁ Γ-[m + 1] (listMax : V → V) :=
  listMax_definable.of_sigmaOne


-- @@ L772-772 verbatim
end «lp_section_11»


-- @@ L774-781 expanded
lemma nth_le_listMax {i v : V} (h : i < len v) : v.[i] ≤ listMax v :=
  by
  induction v using cons_induction_pi1 generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using h)]


-- @@ L783-791 expanded
lemma listMaxss_le {v z : V} (h : ∀ i < len v, v.[i] ≤ z) : listMax v ≤ z :=
  by
  induction v using cons_induction_pi1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih =>
    simp only [listMax_cons, max_le_iff]
    constructor
    · simpa using h 0 (by simp)
    · exact ih (fun i hi ↦ by simpa using h (i + 1) (by simp [hi]))


-- @@ L793-796 verbatim
lemma listMaxss_le_iff {v z : V} : listMax v ≤ z ↔ ∀ i < len v, v.[i] ≤ z := by
  constructor
  · intro h i hi; exact le_trans (nth_le_listMax hi) h
  · exact listMaxss_le


-- @@ L798-798 verbatim
end «lp_section_10»


-- @@ L800-804 verbatim
/-!

### Take Last k-Element

-/


-- @@ L806-806 verbatim
namespace TakeLast


-- @@ L808-813 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : VecRec.Blueprint 1
    where
  nil := .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]) (by simp)
  cons :=
    .mkSigma
      (ExQuantifier.ex
        (Wedge.wedge (LO.FirstOrder.Rewriting.substitute lenDef (vecCons (#0) (vecCons #3 ![])))
          (Wedge.wedge
            (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![#0, #5])
              (LO.FirstOrder.Rewriting.substitute consDef
                (vecCons (#1) (vecCons (#2) (vecCons #3 ![])))))
            (Arrow.arrow (Semiformula.Operator.operator Operator.LE.le ![#5, #0])
              (Semiformula.Operator.operator Operator.Eq.eq ![#1, #4])))))
      (by simp)


-- @@ L815-836 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def construction : VecRec.Construction V blueprint where
  nil _ := 0
  cons (param x xs ih) := if len xs < param 0 then x ∷ xs else ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by
    intro v
    simp only [Fin.isValue, Nat.reduceAdd, Fin.succ_one_eq_two, Fin.succ_zero_eq_one,
      Fin.succ_two_eq_three, Fin.reduceSucc, blueprint, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Semiterm.val_bvar, Matrix.vecCons_zero, Matrix.cons_val_fin_one, Matrix.cons_app_three,
      Matrix.constant_eq_singleton, eval_lenDef, Matrix.cons_val_one,
      LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂, Matrix.cons_app_five,
      Structure.LT.lt, Matrix.cons_app_two, eval_cons, LogicalConnective.Prop.arrow_eq,
      Structure.LE.le, Matrix.cons_app_four, Structure.Eq.eq, LogicalConnective.Prop.and_eq,
      exists_eq_left]
    change (v 0 = if len (v 2) < v 4 then v 1 ∷ v 2 else v 3) ↔
      (len (v 2) < v 4 → v 0 = v 1 ∷ v 2) ∧ (v 4 ≤ len (v 2) → v 0 = v 3)
    rcases lt_or_ge (len (v 2)) (v 4) with (hv | hv)
    · simp [hv]
    · simp [hv, not_lt.mpr hv]


-- @@ L838-838 verbatim
end TakeLast


-- @@ L840-840 verbatim
section «lp_section_12»


-- @@ L842-842 verbatim
open TakeLast


-- @@ L844-845 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def takeLast (v k : V) : V := construction.result ![k] v


-- @@ L847-847 verbatim
@[simp] lemma takeLast_nil : takeLast (0 : V) k = 0 := by simp [takeLast, construction]


-- @@ L849-850 verbatim
lemma takeLast_cons (x v : V) : takeLast (x ∷ v) k = if len v < k then x ∷ v else takeLast v k := by
  simp [takeLast, construction]


-- @@ L852-852 verbatim
section «lp_section_13»


-- @@ L854-855 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.takeLastDef : Sg1.Semisentence 3 := blueprint.resultDef


-- @@ L857-858 expanded
lemma takeLast_defined : DefinedFunction₂ Sg1 (takeLast : V → V → V) takeLastDef :=
  construction.result_defined


-- @@ L860-861 verbatim
@[simp] lemma eval_takeLastDef (v) :
    Semiformula.Evalbm V v takeLastDef.val ↔ v 0 = takeLast (v 1) (v 2) := takeLast_defined.df.iff v


-- @@ L863-863 expanded
instance takeLast_definable : BoldfaceFunction₂ Sg1 (takeLast : V → V → V) :=
  takeLast_defined.to_definable


-- @@ L865-866 expanded
instance takeLast_definable' (Γ m) : BoldfaceFunction₂ Γ-[m + 1] (takeLast : V → V → V) :=
  takeLast_definable.of_sigmaOne


-- @@ L868-868 verbatim
end «lp_section_13»


-- @@ L870-882 expanded
lemma len_takeLast {v k : V} (h : k ≤ len v) : len (takeLast v k) = k :=
  by
  induction v using cons_induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp_all
  case cons x v ih =>
    rw [takeLast_cons]
    have : k = len v + 1 ∨ k ≤ len v :=
      by
      rcases eq_or_lt_of_le h with (h | h)
      · left; simpa using h
      · right; simpa [lt_succ_iff_le] using h
    rcases this with (rfl | hkv)
    · simp
    · simp [not_lt.mpr hkv, ih hkv]


-- @@ L884-885 verbatim
@[simp] lemma takeLast_len_self (v : V) : takeLast v (len v) = v := by
  rcases nil_or_cons v with (rfl | ⟨x, v, rfl⟩) <;> simp [takeLast_cons]


-- @@ L887-889 verbatim
/-- TODO: move -/
@[simp] lemma add_sub_add (a b c : V) : (a + c) - (b + c) = a - b :=
  add_tsub_add_eq_tsub_right a c b


-- @@ L891-895 expanded
@[simp]
lemma takeLast_zero (v : V) : takeLast v 0 = 0 :=
  by
  induction v using cons_induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih => simp [takeLast_cons, ih]


-- @@ L897-909 expanded
lemma takeLast_succ_of_lt {i v : V} (h : i < len v) :
    takeLast v (i + 1) = v.[len v - (i + 1)] ∷ takeLast v i :=
  by
  induction v using cons_induction_sigma1 generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp at h
  case cons x v
    ih =>
    simp only [takeLast_cons, lt_succ_iff_le, len_cons, add_sub_add]
    rcases show i = len v ∨ i < len v from eq_or_lt_of_le (by simpa [lt_succ_iff_le] using h) with
      (rfl | hi)
    · simp
    · have : len v - i = len v - (i + 1) + 1 := by
        rw [← sub_sub, sub_add_self_of_le (pos_iff_one_le.mp (tsub_pos_of_lt hi))]
      simpa [not_le.mpr hi, this, nth_cons_succ, not_lt.mpr (le_of_lt hi)] using ih hi


-- @@ L911-911 verbatim
end «lp_section_12»



-- @@ L914-918 verbatim
/-!

### Concatation

-/


-- @@ L920-920 verbatim
namespace Concat


-- @@ L922-925 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : VecRec.Blueprint 1
    where
  nil :=
    .mkSigma
      (LO.FirstOrder.Rewriting.substitute consDef
        (vecCons (#0) (vecCons (#1) (vecCons (Semiterm.numeral 0) ![]))))
      (by simp)
  cons :=
    .mkSigma
      (LO.FirstOrder.Rewriting.substitute consDef (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))
      (by simp)


-- @@ L927-932 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def construction : VecRec.Construction V blueprint
    where
  nil param := cons (param 0) 0
  cons (_ x _ ih) := x ∷ ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint, Fin.isValue]


-- @@ L934-934 verbatim
end Concat


-- @@ L936-936 verbatim
section «lp_section_14»


-- @@ L938-938 verbatim
open Concat


-- @@ L940-941 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def concat (v z : V) : V := construction.result ![z] v


-- @@ L943-943 expanded
@[simp]
lemma concat_nil (z : V) : concat 0 z = cons z 0 := by simp [concat, construction]


-- @@ L945-946 verbatim
@[simp] lemma concat_cons (x v z : V) : concat (x ∷ v) z = x ∷ concat v z := by
  simp [concat, construction]


-- @@ L948-948 verbatim
section «lp_section_15»


-- @@ L950-951 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.concatDef : Sg1.Semisentence 3 := blueprint.resultDef


-- @@ L953-954 expanded
lemma concat_defined : DefinedFunction₂ Sg1 (concat : V → V → V) concatDef :=
  construction.result_defined


-- @@ L956-957 verbatim
@[simp] lemma eval_concatDef (v) :
    Semiformula.Evalbm V v concatDef.val ↔ v 0 = concat (v 1) (v 2) := concat_defined.df.iff v


-- @@ L959-959 expanded
instance concat_definable : BoldfaceFunction₂ Sg1 (concat : V → V → V) :=
  concat_defined.to_definable


-- @@ L961-962 expanded
instance concat_definable' (Γ m) : BoldfaceFunction₂ Γ-[m + 1] (concat : V → V → V) :=
  concat_definable.of_sigmaOne


-- @@ L964-964 verbatim
end «lp_section_15»


-- @@ L966-970 expanded
@[simp]
lemma len_concat (v z : V) : len (concat v z) = len v + 1 :=
  by
  induction v using cons_induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih => simp [ih]


-- @@ L972-979 expanded
lemma concat_nth_lt (v z : V) {i} (hi : i < len v) : (concat v z).[i] = v.[i] :=
  by
  induction v using cons_induction_sigma1 generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp at hi
  case cons x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]


-- @@ L981-985 expanded
@[simp]
lemma concat_nth_len (v z : V) : (concat v z).[len v] = z :=
  by
  induction v using cons_induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons x v ih => simp [ih]


-- @@ L987-987 verbatim
lemma concat_nth_len' (v z : V) {i} (hi : len v = i) : (concat v z).[i] = z := by rcases hi; simp


-- @@ L989-989 verbatim
end «lp_section_14»


-- @@ L991-995 verbatim
/-!

### Membership

-/


-- @@ L997-997 verbatim
section «lp_section_16»


-- @@ L999-1000 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def MemVec (x v : V) : Prop := ∃ i < len v, x = v.[i]


-- @@ L1002-1003 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:40 " ∈ᵥ " => MemVec


-- @@ L1005-1005 verbatim
@[simp] lemma not_memVec_empty (x : V) : ¬x ∈ᵥ 0 := by rintro ⟨i, h, _⟩; simp at h


-- @@ L1007-1007 verbatim
lemma nth_mem_memVec {i v : V} (h : i < len v) : v.[i] ∈ᵥ v := ⟨i, by simp [h]⟩


-- @@ L1009-1009 verbatim
@[simp] lemma memVec_insert_fst {x v : V} : x ∈ᵥ x ∷ v := ⟨0, by simp⟩


-- @@ L1011-1020 verbatim
@[simp] lemma memVec_cons_iff {x y v : V} : x ∈ᵥ y ∷ v ↔ x = y ∨ x ∈ᵥ v := by
  constructor
  · rintro ⟨i, h, rfl⟩
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · left; simp
    · right; simpa only [nth_cons_succ] using nth_mem_memVec (by simpa using h)
  · rintro (rfl | hx)
    · simp
    · rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i + 1, by simp [hi]⟩


-- @@ L1022-1022 verbatim
lemma le_of_memVec {x v : V} (h : x ∈ᵥ v) : x ≤ v := by rcases h with ⟨i, _, rfl⟩; simp


-- @@ L1024-1024 verbatim
section «lp_section_17»


-- @@ L1026-1029 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.memVecDef : Dlt1.Semisentence 2 :=
  .mkDelta
    (.mkSigma
      (ExQuantifier.ex
        (Wedge.wedge (LO.FirstOrder.Rewriting.substitute lenDef (vecCons (#0) (vecCons #2 ![])))
          (Semiformula.bexLT (#0)
            (LO.FirstOrder.Rewriting.substitute nthDef
              (vecCons (#2) (vecCons (#3) (vecCons #0 ![])))))))
      (by simp))
    (.mkPi
      (UnivQuantifier.univ
        (Arrow.arrow (LO.FirstOrder.Rewriting.substitute lenDef (vecCons (#0) (vecCons #2 ![])))
          (Semiformula.bexLT (#0)
            (UnivQuantifier.univ
              (Arrow.arrow
                (LO.FirstOrder.Rewriting.substitute nthDef
                  (vecCons (#0) (vecCons (#4) (vecCons #1 ![]))))
                (Semiformula.Operator.operator Operator.Eq.eq ![#3, #0]))))))
      (by simp))


-- @@ L1031-1032 expanded
lemma memVec_defined : DefinedRel Dlt1 (MemVec : V → V → Prop) memVecDef :=
  ⟨by intro v; simp [memVecDef], by intro v; simp [memVecDef, MemVec]⟩


-- @@ L1034-1035 verbatim
@[simp] lemma eval_memVecDef (v) :
    Semiformula.Evalbm V v memVecDef.val ↔ v 0 ∈ᵥ v 1 := memVec_defined.df.iff v


-- @@ L1037-1037 expanded
instance memVec_definable : BoldfaceRel Dlt1 (MemVec : V → V → Prop) :=
  memVec_defined.to_definable


-- @@ L1039-1040 expanded
instance memVec_definable' (Γ m) : BoldfaceRel Γ-[m + 1] (MemVec : V → V → Prop) :=
  memVec_definable.of_deltaOne


-- @@ L1042-1042 verbatim
end «lp_section_17»


-- @@ L1044-1044 verbatim
end «lp_section_16»


-- @@ L1046-1050 verbatim
/-!

### Subset

-/


-- @@ L1052-1052 verbatim
section «lp_section_18»


-- @@ L1054-1055 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def SubsetVec (v w : V) : Prop := ∀ x, x ∈ᵥ v → x ∈ᵥ w


-- @@ L1057-1058 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:30 " ⊆ᵥ " => SubsetVec


-- @@ L1060-1060 verbatim
@[simp, refl] lemma _root_.LO.Arith.SubsetVec.refl (v : V) : v ⊆ᵥ v := fun _ hx ↦ hx


-- @@ L1062-1062 verbatim
@[simp] lemma subsetVec_insert_tail (x v : V) : v ⊆ᵥ x ∷ v := by intro y hy; simp [hy]


-- @@ L1064-1064 verbatim
section «lp_section_19»


-- @@ L1066-1069 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.subsetVecDef : Dlt1.Semisentence 2 :=
  .mkDelta
    (.mkSigma
      (Semiformula.ballLTSucc (#0)
        (Arrow.arrow
          (LO.FirstOrder.Rewriting.substitute memVecDef.pi (vecCons (#0) (vecCons #1 ![])))
          (LO.FirstOrder.Rewriting.substitute memVecDef.sigma (vecCons (#0) (vecCons #2 ![])))))
      (by simp))
    (.mkPi
      (Semiformula.ballLTSucc (#0)
        (Arrow.arrow
          (LO.FirstOrder.Rewriting.substitute memVecDef.sigma (vecCons (#0) (vecCons #1 ![])))
          (LO.FirstOrder.Rewriting.substitute memVecDef.pi (vecCons (#0) (vecCons #2 ![])))))
      (by simp))


-- @@ L1071-1084 expanded
lemma subsetVec_defined : DefinedRel Dlt1 (SubsetVec : V → V → Prop) subsetVecDef :=
  ⟨by intro v;
    simp [subsetVecDef, HierarchySymbol.Semiformula.val_sigma, memVec_defined.proper.iff'],
    by
    intro v
    simp only [Fin.isValue, subsetVecDef, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.val_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ballLTSucc', Semiterm.val_bvar,
      LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.vecCons_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.constant_eq_singleton, memVec_defined.proper.iff', eval_memVecDef, Matrix.cons_app_two,
      LogicalConnective.Prop.arrow_eq]
    constructor
    · intro h x _; exact h x
    · intro h x hx; exact h x (le_of_memVec hx) hx⟩


-- @@ L1086-1087 verbatim
@[simp] lemma eval_subsetVecDef (v) :
    Semiformula.Evalbm V v subsetVecDef.val ↔ v 0 ⊆ᵥ v 1 := subsetVec_defined.df.iff v


-- @@ L1089-1090 expanded
instance subsetVec_definable : BoldfaceRel Dlt1 (SubsetVec : V → V → Prop) :=
  subsetVec_defined.to_definable


-- @@ L1092-1093 expanded
instance subsetVec_definable' (Γ m) : BoldfaceRel Γ-[m + 1] (SubsetVec : V → V → Prop) :=
  subsetVec_definable.of_deltaOne


-- @@ L1095-1095 verbatim
end «lp_section_19»


-- @@ L1097-1097 verbatim
end «lp_section_18»


-- @@ L1099-1103 verbatim
/-!

### Repeat

-/


-- @@ L1105-1105 verbatim
section «lp_section_20»


-- @@ L1107-1110 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.repeatVec.blueprint : PR.Blueprint 1
    where
  zero :=
    .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]) (by simp)
  succ :=
    .mkSigma
      (LO.FirstOrder.Rewriting.substitute consDef (vecCons (#0) (vecCons (#3) (vecCons #1 ![]))))
      (by simp)


-- @@ L1112-1117 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.repeatVec.construction : PR.Construction V repeatVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun x _ ih ↦ x 0 ∷ ih
  zero_defined := by intro v; simp [repeatVec.blueprint]
  succ_defined := by intro v; simp [repeatVec.blueprint]


-- @@ L1119-1120 verbatim
/-- `repeatVec x k = x ∷ x ∷ x ∷ ... k times ... ∷ 0` -/
def repeatVec (x k : V) : V := repeatVec.construction.result ![x] k


-- @@ L1122-1123 verbatim
@[simp] lemma repeatVec_zero (x : V) : repeatVec x 0 = 0 := by
  simp [repeatVec, repeatVec.construction]


-- @@ L1125-1126 verbatim
@[simp] lemma repeatVec_succ (x k : V) : repeatVec x (k + 1) = x ∷ repeatVec x k := by
  simp [repeatVec, repeatVec.construction]


-- @@ L1128-1128 verbatim
section «lp_section_21»


-- @@ L1130-1132 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.repeatVecDef : Sg1.Semisentence 3 :=
  repeatVec.blueprint.resultDef |>.rew (Rew.substs ![#0, #2, #1])


-- @@ L1134-1135 expanded
lemma repeatVec_defined : DefinedFunction₂ Sg1 (repeatVec : V → V → V) repeatVecDef := fun v ↦ by
  simp [repeatVec.construction.result_defined_iff, repeatVecDef]; rfl


-- @@ L1137-1139 verbatim
@[simp] lemma eval_repeatVec (v) :
    Semiformula.Evalbm V v repeatVecDef.val ↔ v 0 = repeatVec (v 1) (v 2) :=
      repeatVec_defined.df.iff v


-- @@ L1141-1142 expanded
instance repeatVec_definable : BoldfaceFunction₂ Sg1 (repeatVec : V → V → V) :=
  repeatVec_defined.to_definable


-- @@ L1144-1145 expanded
instance repeatVec_definable' (Γ) : BoldfaceFunction₂ Γ-[m + 1] (repeatVec : V → V → V) :=
  repeatVec_definable.of_sigmaOne


-- @@ L1147-1147 verbatim
end «lp_section_21»


-- @@ L1149-1153 expanded
@[simp]
lemma len_repeatVec (x k : V) : len (repeatVec x k) = k :=
  by
  induction k using induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih => simp [ih]


-- @@ L1155-1155 verbatim
@[simp] lemma le_repaetVec (x k : V) : k ≤ repeatVec x k := by simpa using len_le (repeatVec x k)


-- @@ L1157-1164 expanded
lemma nth_repeatVec (x k : V) {i} (h : i < k) : (repeatVec x k).[i] = x :=
  by
  induction k using induction_sigma1 generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp at h
  case succ k ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simpa using ih (by simpa using h)


-- @@ L1166-1167 verbatim
lemma len_repeatVec_of_nth_le {v m : V} (H : ∀ i < len v, v.[i] ≤ m) : v ≤ repeatVec m (len v) :=
  le_of_nth_le_nth (by simp) (fun i hi ↦ by simp [nth_repeatVec m (len v) hi, H i hi])


-- @@ L1169-1169 verbatim
end «lp_section_20»


-- @@ L1171-1175 verbatim
/-!

### Convert to Set

-/


-- @@ L1177-1177 verbatim
namespace VecToSet


-- @@ L1179-1182 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def blueprint : VecRec.Blueprint 0
    where
  nil := .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]) (by simp)
  cons :=
    .mkSigma
      (LO.FirstOrder.Rewriting.substitute insertDef (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))
      (by simp)


-- @@ L1184-1189 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def construction : VecRec.Construction V blueprint where
  nil _ := ∅
  cons (_ x _ ih) := insert x ih
  nil_defined := by intro v; simp [blueprint, emptyset_def]
  cons_defined := by intro v; simp [blueprint]


-- @@ L1191-1191 verbatim
end VecToSet


-- @@ L1193-1193 verbatim
section «lp_section_22»


-- @@ L1195-1195 verbatim
open VecToSet


-- @@ L1197-1198 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def vecToSet (v : V) : V := construction.result ![] v


-- @@ L1200-1200 verbatim
@[simp] lemma vecToSet_nil : vecToSet (0 : V) = ∅ := by simp [vecToSet, construction]


-- @@ L1202-1203 verbatim
@[simp] lemma vecToSet_cons (x v : V) :
    vecToSet (x ∷ v) = insert x (vecToSet v) := by simp [vecToSet, construction]


-- @@ L1205-1205 verbatim
section «lp_section_23»


-- @@ L1207-1208 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.vecToSetDef : Sg1.Semisentence 2 := blueprint.resultDef


-- @@ L1210-1211 expanded
lemma vecToSet_defined : DefinedFunction₁ Sg1 (vecToSet : V → V) vecToSetDef :=
  construction.result_defined


-- @@ L1213-1214 verbatim
@[simp] lemma eval_vecToSetDef (v) :
    Semiformula.Evalbm V v vecToSetDef.val ↔ v 0 = vecToSet (v 1) := vecToSet_defined.df.iff v


-- @@ L1216-1216 expanded
instance vecToSet_definable : BoldfaceFunction₁ Sg1 (vecToSet : V → V) :=
  vecToSet_defined.to_definable


-- @@ L1218-1219 expanded
instance vecToSet_definable' (Γ) : BoldfaceFunction₁ Γ-[m + 1] (vecToSet : V → V) :=
  vecToSet_definable.of_sigmaOne


-- @@ L1221-1221 verbatim
end «lp_section_23»


-- @@ L1223-1236 expanded
lemma mem_vecToSet_iff {v x : V} : x ∈ vecToSet v ↔ ∃ i < len v, x = v.[i] :=
  by
  induction v using cons_induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case cons y v ih =>
    simp only [vecToSet_cons, mem_bitInsert_iff, ih, len_cons]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by simp [hi]⟩
    · rintro ⟨i, hi, rfl⟩
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · right; exact ⟨i, by simpa using hi, by simp⟩


-- @@ L1238-1239 verbatim
@[simp] lemma nth_mem_vecToSet {v i : V} (h : i < len v) : v.[i] ∈ vecToSet v :=
  mem_vecToSet_iff.mpr ⟨i, h, rfl⟩


-- @@ L1241-1241 verbatim
end «lp_section_22»


-- @@ L1243-1243 verbatim
end Arith

-- @@ L1244-1244 verbatim
end LO
