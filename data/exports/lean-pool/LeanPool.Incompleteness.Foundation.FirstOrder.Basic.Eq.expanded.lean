/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.BinderNotation
public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Elementary
public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Calculus
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness


-- @@ L13-13 verbatim
/-! # Eq -/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace Matrix


-- @@ L19-19 verbatim
variable {α : Type*}


-- @@ L21-22 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α := if h : x < k then v ⟨x, h⟩ else default


-- @@ L24-24 verbatim
end Matrix


-- @@ L26-26 verbatim
namespace LO


-- @@ L28-28 verbatim
namespace FirstOrder


-- @@ L30-30 verbatim
variable {L : Language} {μ : Type*} [Semiformula.Operator.Eq L]


-- @@ L32-32 verbatim
namespace Theory


-- @@ L34-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Sub (T U : Theory L) where
  sub : T ⊆ U


-- @@ L38-38 verbatim
section «lp_section_1»


-- @@ L40-40 verbatim
variable (L)


-- @@ L42-43 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.refl : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq ![&0, &0]


-- @@ L45-46 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.symm : SyntacticFormula L :=
  Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![&0, &1])
    (Semiformula.Operator.operator Operator.Eq.eq ![&1, &0])


-- @@ L48-49 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.trans : SyntacticFormula L :=
  Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![&0, &1])
    (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![&1, &2])
      (Semiformula.Operator.operator Operator.Eq.eq ![&0, &2]))


-- @@ L51-51 verbatim
variable {L}


-- @@ L53-57 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.funcExt {k} (f : L.Func k) : SyntacticFormula L :=
  Arrow.arrow
    (Matrix.conjVec fun i : Fin k ↦ Semiformula.Operator.operator Operator.Eq.eq ![&i, &(k + i)])
    (Operator.Eq.eq.operator ![Semiterm.func f (fun i ↦ &i), Semiterm.func f (fun i ↦ &(k + i))])


-- @@ L59-62 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Eq.relExt {k} (r : L.Rel k) : SyntacticFormula L :=
  Arrow.arrow
    (Matrix.conjVec fun i : Fin k ↦ Semiformula.Operator.operator Operator.Eq.eq ![&i, &(k + i)])
    (Arrow.arrow (Semiformula.rel r (fun i ↦ &i)) (Semiformula.rel r (fun i ↦ &(k + i))))


-- @@ L64-70 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k} (r : L.Rel k) : eqAxiom (Eq.relExt r)


-- @@ L72-73 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐄𝐐" => eqAxiom


-- @@ L75-93 expanded
lemma _root_.LO.FirstOrder.Theory.Eq.defeq :
    eqAxiom =
      {Eq.refl L, Eq.symm L, Eq.trans L} ∪ Set.range (fun f : (k : ℕ) × L.Func k ↦ Eq.funcExt f.2) ∪
        Set.range (fun f : (k : ℕ) × L.Rel k ↦ Eq.relExt f.2) :=
  by
  ext φ; constructor
  · rintro ⟨⟩
    case refl => simp
    case symm => simp
    case trans => simp
    case funcExt k f => left; right; exact ⟨⟨k, f⟩, rfl⟩
    case relExt k r => right; exact ⟨⟨k, r⟩, rfl⟩
  · rintro (((rfl | rfl | rfl) | ⟨f, rfl⟩) | ⟨r, rfl⟩)
    · exact eqAxiom.refl
    · exact eqAxiom.symm
    · exact eqAxiom.trans
    · exact eqAxiom.funcExt _
    · exact eqAxiom.relExt _


-- @@ L95-100 expanded
@[simp]
lemma _root_.LO.FirstOrder.Theory.EqAxiom.finite [L.Finite] : Set.Finite (eqAxiom : Theory L) :=
  by
  have : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  have : Fintype ((k : ℕ) × L.Rel k) := Language.Finite.rel
  rw [Eq.defeq]
  simp [Set.finite_range]


-- @@ L102-102 verbatim
end «lp_section_1»


-- @@ L104-104 verbatim
end Theory


-- @@ L106-106 verbatim
namespace Structure


-- @@ L108-108 verbatim
namespace Eq


-- @@ L110-115 expanded
@[simp]
lemma models_eqAxiom {M : Type u} [Nonempty M] [Structure L M] [Structure.Eq L M] :
    ModelsTheory M (eqAxiom : Theory L) :=
  ⟨by
    intro σ h
    cases h <;>
      try { simp [models_def, Semiterm.val_func, Semiformula.eval_rel, *]; try simp_all
      }⟩


-- @@ L117-117 verbatim
variable (L)


-- @@ L119-120 expanded
instance models_eqAxiom' (M : Type u) [Nonempty M] [Structure L M] [Structure.Eq L M] :
    ModelsTheory M (eqAxiom : Theory L) :=
  Structure.Eq.models_eqAxiom


-- @@ L122-122 verbatim
variable {M : Type u} [Nonempty M] [Structure L M]


-- @@ L124-125 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]


-- @@ L127-127 verbatim
variable {L}


-- @@ L129-129 expanded
variable [H : ModelsTheory M (eqAxiom : Theory L)]


-- @@ L131-131 verbatim
open Semiterm Theory Semiformula


-- @@ L133-135 expanded
lemma eqv_refl (a : M) : eqv L a a :=
  by
  have : Models M (Semiformula.Operator.operator Operator.Eq.eq ![&0, &0]) :=
    H.realize _ (Theory.eqAxiom.refl (L := L))
  simpa [eqv, models_def] using this (fun _ ↦ a)


-- @@ L137-139 expanded
lemma eqv_symm {a b : M} : eqv L a b → eqv L b a :=
  by
  have :
    Models M
      (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![&0, &1])
        (Semiformula.Operator.operator Operator.Eq.eq ![&1, &0])) :=
    H.realize _ (Theory.eqAxiom.symm (L := L))
  simpa [eqv, models_def] using this (cases a fun _ ↦ b)


-- @@ L141-143 expanded
lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c :=
  by
  have :
    Models M
      (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![&0, &1])
        (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![&1, &2])
          (Semiformula.Operator.operator Operator.Eq.eq ![&0, &2]))) :=
    H.realize _ (Theory.eqAxiom.trans (L := L))
  simpa [eqv, models_def] using this (cases a (cases b fun _ ↦ c))


-- @@ L145-154 expanded
lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) :=
  by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have :=
    H.realize _ (eqAxiom.funcExt f (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x)
  have : (∀ i, Operator.Eq.eq.val ![v i, w i]) → Operator.Eq.eq.val ![func f v, func f w] := by {
    simpa [models_def, Matrix.vecAppend_eq_ite, Semiterm.val_func, Matrix.iget,
      show ∀ i : Fin k, i < k + k from fun i ↦ lt_of_lt_of_le i.prop (by simp)] using
      H.realize _ (eqAxiom.funcExt f (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x)
  }
  exact this h


-- @@ L156-163 expanded
lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w :=
  by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have : (∀ i, Operator.Eq.eq.val ![v i, w i]) → rel r v → rel r w := by {
    simpa [models_def, Matrix.vecAppend_eq_ite, Semiterm.val_func, eval_rel (r := r), Matrix.iget,
      show ∀ i : Fin k, i < k + k from fun i ↦ lt_of_lt_of_le i.prop (by simp)] using
      H.realize _ (eqAxiom.relExt r (L := L)) (fun x ↦ Matrix.iget (Matrix.vecAppend rfl v w) x)
  }
  exact this h


-- @@ L165-169 verbatim
lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v = rel r w := by
  simp only [eq_iff_iff]; constructor
  · exact eqv_relExt_aux r h
  · exact eqv_relExt_aux r (fun i => eqv_symm (h i))


-- @@ L171-174 verbatim
lemma eqv_equivalence : Equivalence (eqv L (M := M)) where
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans


-- @@ L176-176 verbatim
variable (L M)


-- @@ L178-179 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def eqvSetoid : Setoid M := Setoid.mk (eqv L) eqv_equivalence


-- @@ L181-182 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def QuotEq := Quotient (eqvSetoid L M)


-- @@ L184-184 verbatim
variable {L M}


-- @@ L186-187 verbatim
instance _root_.LO.FirstOrder.Structure.Eq.QuotEq.inhabited :
    Nonempty (QuotEq L M) := Nonempty.map (⟦·⟧) inferInstance


-- @@ L189-189 verbatim
lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq L M) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid L M)


-- @@ L191-191 verbatim
namespace QuotEq


-- @@ L193-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def func ⦃k⦄ (f : L.Func k) (v : Fin k → QuotEq L M) : QuotEq L M :=
  Quotient.liftVec (s := eqvSetoid L M) (⟦Structure.func f ·⟧) (fun _ _ hvw =>
    of_eq_of.mpr (eqv_funcExt f hvw)) v


-- @@ L198-200 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq L M) : Prop :=
  Quotient.liftVec (s := eqvSetoid L M) (Structure.rel r) (fun _ _ hvw => eqv_relExt r hvw) v


-- @@ L202-204 verbatim
instance struc : Structure L (QuotEq L M) where
  func := QuotEq.func
  rel := QuotEq.rel


-- @@ L206-209 verbatim
lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) :
    Structure.func (M :=
  QuotEq L M) f (fun i => ⟦v i⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _


-- @@ L211-214 verbatim
lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) :
    Structure.rel (M :=
  QuotEq L M) r (fun i => ⟦v i⟧) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _


-- @@ L216-226 expanded
private def mkHom : Hom L M (QuotEq L M)
    where
  toFun := fun a => ⟦a⟧
  func' := by
    intro k f v
    change (⟦Structure.func f v⟧ : QuotEq L M) = Structure.func (M := QuotEq L M) f (fun i => ⟦v i⟧)
    exact (funk_mk f v).symm
  rel' := by
    intro k r v h
    change Structure.rel (M := QuotEq L M) r (fun i => ⟦v i⟧)
    exact (rel_mk r v).mpr h


-- @@ L228-230 verbatim
lemma val_mk {e} {ε} (t : Semiterm L μ n) :
    Semiterm.valm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) t = ⟦Semiterm.valm M e ε t⟧ :=
  by exact (HomClass.val_term (mkHom (L := L) (M := M)) e ε t).symm


-- @@ L232-295 expanded
lemma eval_mk {e} {ε} {φ : Semiformula L μ n} :
    Semiformula.Evalm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) φ ↔
      Semiformula.Evalm M e ε φ :=
  by
  induction φ using Semiformula.rec'
  case hverum => simp only [LogicalConnective.HomClass.map_top, «Prop».top_eq_true]
  case hfalsum => simp only [LogicalConnective.HomClass.map_bot, «Prop».bot_eq_false]
  case hrel r
    v =>
    have hv :
      (fun i => Semiterm.valm (QuotEq L M) (fun j => ⟦e j⟧) (fun j => ⟦ε j⟧) (v i)) = fun i =>
        ⟦Semiterm.valm M e ε (v i)⟧ :=
      by
      funext i
      exact val_mk (e := e) (ε := ε) (v i)
    calc
      Semiformula.Evalm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) (Semiformula.rel r v) ↔
          Structure.rel (M := QuotEq L M) r
            (fun i => Semiterm.valm (QuotEq L M) (fun j => ⟦e j⟧) (fun j => ⟦ε j⟧) (v i)) :=
        Semiformula.eval_rel
      _ ↔ Structure.rel (M := QuotEq L M) r (fun i => ⟦Semiterm.valm M e ε (v i)⟧) :=
        (iff_of_eq (congrArg (Structure.rel (M := QuotEq L M) r) hv))
      _ ↔ Structure.rel r (fun i => Semiterm.valm M e ε (v i)) :=
        rel_mk r (fun i => Semiterm.valm M e ε (v i))
  case hnrel r
    v =>
    have hv :
      (fun i => Semiterm.valm (QuotEq L M) (fun j => ⟦e j⟧) (fun j => ⟦ε j⟧) (v i)) = fun i =>
        ⟦Semiterm.valm M e ε (v i)⟧ :=
      by
      funext i
      exact val_mk (e := e) (ε := ε) (v i)
    calc
      Semiformula.Evalm (QuotEq L M) (fun i => ⟦e i⟧) (fun i => ⟦ε i⟧) (Semiformula.nrel r v) ↔
          ¬Structure.rel (M := QuotEq L M) r
              (fun i => Semiterm.valm (QuotEq L M) (fun j => ⟦e j⟧) (fun j => ⟦ε j⟧) (v i)) :=
        Semiformula.eval_nrel
      _ ↔ ¬Structure.rel (M := QuotEq L M) r (fun i => ⟦Semiterm.valm M e ε (v i)⟧) :=
        (not_congr (iff_of_eq (congrArg (Structure.rel (M := QuotEq L M) r) hv)))
      _ ↔ ¬Structure.rel r (fun i => Semiterm.valm M e ε (v i)) :=
        not_congr (rel_mk r (fun i => Semiterm.valm M e ε (v i)))
  case hand => simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, *]
  case hor => simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, *]
  case hall n φ ih =>
    simp only [Semiformula.eval_all, Nat.succ_eq_add_one]
    constructor
    · intro h a
      exact (ih (e := vecCons a e)).mp (by simp only [Matrix.comp_vecCons] at h ⊢; exact h ⟦a⟧)
    · intro h a;
      induction a using Quotient.ind with
      | _ a => have := ih.mpr (h a); simp only [Matrix.comp_vecCons] at this ⊢; exact this
  case hex n φ ih =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one]
    constructor
    · intro ⟨a, h⟩
      induction a using Quotient.ind with
      | _ a =>
        exact ⟨a, (ih (e := vecCons a e)).mp (by simp only [Matrix.comp_vecCons] at h ⊢; exact h)⟩
    · intro ⟨a, h⟩
      exact ⟨⟦a⟧, by have := ih.mpr h; simp only [Matrix.comp_vecCons] at this ⊢; exact this⟩


-- @@ L297-301 verbatim
lemma eval_mk₀ {ε} {φ : Formula L ξ} :
    Semiformula.Evalfm (QuotEq L M) (fun i => ⟦ε i⟧) φ ↔ Semiformula.Evalfm (L := L) M ε φ := by
  have h := eval_mk (H := H) (e := ![]) (ε := ε) (φ := φ)
  simp only [Matrix.empty_eq] at h
  exact h


-- @@ L303-308 expanded
lemma models_iff {φ : SyntacticFormula L} : Models (QuotEq L M) φ ↔ Models M φ :=
  by
  constructor
  · intro h f; exact eval_mk₀.mp (h (fun x ↦ ⟦f x⟧))
  · intro h f
    induction f using Quotient.induction_on_pi with
    | _ f => exact eval_mk₀.mpr (h f)


-- @@ L310-310 verbatim
variable (L M)


-- @@ L312-312 expanded
lemma elementaryEquiv : ElementaryEquiv L (QuotEq L M) M := fun _ => models_iff


-- @@ L314-314 verbatim
variable {L M}


-- @@ L316-330 verbatim
lemma rel_eq (a b : QuotEq L M) :
    (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq L M) ![a, b] ↔ a = b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      have hEval :
          (@Semiformula.Operator.Eq.eq L _).val (M := QuotEq L M) ![⟦a⟧, ⟦b⟧] ↔
            eqv L a b := by
        have h := eval_mk (H := H) (e := ![a, b]) (ε := Empty.elim)
          (φ := Semiformula.Operator.Eq.eq.sentence)
        simp only [Semiformula.Operator.val, eqv, Matrix.fun_eq_vec₂, Matrix.cons_val_zero,
          Matrix.cons_val_one, Empty.eq_elim] at h ⊢
        exact h
      exact hEval.trans (of_eq_of (L := L) (M := M) (a := a) (b := b)).symm


-- @@ L332-332 verbatim
instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩


-- @@ L334-334 verbatim
end QuotEq


-- @@ L336-336 verbatim
end Eq


-- @@ L338-338 verbatim
end Structure


-- @@ L340-349 expanded
lemma consequence_iff_eq {T : Theory L} [WeakerThan eqAxiom T] {φ : SyntacticFormula L} :
    Consequence (Struc.{v, u} L) T φ ↔
      (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M],
        ModelsTheory M T → Models M φ) :=
  by
  simp only [consequence_iff, Nonempty.forall]; constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    have : Nonempty M := ⟨x⟩
    have H : ModelsTheory M (eqAxiom : Theory L) := models_of_subtheory hM
    have e : ElementaryEquiv L (Structure.Eq.QuotEq L M) M :=
      Structure.Eq.QuotEq.elementaryEquiv L M
    exact e.models.mp <| h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM)


-- @@ L351-354 expanded
lemma consequence_iff_eq' {T : Theory L} [WeakerThan eqAxiom T] {φ : SyntacticFormula L} :
    Consequence (Struc.{v, u} L) T φ ↔
      (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [ModelsTheory M T],
        Models M φ) :=
  by rw [consequence_iff_eq]


-- @@ L356-365 expanded
lemma satisfiable_iff_eq {T : Theory L} [WeakerThan eqAxiom T] :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔
      (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M),
        ModelsTheory M T) :=
  by
  simp only [satisfiable_iff, exists_prop, Nonempty.exists]; constructor
  · intro ⟨M, x, s, hM⟩; have : Nonempty M := ⟨x⟩
    have H : ModelsTheory M (eqAxiom : Theory L) := models_of_subtheory hM
    have e : ElementaryEquiv L (Structure.Eq.QuotEq L M) M :=
      Structure.Eq.QuotEq.elementaryEquiv L M
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩


-- @@ L367-368 expanded
instance {T : Theory L} [WeakerThan eqAxiom T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) :
    ModelsTheory (ModelOfSat sat) (eqAxiom : Theory L) :=
  models_of_subtheory (ModelOfSat.models sat)


-- @@ L370-372 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ModelOfSatEq {T : Theory L} [WeakerThan eqAxiom T]
    (sat : Semantics.Satisfiable (Struc.{v, u} L) T) : Type _ :=
  Structure.Eq.QuotEq L (ModelOfSat sat)


-- @@ L374-374 verbatim
namespace ModelOfSatEq


-- @@ L376-376 expanded
variable {T : Theory L} [WeakerThan eqAxiom T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)


-- @@ L378-378 verbatim
noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited


-- @@ L380-380 verbatim
noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc


-- @@ L382-382 verbatim
noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq


-- @@ L384-387 expanded
lemma models : ModelsTheory (ModelOfSatEq sat) T :=
  have e : ElementaryEquiv L (ModelOfSatEq sat) (ModelOfSat sat) :=
    Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)


-- @@ L389-389 expanded
instance mod : ModelsTheory (ModelOfSatEq sat) T :=
  models sat


-- @@ L391-391 verbatim
open Semiterm Semiformula


-- @@ L393-395 verbatim
noncomputable instance [Operator.Zero L] :
    Zero (ModelOfSatEq sat) :=
  ⟨(@Operator.Zero.zero L _).val ![]⟩


-- @@ L397-397 verbatim
instance strucZero [Operator.Zero L] : Structure.Zero L (ModelOfSatEq sat) := ⟨rfl⟩


-- @@ L399-401 verbatim
noncomputable instance [Operator.One L] :
    One (ModelOfSatEq sat) :=
  ⟨(@Operator.One.one L _).val ![]⟩


-- @@ L403-403 verbatim
instance [Operator.One L] : Structure.One L (ModelOfSatEq sat) := ⟨rfl⟩


-- @@ L405-406 verbatim
noncomputable instance [Operator.Add L] : Add (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩


-- @@ L408-408 verbatim
instance [Operator.Add L] : Structure.Add L (ModelOfSatEq sat) := ⟨fun _ _ => rfl⟩


-- @@ L410-411 verbatim
noncomputable instance [Operator.Mul L] : Mul (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩


-- @@ L413-413 verbatim
instance [Operator.Mul L] : Structure.Mul L (ModelOfSatEq sat) := ⟨fun _ _ => rfl⟩


-- @@ L415-415 verbatim
instance [Operator.LT L] : LT (ModelOfSatEq sat) := ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩


-- @@ L417-417 verbatim
instance [Operator.LT L] : Structure.LT L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L419-420 verbatim
instance [Operator.Mem L] : Membership (ModelOfSatEq sat) (ModelOfSatEq sat) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩


-- @@ L422-422 verbatim
instance [Operator.Mem L] : Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L424-424 verbatim
end ModelOfSatEq


-- @@ L426-426 verbatim
namespace Semiformula


-- @@ L428-430 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ExQuantifier.ex
    (Wedge.wedge (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 fun x ↦ #(finSuccItr x 1)))
      (UnivQuantifier.univ
        (Arrow.arrow (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 fun x ↦ #(finSuccItr x 2)))
          (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]))))


-- @@ L432-433 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:64 "∃'! " => existsUnique


-- @@ L435-435 verbatim
variable {M : Type*} [s : Structure L M] [Structure.Eq L M]


-- @@ L437-439 expanded
@[simp]
lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (existsUnique φ) ↔ ∃! x, Eval s (vecCons x e) ε φ := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons', ExistsUnique]


-- @@ L441-441 verbatim
end Semiformula


-- @@ L443-443 verbatim
namespace BinderNotation


-- @@ L445-445 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L447-448 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃! " firstOrderFormula:0 : firstOrderFormula

-- @@ L449-450 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃! " ident ", " firstOrderFormula:0 : firstOrderFormula


-- @@ L452-460 expanded
macro_rules
  | `(existsUnique foFormula[var1$binders* | $fbinders* | $φ:firstOrderFormula]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(existsUnique foFormula[$binders'* | $fbinders* | $φ])
  | `(existsUnique foFormula[$x$binders* | $fbinders* | $φ]) => do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(existsUnique foFormula[$binders'* | $fbinders* | $φ])


-- @@ L462-462 verbatim
end BinderNotation


-- @@ L464-464 verbatim
end FirstOrder


-- @@ L466-466 verbatim
end LO
