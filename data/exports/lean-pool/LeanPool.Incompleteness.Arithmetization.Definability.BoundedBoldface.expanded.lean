/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Definability.Boldface
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Algebra.Order.Sub.Basic


-- @@ L12-12 verbatim
/-! # BoundedBoldface -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace FirstOrder

-- @@ L19-19 verbatim
namespace Arith


-- @@ L21-21 verbatim
open LO.Arith


-- @@ L23-23 verbatim
variable {ξ : Type*} {n : ℕ}


-- @@ L25-25 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L27-27 verbatim
variable {ℌ : HierarchySymbol} {Γ Γ' : SigmaPiDelta}


-- @@ L29-29 verbatim
variable (ℌ)


-- @@ L31-33 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Bounded (f : (Fin k → V) → V) : Prop where
  bounded : ∃ t : Semiterm oRing V k, ∀ v : Fin k → V, f v ≤ t.valm V v id


-- @@ L35-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Bounded₁ (f : V → V) : Prop := Bounded (k := 1) (fun v ↦ f (v 0))


-- @@ L38-39 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Bounded₂ (f : V → V → V) : Prop := Bounded (k := 2) (fun v ↦ f (v 0) (v 1))


-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Bounded₃ (f : V → V → V → V) : Prop := Bounded (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))


-- @@ L44-46 verbatim
instance (f : (Fin k → V) → V) [h : Bounded f] : Bounded f := by
  rcases h with ⟨t, ht⟩
  exact ⟨Semiterm.lMap Language.oringEmb t, by simpa⟩


-- @@ L48-48 verbatim
variable {ℌ}


-- @@ L50-50 verbatim
namespace Bounded


-- @@ L52-54 expanded
@[simp]
lemma var [ModelsTheory V PeanoMinus] {k} (i : Fin k) : Bounded fun v : Fin k → V ↦ v i :=
  ⟨#i, by intro _; simp⟩


-- @@ L56-58 expanded
@[simp]
lemma const [ModelsTheory V PeanoMinus] {k} (c : V) : Bounded (fun _ : Fin k → V ↦ c) :=
  ⟨&c, by intro _; simp⟩


-- @@ L60-62 expanded
@[simp 1100]
lemma term_retraction [ModelsTheory V PeanoMinus] (t : Semiterm oRing V n) (e : Fin n → Fin k) :
    Bounded fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
  ⟨Rew.substs (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs]⟩


-- @@ L64-66 expanded
lemma term [ModelsTheory V PeanoMinus] (t : Semiterm oRing V k) :
    Bounded fun v : Fin k → V => Semiterm.valm V v id t :=
  ⟨t, by intro _; simp⟩


-- @@ L68-71 verbatim
lemma retraction {f : (Fin k → V) → V} (hf : Bounded f) (e : Fin k → Fin n) :
    Bounded fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.substs (fun x ↦ #(e x)) t, by intro; simp [Semiterm.val_substs, ht]⟩


-- @@ L73-83 expanded
lemma comp [ModelsTheory V PeanoMinus] {k} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V}
    (hf : Bounded f) (hg : ∀ i, Bounded (g i)) : Bounded (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact
      ⟨Rew.substs tg tf, by
        intro v; simp only [Semiterm.val_substs]
        exact
          le_trans (htf (g · v)) (Structure.Monotone.term_monotone tf (fun i ↦ htg i v) (by simp))⟩


-- @@ L85-85 verbatim
end Bounded


-- @@ L87-91 expanded
lemma _root_.LO.FirstOrder.Arith.Bounded₁.comp [ModelsTheory V PeanoMinus] {f : V → V} {k}
    {g : (Fin k → V) → V} (hf : Bounded₁ f) (hg : Bounded g) : Bounded (fun v ↦ f (g v)) :=
  Bounded.comp hf (l := 1) (fun _ ↦ hg)


-- @@ L93-97 expanded
lemma _root_.LO.FirstOrder.Arith.Bounded₂.comp [ModelsTheory V PeanoMinus] {f : V → V → V} {k}
    {g₁ g₂ : (Fin k → V) → V} (hf : Bounded₂ f) (hg₁ : Bounded g₁) (hg₂ : Bounded g₂) :
    Bounded (fun v ↦ f (g₁ v) (g₂ v)) :=
  Bounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])


-- @@ L99-109 expanded
lemma _root_.LO.FirstOrder.Arith.Bounded₃.comp [ModelsTheory V PeanoMinus] {f : V → V → V → V} {k}
    {g₁ g₂ g₃ : (Fin k → V) → V} (hf : Bounded₃ f) (hg₁ : Bounded g₁) (hg₂ : Bounded g₂)
    (hg₃ : Bounded g₃) : Bounded (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) :=
  Bounded.comp hf (g := ![g₁, g₂, g₃])
    (fun i ↦ by
      cases i using Fin.cases with
      | zero => simp [*]
      | succ i =>
        cases i using Fin.cases with
        | zero => simp [*]
        | succ i => simp [*])


-- @@ L111-111 verbatim
namespace Bounded₂


-- @@ L113-113 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L115-116 expanded
instance add : Bounded₂ ((· + ·) : V → V → V) where
  bounded := ⟨Semiterm.Operator.Add.add.operator ![#0, #1], by intro _; simp⟩


-- @@ L118-119 expanded
instance mul : Bounded₂ ((· * ·) : V → V → V) where
  bounded := ⟨Semiterm.Operator.Mul.mul.operator ![#0, #1], by intro _; simp⟩


-- @@ L121-122 expanded
instance hAdd : Bounded₂ (HAdd.hAdd : V → V → V) where
  bounded := ⟨Semiterm.Operator.Add.add.operator ![#0, #1], by intro _; simp⟩


-- @@ L124-125 expanded
instance hMul : Bounded₂ (HMul.hMul : V → V → V) where
  bounded := ⟨Semiterm.Operator.Mul.mul.operator ![#0, #1], by intro _; simp⟩


-- @@ L127-127 verbatim
end Bounded₂


-- @@ L129-130 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def BoldfaceBoundedFunction {k} (f : (Fin k → V) → V) := Bounded f ∧ Sg0.BoldfaceFunction f


-- @@ L132-135 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceBoundedFunction₁ (f : V → V) :
    Prop :=
  BoldfaceBoundedFunction (k := 1) (fun v => f (v 0))


-- @@ L137-140 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceBoundedFunction₂ (f : V → V → V) :
    Prop :=
  BoldfaceBoundedFunction (k := 2) (fun v => f (v 0) (v 1))


-- @@ L142-145 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev BoldfaceBoundedFunction₃ (f : V → V → V → V) :
    Prop :=
  BoldfaceBoundedFunction (k := 3) (fun v => f (v 0) (v 1) (v 2))


-- @@ L147-150 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.bounded {f : (Fin k → V) → V} (h :
    BoldfaceBoundedFunction f) :
    Bounded f :=
  h.1


-- @@ L152-155 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.bounded {f : V → V} (h :
    BoldfaceBoundedFunction₁ f) :
    Bounded₁ f :=
  h.1


-- @@ L157-160 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₂.bounded {f : V → V → V} (h :
    BoldfaceBoundedFunction₂ f) :
    Bounded₂ f :=
  h.1


-- @@ L162-165 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₃.bounded {f : V → V → V → V} (h :
    BoldfaceBoundedFunction₃ f) :
    Bounded₃ f :=
  h.1


-- @@ L167-170 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.definable {f : (Fin k → V) → V} (h :
    BoldfaceBoundedFunction f) :
    ℌ.BoldfaceFunction f :=
  .of_zero h.2


-- @@ L172-175 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.definable {f : V → V} (h :
    BoldfaceBoundedFunction₁ f) :
    ℌ.BoldfaceFunction₁ f :=
  .of_zero h.2


-- @@ L177-180 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₂.definable {f : V → V → V} (h :
    BoldfaceBoundedFunction₂ f) :
    ℌ.BoldfaceFunction₂ f :=
  .of_zero h.2


-- @@ L182-185 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₃.definable {f : V → V → V → V} (h :
    BoldfaceBoundedFunction₃ f) :
    ℌ.BoldfaceFunction₃ f :=
  .of_zero h.2


-- @@ L187-187 verbatim
namespace BoldfaceBoundedFunction


-- @@ L189-191 verbatim
lemma of_polybounded_of_definable (f : (Fin k → V) → V) [hb : Bounded f] [hf :
    Sg0.BoldfaceFunction f] :
    BoldfaceBoundedFunction f := ⟨hb, hf⟩


-- @@ L193-195 verbatim
@[simp] lemma of_polybounded_of_definable₁ (f : V → V) [hb : Bounded₁ f] [hf :
    Sg0.BoldfaceFunction₁ f] :
    BoldfaceBoundedFunction₁ f := ⟨hb, hf⟩


-- @@ L197-199 verbatim
@[simp] lemma of_polybounded_of_definable₂ (f : V → V → V) [hb : Bounded₂ f] [hf :
    Sg0.BoldfaceFunction₂ f] :
    BoldfaceBoundedFunction₂ f := ⟨hb, hf⟩


-- @@ L201-203 verbatim
@[simp] lemma of_polybounded_of_definable₃ (f : V → V → V → V) [hb : Bounded₃ f] [hf :
    Sg0.BoldfaceFunction₃ f] :
    BoldfaceBoundedFunction₃ f := ⟨hb, hf⟩


-- @@ L205-207 verbatim
lemma retraction {f : (Fin k → V) → V} (hf : BoldfaceBoundedFunction f) (e : Fin k → Fin n) :
    BoldfaceBoundedFunction fun v ↦ f (fun i ↦ v (e i)) :=
      ⟨hf.bounded.retraction e, hf.definable.retraction e⟩


-- @@ L209-209 verbatim
end BoldfaceBoundedFunction


-- @@ L211-211 verbatim
namespace HierarchySymbol

-- @@ L212-212 verbatim
namespace Boldface


-- @@ L214-214 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L216-216 verbatim
variable {P Q : (Fin k → V) → Prop}


-- @@ L218-233 expanded
lemma ball_blt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V} (hf : BoldfaceBoundedFunction f)
    (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) : ℌ.Boldface fun v ↦ ∀ x < f v, P v x :=
  by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have :
    ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∀ y < x, P v y)
      (HierarchySymbol.Semiformula.bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
        (Wedge.wedge f_graph
          (HierarchySymbol.Semiformula.ball (#0)
            (HierarchySymbol.Semiformula.rew (Rew.substs (vecCons #0 fun i ↦ #i.succ.succ)) φ)))) :=
    by
    simpa [← le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and ((hp.retraction (vecCons 0 (·.succ.succ))).ball #0)).bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
  exact
    .of_iff ⟨_, this⟩
      (fun v ↦
        ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
          rintro ⟨y, hy, rfl, h⟩
          exact h⟩)


-- @@ L236-251 expanded
lemma bex_blt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V} (hf : BoldfaceBoundedFunction f)
    (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) : ℌ.Boldface fun v ↦ ∃ x < f v, P v x :=
  by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have :
    ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∃ y < x, P v y)
      (HierarchySymbol.Semiformula.bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
        (Wedge.wedge f_graph
          (HierarchySymbol.Semiformula.bex (#0)
            (HierarchySymbol.Semiformula.rew (Rew.substs (vecCons #0 fun i => #i.succ.succ))
              φ)))) :=
    by
    simpa [← le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and ((hp.retraction (vecCons 0 (·.succ.succ))).bex #0)).bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
  exact
    .of_iff ⟨_, this⟩
      (fun v ↦
        ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
          rintro ⟨y, hy, rfl, h⟩
          exact h⟩)


-- @@ L253-268 expanded
lemma ball_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V} (hf : BoldfaceBoundedFunction f)
    (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) : ℌ.Boldface fun v ↦ ∀ x ≤ f v, P v x :=
  by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have :
    ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∀ y ≤ x, P v y)
      (HierarchySymbol.Semiformula.bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
        (Wedge.wedge f_graph
          (HierarchySymbol.Semiformula.ball
            (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1])
            (HierarchySymbol.Semiformula.rew (Rew.substs (vecCons #0 fun i => #i.succ.succ))
              φ)))) :=
    by
    simpa [← le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and
            ((hp.retraction (vecCons 0 (·.succ.succ))).ball
              (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]))).bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
  exact
    .of_iff ⟨_, this⟩
      (fun v ↦
        ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
          rintro ⟨y, hy, rfl, h⟩
          exact h⟩)


-- @@ L270-285 expanded
lemma bex_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V} (hf : BoldfaceBoundedFunction f)
    (h : ℌ.Boldface fun w ↦ P (w ·.succ) (w 0)) : ℌ.Boldface fun v ↦ ∃ x ≤ f v, P v x :=
  by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨φ, hp⟩
  have :
    ℌ.DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm V v id bf, x = f v ∧ ∃ y ≤ x, P v y)
      (HierarchySymbol.Semiformula.bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
        (Wedge.wedge f_graph
          (HierarchySymbol.Semiformula.bex
            (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1])
            (HierarchySymbol.Semiformula.rew (Rew.substs (vecCons #0 fun i => #i.succ.succ))
              φ)))) :=
    by
    simpa [← le_iff_lt_succ, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      (hf_graph.and
            ((hp.retraction (vecCons 0 (·.succ.succ))).bex
              (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]))).bex
        (Semiterm.Operator.Add.add.operator ![bf, Semiterm.numeral 1])
  exact
    .of_iff ⟨_, this⟩
      (fun v ↦
        ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by
          rintro ⟨y, hy, rfl, h⟩
          exact h⟩)


-- @@ L287-289 verbatim
lemma ball_blt_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∀ x < f v, P v x := ball_blt hf h


-- @@ L291-293 verbatim
lemma bex_blt_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∃ x < f v, P v x := bex_blt hf h


-- @@ L295-297 verbatim
lemma ball_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∀ x ≤ f v, P v x := ball_ble hf h


-- @@ L299-301 verbatim
lemma bex_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : BoldfaceBoundedFunction f) (h : Γ-[0].Boldface fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Boldface fun v ↦ ∃ x ≤ f v, P v x := bex_ble hf h


-- @@ L303-326 expanded
lemma bex_vec_le_boldfaceBoundedFunction {k} {φ : Fin l → (Fin k → V) → V}
    {P : (Fin k → V) → (Fin l → V) → Prop} (pp : ∀ i, BoldfaceBoundedFunction (φ i))
    (hP :
      ℌ.Boldface fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    ℌ.Boldface fun v ↦ ∃ w ≤ (φ · v), P v w :=
  by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq (α := V)] using hP
  case succ l ih =>
    simp only [exists_le_vec_iff_exists_le_exists_vec]
    apply bex_ble (pp 0)
    apply ih
    · intro i; apply BoldfaceBoundedFunction.retraction (pp i.succ)
    · let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
        Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l)
          (vecCons (Fin.castAdd l 0) fun j ↦ j.natAdd (k + 1))
      exact
        of_iff (retraction hP g) <| by
          intro v; simp only [g]
          apply iff_of_eq; congr
          · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · ext i
            cases i using Fin.cases with
            | zero => simp only [Matrix.vecCons_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
            | succ i => simp only [Matrix.vecCons_succ]; congr 1; ext;
              simp [Matrix.vecAppend_eq_ite]


-- @@ L328-342 expanded
lemma substitution_boldfaceBoundedFunction {f : Fin k → (Fin l → V) → V} (hP : ℌ.Boldface P)
    (hf : ∀ i, BoldfaceBoundedFunction (f i)) : ℌ.Boldface fun z ↦ P (f · z) :=
  by
  have : ℌ.Boldface fun v ↦ ∃ w ≤ (f · v), (∀ i, w i = f i v) ∧ P w :=
    by
    apply bex_vec_le_boldfaceBoundedFunction hf
    apply and
    · apply conj; intro i
      simpa using retraction (.of_zero (hf i).2) (vecCons (i.natAdd l) (Fin.castAdd k))
    · apply retraction hP
  apply
    of_iff this <| by
      intro v; constructor
      · intro h; exact ⟨(f · v), by intro i; simp, by simp, h⟩
      · rintro ⟨w, hw, e, h⟩
        rcases funext e
        exact h


-- @@ L344-344 verbatim
end Boldface

-- @@ L345-345 verbatim
end HierarchySymbol


-- @@ L347-347 verbatim
namespace BoldfaceBoundedFunction


-- @@ L349-352 verbatim
lemma of_iff {f g : (Fin k → V) → V} (H : BoldfaceBoundedFunction f) (h : ∀ v, f v = g v) :
    BoldfaceBoundedFunction g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H


-- @@ L354-354 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L356-358 verbatim
@[simp] lemma var {k} (i : Fin k) : BoldfaceBoundedFunction (fun v :
    Fin k → V ↦ v i) :=
  ⟨by simp, by simp⟩


-- @@ L360-362 verbatim
@[simp] lemma const {k} (c : V) : BoldfaceBoundedFunction (fun _ :
    Fin k → V ↦ c) :=
  ⟨by simp, by simp⟩


-- @@ L364-366 expanded
@[simp 1100]
lemma term_retraction (t : Semiterm oRing V n) (e : Fin n → Fin k) :
    BoldfaceBoundedFunction fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
  ⟨by simp, by simp⟩


-- @@ L368-369 expanded
lemma term (t : Semiterm oRing V k) :
    BoldfaceBoundedFunction fun v : Fin k → V ↦ Semiterm.valm V v id t :=
  ⟨by simp, by simp⟩


-- @@ L371-371 verbatim
end BoldfaceBoundedFunction


-- @@ L373-373 verbatim
namespace HierarchySymbol

-- @@ L374-374 verbatim
namespace Boldface


-- @@ L376-376 verbatim
open BoldfaceBoundedFunction


-- @@ L378-378 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L380-383 verbatim
lemma bcomp₁ {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : ℌ.BoldfacePred P] (hf :
    BoldfaceBoundedFunction f) :
    ℌ.Boldface fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction (f := ![f]) hP (by simp [*])


-- @@ L385-389 verbatim
lemma bcomp₂ {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : ℌ.BoldfaceRel R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    ℌ.Boldface fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L391-396 verbatim
lemma bcomp₃ {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR : ℌ.BoldfaceRel₃ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    ℌ.Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L398-403 verbatim
lemma bcomp₄ {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR : ℌ.BoldfaceRel₄ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) (hf₄ : BoldfaceBoundedFunction f₄) :
    ℌ.Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃, f₄]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L405-408 verbatim
lemma bcomp₁_zero {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : Γ-[0].BoldfacePred P] (hf :
    BoldfaceBoundedFunction f) :
    Γ-[0].Boldface fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction (f := ![f]) hP (by simp [*])


-- @@ L410-414 verbatim
lemma bcomp₂_zero {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : Γ-[0].BoldfaceRel R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    Γ-[0].Boldface fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L416-422 verbatim
lemma bcomp₃_zero {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR :
    Γ-[0].BoldfaceRel₃ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    Γ-[0].Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L424-430 verbatim
lemma bcomp₄_zero {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR :
    Γ-[0].BoldfaceRel₄ R]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) (hf₄ : BoldfaceBoundedFunction f₄) :
    Γ-[0].Boldface fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction (f :=
    ![f₁, f₂, f₃, f₄]) hR (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L432-432 verbatim
end Boldface

-- @@ L433-433 verbatim
end HierarchySymbol


-- @@ L435-435 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L437-447 expanded
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction.bcomp {k} {F : (Fin l → V) → V}
    {f : Fin l → (Fin k → V) → V} (hF : ℌ.BoldfaceFunction F)
    (hf : ∀ i, BoldfaceBoundedFunction (f i)) : ℌ.BoldfaceFunction (fun v ↦ F (f · v)) := by
  simpa using
    HierarchySymbol.Boldface.substitution_boldfaceBoundedFunction (f :=
        vecCons (· 0) fun i w ↦ f i (w ·.succ)) hF <|
      by
      intro i
      cases i using Fin.cases with
      | zero => simp
      | succ i => simpa using BoldfaceBoundedFunction.retraction (hf i) Fin.succ


-- @@ L449-453 verbatim
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₁.bcomp {k} {F : V → V} {f :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₁ F) (hf : BoldfaceBoundedFunction f) :
    ℌ.BoldfaceFunction (fun v ↦ F (f v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f := ![f]) hF (by simp [*])


-- @@ L455-462 verbatim
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₂.bcomp {k} {F :
    V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₂ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    ℌ.BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f :=
    ![f₁, f₂]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L464-472 verbatim
lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.bcomp {k} {F :
    V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₃ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    ℌ.BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f :=
    ![f₁, f₂, f₃]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])


-- @@ L474-476 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : BoldfaceBoundedFunction₁ F) (hf : BoldfaceBoundedFunction f) :
    BoldfaceBoundedFunction (fun v ↦ F (f v)) := ⟨hF.bounded.comp hf.bounded, hF.definable.bcomp hf⟩


-- @@ L478-483 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₂.comp {k} {F : V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    (hF : BoldfaceBoundedFunction₂ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
      ⟨hF.bounded.comp hf₁.bounded hf₂.bounded, hF.definable.bcomp hf₁ hf₂⟩


-- @@ L485-491 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₃.comp {k} {F : V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hF : BoldfaceBoundedFunction₃ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  ⟨hF.bounded.comp hf₁.bounded hf₂.bounded hf₃.bounded, hF.definable.bcomp hf₁ hf₂ hf₃⟩


-- @@ L493-495 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.comp₁ {k} {F : V → V} {f : (Fin k → V) → V}
    [hFb : Bounded₁ F] [hFd : Sg0.BoldfaceFunction₁ F] (hf : BoldfaceBoundedFunction f) :
    BoldfaceBoundedFunction (fun v ↦ F (f v)) := BoldfaceBoundedFunction₁.comp ⟨hFb, hFd⟩ hf


-- @@ L497-502 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.comp₂ {k} {F : V → V → V} {f₁ f₂ :
    (Fin k → V) → V}
    [hFb : Bounded₂ F] [hFd : Sg0.BoldfaceFunction₂ F]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
      BoldfaceBoundedFunction₂.comp ⟨hFb, hFd⟩ hf₁ hf₂


-- @@ L504-510 verbatim
lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction.comp₃ {k} {F : V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    [hFb : Bounded₃ F] [hFd : Sg0.BoldfaceFunction₃ F]
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    BoldfaceBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
      BoldfaceBoundedFunction₃.comp ⟨hFb, hFd⟩ hf₁ hf₂ hf₃


-- @@ L512-516 verbatim
section «lp_section_1»

-- Source:
-- https://github.com/leanprover-community/mathlib4/blob/
-- 77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26

-- @@ L517-517 verbatim
open Lean.Parser.Tactic (config)


-- @@ L519-519 verbatim
open HierarchySymbol


-- @@ L521-524 verbatim
attribute [aesop (rule_sets := [Definability]) norm]
  sq
  Arith.pow_three
  pow_four


-- @@ L526-532 verbatim
attribute [aesop 5 (rule_sets := [Definability]) safe]
  BoldfaceFunction.comp₁
  BoldfaceFunction.comp₂
  BoldfaceFunction.comp₃
  BoldfaceBoundedFunction.comp₁
  BoldfaceBoundedFunction.comp₂
  BoldfaceBoundedFunction.comp₃


-- @@ L534-543 verbatim
attribute [aesop 6 (rule_sets := [Definability]) safe]
  Boldface.comp₁
  Boldface.comp₂
  Boldface.comp₃
  Boldface.comp₄
  Boldface.const
  Boldface.bcomp₁_zero
  Boldface.bcomp₂_zero
  Boldface.bcomp₃_zero
  Boldface.bcomp₄_zero


-- @@ L545-553 verbatim
attribute [aesop 8 (rule_sets := [Definability]) safe]
  Boldface.ball_lt
  Boldface.ball_le
  Boldface.bex_lt
  Boldface.bex_le
  Boldface.ball_blt_zero
  Boldface.ball_ble_zero
  Boldface.bex_blt_zero
  Boldface.bex_ble_zero


-- @@ L555-558 verbatim
attribute [aesop 10 (rule_sets := [Definability]) safe]
  Boldface.not
  Boldface.imp
  Boldface.iff


-- @@ L560-564 verbatim
attribute [aesop 11 (rule_sets := [Definability]) safe]
  Boldface.and
  Boldface.or
  Boldface.all
  Boldface.ex


-- @@ L566-568 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)


-- @@ L570-573 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
macro (name := definabilityTactic) "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent
    `Definability):ident]))


-- @@ L575-578 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
macro (name := definabilityQuestionTactic) "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent
    `Definability):ident]))


-- @@ L580-580 expanded
example (c : V) : BoldfaceBoundedFunction₂ (fun x _y : V ↦ c + 2 * x ^ 2) := by
  aesop  (config := { terminal := true })  (rule_sets := [Definability])


-- @@ L582-586 expanded
example {ex : V → V} [Sg0.BoldfaceFunction₁ ex] (c : V) :
    Pg0.BoldfaceRel
      (fun x y : V ↦ ∃ z < x + c * y, (ex x = x ∧ x < y) ↔ ex x = z ∧ ex (x + 1) = 2 * z) :=
  by
  simp only [Function.Graph.iff_left ex]
  aesop?  (config := { terminal := true })  (rule_sets := [Definability])


-- @@ L588-589 expanded
example {ex : V → V} [h : Dlt1.BoldfaceFunction₁ ex] :
    Sg1.BoldfaceRel (fun x y : V ↦ ∃ z, x < y ↔ ex (ex x) = z) := by
  aesop?  (config := { terminal := true })  (rule_sets := [Definability])


-- @@ L591-592 expanded
example {ex : V → V} [h : Sg1.BoldfaceFunction₁ ex] :
    Sg1.BoldfaceRel (fun x y : V ↦ ∀ z < ex y, x < y ↔ ex (ex x) = z) := by
  aesop?  (config := { terminal := true })  (rule_sets := [Definability])


-- @@ L594-594 verbatim
end «lp_section_1»


-- @@ L596-596 verbatim
end Arith

-- @@ L597-597 verbatim
end FirstOrder

-- @@ L598-598 verbatim
end LO
