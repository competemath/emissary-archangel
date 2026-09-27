/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Definability.Boldface
import LeanPool.Incompleteness.Arithmetization.Basic.PeanoMinus
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Corollaries
import Mathlib.Algebra.Order.Sub.Basic


-- @@ L14-14 verbatim
/-! # Ind -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace FirstOrder

-- @@ L21-21 verbatim
namespace Arith


-- @@ L23-23 verbatim
open FirstOrder.Theory


-- @@ L25-25 expanded
variable {C C' : Semiformula oRing ℕ 1 → Prop}


-- @@ L27-28 expanded
lemma mem_indScheme_of_mem {φ : Semiformula oRing ℕ 1} (hp : C φ) : succInd φ ∈ indScheme oRing C :=
  by exact ⟨φ, hp, rfl⟩


-- @@ L30-31 expanded
lemma mem_iOpen_of_qfree {φ : Semiformula oRing ℕ 1} (hp : φ.Open) :
    succInd φ ∈ indScheme oRing Semiformula.Open := by exact ⟨φ, hp, rfl⟩


-- @@ L33-36 expanded
lemma indScheme_subset (h : ∀ {φ : Semiformula oRing ℕ 1}, C φ → C' φ) :
    indScheme oRing C ⊆ indScheme oRing C' :=
  by
  rintro _ ⟨φ, hp, rfl⟩
  exact ⟨φ, h hp, rfl⟩


-- @@ L38-39 expanded
lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : iSigma s₁ ⊆ iSigma s₂ :=
  Set.union_subset_union_right _ (indScheme_subset (fun H ↦ H.mono h))


-- @@ L41-41 verbatim
end Arith

-- @@ L42-42 verbatim
end FirstOrder

-- @@ L43-43 verbatim
end LO


-- @@ L45-45 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L47-47 verbatim
namespace LO

-- @@ L48-48 verbatim
namespace Arith


-- @@ L50-50 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L52-52 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L54-54 verbatim
section «lp_section_1»


-- @@ L56-56 verbatim
section «lp_section_2»


-- @@ L58-58 expanded
variable {C : Semiformula oRing ℕ 1 → Prop} [ModelsTheory V (Theory.indScheme oRing C)]


-- @@ L60-72 expanded
private lemma induction_eval {φ : Semiformula oRing ℕ 1} (hp : C φ) (v) :
    Semiformula.Evalm V ![0] v φ →
      (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
        ∀ x, Semiformula.Evalm V ![x] v φ :=
  by
  have : Models V (succInd φ) :=
    ModelsTheory.models (T := Theory.indScheme _ C) V (by simpa using mem_indScheme_of_mem hp)
  simp only [succInd, Nat.reduceAdd, Fin.isValue, models_iff, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_substs, Matrix.cons_val_fin_one, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, Matrix.constant_eq_singleton,
    Semiformula.eval_all, Nat.succ_eq_add_one, Semiterm.val_bvar, Semiterm.val_operator₂,
    ORingStruc.one_eq_one, Structure.Add.add, LogicalConnective.Prop.arrow_eq] at this
  exact this v


-- @@ L74-78 expanded
@[elab_as_elim]
lemma induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : Semiformula oRing ℕ 1, C φ ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] e φ) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by rcases hP with ⟨e, φ, Cp, hp⟩;
  simpa [← hp] using induction_eval (V := V) Cp e


-- @@ L80-80 verbatim
end «lp_section_2»


-- @@ L82-82 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L84-84 verbatim
section «lp_section_3»


-- @@ L86-86 expanded
variable (Γ : Polarity) (m : ℕ) [ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy Γ m))]


-- @@ L88-101 expanded
lemma induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P) (zero : P 0)
    (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy Γ m)
    (by
      rcases hP with ⟨φ, hp⟩
      have : Inhabited V := Classical.inhabited_of_nonempty'
      exact
        ⟨φ.val.fvarEnumInv, app (Rew.rewriteMap φ.val.fvarEnum) φ.val, by simp [],
          by
          intro x; simp [Semiformula.eval_rewriteMap]
          have :
            (Semiformula.Evalm V ![x] fun x ↦ φ.val.fvarEnumInv (φ.val.fvarEnum x)) φ.val ↔
              (Semiformula.Evalm V ![x] id) φ.val :=
            Semiformula.eval_iff_of_funEqOn _
              (by
                intro x hx
                simp [Semiformula.fvarEnumInv_fvarEnum (Semiformula.mem_fvarList_iff_fvar?.mpr hx)])
          simp [this, hp.df.iff]⟩)
    zero succ


-- @@ L103-118 verbatim
lemma order_induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using induction_h
  · exact Γ
  · exact m
  · suffices Γ-[m].BoldfacePred fun x => ∀ y < x, P y by exact this
    exact HierarchySymbol.Boldface.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => exact inferInstance


-- @@ L120-144 expanded
private lemma neg_induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P) (nzero : ¬P 0)
    (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x :=
  by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using induction_h
    · exact Γ
    · exact m
    · suffices Γ-[m].BoldfacePred fun x => x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Boldface.imp
      ·
        apply
          HierarchySymbol.Boldface.bcomp₂
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
      ·
        apply
          HierarchySymbol.Boldface.bcomp₁
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
    case zero => intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact
        (not_imp_not.mp <| nsucc (a - (x + 1)))
          (by
            rw [← sub_sub, sub_add_self_of_le]
            · exact this
            · exact le_tsub_of_add_le_left hx)
    case inst => exact inferInstance
  have : P 0 := by simpa using this a (by rfl)
  contradiction


-- @@ L146-163 expanded
lemma models_indScheme_alt : ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy Γ.alt m)) :=
  by
  simp only [Theory.indScheme, Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp]
  rintro _ φ hp rfl
  simp only [succInd, Nat.reduceAdd, Fin.isValue, models_iff, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_substs, Matrix.cons_val_fin_one, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, Matrix.constant_eq_singleton,
    Semiformula.eval_all, Nat.succ_eq_add_one, Semiterm.val_bvar, Semiterm.val_operator₂,
    ORingStruc.one_eq_one, Structure.Add.add, LogicalConnective.Prop.arrow_eq]
  intro v H0 Hsucc x
  have :
    Semiformula.Evalm V ![0] v φ →
      (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
        ∀ x, Semiformula.Evalm V ![x] v φ :=
    by
    simpa using
      neg_induction_h Γ m (P := fun x ↦ ¬Semiformula.Evalm V ![x] v φ)
        (.mkPolarity (Tilde.tilde (app (Rew.rewriteMap v) φ)) (by simpa using hp)
          (by intro x; simp [← Matrix.constant_eq_singleton', Semiformula.eval_rewriteMap]))
  exact this H0 Hsucc x


-- @@ L165-165 expanded
instance : ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy Γ.alt m)) :=
  models_indScheme_alt Γ m


-- @@ L167-189 expanded
lemma least_number_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using induction_h
    · exact Γ.alt
    · exact m
    · suffices Γ.alt-[m].BoldfacePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply
        HierarchySymbol.Boldface.ball_blt
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
      apply HierarchySymbol.Boldface.not
      apply
        HierarchySymbol.Boldface.bcomp₁ (hP := by simpa using hP)
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => exact inferInstance
  exact this (x + 1) x (by simp) h


-- @@ L191-191 verbatim
end «lp_section_3»


-- @@ L193-193 verbatim
section «lp_section_4»


-- @@ L195-195 expanded
variable (Γ : SigmaPiDelta) (m : ℕ)
  [ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy SigmaSymbol.sigma m))]


-- @@ L197-204 expanded
lemma induction_hh {P : V → Prop} (hP : Γ-[m].BoldfacePred P) (zero : P 0)
    (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | SigmaSymbol.sigma => induction_h SigmaSymbol.sigma m hP zero succ
  | PiSymbol.pi =>
    haveI : ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy PiSymbol.pi m)) :=
      models_indScheme_alt SigmaSymbol.sigma m
    induction_h PiSymbol.pi m hP zero succ
  | DeltaSymbol.delta => induction_h SigmaSymbol.sigma m hP.of_delta zero succ


-- @@ L206-213 expanded
lemma order_induction_hh {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | SigmaSymbol.sigma => order_induction_h SigmaSymbol.sigma m hP ind
  | PiSymbol.pi =>
    haveI : ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy PiSymbol.pi m)) :=
      models_indScheme_alt SigmaSymbol.sigma m
    order_induction_h PiSymbol.pi m hP ind
  | DeltaSymbol.delta => order_induction_h SigmaSymbol.sigma m hP.of_delta ind


-- @@ L215-222 expanded
lemma least_number_hh {P : V → Prop} (hP : Γ-[m].BoldfacePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | SigmaSymbol.sigma => least_number_h SigmaSymbol.sigma m hP h
  | PiSymbol.pi =>
    haveI : ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy PiSymbol.pi m)) :=
      models_indScheme_alt SigmaSymbol.sigma m
    least_number_h PiSymbol.pi m hP h
  | DeltaSymbol.delta => least_number_h SigmaSymbol.sigma m hP.of_delta h


-- @@ L224-224 verbatim
end «lp_section_4»


-- @@ L226-230 expanded
instance [ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy SigmaSymbol.sigma m))] :
    ModelsTheory V (Theory.indScheme oRing (Arith.Hierarchy Γ m)) :=
  by
  rcases Γ
  · exact inferInstance
  · exact models_indScheme_alt SigmaSymbol.sigma m


-- @@ L232-232 verbatim
end «lp_section_1»


-- @@ L234-237 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma mod_IOpen_of_mod_indH (Γ n) [ModelsTheory V ((indH Γ) n)] : ModelsTheory V iOpen :=
  ModelsTheory.of_ss (U := (indH Γ) n) inferInstance
    (Set.union_subset_union_right _ (indScheme_subset Hierarchy.of_open))


-- @@ L239-242 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [ModelsTheory V (Theory.iSigma n₂)] :
    ModelsTheory V (Theory.iSigma n₁) :=
  ModelsTheory.of_ss inferInstance (iSigma_subset_mono h)


-- @@ L244-246 expanded
instance [ModelsTheory V iOpen] : ModelsTheory V PeanoMinus :=
  ModelsTheory.of_add_left V PeanoMinus (Theory.indScheme _ Semiformula.Open)


-- @@ L248-248 expanded
instance [ModelsTheory V (iSigma 0)] : ModelsTheory V iOpen :=
  mod_IOpen_of_mod_indH SigmaSymbol.sigma 0


-- @@ L250-250 expanded
instance [ModelsTheory V (iSigma 1)] : ModelsTheory V (iSigma 0) :=
  mod_ISigma_of_le (show 0 ≤ 1 from by simp)


-- @@ L252-254 expanded
instance [ModelsTheory V (Theory.iSigma n)] : ModelsTheory V (Theory.iPi n) :=
  haveI : ModelsTheory V PeanoMinus := models_PeanoMinus_of_models_indH SigmaSymbol.sigma n
  inferInstance


-- @@ L256-258 expanded
instance [ModelsTheory V (Theory.iPi n)] : ModelsTheory V (Theory.iSigma n) :=
  haveI : ModelsTheory V PeanoMinus := Arith.models_PeanoMinus_of_models_indH PiSymbol.pi n
  by simp [*]; simpa [Theory.iPi] using models_indScheme_alt (V := V) PiSymbol.pi n


-- @@ L260-261 expanded
lemma models_ISigma_iff_models_IPi {n} : ModelsTheory V (iSigma n) ↔ ModelsTheory V (iPi n) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L263-266 expanded
instance [ModelsTheory V (Theory.iSigma n)] : ModelsTheory V (Theory.indH Γ n) :=
  match Γ with
  | SigmaSymbol.sigma => inferInstance
  | PiSymbol.pi => inferInstance


-- @@ L268-270 expanded
@[elab_as_elim]
lemma induction_sigma0 [ModelsTheory V (iSigma 0)] {P : V → Prop} (hP : Sg0.BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction_h SigmaSymbol.sigma 0 hP zero succ


-- @@ L272-274 expanded
@[elab_as_elim]
lemma induction_sigma1 [ModelsTheory V (iSigma 1)] {P : V → Prop} (hP : BoldfacePred Sg1 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction_h SigmaSymbol.sigma 1 hP zero succ


-- @@ L276-278 expanded
@[elab_as_elim]
lemma induction_pi1 [ModelsTheory V (iSigma 1)] {P : V → Prop} (hP : BoldfacePred Pg1 P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction_h PiSymbol.pi 1 hP zero succ


-- @@ L280-283 expanded
@[elab_as_elim]
lemma order_induction_sigma0 [ModelsTheory V (iSigma 0)] {P : V → Prop} (hP : BoldfacePred Sg0 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h SigmaSymbol.sigma 0 hP ind


-- @@ L285-288 expanded
@[elab_as_elim]
lemma order_induction_sigma1 [ModelsTheory V (iSigma 1)] {P : V → Prop} (hP : BoldfacePred Sg1 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h SigmaSymbol.sigma 1 hP ind


-- @@ L290-293 expanded
@[elab_as_elim]
lemma order_induction_pi1 [ModelsTheory V (iSigma 1)] {P : V → Prop} (hP : BoldfacePred Pg1 P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h PiSymbol.pi 1 hP ind


-- @@ L295-297 expanded
lemma least_number_sigma0 [ModelsTheory V (iSigma 0)] {P : V → Prop} (hP : BoldfacePred Sg0 P) {x}
    (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  least_number_h SigmaSymbol.sigma 0 hP h


-- @@ L299-301 expanded
@[elab_as_elim]
lemma induction_h_sigma1 [ModelsTheory V (iSigma 1)] (Γ) {P : V → Prop} (hP : BoldfacePred Γ-[1] P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction_hh Γ 1 hP zero succ


-- @@ L303-305 expanded
@[elab_as_elim]
lemma order_induction_h_sigma1 [ModelsTheory V (iSigma 1)] (Γ) {P : V → Prop}
    (hP : BoldfacePred Γ-[1] P) (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_hh Γ 1 hP ind


-- @@ L307-307 verbatim
end Arith

-- @@ L308-308 verbatim
end LO


-- @@ L310-310 verbatim
end «lp_nc_section_1»
