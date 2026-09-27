/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Theory
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Corollaries


-- @@ L13-13 verbatim
/-! # Model -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO


-- @@ L20-20 verbatim
namespace FirstOrder


-- @@ L22-22 verbatim
namespace Arith

-- @@ L23-23 verbatim
open Language


-- @@ L25-25 verbatim
section «lp_section_1»


-- @@ L27-27 verbatim
variable {L : Language} [L.ORing]


-- @@ L29-32 expanded
@[simp]
lemma oringEmb_operator_zero_val :
    Semiterm.Operator.Zero.zero.term.lMap (Language.oringEmb : oRing →ᵥ L) =
      Semiterm.Operator.Zero.zero.term :=
  by simp [Semiterm.Operator.Zero.term_eq, Semiterm.lMap_func, Matrix.empty_eq]


-- @@ L34-37 expanded
@[simp]
lemma oringEmb_operator_one_val :
    Semiterm.Operator.One.one.term.lMap (Language.oringEmb : oRing →ᵥ L) =
      Semiterm.Operator.One.one.term :=
  by simp [Semiterm.Operator.One.term_eq, Semiterm.lMap_func, Matrix.empty_eq]


-- @@ L39-42 expanded
@[simp]
lemma oringEmb_operator_add_val :
    Semiterm.Operator.Add.add.term.lMap (Language.oringEmb : oRing →ᵥ L) =
      Semiterm.Operator.Add.add.term :=
  by simp [Semiterm.Operator.Add.term_eq, Semiterm.lMap_func]


-- @@ L44-47 expanded
@[simp]
lemma oringEmb_operator_mul_val :
    Semiterm.Operator.Mul.mul.term.lMap (Language.oringEmb : oRing →ᵥ L) =
      Semiterm.Operator.Mul.mul.term :=
  by simp [Semiterm.Operator.Mul.term_eq, Semiterm.lMap_func]


-- @@ L49-52 expanded
@[simp]
lemma oringEmb_operator_eq_val :
    .lMap (Language.oringEmb : oRing →ᵥ L) Semiformula.Operator.Eq.eq.sentence =
      Semiformula.Operator.Eq.eq.sentence :=
  by simp [Semiformula.Operator.Eq.sentence_eq, Semiformula.lMap_rel]


-- @@ L54-57 expanded
@[simp]
lemma oringEmb_operator_lt_val :
    .lMap (Language.oringEmb : oRing →ᵥ L) Semiformula.Operator.LT.lt.sentence =
      Semiformula.Operator.LT.lt.sentence :=
  by simp [Semiformula.Operator.LT.sentence_eq, Semiformula.lMap_rel]


-- @@ L59-59 verbatim
end «lp_section_1»


-- @@ L61-61 verbatim
section «lp_section_2»


-- @@ L63-63 verbatim
section «lp_section_3»


-- @@ L65-65 verbatim
variable (M : Type*) [ORingStruc M]


-- @@ L67-77 expanded
instance standardModel : Structure oRing M
    where
  func := fun _ f =>
    match f with
    | ORing.Func.zero => fun _ => 0
    | ORing.Func.one => fun _ => 1
    | ORing.Func.add => fun v => v 0 + v 1
    | ORing.Func.mul => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1


-- @@ L79-81 expanded
instance : Structure.Eq oRing M :=
  ⟨by intro a b;
    simp [standardModel, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.eval_rel]⟩


-- @@ L83-83 expanded
instance : Structure.Zero oRing M :=
  ⟨rfl⟩


-- @@ L85-85 expanded
instance : Structure.One oRing M :=
  ⟨rfl⟩


-- @@ L87-87 expanded
instance : Structure.Add oRing M :=
  ⟨fun _ _ => rfl⟩


-- @@ L89-89 expanded
instance : Structure.Mul oRing M :=
  ⟨fun _ _ => rfl⟩


-- @@ L91-91 expanded
instance : Structure.Eq oRing M :=
  ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L93-93 expanded
instance : Structure.LT oRing M :=
  ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L95-95 expanded
instance : ORing oRing :=
  ORing.mk


-- @@ L97-110 expanded
lemma standardModel_unique' (s : Structure oRing M) (hZero : Structure.Zero oRing M)
    (hOne : Structure.One oRing M) (hAdd : Structure.Add oRing M) (hMul : Structure.Mul oRing M)
    (hEq : Structure.Eq oRing M) (hLT : Structure.LT oRing M) : s = standardModel M :=
  Structure.ext
    (funext₃ fun k f _ =>
      match k, f with
      | _, Language.Zero.zero => by simp [Matrix.empty_eq]
      | _, Language.One.one => by simp [Matrix.empty_eq]
      | _, Language.Add.add => by simp
      | _, Language.Mul.mul => by simp)
    (funext₃ fun k r _ =>
      match k, r with
      | _, Language.Eq.eq => by simp
      | _, Language.LT.lt => by simp)


-- @@ L112-116 expanded
lemma standardModel_unique (s : Structure oRing M) [hZero : Structure.Zero oRing M]
    [hOne : Structure.One oRing M] [hAdd : Structure.Add oRing M] [hMul : Structure.Mul oRing M]
    [hEq : Structure.Eq oRing M] [hLT : Structure.LT oRing M] : s = standardModel M :=
  standardModel_unique' M s hZero hOne hAdd hMul hEq hLT


-- @@ L118-120 verbatim
variable {L : Language} [L.ORing] [s : Structure L M]
  [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M] [Structure.Eq L
    M] [Structure.LT L M]


-- @@ L122-136 expanded
lemma standardModel_lMap_oringEmb_eq_standardModel :
    s.lMap (Language.oringEmb : oRing →ᵥ L) = standardModel M :=
  by
  apply standardModel_unique' M _
  ·
    exact
      @Structure.Zero.mk oRing M (s.lMap Language.oringEmb) _ _
        (by simpa [Semiterm.Operator.val, ← Semiterm.val_lMap] using Structure.Zero.zero)
  ·
    exact
      @Structure.One.mk oRing M (s.lMap Language.oringEmb) _ _
        (by simpa [Semiterm.Operator.val, ← Semiterm.val_lMap] using Structure.One.one)
  ·
    exact
      @Structure.Add.mk oRing M (s.lMap Language.oringEmb) _ _
        (fun a b ↦ by
          simpa [Semiterm.Operator.val, ← Semiterm.val_lMap] using Structure.Add.add a b)
  ·
    exact
      @Structure.Mul.mk oRing M (s.lMap Language.oringEmb) _ _
        (fun a b ↦ by
          simpa [Semiterm.Operator.val, ← Semiterm.val_lMap] using Structure.Mul.mul a b)
  ·
    exact
      @Structure.Eq.mk oRing M (s.lMap Language.oringEmb) _
        (fun a b ↦ by
          simpa [Semiformula.Operator.val, ← Semiformula.eval_lMap] using Structure.Eq.eq a b)
  ·
    exact
      @Structure.LT.mk oRing M (s.lMap Language.oringEmb) _ _
        (fun a b ↦ by
          simpa [Semiformula.Operator.val, ← Semiformula.eval_lMap] using Structure.LT.lt a b)


-- @@ L138-138 verbatim
variable {M} {e : Fin n → M} {ε : ξ → M}


-- @@ L140-142 expanded
@[simp]
lemma val_lMap_oringEmb {t : Semiterm oRing ξ n} :
    (t.lMap Language.oringEmb : Semiterm L ξ n).valm M e ε = t.valm M e ε := by
  simp [Semiterm.val_lMap, standardModel_lMap_oringEmb_eq_standardModel]


-- @@ L144-147 expanded
@[simp]
lemma eval_lMap_oringEmb {φ : Semiformula oRing ξ n} :
    Semiformula.Evalm M e ε (.lMap Language.oringEmb φ : Semiformula L ξ n) ↔
      Semiformula.Evalm M e ε φ :=
  by simp [Semiformula.eval_lMap, standardModel_lMap_oringEmb_eq_standardModel]


-- @@ L149-149 verbatim
end «lp_section_3»


-- @@ L151-151 verbatim
section «lp_section_4»


-- @@ L153-153 verbatim
variable {L : Language} [L.ORing]

-- @@ L154-156 verbatim
variable {M : Type*} [ORingStruc M] [s : Structure L M]
  [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M] [Structure.Eq L
    M] [Structure.LT L M]


-- @@ L158-165 expanded
@[simp]
lemma modelsTheory_lMap_oringEmb (T : Theory oRing) :
    ModelsTheory M (T.lMap oringEmb : Theory L) ↔ ModelsTheory M T :=
  by
  simp only [modelsTheory_iff]
  constructor
  · intro H φ hp f
    exact eval_lMap_oringEmb.mp <| @H (Semiformula.lMap oringEmb φ) (Set.mem_image_of_mem _ hp) f
  · simp only [Theory.lMap, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro H φ hp f; exact eval_lMap_oringEmb.mpr (H hp f)


-- @@ L167-168 expanded
instance [ModelsTheory M iOpen] : ModelsTheory M PeanoMinus :=
  ModelsTheory.of_add_left M PeanoMinus (Theory.indScheme _ Semiformula.Open)


-- @@ L170-171 expanded
instance [ModelsTheory M iOpen] : ModelsTheory M (Theory.indScheme oRing Semiformula.Open) :=
  ModelsTheory.of_add_right M PeanoMinus (Theory.indScheme _ Semiformula.Open)


-- @@ L173-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma models_PeanoMinus_of_models_indH (Γ n) [ModelsTheory M (Theory.indH Γ n)] :
    ModelsTheory M PeanoMinus :=
  ModelsTheory.of_add_left M PeanoMinus (Theory.indScheme _ (Arith.Hierarchy Γ n))


-- @@ L177-180 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma models_indScheme_of_models_indH (Γ n) [ModelsTheory M (Theory.indH Γ n)] :
    ModelsTheory M (Theory.indScheme oRing (Arith.Hierarchy Γ n)) :=
  ModelsTheory.of_add_right M PeanoMinus (Theory.indScheme _ (Arith.Hierarchy Γ n))


-- @@ L182-183 expanded
instance models_PeanoMinus_of_models_peano [ModelsTheory M peano] : ModelsTheory M PeanoMinus :=
  ModelsTheory.of_add_left M PeanoMinus (Theory.indScheme _ Set.univ)


-- @@ L185-185 verbatim
end «lp_section_4»


-- @@ L187-187 verbatim
end «lp_section_2»


-- @@ L189-189 verbatim
namespace Standard


-- @@ L191-191 verbatim
variable {ξ : Type v} (e : Fin n → ℕ) (ε : ξ → ℕ)


-- @@ L193-200 expanded
instance models_CobhamR0 : ModelsTheory ℕ CobhamR0 :=
  ⟨by
    intro σ h
    rcases h <;>
      try { simp [models_def]; done
      }
    case equal h =>
      have : ModelsTheory ℕ (eqAxiom : Theory oRing) := inferInstance
      simpa [models_def] using modelsTheory_iff.mp this h
    case Ω₃ h => simpa [models_def, ← le_iff_eq_or_lt] using h⟩


-- @@ L202-227 expanded
instance models_PeanoMinus : ModelsTheory ℕ PeanoMinus :=
  ⟨by
    intro σ h
    rcases h <;>
      simp only [models_def, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg, Semiformula.eval_operator₂, Semiformula.eval_ex,
        Semiterm.val_operator₂, Semiterm.val_fvar, Semiterm.val_const, Semiterm.val_bvar,
        Matrix.vecCons_zero, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
        ORingStruc.one_eq_one, Structure.Add.add, Structure.Mul.mul, Structure.Eq.eq,
        Structure.LT.lt, Structure.LE.le, LogicalConnective.Prop.arrow_eq,
        LogicalConnective.Prop.and_eq, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq,
        add_zero, mul_zero, mul_one, zero_le, zero_lt_one, add_lt_add_iff_right, lt_self_iff_false,
        not_false_eq_true, implies_true, imp_self, and_imp, Nat.reduceAdd, Nat.succ_eq_add_one,
        Fin.isValue]
    case addAssoc => intro f; exact add_assoc _ _ _
    case addComm => intro f; exact add_comm _ _
    case mulAssoc => intro f; exact mul_assoc _ _ _
    case mulComm => intro f; exact mul_comm _ _
    case addEqOfLt => intro f h; exact ⟨f 1 - f 0, Nat.add_sub_of_le (le_of_lt h)⟩
    case oneLeOfZeroLt => intro n hn; exact hn
    case mulLtMul => rintro f h hl; exact (Nat.mul_lt_mul_right hl).mpr h
    case distr => intro f; exact Nat.mul_add _ _ _
    case ltTrans => intro f; exact Nat.lt_trans
    case ltTri => intro f; exact Nat.lt_trichotomy _ _
    case equal h =>
      have : ModelsTheory ℕ (eqAxiom : Theory oRing) := inferInstance
      exact modelsTheory_iff.mp this h⟩


-- @@ L229-239 expanded
lemma models_succInd (φ : Semiformula oRing ℕ 1) : Models ℕ (succInd φ) :=
  by
  simp only [succInd, Nat.reduceAdd, Fin.isValue, models_iff, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_substs, Matrix.cons_val_fin_one, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, Matrix.constant_eq_singleton,
    Semiformula.eval_all, Nat.succ_eq_add_one, Semiterm.val_bvar, Semiterm.val_operator₂,
    ORingStruc.one_eq_one, Structure.Add.add, LogicalConnective.Prop.arrow_eq]
  intro e hzero hsucc x
  induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih


-- @@ L241-244 expanded
instance models_iSigma (Γ k) : ModelsTheory ℕ ((indH Γ) k) :=
  by
  simp only [ModelsTheory.add_iff, models_PeanoMinus, Theory.indScheme,
    Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]


-- @@ L246-246 expanded
instance models_iSigmaZero : ModelsTheory ℕ (iSigma 0) :=
  inferInstance


-- @@ L248-248 expanded
instance models_iSigmaOne : ModelsTheory ℕ (iSigma 1) :=
  inferInstance


-- @@ L250-253 expanded
instance models_peano : ModelsTheory ℕ peano :=
  by
  simp only [Theory.peano, Theory.indScheme, ModelsTheory.add_iff, models_PeanoMinus,
    Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]


-- @@ L255-255 verbatim
end Standard


-- @@ L257-257 verbatim
section «lp_section_5»


-- @@ L259-259 verbatim
variable (L : Language.{u}) [ORing L]


-- @@ L261-266 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure Cut (M : Type w) [s : Structure L M] where
  /-- Imported declaration from the Incompleteness formalization. -/
  domain : Set M
  closedSucc :
    ∀ x ∈ domain,
      (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]).valb s ![x] ∈ domain
  closedLt :
    ∀ x y : M,
      Semiformula.Evalb s ![x, y] (Semiformula.Operator.operator Operator.LT.lt ![#0, #1]) →
        y ∈ domain → x ∈ domain


-- @@ L268-270 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt :
    ∀ x y : M,
      Semiformula.Evalb s ![x, y] (Semiformula.Operator.operator Operator.LT.lt ![#0, #1]) →
        y ∈ domain → x ∈ domain


-- @@ L272-272 verbatim
end «lp_section_5»


-- @@ L274-275 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.Theory.TrueArith : Theory oRing :=
  Structure.theory oRing ℕ


-- @@ L277-278 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐓𝐀" => Theory.TrueArith


-- @@ L280-281 expanded
instance _root_.LO.FirstOrder.Arith.Standard.models_trueArith : ModelsTheory ℕ Theory.TrueArith :=
  modelsTheory_iff.mpr fun {φ} ↦ by simp


-- @@ L283-285 expanded
lemma trueArith_provable_iff {φ : SyntacticFormula oRing} :
    Provable Theory.TrueArith φ ↔ Models ℕ φ :=
  ⟨fun h ↦ consequence_iff'.mp (sound₀! h) ℕ, fun h ↦ Entailment.by_axm _ h⟩


-- @@ L287-290 expanded
instance (T : Theory oRing) [ModelsTheory ℕ T] : WeakerThan T Theory.TrueArith :=
  ⟨by
    rintro φ h
    have : Models ℕ φ := consequence_iff'.mp (sound₀! h) ℕ
    exact trueArith_provable_iff.mpr this⟩


-- @@ L292-296 expanded
lemma oRing_consequence_of (T : Theory oRing) [WeakerThan eqAxiom T] (φ : SyntacticFormula oRing)
    (H : ∀ (M : Type*) [ORingStruc M] [ModelsTheory M T], Models M φ) : Consequence T φ :=
  consequence_of T φ fun M _ s _ _ ↦
    by
    rcases standardModel_unique M s
    exact H M


-- @@ L298-304 expanded
lemma oRing_weakerThan_of (T S : Theory oRing) [WeakerThan eqAxiom S]
    (H : ∀ (M : Type*) [ORingStruc M] [ModelsTheory M S], ModelsTheory M T) : WeakerThan T S :=
  Entailment.weakerThan_iff.mpr fun h ↦
    complete <| oRing_consequence_of _ _ fun M _ _ ↦ sound! h (H M)


-- @@ L306-306 verbatim
end Arith


-- @@ L308-308 verbatim
namespace Theory


-- @@ L310-310 verbatim
open _root_.LO.FirstOrder.Arith


-- @@ L312-313 expanded
instance _root_.LO.FirstOrder.Theory.CobhamR0.consistent : Entailment.Consistent CobhamR0 :=
  Sound.consistent_of_satisfiable ⟨_, (inferInstance : ModelsTheory ℕ CobhamR0)⟩


-- @@ L315-316 expanded
instance _root_.LO.FirstOrder.Theory.Peano.consistent : Entailment.Consistent peano :=
  Sound.consistent_of_satisfiable ⟨_, (inferInstance : ModelsTheory ℕ peano)⟩


-- @@ L318-319 expanded
instance _root_.LO.FirstOrder.Theory.TrueArith.consistent :
    Entailment.Consistent Theory.TrueArith :=
  Sound.consistent_of_satisfiable ⟨_, (inferInstance : ModelsTheory ℕ Theory.TrueArith)⟩


-- @@ L321-321 verbatim
end Theory


-- @@ L323-323 verbatim
end FirstOrder


-- @@ L325-325 verbatim
end LO
