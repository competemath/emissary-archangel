/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Semantics
public import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.Bound.Init


-- @@ L13-13 verbatim
/-! # Ultraproduct -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO


-- @@ L20-20 verbatim
namespace FirstOrder


-- @@ L22-22 verbatim
section «lp_section_1»


-- @@ L24-24 verbatim
universe u v


-- @@ L26-29 verbatim
variable {L : Language.{u}} {μ : Type v}
 {I : Type u} (A : I → Type u)
 [s : (i : I) → FirstOrder.Structure L (A i)]
 (𝓤 : Ultrafilter I)


-- @@ L31-31 verbatim
namespace Structure


-- @@ L33-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Uprod (𝓤 : Ultrafilter I) where
  /-- Imported declaration from the Incompleteness formalization. -/
  val : (i : I) → A i


-- @@ L38-40 verbatim
instance UprodStruc : Structure L (Uprod A 𝓤) where
  func := fun _ f v => ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩
  rel  := fun _ r v => {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤


-- @@ L42-43 verbatim
instance [(i : I) → Nonempty (A i)] :
    Nonempty (Uprod A 𝓤) := Nonempty.map (⟨·⟩) inferInstance


-- @@ L45-46 verbatim
@[simp] lemma func_Uprod {k} (f : L.Func k) (v : Fin k → Uprod A 𝓤) :
    Structure.func f v = ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩ := rfl


-- @@ L48-49 verbatim
@[simp] lemma rel_Uprod {k} (r : L.Rel k) (v : Fin k → Uprod A 𝓤) :
    Structure.rel r v ↔ {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤 := of_eq rfl


-- @@ L51-51 verbatim
end Structure


-- @@ L53-53 verbatim
namespace Semiterm


-- @@ L55-55 verbatim
open Structure


-- @@ L57-57 verbatim
variable (e : Fin n → Uprod A 𝓤) (ε : μ → Uprod A 𝓤)


-- @@ L59-61 verbatim
lemma val_Uprod (t : Semiterm L μ n) :
    t.valm (Uprod A 𝓤) e ε = ⟨fun i ↦ t.val (s i) (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i)⟩ :=
  by induction t <;> simp[*, val_func]


-- @@ L63-63 verbatim
end Semiterm


-- @@ L65-65 verbatim
open Structure


-- @@ L67-67 verbatim
variable {A} {𝓤}


-- @@ L69-69 verbatim
namespace Semiformula


-- @@ L71-71 verbatim
variable {e : Fin n → Uprod A 𝓤} {ε : μ → Uprod A 𝓤}


-- @@ L73-75 expanded
lemma val_vecCons_val_eq {z : Uprod A 𝓤} {i : I} :
    (vecCons (z.val i) fun x ↦ (e x).val i) = (fun x ↦ ((vecCons z e) x).val i) := by
  simp [Matrix.comp_vecCons (Uprod.val · i), Function.comp_def]


-- @@ L77-123 expanded
lemma eval_Uprod [(i : I) → Nonempty (A i)] {φ : Semiformula L μ n} :
    Evalm (Uprod A 𝓤) e ε φ ↔ {i | Eval (s i) (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ} ∈ 𝓤 :=
  by
  induction φ using rec' <;>
    simp only [LogicalConnective.HomClass.map_top, «Prop».top_eq_true, Set.ofPred_true, true_iff,
      LogicalConnective.HomClass.map_bot, «Prop».bot_eq_false, Set.ofPred_false,
      Ultrafilter.empty_notMem, eval_rel, eval_nrel, Semiterm.val_Uprod, rel_Uprod,
      LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
      LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, eval_all, eval_ex,
      Nat.succ_eq_add_one, *]
  case hverum => exact Filter.univ_mem
  case hnrel k r v => exact Ultrafilter.compl_mem_iff_notMem.symm
  case hand => exact Filter.inter_mem_iff.symm
  case hor φ ψ ihp ihq => exact Ultrafilter.union_mem_iff.symm
  case hall φ _ =>
    constructor
    · intro h
      let z : Uprod A 𝓤 :=
        ⟨fun i =>
          Classical.epsilon
            (fun z => ¬Eval (s i) (vecCons z fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ)⟩
      exact
        Filter.mem_of_superset (h z)
          (by
            intro i hι a
            have : Eval (s i) (vecCons (z.val i) fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ := by
              rw [val_vecCons_val_eq]; exact hι
            by_contra hc
            have : ¬Evalm (A i) (vecCons (z.val i) fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ :=
              Classical.epsilon_spec (p := fun z =>
                ¬(Eval (s i) (vecCons z fun x ↦ (e x).val i) _ φ)) ⟨a, hc⟩
            contradiction)
    · intro h x
      exact Filter.mem_of_superset h (by intro i h; simpa [val_vecCons_val_eq] using h (x.val i))
  case hex φ _ =>
    constructor
    · rintro ⟨x, hx⟩
      exact
        Filter.mem_of_superset hx (by intro i h; use x.val i; simpa [val_vecCons_val_eq] using h)
    · intro h
      let z : Uprod A 𝓤 :=
        ⟨fun i =>
          Classical.epsilon
            (fun z => Eval (s i) (vecCons z fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ)⟩
      use z
      exact
        Filter.mem_of_superset h
          (by
            intro i; rintro ⟨x, hx⟩
            have : Eval (s i) (vecCons (z.val i) fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ :=
              Classical.epsilon_spec (p := fun z => Eval (s i) (vecCons z fun x ↦ (e x).val i) _ φ)
                ⟨x, hx⟩
            rw [val_vecCons_val_eq] at this; exact this)


-- @@ L125-127 verbatim
lemma val_Uprod [(i : I) → Nonempty (A i)] {φ : Formula L μ} :
    Evalfm (Uprod A 𝓤) ε φ ↔ {i | Evalf (s i) (fun x ↦ (ε x).val i) φ} ∈ 𝓤 := by
  simp [Evalf, eval_Uprod, Matrix.empty_eq]


-- @@ L129-129 verbatim
end Semiformula


-- @@ L131-133 expanded
lemma models_Uprod [(i : I) → Nonempty (A i)] {φ : SyntacticFormula L} :
    Models (Uprod A 𝓤) φ ↔ {i | Models (A i) φ} ∈ 𝓤 := by
  simp [models_iff₀, Semiformula.val_Uprod, Empty.eq_elim]


-- @@ L135-135 verbatim
variable (A)


-- @@ L137-140 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Semiformula.domain [(i : I) → Nonempty (A i)] (φ : SyntacticFormula L) :=
  {i | Models (A i) φ}


-- @@ L142-142 verbatim
end «lp_section_1»


-- @@ L144-144 verbatim
section «lp_section_2»


-- @@ L146-146 verbatim
variable {L : Language.{u}} {T : Theory L}


-- @@ L148-149 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev FinSubtheory (T : Theory L) := {t : Finset (SyntacticFormula L) // ↑t ⊆ T}


-- @@ L151-151 verbatim
variable (A : FinSubtheory T → Type u) [s : (i : FinSubtheory T) → Structure L (A i)]


-- @@ L153-153 verbatim
instance : Nonempty (FinSubtheory T) := ⟨∅, by simp⟩


-- @@ L155-167 expanded
lemma ultrafilter_exists [(t : FinSubtheory T) → Nonempty (A t)]
    (H : ∀ (i : FinSubtheory T), ModelsTheory (A i) (i.val : Theory L)) :
    ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Semiformula.domain A) T ⊆ 𝓤.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _
    (by
      have : DecidableEq (Set (FinSubtheory T)) := fun _ _ => Classical.propDecidable _
      intro t ht
      have :
        ∃ t' : Finset (SyntacticFormula L), ↑t' ⊆ T ∧ Finset.image (Semiformula.domain A) t' = t :=
        by simpa [Finset.subset_set_image_iff] using ht
      rcases this with ⟨t, htT, rfl⟩
      exact
        ⟨⟨t, htT⟩,
          by
          suffices ∀ i ∈ t, Models (A ⟨t, htT⟩) i by simpa [Semiformula.domain] using this
          intro i hi; exact (H ⟨t, htT⟩).all_realize hi⟩)


-- @@ L169-183 expanded
lemma compactness_aux : Satisfiable T ↔ ∀ i : FinSubtheory T, Satisfiable (i.val : Theory L) :=
  by
  constructor
  · rintro h ⟨t, ht⟩; exact Semantics.Satisfiable.of_subset h ht
  · intro h
    have :
      ∀ i : FinSubtheory T,
        ∃ (M : Type u) (_ : Nonempty M) (_ : Structure L M), ModelsTheory M (i.val : Theory L) :=
      by intro i; exact satisfiable_iff.mp (h i)
    choose A si s hA using this
    have : ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Semiformula.domain A) T ⊆ 𝓤.sets :=
      ultrafilter_exists A hA
    rcases this with ⟨𝓤, h𝓤⟩
    have : ModelsTheory (Structure.Uprod A 𝓤) T :=
      ⟨by intro σ hσ; exact models_Uprod.mpr (h𝓤 <| Set.mem_image_of_mem (Semiformula.domain A) hσ)⟩
    exact satisfiable_intro (Structure.Uprod A 𝓤) this


-- @@ L185-187 verbatim
theorem compact :
    Satisfiable T ↔ ∀ u : Finset (SyntacticFormula L), ↑u ⊆ T → Satisfiable (u : Theory L) := by
  rw[compactness_aux]; simp


-- @@ L189-189 verbatim
instance : Compact (SmallStruc L) := ⟨compact⟩


-- @@ L191-191 verbatim
end «lp_section_2»


-- @@ L193-193 verbatim
end FirstOrder


-- @@ L195-195 verbatim
end LO
