/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Coloring.Membership
import DescriptiveComplexity.Problems.ThreeColorability.Defs
import DescriptiveComplexity.Counting.Class


-- @@ L10-19 verbatim
/-!
# #3-Colorability: counting the proper 3-colorings

The counting version of `DescriptiveComplexity.ThreeCol`: the number of
proper colorings of a graph with the three colors `Fin 3`
(`DescriptiveComplexity.SharpThreeCol`). It is in `#P`
(`DescriptiveComplexity.sharpThreeCol_mem_sharpP`), the coloring being three
guessed color classes partitioning the vertices; its one-call completeness is
in `DescriptiveComplexity.Problems.ThreeColorability.CountDraw`.
-/


-- @@ L21-21 verbatim
namespace DescriptiveComplexity


-- @@ L23-23 verbatim
open FirstOrder


-- @@ L25-25 verbatim
open Language Structure SOBlock


-- @@ L27-27 verbatim
section Kernel


-- @@ L29-32 expanded
/-- Kernel clause: no vertex is in two color classes. -/
noncomputable def colExclusiveClause : (kColSOLang 3).Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (FirstOrder.Language.Formula.iInf
      (fun i : Fin 3 =>
        FirstOrder.Language.Formula.iInf
          (fun j : Fin 3 =>
            (FirstOrder.Language.Relations.formula₁ (kcColorSym i)
                  (FirstOrder.Language.Term.var (Sum.inr 0))).imp
              ((FirstOrder.Language.Relations.formula₁ (kcColorSym j)
                    (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                (if i = j then ⊤ else ⊥)))))


-- @@ L34-37 verbatim
/-- The kernel of #3-Colorability: the color classes partition the vertices
and no edge stays inside a class. -/
noncomputable def sharpThreeColKernel : (kColSOLang 3).Sentence :=
  kColKernel 3 ⊓ colExclusiveClause


-- @@ L39-39 verbatim
variable {V : Type} [Language.graph.Structure V]


-- @@ L41-70 verbatim
theorem realize_sharpThreeColKernel (ρ : (colorGuessBlock 3).Assignment V) :
    (@Sentence.Realize (kColSOLang 3) V
        (@sumStructure _ _ V _ ((colorGuessBlock 3).structure ρ)) sharpThreeColKernel) ↔
      ((∀ x : V, ∃ i : Fin 3, ρ i ![x]) ∧
        ∀ x y : V, RelMap adj ![x, y] → ∀ i : Fin 3, ¬(ρ i ![x] ∧ ρ i ![y])) ∧
      ∀ (x : V) (i j : Fin 3), ρ i ![x] → ρ j ![x] → i = j := by
  let := (colorGuessBlock 3).structure ρ
  have hsub : ∀ (i : Fin 3) (w : Fin 1 → V),
      RelMap (L := kColSOLang 3) (M := V) (kcColorSym i) w ↔ ρ i w :=
    fun _ _ => Iff.rfl
  have hw : ∀ w : Fin 1 → V, w = ![w 0] := fun w => funext fun k => by fin_cases k; rfl
  rw [sharpThreeColKernel, kColKernel, colExclusiveClause]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iSup, Formula.realize_iInf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  refine and_congr (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
    ⟨fun h x y hxy i => ?_, fun h i hi j => ?_⟩) ⟨fun h x i j hi hj => ?_, fun h w i j hi hj => ?_⟩
  · obtain ⟨i, hi⟩ := h fun _ => x
    exact ⟨i, hi⟩
  · obtain ⟨j, hj⟩ := h (i 0)
    exact ⟨j, by rw [hw i]; exact hj⟩
  · exact h ![x, y] (by simpa using hxy) i
  · exact h (i 0) (i 1) (by simpa using hi) j
  · have := h (fun _ => x) i j hi hj
    by_contra hij
    rw [ite_eq_right hij] at this
    exact this
  · rw [h (w 0) i j hi hj, ite_eq_left rfl]
    exact Formula.realize_top.mpr trivial


-- @@ L72-74 verbatim
/-- A 3-coloring, as an assignment of the three color classes. -/
def colorAssign (χ : V → Fin 3) : (colorGuessBlock 3).Assignment V :=
  fun i (w : Fin 1 → V) => χ (w 0) = i


-- @@ L76-110 verbatim
/-- **The proper 3-colorings are the witnesses of the kernel.** -/
noncomputable def threeColEquiv (V : Type) [Language.graph.Structure V] :
    {ρ : (colorGuessBlock 3).Assignment V //
        @Sentence.Realize (kColSOLang 3) V
          (@sumStructure _ _ V _ ((colorGuessBlock 3).structure ρ)) sharpThreeColKernel} ≃
      {χ : V → Fin 3 // ∀ x y : V, RelMap adj ![x, y] → χ x ≠ χ y} where
  toFun ρ := ⟨fun x => Classical.choose (((realize_sharpThreeColKernel ρ.1).mp ρ.2).1.1 x),
    fun x y hxy hc => by
      have h := (realize_sharpThreeColKernel ρ.1).mp ρ.2
      have hx := Classical.choose_spec (h.1.1 x)
      have hy := Classical.choose_spec (h.1.1 y)
      change Classical.choose (h.1.1 x) = Classical.choose (h.1.1 y) at hc
      rw [← hc] at hy
      exact h.1.2 x y hxy _ ⟨hx, hy⟩⟩
  invFun χ := ⟨colorAssign χ.1, (realize_sharpThreeColKernel _).mpr
    ⟨⟨fun x => ⟨χ.1 x, rfl⟩, fun x y hxy i hi => χ.2 x y hxy (hi.1.trans hi.2.symm)⟩,
      fun x i j hi hj => hi.symm.trans hj⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have h := (realize_sharpThreeColKernel ρ).mp hρ
    refine Subtype.ext (funext fun i => funext fun (w : Fin 1 → V) => propext ?_)
    have hw : w = ![w 0] := funext fun k => by fin_cases k; rfl
    have hspec := Classical.choose_spec (h.1.1 (w 0))
    constructor
    · intro hc
      change Classical.choose (h.1.1 (w 0)) = i at hc
      rw [hw, ← hc]
      exact hspec
    · intro hi
      change Classical.choose (h.1.1 (w 0)) = i
      rw [hw] at hi
      exact h.2 (w 0) _ _ hspec hi
  right_inv χ := Subtype.ext (funext fun x => by
    have h := Classical.choose_spec (⟨χ.1 x, rfl⟩ : ∃ i, colorAssign χ.1 i ![x])
    exact h.symm)


-- @@ L112-112 verbatim
end Kernel


-- @@ L114-121 verbatim
/-- **#3-Colorability**: the number of proper colorings of a graph with three
colors. -/
noncomputable def SharpThreeCol : CountingProblem Language.graph where
  Count := fun V inst =>
    Nat.card {χ : V → Fin 3 // ∀ x y : V, @RelMap _ V inst _ adj ![x, y] → χ x ≠ χ y}
  iso_invariant := fun {A B} _ _ e => by
    rw [← Nat.card_congr (threeColEquiv A), ← Nat.card_congr (threeColEquiv B)]
    exact witnessCount_iso (colorGuessBlock 3) sharpThreeColKernel e


-- @@ L123-125 verbatim
theorem sharpThreeCol_apply (V : Type) [Language.graph.Structure V] :
    SharpThreeCol V = Nat.card {χ : V → Fin 3 // ∀ x y : V, RelMap adj ![x, y] → χ x ≠ χ y} :=
  rfl


-- @@ L127-130 verbatim
/-- **#3-Colorability is in `#P`.** -/
theorem sharpThreeCol_mem_sharpP : SharpThreeCol ∈ SharpP :=
  sharpPDefinable_congr (fun V _ _ => Nat.card_congr (threeColEquiv V))
    (sharpPDefinable_ofKernel (colorGuessBlock 3) sharpThreeColKernel)


-- @@ L132-132 verbatim
end DescriptiveComplexity
