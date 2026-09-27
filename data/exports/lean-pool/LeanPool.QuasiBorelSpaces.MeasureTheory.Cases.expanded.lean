/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions


-- @@ L10-14 verbatim
/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Cases

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Cases`.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
open scoped MeasureTheory


-- @@ L21-21 verbatim
namespace MeasureTheory


-- @@ L23-25 verbatim
variable
  {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {I : Type*} [Countable I]


-- @@ L27-38 verbatim
lemma measurable_cases
    {ix : A → I} {f : I → A → B}
    (hix : Measurable[_, ⊤] ix) (hf : ∀ i, Measurable (f i))
    : Measurable (fun x ↦ f (ix x) x) := by
  intro s hs
  have : ((fun x ↦ f (ix x) x) ⁻¹' s) = ⋃i, { x | ix x ∈ ({i} : Set I) } ∩ { x | f i x ∈ s } := by
    ext
    simp_all
  rw [this]
  refine MeasurableSet.iUnion fun i ↦ MeasurableSet.inter ?_ ?_
  · exact hix MeasurableSpace.measurableSet_top
  · exact hf i hs



-- @@ L41-49 verbatim
@[fun_prop]
lemma measurable_decide
    {p : A → Prop} [inst : DecidablePred p] (hp : Measurable p)
    : Measurable (fun x ↦ decide (p x)) := by
  classical
  have : inst = fun x ↦ Classical.dec (p x) := by subsingleton
  subst this
  apply measurable_cases (f := fun p _ ↦ decide p) hp
  simp only [measurable_const, implies_true]


-- @@ L51-63 verbatim
@[fun_prop]
lemma measurable_dite
    {p : A → Prop} (hp₁ : Measurable p) (hp₂ : DecidablePred p)
    {f : (x : A) → p x → B} (hf : Measurable fun x : Subtype p ↦ f x.val x.property)
    {g : (x : A) → ¬p x → B} (hg : Measurable fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property)
    : Measurable (fun x ↦ if h : p x then f x h else g x h) := by
  let f' (x : Subtype p) := f x.val x.property
  let g' (x : Subtype fun x ↦ ¬p x) := g x.val x.property
  change Measurable fun x ↦ if h : x ∈ { x | p x } then f' ⟨x, h⟩ else g' ⟨x, h⟩
  apply Measurable.dite
  · exact hf
  · exact hg
  · simp_all


-- @@ L65-65 verbatim
end MeasureTheory
