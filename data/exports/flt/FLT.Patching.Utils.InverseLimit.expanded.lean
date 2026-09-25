/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import Mathlib.Topology.Constructions
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Data.Finset.Order


-- @@ L12-17 verbatim
/-!
# Inverse-limit utilities

Density and non-emptiness lemmas for inverse limits used in the patching
argument.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≥ ·)]

-- @@ L22-22 verbatim
variable (α : ι → Type*) (f : ∀ i j, i ≤ j → α i → α j)


-- @@ L24-24 verbatim
section Topology


-- @@ L26-26 verbatim
variable [∀ i, TopologicalSpace (α i)]

-- @@ L27-27 verbatim
variable (hf : ∀ i j h, Continuous (f i j h))


-- @@ L29-43 verbatim
set_option backward.isDefEq.respectTransparency.types false in
include hf in
lemma dense_inverseLimit_of_forall_image_dense
    (s : Set { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hs : ∀ i, Dense ((fun x ↦ (Subtype.val x) i) '' s)) : Dense s := by
  classical
  rw [dense_iff_inter_open]
  rintro U ⟨t, ht, rfl⟩ ⟨x, hx⟩
  obtain ⟨I, u, hu₁, hu₂⟩ := isOpen_pi_iff.mp ht _ hx
  obtain ⟨i, hi⟩ := Finset.exists_le (α := ιᵒᵈ) I
  let U : Set (α i) := ⋂ (j : I), (f _ _ (hi j.1 j.2)) ⁻¹' u _
  have hU : IsOpen U := isOpen_iInter_of_finite fun j ↦ (hu₁ j.1 j.2).1.preimage (hf ..)
  obtain ⟨_, hz₁, z, hz₂, rfl⟩ := dense_iff_inter_open.mp (hs i) U hU
    ⟨x.1 _, by simp [U, x.2, hu₁]⟩
  exact ⟨z, hu₂ (by simpa [U, z.2] using hz₁), hz₂⟩


-- @@ L45-51 verbatim
include hf in
lemma denseRange_inverseLimit {β}
    (g : β → { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hg : ∀ i, DenseRange (fun x ↦ (g x).1 i)) : DenseRange g := by
  refine dense_inverseLimit_of_forall_image_dense α f hf _ fun i ↦ ?_
  rw [← Set.range_comp]
  exact hg _


-- @@ L53-53 verbatim
end Topology


-- @@ L55-55 verbatim
section MittagLeffler


-- @@ L57-57 verbatim
variable (hf₀ : ∀ i, f i i le_rfl = id)

-- @@ L58-58 verbatim
variable (hf : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), f j k hjk ∘ f i j hij = f i k (hij.trans hjk))

-- @@ L59-59 verbatim
variable {l : ℕ → ι} (hl : Antitone l) (hl' : ∀ x, ∃ n, l n ≤ x)


-- @@ L61-61 verbatim
open scoped TypeCat


-- @@ L63-63 verbatim
open CategoryTheory

-- @@ L64-82 verbatim
set_option backward.isDefEq.respectTransparency.types false in
omit [Nonempty ι] [IsDirected ι (· ≥ ·)] in
include hf₀ hf hl hl' in
theorem nonempty_inverseLimit_of_finite [∀ i, Finite (α i)] [∀ i, Nonempty (α i)] :
    Nonempty { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j } := by
  let f' : ιᵒᵈᵒᵖ ⥤ Type _ :=
  { obj i := α i.1,
    map e := ↾(f _ _ e.unop.le),
    map_id i := by ext; simp [hf₀],
    map_comp f g := by ext; simp [← hf _ _ _ f.unop.le g.unop.le] }
  have : IsDirected ιᵒᵈ (· ≤ ·) := by
    constructor
    intros i j
    obtain ⟨i', hi'⟩ := hl' i
    obtain ⟨j', hj'⟩ := hl' j
    refine ⟨l (max i' j'), le_trans hi' (hl (le_max_left _ _)),
      le_trans hj' (hl (le_max_right _ _))⟩
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system f'
  exact ⟨⟨fun i ↦ x ⟨i⟩, fun i j e ↦ hx (homOfLE e).op⟩⟩


-- @@ L84-84 verbatim
end MittagLeffler
