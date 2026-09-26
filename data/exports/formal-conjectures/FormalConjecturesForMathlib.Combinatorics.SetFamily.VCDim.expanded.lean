/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Data.Set.Card


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-26 verbatim
/-!
# VC dimension of a set family

This file defines the VC dimension of a set family as the maximum size of a set it shatters.
-/


-- @@ L28-28 verbatim
variable {α : Type*} {𝒜 ℬ : Set (Set α)} {A B : Set α} {a : α} {d d' : ℕ}


-- @@ L30-33 verbatim
variable (𝒜 A) in
/-- A set family `𝒜` shatters a set `A` if restricting `𝒜` to `A` gives rise to all subsets of `A`.
-/
def Shatters : Prop := ∀ ⦃B⦄, B ⊆ A → ∃ C ∈ 𝒜, A ∩ C = B


-- @@ L35-36 verbatim
lemma Shatters.exists_inter_eq_singleton (hs : Shatters 𝒜 A) (ha : a ∈ A) : ∃ B ∈ 𝒜, A ∩ B = {a} :=
  hs <| Set.singleton_subset_iff.2 ha


-- @@ L38-39 verbatim
lemma Shatters.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hB ↦ let ⟨u, hu, hut⟩ := h𝒜 hB; ⟨u, h hu, hut⟩


-- @@ L41-42 verbatim
lemma Shatters.mono_right (h : B ⊆ A) (hs : Shatters 𝒜 A) : Shatters 𝒜 B := fun u hu ↦ by
  obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu <| inf_le_of_left_le h⟩


-- @@ L44-45 verbatim
lemma Shatters.exists_superset (h : Shatters 𝒜 A) : ∃ B ∈ 𝒜, A ⊆ B :=
  let ⟨B, hB, hst⟩ := h .rfl; ⟨B, hB, Set.inter_eq_left.1 hst⟩


-- @@ L47-48 verbatim
lemma Shatters.of_forall_subset (h : ∀ B, B ⊆ A → B ∈ 𝒜) : Shatters 𝒜 A :=
  fun B hB ↦ ⟨B, h _ hB, Set.inter_eq_right.2 hB⟩


-- @@ L50-51 verbatim
protected lemma Shatters.nonempty (h : Shatters 𝒜 A) : 𝒜.Nonempty :=
  let ⟨B, hB, _⟩ := h .rfl; ⟨B, hB⟩


-- @@ L53-54 verbatim
@[simp] lemma shatters_empty : Shatters 𝒜 ∅ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨A, hs⟩ B hB ↦ ⟨A, hs, by simpa [eq_comm] using hB⟩⟩


-- @@ L56-57 verbatim
protected lemma Shatters.subset_iff (h : Shatters 𝒜 A) : B ⊆ A ↔ ∃ u ∈ 𝒜, A ∩ u = B :=
  ⟨fun hB ↦ h hB, by rintro ⟨u, _, rfl⟩; exact Set.inter_subset_left⟩


-- @@ L59-60 verbatim
lemma shatters_iff : Shatters 𝒜 A ↔ (A ∩ ·) '' 𝒜 = A.powerset :=
  ⟨fun h ↦ by ext B; simp [h.subset_iff], fun h B hB ↦ h.superset hB⟩


-- @@ L62-62 verbatim
lemma univ_shatters : Shatters .univ A := .of_forall_subset <| by simp


-- @@ L64-65 verbatim
@[simp] lemma shatters_univ : Shatters 𝒜 .univ ↔ 𝒜 = .univ := by
  simp [Shatters, Set.eq_univ_iff_forall]


-- @@ L67-73 verbatim
variable (𝒜 d) in
/-- A set family `𝒜` has VC dimension at most `d` if there are no families `x` of elements indexed
by `[d + 1]` and `A` of sets of `𝒜` indexed by `2^[d + 1]` such that `x i ∈ A s ↔ i ∈ s` for all
`i ∈ [d + 1], s ⊆ [d + 1]`. -/
def HasVCDimAtMost : Prop :=
  ∀ (x : Fin (d + 1) → α) (A : Set (Fin (d + 1)) → Set α),
    (∀ s, A s ∈ 𝒜) → ¬ ∀ i s, x i ∈ A s ↔ i ∈ s


-- @@ L75-76 verbatim
lemma HasVCDimAtMost.anti (h𝒜ℬ : 𝒜 ≤ ℬ) (hℬ : HasVCDimAtMost ℬ d) : HasVCDimAtMost 𝒜 d :=
  fun _x _A hA ↦ hℬ _ _ fun _s ↦ h𝒜ℬ <| hA _


-- @@ L78-82 verbatim
lemma HasVCDimAtMost.mono (h : d ≤ d') (hd : HasVCDimAtMost 𝒜 d) : HasVCDimAtMost 𝒜 d' := by
  rintro x A hA hxA
  replace h : d + 1 ≤ d' + 1 := by omega
  exact hd (x ∘ Fin.castLE h) (A ∘ Set.image (Fin.castLE h)) (by simp [hA]) fun i s ↦
    (hxA ..).trans <| by simp


-- @@ L84-84 verbatim
@[simp] lemma HasVCDimAtMost.empty : HasVCDimAtMost (∅ : Set (Set α)) d := by simp [HasVCDimAtMost]


-- @@ L86-86 verbatim
proof_wanted hasVCDimAtMost_iff_shatters : HasVCDimAtMost 𝒜 d ↔ ∀ A, Shatters 𝒜 A → A.encard ≤ d
