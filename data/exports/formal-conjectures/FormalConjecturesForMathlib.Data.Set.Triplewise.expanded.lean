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

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.Ineq


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-26 verbatim
def Triplewise {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ ⦃i j k ⦄, i ≠ j → j ≠ k → i ≠ k → r i j k


-- @@ L28-28 verbatim
namespace Set


-- @@ L30-30 verbatim
variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}


-- @@ L32-37 verbatim
/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z


-- @@ L39-43 verbatim
protected theorem Triplewise.eq (hs : s.Triplewise r)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (h : ¬r x y z) :
    x = y ∨ y = z ∨ x = z := by
  have := (h <| hs hx hy hz · · ·)
  tauto


-- @@ L45-47 verbatim
theorem Triplewise.mono (h : t ⊆ s) (hs : s.Triplewise r) :
    t.Triplewise r :=
  fun _ hx _ hy _ hz hxy hyz hxz ↦ hs (h hx) (h hy) (h hz) hxy hyz hxz


-- @@ L49-52 verbatim
@[simp]
theorem Triplewise_univ_iff :
    Set.univ.Triplewise r ↔ Triplewise r := by
  simp [Set.Triplewise, Triplewise]


-- @@ L54-62 verbatim
theorem triplewise_of_encard_lt (r : α → α → α → Prop)
    (h : s.encard < 3) : s.Triplewise r := by
  unfold Set.Triplewise
  contrapose! h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, _⟩ := h
  trans encard {x, y, z}
  · simp [Set.encard_insert_of_notMem, *]
    norm_num
  · exact encard_le_encard_of_injOn (by simp [MapsTo, hx, hy, hz]) (injOn_id _)


-- @@ L64-67 verbatim
@[simp]
theorem triplewise_empty (r : α → α → α → Prop) :
    Set.Triplewise ∅ r :=
  (notMem_empty · · |>.elim)


-- @@ L69-73 verbatim
@[simp]
theorem triplewise_singleton (r : α → α → α → Prop) :
    Set.Triplewise {x} r := by
  apply triplewise_of_encard_lt
  simp


-- @@ L75-81 verbatim
@[simp]
theorem triplewise_pair
    (r : α → α → α → Prop) : Set.Triplewise {x, y} r := by
  apply triplewise_of_encard_lt
  apply (encard_insert_le {y} x).trans_lt
  simp
  norm_num


-- @@ L83-102 verbatim
theorem triplewise_insert :
    (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
  refine ⟨fun hxs ↦ ?_, fun ⟨hs, hxs⟩ ↦ ?_⟩
  · refine ⟨hxs.mono (subset_insert x s), fun y hy z hz hxy hxz hyz ↦ ⟨?_, ?_, ?_⟩⟩
    · exact hxs (mem_insert x s) (mem_insert_of_mem x hy) (mem_insert_of_mem x hz) hxy hyz hxz
    · exact hxs (mem_insert_of_mem x hy) (mem_insert x s) (mem_insert_of_mem x hz) hxy.symm hxz hyz
    · exact hxs (mem_insert_of_mem x hy) (mem_insert_of_mem x hz)
        (mem_insert x s) hyz hxz.symm hxy.symm
  · intro w hw y hy z hz hwy hyz hwz
    rw [mem_insert_iff] at hw hy hz
    obtain rfl | hw := hw
    · refine (hxs y ?_ z ?_ hwy hwz hyz).1
      · simpa [hwy.symm] using hy
      · simpa [hwz.symm] using hz
    obtain rfl | hy := hy
    · exact (hxs w hw z (by simpa [hyz.symm] using hz) hwy.symm hyz hwz).2.1
    obtain rfl | hz := hz
    · exact (hxs w hw y hy hwz.symm hyz.symm hwy).2.2
    exact hs hw hy hz hwy hyz hwz


-- @@ L104-109 verbatim
theorem triplewise_insert_of_not_mem (hx : x ∉ s) :
    (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
  refine Set.triplewise_insert.trans <| and_congr_right' <| forall₄_congr ?_
  intro y hy z hz
  simp [(ne_of_mem_of_not_mem hy hx).symm, (ne_of_mem_of_not_mem hz hx).symm]


-- @@ L111-114 verbatim
protected theorem Triplewise.insert (hs : s.Triplewise r)
    (h : ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
    (insert x s).Triplewise r :=
  Set.triplewise_insert.mpr ⟨hs, h⟩


-- @@ L116-120 verbatim
protected theorem Triplewise.insert_of_not_mem
    (hx : x ∉ s) (hs : s.Triplewise r)
    (h : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
    (insert x s).Triplewise r :=
  (Set.triplewise_insert_of_not_mem hx).mpr ⟨hs, h⟩


-- @@ L122-131 verbatim
theorem triplewise_set_pred_iff {S : Set α} {P : Set α → Prop} :
    S.Triplewise (P {·, ·, ·}) ↔ ∀ T ⊆ S, T.ncard = 3 → P T := by
  constructor
  · intro h T hT T_ncard
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := ncard_eq_three.mp T_ncard
    simp_rw [insert_subset_iff, singleton_subset_iff] at hT
    exact h hT.1 hT.2.1 hT.2.2 hxy hyz hxz
  · intro h x hx y hy z hz hxy hyz hxz
    refine h _ ?_ (ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩)
    simp [insert_subset_iff, hx, hy, hz]


-- @@ L133-133 verbatim
end Set
