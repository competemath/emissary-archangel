/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Basic
public import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases


-- @@ L13-44 verbatim
/-!
# Example 1.4 (Scott 1981, PRG-19, §1)

Scott's third worked example: the **binary tree** of depth 2. Tokens are the
finite binary
sequences of length ≤ 2, `Δ = {Λ, 0, 1, 00, 01, 10, 11}`, and the neighbourhoods
are the
subtrees rooted at each node:

`𝒟 = {Δ, {0,00,01}, {1,10,11}, {00}, {01}, {10}, {11}}`.

We encode the seven tokens as `Fin 7`:

| token | `Λ` | `0` | `1` | `00` | `01` | `10` | `11` |
| ----- | --- | --- | --- | ---- | ---- | ---- | ---- |
| `Fin 7` | `0` | `1` | `2` | `3` | `4` | `5` | `6` |

so `left = {0,00,01} = {1,3,4}`, `right = {1,10,11} = {2,5,6}`, and the four
leaves are the
singletons `{3}, {4}, {5}, {6}`.

We build the neighbourhood system (Definition 1.1) and classify its domain
elements
(Definition 1.6): there are exactly **seven** filters. Unlike Example 1.3's linear
chain, this is
the first example with **branching** — at the partial elements
`elemZero`/`elemOne` one has a
*choice* of how to refine toward one of the four total (leaf) elements.

This is a concrete finite computation (`fin_cases`/`simp`); footprint
`[propext, Classical.choice, Quot.sound]` — same as Examples 1.2/1.3.
-/


-- @@ L46-46 verbatim
@[expose] public section


-- @@ L48-48 verbatim
namespace Domain.Neighborhood.Example14


-- @@ L50-53 verbatim
/-- Tokens for Example 1.4: the binary tree `Δ = {Λ,0,1,00,01,10,11}`, encoded as
`Fin 7`
(`Λ=0, 0=1, 1=2, 00=3, 01=4, 10=5, 11=6`). -/
abbrev Token := Fin 7


-- @@ L55-56 verbatim
/-- The master neighbourhood `Δ` (the whole tree). -/
def master : Set Token := Set.univ


-- @@ L58-59 verbatim
/-- The left subtree `{0, 00, 01} = {1, 3, 4}`. -/
def left : Set Token := {1, 3, 4}


-- @@ L61-62 verbatim
/-- The right subtree `{1, 10, 11} = {2, 5, 6}`. -/
def right : Set Token := {2, 5, 6}


-- @@ L64-65 verbatim
/-- The leaf `{00} = {3}`. -/
def leaf00 : Set Token := {3}


-- @@ L67-68 verbatim
/-- The leaf `{01} = {4}`. -/
def leaf01 : Set Token := {4}


-- @@ L70-71 verbatim
/-- The leaf `{10} = {5}`. -/
def leaf10 : Set Token := {5}


-- @@ L73-74 verbatim
/-- The leaf `{11} = {6}`. -/
def leaf11 : Set Token := {6}


-- @@ L76-77 verbatim
/-- The seven neighbourhoods of Example 1.4. -/
def memSet : Set (Set Token) := {master, left, right, leaf00, leaf01, leaf10, leaf11}


-- @@ L79-80 verbatim
/-- Membership in the neighbourhood system `𝒟` of Example 1.4. -/
def mem (X : Set Token) : Prop := X ∈ memSet


-- @@ L82-83 verbatim
theorem mem_master : mem master := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

-- @@ L84-85 verbatim
theorem mem_left : mem left := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

-- @@ L86-87 verbatim
theorem mem_right : mem right := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

-- @@ L88-89 verbatim
theorem mem_leaf00 : mem leaf00 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

-- @@ L90-91 verbatim
theorem mem_leaf01 : mem leaf01 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

-- @@ L92-93 verbatim
theorem mem_leaf10 : mem leaf10 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

-- @@ L94-95 verbatim
theorem mem_leaf11 : mem leaf11 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]


-- @@ L97-112 verbatim
/-- A neighbourhood of Example 1.4 is exactly one of the seven. -/
theorem mem_iff (X : Set Token) :
    mem X ↔ X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X =
      leaf11 := by
  constructor
  · intro h
    simpa [mem, memSet] using h
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_right
    · exact mem_leaf00
    · exact mem_leaf01
    · exact mem_leaf10
    · exact mem_leaf11


-- @@ L114-130 verbatim
theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h | h | h | h | h
  · have : (0 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [master]
    simp at this
  · have : (1 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [left]
    simp at this
  · have : (2 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [right]
    simp at this
  · have : (3 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf00]
    simp at this
  · have : (4 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf01]
    simp at this
  · have : (5 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf10]
    simp at this
  · have : (6 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf11]
    simp at this


-- @@ L132-132 verbatim
/-! ### Distinctness of neighbourhoods (only the pairs needed below). -/


-- @@ L134-137 verbatim
private theorem left_ne_master : left ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ left := by rw [h]; simp [master]
  simp [left] at hmem


-- @@ L139-142 verbatim
private theorem right_ne_master : right ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ right := by rw [h]; simp [master]
  simp [right] at hmem


-- @@ L144-147 verbatim
private theorem leaf00_ne_master : leaf00 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf00 := by rw [h]; simp [master]
  simp [leaf00] at hmem


-- @@ L149-152 verbatim
private theorem leaf01_ne_master : leaf01 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf01 := by rw [h]; simp [master]
  simp [leaf01] at hmem


-- @@ L154-157 verbatim
private theorem leaf10_ne_master : leaf10 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf10 := by rw [h]; simp [master]
  simp [leaf10] at hmem


-- @@ L159-162 verbatim
private theorem leaf11_ne_master : leaf11 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf11 := by rw [h]; simp [master]
  simp [leaf11] at hmem


-- @@ L164-167 verbatim
private theorem leaf00_ne_left : leaf00 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf00 := by rw [h]; simp [left]
  simp [leaf00] at hmem


-- @@ L169-172 verbatim
private theorem leaf01_ne_left : leaf01 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf01 := by rw [h]; simp [left]
  simp [leaf01] at hmem


-- @@ L174-177 verbatim
private theorem leaf10_ne_right : leaf10 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf10 := by rw [h]; simp [right]
  simp [leaf10] at hmem


-- @@ L179-182 verbatim
private theorem leaf11_ne_right : leaf11 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf11 := by rw [h]; simp [right]
  simp [leaf11] at hmem


-- @@ L184-184 verbatim
/-! ### Nested-subset facts. -/


-- @@ L186-187 verbatim
private theorem leaf00_subset_left : leaf00 ⊆ left := by
  intro t ht; fin_cases t <;> simp [leaf00, left] at ht ⊢


-- @@ L189-190 verbatim
private theorem leaf01_subset_left : leaf01 ⊆ left := by
  intro t ht; fin_cases t <;> simp [leaf01, left] at ht ⊢


-- @@ L192-193 verbatim
private theorem leaf10_subset_right : leaf10 ⊆ right := by
  intro t ht; fin_cases t <;> simp [leaf10, right] at ht ⊢


-- @@ L195-196 verbatim
private theorem leaf11_subset_right : leaf11 ⊆ right := by
  intro t ht; fin_cases t <;> simp [leaf11, right] at ht ⊢


-- @@ L198-198 verbatim
/-! ### "Which neighbourhoods contain a given one" (upward classification). -/


-- @@ L200-208 verbatim
private theorem eq_of_master_subset {Y : Set Token} (hY : mem Y) (h : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [left])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [right])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf00])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf01])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf10])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf11])


-- @@ L210-219 verbatim
private theorem left_subset_cases {Y : Set Token} (hY : mem Y) (h : left ⊆ Y) :
    Y = master ∨ Y = left := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [right])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf00])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf01])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf10])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf11])


-- @@ L221-230 verbatim
private theorem right_subset_cases {Y : Set Token} (hY : mem Y) (h : right ⊆ Y) :
    Y = master ∨ Y = right := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [left])
  · exact Or.inr rfl
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf00])
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf01])
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf10])
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf11])


-- @@ L232-241 verbatim
private theorem leaf00_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf00 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf00 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [right])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [leaf01])
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [leaf10])
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [leaf11])


-- @@ L243-252 verbatim
private theorem leaf01_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf01 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf01 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [right])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf00])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf10])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf11])


-- @@ L254-263 verbatim
private theorem leaf10_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf10 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf10 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [left])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf00])
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf01])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf11])


-- @@ L265-274 verbatim
private theorem leaf11_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf11 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf11 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [left])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [leaf00])
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [leaf01])
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [leaf10])
  · exact Or.inr (Or.inr rfl)


-- @@ L276-276 verbatim
/-! ### Intersections. -/


-- @@ L278-279 verbatim
private theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A


-- @@ L281-282 verbatim
private theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A


-- @@ L284-285 verbatim
private theorem left_inter_leaf00 : left ∩ leaf00 = leaf00 := by
  ext t; fin_cases t <;> simp [left, leaf00]

-- @@ L286-287 verbatim
private theorem leaf00_inter_left : leaf00 ∩ left = leaf00 := by
  rw [Set.inter_comm]; exact left_inter_leaf00

-- @@ L288-289 verbatim
private theorem left_inter_leaf01 : left ∩ leaf01 = leaf01 := by
  ext t; fin_cases t <;> simp [left, leaf01]

-- @@ L290-291 verbatim
private theorem leaf01_inter_left : leaf01 ∩ left = leaf01 := by
  rw [Set.inter_comm]; exact left_inter_leaf01

-- @@ L292-293 verbatim
private theorem right_inter_leaf10 : right ∩ leaf10 = leaf10 := by
  ext t; fin_cases t <;> simp [right, leaf10]

-- @@ L294-295 verbatim
private theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  rw [Set.inter_comm]; exact right_inter_leaf10

-- @@ L296-297 verbatim
private theorem right_inter_leaf11 : right ∩ leaf11 = leaf11 := by
  ext t; fin_cases t <;> simp [right, leaf11]

-- @@ L298-299 verbatim
private theorem leaf11_inter_right : leaf11 ∩ right = leaf11 := by
  rw [Set.inter_comm]; exact right_inter_leaf11


-- @@ L301-302 verbatim
private theorem left_inter_right : left ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, right]

-- @@ L303-304 verbatim
private theorem right_inter_left : right ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_right

-- @@ L305-306 verbatim
private theorem left_inter_leaf10 : left ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf10]

-- @@ L307-308 verbatim
private theorem leaf10_inter_left : leaf10 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf10

-- @@ L309-310 verbatim
private theorem left_inter_leaf11 : left ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf11]

-- @@ L311-312 verbatim
private theorem leaf11_inter_left : leaf11 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf11

-- @@ L313-314 verbatim
private theorem right_inter_leaf00 : right ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf00]

-- @@ L315-316 verbatim
private theorem leaf00_inter_right : leaf00 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf00

-- @@ L317-318 verbatim
private theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]

-- @@ L319-320 verbatim
private theorem leaf01_inter_right : leaf01 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf01

-- @@ L321-322 verbatim
private theorem leaf00_inter_leaf01 : leaf00 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf01]

-- @@ L323-324 verbatim
private theorem leaf01_inter_leaf00 : leaf01 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf01

-- @@ L325-326 verbatim
private theorem leaf00_inter_leaf10 : leaf00 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf10]

-- @@ L327-328 verbatim
private theorem leaf10_inter_leaf00 : leaf10 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf10

-- @@ L329-330 verbatim
private theorem leaf00_inter_leaf11 : leaf00 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf11]

-- @@ L331-332 verbatim
private theorem leaf11_inter_leaf00 : leaf11 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf11

-- @@ L333-334 verbatim
private theorem leaf01_inter_leaf10 : leaf01 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf10]

-- @@ L335-336 verbatim
private theorem leaf10_inter_leaf01 : leaf10 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf10

-- @@ L337-338 verbatim
private theorem leaf01_inter_leaf11 : leaf01 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf11]

-- @@ L339-340 verbatim
private theorem leaf11_inter_leaf01 : leaf11 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf11

-- @@ L341-342 verbatim
private theorem leaf10_inter_leaf11 : leaf10 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf10, leaf11]

-- @@ L343-344 verbatim
private theorem leaf11_inter_leaf10 : leaf11 ∩ leaf10 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf10_inter_leaf11


-- @@ L346-363 verbatim
/-- Every binary intersection of two neighbourhoods is again a neighbourhood, or
is empty
(the tree's "nested-or-disjoint" property). -/
private theorem inter_eq (X Y : Set Token) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = left ∨ X ∩ Y = right ∨ X ∩ Y = leaf00 ∨
      X ∩ Y = leaf01 ∨ X ∩ Y = leaf10 ∨ X ∩ Y = leaf11 ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [master_inter, inter_master, Set.inter_self,
      left_inter_right, right_inter_left, left_inter_leaf10, leaf10_inter_left,
      left_inter_leaf11, leaf11_inter_left, right_inter_leaf00, leaf00_inter_right,
      right_inter_leaf01, leaf01_inter_right, leaf00_inter_leaf01, leaf01_inter_leaf00,
      leaf00_inter_leaf10, leaf10_inter_leaf00, leaf00_inter_leaf11, leaf11_inter_leaf00,
      leaf01_inter_leaf10, leaf10_inter_leaf01, leaf01_inter_leaf11, leaf11_inter_leaf01,
      leaf10_inter_leaf11, leaf11_inter_leaf10,
      left_inter_leaf00, leaf00_inter_left, left_inter_leaf01, leaf01_inter_left,
      right_inter_leaf10, leaf10_inter_right, right_inter_leaf11, leaf11_inter_right,
      true_or, or_true]


-- @@ L365-382 verbatim
/-- **Example 1.4.** The binary-tree neighbourhood system on `Δ =
{Λ,0,1,00,01,10,11}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h | h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_left
    · rw [h]; exact mem_right
    · rw [h]; exact mem_leaf00
    · rw [h]; exact mem_leaf01
    · rw [h]; exact mem_leaf10
    · rw [h]; exact mem_leaf11
    · simp_all


-- @@ L384-384 verbatim
namespace neighborhoodSystem


-- @@ L386-386 verbatim
open NeighborhoodSystem


-- @@ L388-398 verbatim
/-- The bottom element `⊥ = {Δ}` (node `Λ`). -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    simp_all
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY


-- @@ L400-421 verbatim
/-- The partial element `{Δ, left}` (node `0`): the left branch is decided. -/
def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_left
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr h


-- @@ L423-444 verbatim
/-- The partial element `{Δ, right}` (node `1`): the right branch is decided. -/
def elemOne : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_right
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr h


-- @@ L446-477 verbatim
/-- The total element `{Δ, left, leaf00}` (leaf `00`). -/
def elem00 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf00
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf00
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf00)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf00_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf00_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)


-- @@ L479-479 verbatim
@[simp] theorem elem00_mem_leaf00 : elem00.mem leaf00 := Or.inr (Or.inr rfl)


-- @@ L481-512 verbatim
/-- The total element `{Δ, left, leaf01}` (leaf `01`). -/
def elem01 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf01
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf01
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf01)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf01_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf01_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)


-- @@ L514-545 verbatim
/-- The total element `{Δ, right, leaf10}` (leaf `10`). -/
def elem10 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf10
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf10
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf10)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf10_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf10_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)


-- @@ L547-578 verbatim
/-- The total element `{Δ, right, leaf11}` (leaf `11`). -/
def elem11 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf11
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf11
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf11)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf11_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf11_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)


-- @@ L580-580 verbatim
/-! ### Filter classification: the seven elements. -/


-- @@ L582-617 verbatim
private theorem mem_leaf00_imp (x : neighborhoodSystem.Element) (h : x.mem leaf00) :
    x = elem00 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf00_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (right ∩ leaf00 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [right, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf00 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf01, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf00 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf10, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf00 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf11, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h


-- @@ L619-654 verbatim
private theorem mem_leaf01_imp (x : neighborhoodSystem.Element) (h : x.mem leaf01) :
    x = elem01 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf01_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (right ∩ leaf01 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [right, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf01 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf00, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf01 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf10, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf01 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf11, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h


-- @@ L656-691 verbatim
private theorem mem_leaf10_imp (x : neighborhoodSystem.Element) (h : x.mem leaf10) :
    x = elem10 := by
  have hright : x.mem right := x.up_mem h mem_right leaf10_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (left ∩ leaf10 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [left, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf10 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf00, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf10 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf01, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf10 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf11, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h


-- @@ L693-728 verbatim
private theorem mem_leaf11_imp (x : neighborhoodSystem.Element) (h : x.mem leaf11) :
    x = elem11 := by
  have hright : x.mem right := x.up_mem h mem_right leaf11_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (left ∩ leaf11 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [left, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf11 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf00, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf11 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf01, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf11 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [leaf10, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h


-- @@ L730-759 verbatim
private theorem mem_left_imp (x : neighborhoodSystem.Element) (hl : x.mem left)
    (h00 : ¬x.mem leaf00) (h01 : ¬x.mem leaf01) : x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ right : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [left, right]] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h00
    · exact absurd hx h01
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ leaf10 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [left, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ leaf11 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [left, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hl


-- @@ L761-790 verbatim
private theorem mem_right_imp (x : neighborhoodSystem.Element) (hr : x.mem right)
    (h10 : ¬x.mem leaf10) (h11 : ¬x.mem leaf11) : x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ left : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [right, left]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ leaf00 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [right, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ leaf01 : Set Token) = ∅ from by
        ext t; fin_cases t <;> simp [right, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hr


-- @@ L792-824 verbatim
/-- **Example 1.4 classification.** Every filter is one of the seven: the bottom
`⊥`, the two
branch partials `elemZero`/`elemOne`, or one of the four total leaf elements. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne ∨ x = elem00 ∨ x = elem01 ∨ x = elem10 ∨ x = elem11 := by
  by_cases h00 : x.mem leaf00
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf00_imp x h00))))
  by_cases h01 : x.mem leaf01
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf01_imp x h01)))))
  by_cases h10 : x.mem leaf10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf10_imp x h10))))))
  by_cases h11 : x.mem leaf11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_leaf11_imp x h11))))))
  by_cases hl : x.mem left
  · exact Or.inr (Or.inl (mem_left_imp x hl h00 h01))
  by_cases hr : x.mem right
  · exact Or.inr (Or.inr (Or.inl (mem_right_imp x hr h10 h11)))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hx hl
    · exact absurd hx hr
    · exact absurd hx h00
    · exact absurd hx h01
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rw [hx]
    exact x.master_mem


-- @@ L826-826 verbatim
/-! ### The approximation order (Definition 1.8): a branching tree. -/


-- @@ L828-832 verbatim
theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact left_ne_master (h left (Or.inr rfl))


-- @@ L834-838 verbatim
theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact right_ne_master (h right (Or.inr rfl))


-- @@ L840-849 verbatim
theorem elemZero_lt_elem00 : elemZero < elem00 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf00 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf00_ne_master h1
    · exact leaf00_ne_left h1


-- @@ L851-860 verbatim
theorem elemZero_lt_elem01 : elemZero < elem01 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf01 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf01_ne_master h1
    · exact leaf01_ne_left h1


-- @@ L862-871 verbatim
theorem elemOne_lt_elem10 : elemOne < elem10 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf10 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf10_ne_master h1
    · exact leaf10_ne_right h1


-- @@ L873-882 verbatim
theorem elemOne_lt_elem11 : elemOne < elem11 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf11 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf11_ne_master h1
    · exact leaf11_ne_right h1


-- @@ L884-885 verbatim
theorem elem00_maximal (x : neighborhoodSystem.Element) (h : elem00 ≤ x) : x = elem00 :=
  mem_leaf00_imp x (h leaf00 (Or.inr (Or.inr rfl)))


-- @@ L887-888 verbatim
theorem elem01_maximal (x : neighborhoodSystem.Element) (h : elem01 ≤ x) : x = elem01 :=
  mem_leaf01_imp x (h leaf01 (Or.inr (Or.inr rfl)))


-- @@ L890-891 verbatim
theorem elem10_maximal (x : neighborhoodSystem.Element) (h : elem10 ≤ x) : x = elem10 :=
  mem_leaf10_imp x (h leaf10 (Or.inr (Or.inr rfl)))


-- @@ L893-894 verbatim
theorem elem11_maximal (x : neighborhoodSystem.Element) (h : elem11 ≤ x) : x = elem11 :=
  mem_leaf11_imp x (h leaf11 (Or.inr (Or.inr rfl)))


-- @@ L896-896 verbatim
end neighborhoodSystem


-- @@ L898-898 verbatim
end Domain.Neighborhood.Example14
