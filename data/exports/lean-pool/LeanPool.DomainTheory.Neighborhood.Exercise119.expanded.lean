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


-- @@ L13-40 verbatim
/-!
# Exercise 1.19 (Scott 1981, PRG-19, §1) — positive neighbourhood systems

Scott replaces condition (ii) of Definition 1.1 by the biconditional **(ii′)**:
whenever
`X, Y ∈ 𝒟`, then `X ∩ Y ≠ ∅ iff X ∩ Y ∈ 𝒟`. The predicate `IsPositive` and the
builder
`ofPositive` (positive ⟹ neighbourhood system) live in `Basic.lean`.

This file supplies the two examples requested by the exercise:

* `positiveExample` — a genuinely *positive* system (all non-empty subsets of `Δ`,
built with
  `ofPositive`), with `positiveExample_isPositive`;
* a *non-positive* neighbourhood system `notPositiveSystem` over `Δ = {0,1,2}`
with
  `𝒟 = {Δ, {0,1}, {1,2}}`. It satisfies Definition 1.1 (the only overlapping pair
  `{0,1}`,
  `{1,2}` has intersection `{1}`, which has **no** consistency witness in `𝒟`, so
  (ii) never
  fires) yet fails (ii′): `{0,1} ∩ {1,2} = {1}` is non-empty but is not a
  neighbourhood
  (`not_isPositive`). This is a small stand-in for Hoare's `ℕ × ℕ` example (Scott
  notes
  "smaller examples are of course possible").

Everything is `[propext, Quot.sound]`.
-/


-- @@ L42-42 verbatim
@[expose] public section


-- @@ L44-44 verbatim
namespace Domain.Neighborhood.Exercise119


-- @@ L46-46 verbatim
open Domain.Neighborhood


-- @@ L48-48 verbatim
/-! ### A positive system: all non-empty subsets of `Fin 2`. -/


-- @@ L50-56 verbatim
/-- All non-empty subsets of `Fin 2` form a *positive* neighbourhood system: there
`X ∩ Y ∈ 𝒟`
literally **is** `(X ∩ Y).Nonempty`, so (ii′) is `Iff.rfl`. -/
def positiveExample : NeighborhoodSystem (Fin 2) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩) (by intro X _; exact Set.subset_univ X)
    (by intro X Y _ _; exact Iff.rfl)


-- @@ L58-60 verbatim
theorem positiveExample_isPositive : positiveExample.IsPositive := by
  intro X Y _ _
  exact Iff.rfl


-- @@ L62-62 verbatim
/-! ### A non-positive system over `Δ = {0,1,2}`. -/


-- @@ L64-65 verbatim
/-- Tokens `Δ = {0, 1, 2}`. -/
abbrev Tok := Fin 3


-- @@ L67-68 verbatim
/-- The master neighbourhood `Δ`. -/
def master : Set Tok := Set.univ


-- @@ L70-71 verbatim
/-- The neighbourhood `{0, 1}`. -/
def a : Set Tok := {0, 1}


-- @@ L73-74 verbatim
/-- The neighbourhood `{1, 2}`. -/
def b : Set Tok := {1, 2}


-- @@ L76-77 verbatim
/-- `𝒟 = {Δ, {0,1}, {1,2}}`. -/
def memSet : Set (Set Tok) := {master, a, b}


-- @@ L79-80 verbatim
/-- Membership in `𝒟`. -/
def mem (X : Set Tok) : Prop := X ∈ memSet


-- @@ L82-83 verbatim
theorem mem_iff (X : Set Tok) : mem X ↔ X = master ∨ X = a ∨ X = b := by
  simp only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff]


-- @@ L85-85 verbatim
theorem mem_master : mem master := (mem_iff _).mpr (Or.inl rfl)

-- @@ L86-86 verbatim
theorem mem_a : mem a := (mem_iff _).mpr (Or.inr (Or.inl rfl))

-- @@ L87-87 verbatim
theorem mem_b : mem b := (mem_iff _).mpr (Or.inr (Or.inr rfl))


-- @@ L89-90 verbatim
/-- `{0,1} ∩ {1,2} = {1}`. -/
theorem a_inter_b : a ∩ b = ({1} : Set Tok) := by ext x; fin_cases x <;> simp [a, b]


-- @@ L92-101 verbatim
/-- `{1}` is not a neighbourhood (it is neither `Δ`, `{0,1}`, nor `{1,2}`). -/
theorem one_not_mem : ¬ mem ({1} : Set Tok) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h
  · have h0 : (0 : Tok) ∈ master := by simp [master]
    rw [← h] at h0; simp at h0
  · have h0 : (0 : Tok) ∈ a := by simp [a]
    rw [← h] at h0; simp at h0
  · have h2 : (2 : Tok) ∈ b := by simp [b]
    rw [← h] at h2; simp at h2


-- @@ L103-110 verbatim
/-- No neighbourhood is contained in `{1}` (each contains a token other than `1`).
This is why
the overlapping pair `{0,1}`, `{1,2}` never triggers condition (ii). -/
theorem not_mem_sub_one {Z : Set Tok} (hZ : mem Z) (hsub : Z ⊆ ({1} : Set Tok)) : False := by
  rcases (mem_iff Z).mp hZ with rfl | rfl | rfl
  · exact absurd (hsub (show (0 : Tok) ∈ master by simp [master])) (by simp)
  · exact absurd (hsub (show (0 : Tok) ∈ a by simp [a])) (by simp)
  · exact absurd (hsub (show (2 : Tok) ∈ b by simp [b])) (by simp)


-- @@ L112-127 verbatim
/-- Classification of binary intersections in `𝒟`. -/
theorem inter_eq (X Y : Set Tok) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = a ∨ X ∩ Y = b ∨ X ∩ Y = ({1} : Set Tok) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inl (by ext x; fin_cases x <;> simp [master])
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a]))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a]))
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [a]))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, b])))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [a, b])))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [b])))


-- @@ L129-145 verbatim
/-- **Exercise 1.19 — the non-positive example is a neighbourhood system.** The
only intersection
that is not already a neighbourhood is `{0,1} ∩ {1,2} = {1}`, and that case is
impossible: a
consistency witness `Z ⊆ {1}` with `Z ∈ 𝒟` does not exist (`not_mem_sub_one`). -/
def notPositiveSystem : NeighborhoodSystem Tok where
  mem := mem
  master := master
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_a
    · rw [h]; exact mem_b
    · rw [h] at hZsub; exact (not_mem_sub_one hZ hZsub).elim


-- @@ L147-154 verbatim
/-- **Exercise 1.19 — the example is not positive.** `{0,1}` and `{1,2}` are
neighbourhoods whose
intersection `{1}` is non-empty but is *not* a neighbourhood, contradicting (ii′). -/
theorem not_isPositive : ¬ notPositiveSystem.IsPositive := by
  intro h
  have hab := h (X := a) (Y := b) mem_a mem_b
  rw [a_inter_b] at hab
  exact one_not_mem (hab.mpr ⟨1, rfl⟩)


-- @@ L156-156 verbatim
end Domain.Neighborhood.Exercise119
