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


-- @@ L13-27 verbatim
/-!
# Example 1.3 (Scott 1981, PRG-19, §1)

Scott's second worked example: tokens `Δ = {0, 1, 2}` and neighbourhoods
`𝒟 = {{0, 1, 2}, {1, 2}, {2}}`.

We construct the neighbourhood system, prove it satisfies Definition 1.1, and
classify
its domain elements (Definition 1.6): there are exactly three filters in a linear
chain
`⊥ < {Δ,{1,2}} < {Δ,{1,2},{2}}`, with token `2` the sole total element.

This is a concrete finite computation (`fin_cases`/`simp`); footprint
`[propext, Classical.choice, Quot.sound]` — same as Example 1.2.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace Domain.Neighborhood.Example13


-- @@ L33-34 verbatim
/-- Tokens for Example 1.3: `Δ = {0, 1, 2}`. -/
abbrev Token := Fin 3


-- @@ L36-37 verbatim
/-- The master neighbourhood `Δ = {0, 1, 2}`. -/
def master : Set Token := Set.univ


-- @@ L39-40 verbatim
/-- The neighbourhood `{1, 2}`. -/
def twelve : Set Token := (insert 2 {1} : Set Token)


-- @@ L42-43 verbatim
/-- The neighbourhood `{2}`. -/
def two : Set Token := {2}


-- @@ L45-46 verbatim
/-- The three neighbourhoods of Example 1.3. -/
def memSet : Set (Set Token) := {master, twelve, two}


-- @@ L48-49 verbatim
/-- Membership in the neighbourhood system `𝒟` of Example 1.3. -/
def mem (X : Set Token) : Prop := X ∈ memSet


-- @@ L51-51 verbatim
theorem mem_master : mem master := by simp [mem, memSet, master, twelve, two]

-- @@ L52-52 verbatim
theorem mem_twelve : mem twelve := by simp [mem, memSet, master, twelve, two]

-- @@ L53-53 verbatim
theorem mem_two : mem two := by simp [mem, memSet, master, twelve, two]


-- @@ L55-69 verbatim
/-- A neighbourhood of Example 1.3 is exactly one of `Δ`, `{1,2}`, or `{2}`. -/
theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = twelve ∨ X = two := by
  constructor
  · intro h
    simp only [mem, memSet, master, twelve, two, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two


-- @@ L71-76 verbatim
private theorem twelve_ne_master : twelve ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ twelve := by
    rw [h]
    simp [master]
  simp [twelve] at hmem


-- @@ L78-83 verbatim
private theorem two_ne_master : two ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ two := by
    rw [h]
    simp [master]
  simp [two] at hmem


-- @@ L85-90 verbatim
private theorem two_ne_twelve : two ≠ twelve := by
  intro h
  have hmem : (1 : Token) ∈ two := by
    rw [h]
    simp [twelve]
  simp [two] at hmem


-- @@ L92-95 verbatim
private theorem master_not_subset_twelve : ¬master ⊆ twelve := by
  intro h
  have : (0 : Token) ∈ twelve := h (by simp [master])
  simp [twelve] at this


-- @@ L97-100 verbatim
private theorem master_not_subset_two : ¬master ⊆ two := by
  intro h
  have : (0 : Token) ∈ two := h (by simp [master])
  simp [two] at this


-- @@ L102-105 verbatim
private theorem twelve_not_subset_two : ¬twelve ⊆ two := by
  intro h
  have : (1 : Token) ∈ two := h (by simp [twelve])
  simp [two] at this


-- @@ L107-112 verbatim
private theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) :
  Y = master := by
  rcases (mem_iff Y).mp h with rfl | htwelve | htwo
  · rfl
  · exact absurd htwelve (fun h' => master_not_subset_twelve (h' ▸ hsub))
  · exact absurd htwo (fun h' => master_not_subset_two (h' ▸ hsub))


-- @@ L114-115 verbatim
private theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A


-- @@ L117-118 verbatim
private theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A


-- @@ L120-122 verbatim
private theorem twelve_inter_two : twelve ∩ two = two := by
  ext t
  fin_cases t <;> simp [twelve, two]


-- @@ L124-126 verbatim
private theorem two_inter_twelve : two ∩ twelve = two := by
  ext t
  fin_cases t <;> simp [twelve, two]


-- @@ L128-140 verbatim
private theorem inter_eq (X Y : Set Token) (h : mem X) (h' : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = twelve ∨ X ∩ Y = two := by
  rcases (mem_iff X).mp h with rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp h' with rfl | rfl | rfl
  · exact Or.inl (master_inter _)
  · exact Or.inr (Or.inl (master_inter _))
  · exact Or.inr (Or.inr (master_inter _))
  · exact Or.inr (Or.inl (inter_master _))
  · exact Or.inr (Or.inl (Set.inter_self _))
  · exact Or.inr (Or.inr (twelve_inter_two))
  · exact Or.inr (Or.inr (inter_master _))
  · exact Or.inr (Or.inr (two_inter_twelve))
  · exact Or.inr (Or.inr (Set.inter_self _))


-- @@ L142-153 verbatim
/-- **Example 1.3.** The neighbourhood system on `Δ = {0, 1, 2}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_twelve
    · rw [h]; exact mem_two


-- @@ L155-155 verbatim
namespace neighborhoodSystem


-- @@ L157-157 verbatim
open NeighborhoodSystem


-- @@ L159-169 verbatim
/-- The bottom element `⊥ = {Δ}`. -/
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


-- @@ L171-193 verbatim
/-- The intermediate partial element `{Δ, {1,2}}`. -/
def elemTwelve : neighborhoodSystem.Element where
  mem X := X = master ∨ X = twelve
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_twelve
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
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hXY twelve_not_subset_two


-- @@ L195-227 verbatim
/-- The total element `{Δ, {1,2}, {2}}`. -/
def elemTwo : neighborhoodSystem.Element where
  mem X := X = master ∨ X = twelve ∨ X = two
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr (twelve_inter_two))
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr (two_inter_twelve))
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)


-- @@ L229-231 verbatim
private theorem two_subset_twelve : two ⊆ twelve := by
  intro t ht
  fin_cases t <;> simp [two, twelve] at ht ⊢


-- @@ L233-247 verbatim
private theorem mem_two_of_mem (x : neighborhoodSystem.Element) (h : x.mem two) :
    x = elemTwo := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hX12 | htwo
    · exact Or.inl rfl
    · rw [hX12]; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr htwo)
  · intro hx
    rcases hx with rfl | hx | hx
    · exact x.master_mem
    · rw [hx]; exact x.up_mem h mem_twelve two_subset_twelve
    · rw [hx]; exact h


-- @@ L249-262 verbatim
private theorem mem_twelve_of_mem (x : neighborhoodSystem.Element) (htwelve : x.mem twelve)
    (htwo : ¬x.mem two) : x = elemTwelve := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hX12 | hX2
    · exact Or.inl rfl
    · exact Or.inr hX12
    · simp_all
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact htwelve


-- @@ L264-282 verbatim
/-- Every element of Example 1.3 is one of the three filters in the linear chain. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemTwelve ∨ x = elemTwo := by
  by_cases htwo : x.mem two
  · exact Or.inr (Or.inr (mem_two_of_mem x htwo))
  by_cases htwelve : x.mem twelve
  · exact Or.inr (Or.inl (mem_twelve_of_mem x htwelve htwo))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | htwelve' | htwo'
    · rfl
    · exact absurd (htwelve' ▸ hx) htwelve
    · exact absurd (htwo' ▸ hx) htwo
  · intro hx
    rw [hx]
    exact x.master_mem


-- @@ L284-291 verbatim
theorem bot_lt_elemTwelve : bot < elemTwelve := by
  constructor
  · intro X hx
    rw [hx]
    exact Or.inl rfl
  · intro h
    have : bot.mem twelve := h twelve (Or.inr rfl)
    exact twelve_ne_master this


-- @@ L293-304 verbatim
theorem elemTwelve_lt_elemTwo : elemTwelve < elemTwo := by
  constructor
  · intro X hx
    rcases hx with rfl | hX12
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hX12)
  · intro h
    exfalso
    have ht := h two (Or.inr (Or.inr rfl))
    rcases ht with h1 | h2
    · exact absurd h1 two_ne_master
    · exact two_ne_twelve h2


-- @@ L306-316 verbatim
theorem elemTwo_maximal (x : neighborhoodSystem.Element) (h : elemTwo ≤ x) : x = elemTwo := by
  rcases element_classification x with rfl | rfl | rfl
  · exfalso
    have : bot.mem twelve := h twelve (Or.inr (Or.inl rfl))
    exact twelve_ne_master this
  · exfalso
    have ht := h two (Or.inr (Or.inr rfl))
    rcases ht with h1 | h2
    · exact absurd h1 two_ne_master
    · exact two_ne_twelve h2
  · rfl


-- @@ L318-318 verbatim
end neighborhoodSystem


-- @@ L320-320 verbatim
end Domain.Neighborhood.Example13
