/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Example43
public import LeanPool.DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L17-60 verbatim
/-!
# Exercise 4.25 (Scott 1981, PRG-19, Lecture IV) — the unary sequence domain `C₁`

*"Perhaps the domains `N` and `C` are not exactly analogous?"* `C` (Example 4.4)
was built over the
two-letter alphabet `{0,1}`. Scott asks to build the analogue `C₁` over `{1}*` —
finite strings of
`1`s, which we encode by their length `n ∈ ℕ` (so `1ⁿ ↔ n`). The neighbourhoods
are the **tails**
and the **singletons**:

`C₁ = {{1ᵐ ∣ m ≥ n} ∣ n ∈ ℕ} ∪ {{1ⁿ} ∣ n ∈ ℕ}`     (`tail n = {m ∣ n ≤ m}`,
`{n}`).

This is again a nested-or-disjoint system (`ofNestedOrDisjoint`): the tails form a
descending chain
and a singleton is either inside a tail or disjoint from it. The total elements
are the finite
strings `1ⁿ` (`oneElem n = ↑{n}`) and the partial elements `1ⁿ⊥` ("at least `n`
ones",
`oneBot n = ↑(tail n)`).

The structure **analogous to `C`** is the single successor `x ↦ 1x` (`consMap`,
prepending a `1`,
i.e. shifting the length up by one), with `consMap_oneElem`/`consMap_oneBot`.
Crucially — and this is
Scott's point that `N` and `C` are *not* analogous — `C₁` is **not flat** like
`N`: the successor has
a genuine *infinite* fixed point `1^∞ = 1·1^∞` (`infElt`, `infElt_eq`), the limit
`⊔ₙ 1ⁿ⊥` of the
tails, which has no counterpart among the elements `⊥, 0̂, 1̂, 2̂, …` of the flat
domain `N`. So `C₁`
is the genuine unary analogue of `C` (`= C₂`), distinct from `N`.

Finally, the systems are **related by approximable maps**: e.g. `relateNToC1 : N →
C₁` sends the
numeral `n̂` to the finite string `1ⁿ` and is strict (`⊥ ↦ ⊥`) — the natural
"length ↦ unary
expansion" map (`relateNToC1_natElem`, `relateNToC1_bot`).

The data (`C₁`, `consMap`, `relateNToC1`) is **choice-free** (`#print axioms ⊆
{propext,
Quot.sound}`).
-/


-- @@ L62-62 verbatim
@[expose] public section


-- @@ L64-64 verbatim
namespace Domain.Neighborhood.Exercise425


-- @@ L66-66 verbatim
open Domain.Neighborhood NeighborhoodSystem ApproximableMap


-- @@ L68-68 verbatim
/-! ### Tails, singletons, and the shift. -/


-- @@ L70-72 verbatim
/-- The tail `tail n = {1ᵐ ∣ m ≥ n} = {m ∣ n ≤ m}` (the partial information "at
least `n` ones"). -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}


-- @@ L74-77 verbatim
/-- Shifting a set up by one length: `shift X = {m + 1 ∣ m ∈ X}` (the token action
of prepending a
`1`). -/
def shift (X : Set ℕ) : Set ℕ := {k | ∃ m ∈ X, k = m + 1}


-- @@ L79-79 verbatim
theorem tail_zero : tail 0 = Set.univ := by ext k; simp [tail]


-- @@ L81-81 verbatim
@[simp] theorem mem_tail {n k : ℕ} : k ∈ tail n ↔ n ≤ k := Iff.rfl


-- @@ L83-89 verbatim
/-- `1·(1ⁿ⊥) = 1ⁿ⁺¹⊥`: shifting a tail. -/
theorem shift_tail (n : ℕ) : shift (tail n) = tail (n + 1) := by
  ext k
  simp only [shift, tail, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨k - 1, by omega, by omega⟩


-- @@ L91-95 verbatim
/-- `1·{1ⁿ} = {1ⁿ⁺¹}`: shifting a singleton. -/
theorem shift_singleton (n : ℕ) : shift ({n} : Set ℕ) = {n + 1} := by
  ext k
  simp only [shift, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  simp_all


-- @@ L97-98 verbatim
theorem shift_mono {X X' : Set ℕ} (h : X' ⊆ X) : shift X' ⊆ shift X := by
  rintro k ⟨m, hm, rfl⟩; exact ⟨m, h hm, rfl⟩


-- @@ L100-100 verbatim
/-! ### The neighbourhood system `C₁`. -/


-- @@ L102-103 verbatim
/-- Membership in `C₁`: a neighbourhood is a tail `tail n` or a singleton `{n}`. -/
def memC1 (X : Set ℕ) : Prop := (∃ n, X = tail n) ∨ (∃ n, X = {n})


-- @@ L105-105 verbatim
theorem memC1_tail (n : ℕ) : memC1 (tail n) := Or.inl ⟨n, rfl⟩


-- @@ L107-107 verbatim
theorem memC1_singleton (n : ℕ) : memC1 ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩


-- @@ L109-109 verbatim
theorem memC1_univ : memC1 (Set.univ : Set ℕ) := Or.inl ⟨0, tail_zero.symm⟩


-- @@ L111-116 verbatim
/-- Shifting keeps us inside `C₁` (`shift (tail n) = tail (n+1)`, `shift {n} =
{n+1}`). -/
theorem memC1_shift {X : Set ℕ} (hX : memC1 X) : memC1 (shift X) := by
  rcases hX with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact Or.inl ⟨n + 1, shift_tail n⟩
  · exact Or.inr ⟨n + 1, shift_singleton n⟩


-- @@ L118-123 verbatim
/-- A singleton and a tail are nested or disjoint. -/
theorem singleton_tail_nd (n k : ℕ) :
    ({k} : Set ℕ) ⊆ tail n ∨ tail n ⊆ {k} ∨ ({k} : Set ℕ) ∩ tail n = ∅ := by
  by_cases h : n ≤ k
  · exact Or.inl (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  · simp_all


-- @@ L125-141 verbatim
/-- Any two neighbourhoods of `C₁` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC1 := by
  rintro X Y (⟨n, rfl⟩ | ⟨n, rfl⟩) (⟨m, rfl⟩ | ⟨m, rfl⟩)
  · rcases le_total n m with h | h
    · exact Or.inr (Or.inl (fun k hk => le_trans h hk))
    · exact Or.inl (fun k hk => le_trans h hk)
  · rcases singleton_tail_nd n m with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_tail_nd m n with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · simp_all


-- @@ L143-147 verbatim
/-- **Exercise 4.25 (Scott 1981, PRG-19).** The unary sequence system `C₁` on `Δ =
{1}* ≅ ℕ`. -/
def C1 : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memC1 Set.univ memC1_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)


-- @@ L149-149 verbatim
@[simp] theorem C1_mem {X : Set ℕ} : C1.mem X ↔ memC1 X := Iff.rfl


-- @@ L151-151 verbatim
@[simp] theorem C1_master : C1.master = (Set.univ : Set ℕ) := rfl


-- @@ L153-153 verbatim
/-! ### Elements: `1ⁿ` (total) and `1ⁿ⊥` (partial). -/


-- @@ L155-156 verbatim
/-- The partial element `1ⁿ⊥ = ↑(tail n)` ("at least `n` ones"). -/
def oneBot (n : ℕ) : C1.Element := C1.principal (memC1_tail n)


-- @@ L158-159 verbatim
/-- The total element `1ⁿ = ↑{n}` (the finite string of exactly `n` ones). -/
def oneElem (n : ℕ) : C1.Element := C1.principal (memC1_singleton n)


-- @@ L161-161 verbatim
/-! ### The successor `x ↦ 1x`. -/


-- @@ L163-178 verbatim
/-- **Exercise 4.25 — the successor `x ↦ 1x`** (analogous to the two successors of
`C`). The
approximable map prepending a `1`, i.e. shifting the length: `X (1x) Y ↔ shift X ⊆
Y`. -/
def consMap : ApproximableMap C1 C1 where
  rel X Y := memC1 X ∧ memC1 Y ∧ shift X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨memC1_univ, memC1_univ, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : shift X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, C1.inter_mem hY hY' (memC1_shift hX) hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (shift_mono hX'X).trans (hsub.trans hYY')⟩


-- @@ L180-191 verbatim
/-- `1·(1ⁿ⊥) = 1ⁿ⁺¹⊥`. -/
theorem consMap_oneBot (n : ℕ) : consMap.toElementMap (oneBot n) = oneBot (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift (tail n) ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_tail] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨tail n, ⟨memC1_tail n, subset_rfl⟩, memC1_tail n, hY, ?_⟩
    rw [shift_tail]; exact hsub


-- @@ L193-204 verbatim
/-- `1·(1ⁿ) = 1ⁿ⁺¹`. -/
theorem consMap_oneElem (n : ℕ) : consMap.toElementMap (oneElem n) = oneElem (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift {n} ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{n}, ⟨memC1_singleton n, subset_rfl⟩, memC1_singleton n, hY, ?_⟩
    rw [shift_singleton]; exact hsub


-- @@ L206-206 verbatim
/-! ### The infinite element `1^∞ = 1·1^∞`. -/


-- @@ L208-215 verbatim
/-- **Exercise 4.25 — the infinite unary sequence `1^∞`.** Unlike the flat domain
`N` (whose only
elements are `⊥` and the numerals `n̂`), `C₁` has a genuine *infinite* element:
the least fixed point
of the successor `x ↦ 1x`, satisfying `1^∞ = 1·1^∞` (`infElt_eq`). This is what
distinguishes the
*non-flat* `C₁` (the true analogue of `C`) from `N`. -/
def infElt : C1.Element := consMap.fixElement


-- @@ L217-219 verbatim
/-- `1^∞ = 1·1^∞`: the infinite sequence is fixed by the successor. -/
theorem infElt_eq : consMap.toElementMap infElt = infElt :=
  toElementMap_fixElement consMap


-- @@ L221-221 verbatim
/-! ### An approximable map relating `N` and `C₁`. -/


-- @@ L223-228 verbatim
/-- **Exercise 4.25 — relating `N` and `C₁`.** The "length ↦ unary expansion" map
`N → C₁` sending
the numeral `n̂` to the finite string `1ⁿ` and `⊥` to `⊥` (strict). Built from the
strict-lift
combinator `constLiftN` of Example 4.3. -/
def relateNToC1 : ApproximableMap Example43.N C1 := Example43.constLiftN C1 oneElem


-- @@ L230-233 verbatim
/-- `relateNToC1(n̂) = 1ⁿ`. -/
theorem relateNToC1_natElem (n : ℕ) :
    relateNToC1.toElementMap (Example43.natElem n) = oneElem n :=
  Example43.constLiftN_natElem C1 oneElem n


-- @@ L235-237 verbatim
/-- `relateNToC1(⊥) = ⊥`. -/
theorem relateNToC1_bot : relateNToC1.toElementMap Example43.N.bot = C1.bot :=
  Example43.constLiftN_bot C1 oneElem


-- @@ L239-239 verbatim
end Domain.Neighborhood.Exercise425
