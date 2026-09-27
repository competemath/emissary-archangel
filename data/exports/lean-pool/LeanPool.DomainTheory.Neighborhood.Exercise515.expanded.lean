/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic


-- @@ L12-53 verbatim
/-!
# Exercise 5.15 (Scott 1981, PRG-19, Lecture V) — free-semigroup powerset and
Arden's lemma

> (For algebraists.) Regard `⟨{0,1}*, Λ, ·⟩` as the free semigroup on two
generators. The powerset
> `P{0,1}*` is a domain (Exercise 4.17). For a word `e` set `e* = {Λ, e, e², …}`.
>
> (1) The least fixed point of `z = {e}·z ∪ {e'}` is `z = e*·{e'}`.
> (2) (David Park) The least solution of
> `x = a·x ∪ b·y ∪ c`, `y = b·x ∪ a·y ∪ d`
> is `x = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`, where `z* = Λ ∪ z*·z`.

Following Exercise 4.17, the powerset domain `P S` of a monoid `S` is the complete
lattice
`(Set S, ⊆)` with pointwise product `s·t = {u·v ∣ u ∈ s, v ∈ t}` (`Set.mul`, `open
Pointwise`).
Both parts are facts about the **Kleene algebra** `(Set S, ∪, ·, ∅, {1})` and hold
for *any* monoid;
we prove them with `S` a general `Monoid` and specialise part (1) to `S =
FreeMonoid Bool = {0,1}*`.

## Choice discipline

Mathlib's `Set`-level multiplicative lemmas (`mul_assoc`, `Set.union_mul`,
`Set.mul_union`,
`Set.singleton_mul_singleton`), the order lemmas
`Set.subset_iUnion`/`Set.iUnion_subset`, `Set`-power
(`pow_succ'`), `Submonoid.mem_powers_iff`, and `Monotone` over `Set` all depend on
`Classical.choice`
in this toolchain (they route through `Set.image2`/`CompleteLattice` choice-using
machinery). Every
*membership* iff (`Set.mem_mul`, `Set.mem_union`, `Set.mem_one`,
`Set.mem_singleton_iff`) and every
*element-level* monoid lemma is choice-free. So we reprove the small slice of
Kleene algebra we need
(`smul_assoc`, `sunion_mul`, `smul_union`) at the membership level, define `star`
by an explicit
recursion (`kpow`) rather than `⋃ₙ zⁿ`, and phrase Arden's lemma without
`Monotone` — keeping
everything **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/


-- @@ L55-55 verbatim
@[expose] public section


-- @@ L57-57 verbatim
namespace Domain.Neighborhood.Exercise515


-- @@ L59-59 verbatim
open Pointwise

-- @@ L60-60 verbatim
open Domain.Neighborhood.Exercise414


-- @@ L62-62 verbatim
variable {S : Type*} [Monoid S]


-- @@ L64-64 verbatim
/-! ### A choice-free slice of Kleene algebra on `Set S` -/


-- @@ L66-73 verbatim
/-- Associativity of the pointwise product (membership proof, choice-free). -/
theorem smul_assoc (a b c : Set S) : a * b * c = a * (b * c) := by
  ext s; simp only [Set.mem_mul]
  constructor
  · rintro ⟨u, ⟨p, hp, q, hq, rfl⟩, w, hw, rfl⟩
    exact ⟨p, hp, q * w, ⟨q, hq, w, hw, rfl⟩, by rw [mul_assoc]⟩
  · rintro ⟨p, hp, u, ⟨q, hq, w, hw, rfl⟩, rfl⟩
    exact ⟨p * q, ⟨p, hp, q, hq, rfl⟩, w, hw, by rw [mul_assoc]⟩


-- @@ L75-84 verbatim
/-- Right distributivity `(a ∪ b)·c = a·c ∪ b·c` (choice-free). -/
theorem sunion_mul (a b c : Set S) : (a ∪ b) * c = a * c ∪ b * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, (hu | hu), w, hw, rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, Or.inl hu, w, hw, rfl⟩
    · exact ⟨u, Or.inr hu, w, hw, rfl⟩


-- @@ L86-95 verbatim
/-- Left distributivity `a·(b ∪ c) = a·b ∪ a·c` (choice-free). -/
theorem smul_union (a b c : Set S) : a * (b ∪ c) = a * b ∪ a * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, hu, w, (hw | hw), rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, hu, w, Or.inl hw, rfl⟩
    · exact ⟨u, hu, w, Or.inr hw, rfl⟩


-- @@ L97-97 verbatim
/-! ### The star `z* = ⋃ₙ zⁿ`, by explicit recursion -/


-- @@ L99-102 verbatim
/-- `zⁿ` as an iterated pointwise product (left-recursion `z^{n+1} = z·zⁿ`). -/
def kpow (z : Set S) : ℕ → Set S
  | 0 => 1
  | n + 1 => z * kpow z n


-- @@ L104-104 verbatim
@[simp] theorem kpow_zero (z : Set S) : kpow z 0 = 1 := rfl

-- @@ L105-105 verbatim
@[simp] theorem kpow_succ (z : Set S) (n : ℕ) : kpow z (n + 1) = z * kpow z n := rfl


-- @@ L107-111 verbatim
/-- Scott's `z*`: the set of all finite products of elements of `z` (including the
empty product
`1`). Defined as `{s ∣ ∃ n, s ∈ zⁿ}` to stay choice-free (avoiding `⋃` order
lemmas). -/
def star (z : Set S) : Set S := {s | ∃ n, s ∈ kpow z n}


-- @@ L113-113 verbatim
theorem mem_star {z : Set S} {s : S} : s ∈ star z ↔ ∃ n, s ∈ kpow z n := Iff.rfl


-- @@ L115-136 verbatim
/-- **Scott's unfolding** `z* = Λ ∪ z·z*`. -/
theorem star_eq (z : Set S) : star z = (1 : Set S) ∪ z * star z := by
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨n, hn⟩ := mem_star.mp hs
    cases n with
    | zero =>
        simp_all
    | succ m =>
        rw [kpow_succ, Set.mem_mul] at hn
        obtain ⟨a, ha, t, ht, rfl⟩ := hn
        rw [Set.mem_union]; right
        rw [Set.mem_mul]
        exact ⟨a, ha, t, mem_star.mpr ⟨m, ht⟩, rfl⟩
  · intro s hs
    rw [Set.mem_union] at hs
    rcases hs with h1 | h2
    · exact mem_star.mpr ⟨0, by rw [kpow_zero]; exact h1⟩
    · rw [Set.mem_mul] at h2
      obtain ⟨a, ha, t, ht, rfl⟩ := h2
      obtain ⟨m, hm⟩ := mem_star.mp ht
      exact mem_star.mpr ⟨m + 1, by rw [kpow_succ, Set.mem_mul]; exact ⟨a, ha, t, hm, rfl⟩⟩


-- @@ L138-143 verbatim
/-- `z*·v` is a fixed point of `w ↦ z·w ∪ v`: the star identity `z·(z*·v) ∪ v =
z*·v`. -/
theorem star_mul_isFixed (z v : Set S) : z * (star z * v) ∪ v = star z * v := by
  conv_rhs => rw [star_eq z]
  rw [sunion_mul, one_mul, smul_assoc]
  exact Set.union_comm _ _


-- @@ L145-162 verbatim
/-- For any prefixed point `w₀` of `w ↦ z·w ∪ v` (i.e. `z·w₀ ∪ v ⊆ w₀`), the
candidate `z*·v` is
below `w₀`: the induction `zⁿ·v ⊆ w₀`. -/
theorem star_mul_subset_prefixed (z v x : Set S) (hx : z * x ∪ v ⊆ x) : star z * v ⊆ x := by
  have hvx : v ⊆ x := Set.subset_union_right.trans hx
  have hzx : z * x ⊆ x := Set.subset_union_left.trans hx
  have hpow : ∀ n, kpow z n * v ⊆ x := by
    intro n
    induction n with
    | zero => rw [kpow_zero, one_mul]; exact hvx
    | succ m ih =>
        rw [kpow_succ, smul_assoc]
        exact (Set.mul_subset_mul_left ih).trans hzx
  intro s hs
  rw [Set.mem_mul] at hs
  obtain ⟨a, ha, t, ht, rfl⟩ := hs
  obtain ⟨n, hn⟩ := mem_star.mp ha
  exact hpow n (by rw [Set.mem_mul]; exact ⟨a, hn, t, ht, rfl⟩)


-- @@ L164-164 verbatim
/-! ### Arden's lemma -/


-- @@ L166-169 verbatim
/-- Scott's operator `w ↦ z·w ∪ v`, whose least fixed point is the least solution
of `w = z·w ∪
v`. -/
def G (z v : Set S) (w : Set S) : Set S := z * w ∪ v


-- @@ L171-180 verbatim
/-- **Arden's lemma.** The least solution of `w = z·w ∪ v` in `P S` is `z*·v`.
(Stated via
`lfpSet`, Exercise 4.14; the proof uses neither `Monotone` nor `⋃` order lemmas,
so it is
choice-free.) -/
theorem arden (z v : Set S) : lfpSet (G z v) = star z * v := by
  apply Set.Subset.antisymm
  · exact lfpSet_least (G z v) (star_mul_isFixed z v)
  · intro s hs x hx
    exact star_mul_subset_prefixed z v x hx hs


-- @@ L182-182 verbatim
/-! ### Part (1): the single equation `z = {e}·z ∪ {e'}` -/


-- @@ L184-192 verbatim
/-- `{e}ⁿ = {eⁿ}` at the membership level (choice-free). -/
theorem mem_kpow_singleton (e s : S) (n : ℕ) : s ∈ kpow ({e} : Set S) n ↔ s = e ^ n := by
  induction n generalizing s with
  | zero => rw [kpow_zero, pow_zero]; exact Set.mem_one
  | succ m ih =>
      rw [kpow_succ, pow_succ', Set.mem_mul]
      constructor
      · simp_all
      · simp_all


-- @@ L194-200 verbatim
/-- `{e}* = e* = {Λ, e, e², …}`: a point lies in `star {e}` iff it is some power
of `e`. -/
theorem mem_star_singleton (e s : S) : s ∈ star ({e} : Set S) ↔ ∃ n, s = e ^ n := by
  rw [mem_star]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_kpow_singleton e s n).mp hn⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, (mem_kpow_singleton e (e ^ n) n).mpr rfl⟩


-- @@ L202-208 verbatim
/-- **Exercise 5.15(1).** The least fixed point of `z = {e}·z ∪ {e'}` is `e*·{e'}`
(`star {e}` is
`e*` by `mem_star_singleton`). -/
theorem part1 (e e' : S) :
    lfpSet (fun w => ({e} : Set S) * w ∪ {e'}) = star ({e} : Set S) * {e'} := by
  have hG : (fun w => ({e} : Set S) * w ∪ {e'}) = G ({e} : Set S) {e'} := rfl
  rw [hG]; exact arden {e} {e'}


-- @@ L210-215 verbatim
/-- The free semigroup `{0,1}*` of the exercise. Part (1) holds here as a special
case. -/
theorem part1_freeMonoid (e e' : FreeMonoid Bool) :
    lfpSet (fun w => ({e} : Set (FreeMonoid Bool)) * w ∪ {e'})
      = star ({e} : Set (FreeMonoid Bool)) * {e'} :=
  part1 e e'


-- @@ L217-217 verbatim
/-! ### Part (2): David Park's simultaneous system -/


-- @@ L219-220 verbatim
/-- The "feedback" coefficient `A = a ∪ b·a*·b` of the eliminated system. -/
def parkA (a b : Set S) : Set S := a ∪ b * star a * b


-- @@ L222-223 verbatim
/-- The "feedback" constant `C = c ∪ b·a*·d`. -/
def parkC (a b c d : Set S) : Set S := c ∪ b * star a * d


-- @@ L225-226 verbatim
/-- Park's least solution for `x`: `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`. -/
def parkX (a b c d : Set S) : Set S := star (parkA a b) * parkC a b c d


-- @@ L228-229 verbatim
/-- The accompanying least solution for `y`: `y₀ = a*·(b·x₀ ∪ d)`. -/
def parkY (a b c d : Set S) : Set S := star a * (b * parkX a b c d ∪ d)


-- @@ L231-238 verbatim
/-- `x₀` satisfies the first equation `x = a·x ∪ b·y ∪ c`. -/
theorem parkX_eq (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c := by
  have hfix : parkA a b * parkX a b c d ∪ parkC a b c d = parkX a b c d :=
    star_mul_isFixed (parkA a b) (parkC a b c d)
  conv_lhs => rw [← hfix]
  simp only [parkA, parkC, parkY, sunion_mul, smul_union, smul_assoc,
    Set.union_comm, Set.union_left_comm]


-- @@ L240-246 verbatim
/-- `y₀` satisfies the second equation `y = b·x ∪ a·y ∪ d`. -/
theorem parkY_eq (a b c d : Set S) :
    parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d := by
  have hfix : a * parkY a b c d ∪ (b * parkX a b c d ∪ d) = parkY a b c d :=
    star_mul_isFixed a (b * parkX a b c d ∪ d)
  conv_lhs => rw [← hfix]
  simp only [Set.union_assoc, Set.union_comm]


-- @@ L248-252 verbatim
/-- **Exercise 5.15(2), existence.** `(x₀, y₀)` solves David Park's system. -/
theorem park_solves (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c ∧
      parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d :=
  ⟨parkX_eq a b c d, parkY_eq a b c d⟩


-- @@ L254-309 verbatim
/-- **Exercise 5.15(2), leastness.** Any solution `(x, y)` of the system dominates
`(x₀, y₀)`. Hence
`(x₀, y₀)` is the *least* solution, and `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)` as
claimed. The proof is
Gaussian elimination: solve the second equation for `y` by `arden`, substitute,
apply `arden`
again. -/
theorem park_least (a b c d : Set S) {x y : Set S}
    (hx : x = a * x ∪ b * y ∪ c) (hy : y = b * x ∪ a * y ∪ d) :
    parkX a b c d ⊆ x ∧ parkY a b c d ⊆ y := by
  have hax : a * x ⊆ x := by
    calc a * x ⊆ a * x ∪ b * y ∪ c := Set.subset_union_left.trans Set.subset_union_left
      _ = x := hx.symm
  have hby : b * y ⊆ x := by
    calc b * y ⊆ a * x ∪ b * y ∪ c := Set.subset_union_right.trans Set.subset_union_left
      _ = x := hx.symm
  have hcx : c ⊆ x := by
    calc c ⊆ a * x ∪ b * y ∪ c := Set.subset_union_right
      _ = x := hx.symm
  have hay : a * y ⊆ y := by
    calc a * y ⊆ b * x ∪ a * y ∪ d := Set.subset_union_right.trans Set.subset_union_left
      _ = y := hy.symm
  have hbx : b * x ⊆ y := by
    calc b * x ⊆ b * x ∪ a * y ∪ d := Set.subset_union_left.trans Set.subset_union_left
      _ = y := hy.symm
  have hdy : d ⊆ y := by
    calc d ⊆ b * x ∪ a * y ∪ d := Set.subset_union_right
      _ = y := hy.symm
  -- The eliminated `y`: `a*·(b·x ∪ d) ⊆ y`.
  have hpre : a * y ∪ (b * x ∪ d) ⊆ y := Set.union_subset hay (Set.union_subset hbx hdy)
  have hyy : star a * (b * x ∪ d) ⊆ y := by
    rw [← arden a (b * x ∪ d)]
    exact lfpSet_subset (G a (b * x ∪ d)) hpre
  -- The decisive identity `(b·a*·b)·x ∪ b·a*·d = b·(a*·(b·x ∪ d))`.
  have key : b * star a * b * x ∪ b * star a * d = b * (star a * (b * x ∪ d)) := by
    simp only [smul_assoc, smul_union]
  -- `x` is a prefixed point of `w ↦ A·w ∪ C`, so `x₀ ⊆ x`.
  have hprefixX : parkA a b * x ∪ parkC a b c d ⊆ x := by
    have hmid : b * star a * b * x ∪ b * star a * d ⊆ x := by
      rw [key]; exact (Set.mul_subset_mul_left hyy).trans hby
    have hm1 : b * star a * b * x ⊆ x := Set.subset_union_left.trans hmid
    have hm2 : b * star a * d ⊆ x := Set.subset_union_right.trans hmid
    unfold parkA parkC
    rw [sunion_mul]
    exact Set.union_subset (Set.union_subset hax hm1) (Set.union_subset hcx hm2)
  have hPX : parkX a b c d ⊆ x := by
    have harden : parkX a b c d = lfpSet (G (parkA a b) (parkC a b c d)) :=
      (arden (parkA a b) (parkC a b c d)).symm
    rw [harden]
    exact lfpSet_subset (G (parkA a b) (parkC a b c d)) hprefixX
  have hPY : parkY a b c d ⊆ y := by
    change star a * (b * parkX a b c d ∪ d) ⊆ y
    have h1 : b * parkX a b c d ∪ d ⊆ b * x ∪ d :=
      Set.union_subset_union_left d (Set.mul_subset_mul_left hPX)
    exact (Set.mul_subset_mul_left h1).trans hyy
  exact ⟨hPX, hPY⟩


-- @@ L311-311 verbatim
end Domain.Neighborhood.Exercise515
