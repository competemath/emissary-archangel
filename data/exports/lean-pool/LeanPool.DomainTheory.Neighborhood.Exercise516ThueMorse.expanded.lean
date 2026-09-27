/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Exercise516
public import Mathlib.Data.Nat.Bits
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF


-- @@ L18-65 verbatim
/-!
# Exercise 5.16 follow-up (Scott 1981, PRG-19, Lecture V) — the Thue–Morse
sequence `t`

The unfinished tail of Exercise 5.16. Returning to the domain `C` of
finite/infinite binary
sequences (Example 4.4), Scott studies the element

`t = 0·merge(neg t, tail t)`,

the least fixed point of `Φ(x) = 0·merge(neg x, tail x)`, and (Lambek's
observation) identifies its
`n`-th digit with the parity of the binary digits of `n` — the **Thue–Morse
sequence**.

This module formalizes:

* **Step 0 — the element and its unfolding.** `tElt := Φ.fixElement` and
`tElt_unfold` proving
  `t = 0·merge(neg t, tail t)`.
* **The Thue–Morse morphism `expand`** (the substitution `0 ↦ 01`, `1 ↦ 10`) and
the key bridge
  `Phi_strBot_expand`: applied to a partial element `(0σ)⊥`, the operator `Φ` is
  exactly `expand`.
  Consequently the finite approximants of the least fixed point are `Φⁿ⁺¹(⊥) =
  (expandⁿ[0])⊥`
  (`iterElem_succ_eq`).
* **The parity bit-function `tm`** with `tm n = ⊕ (binary digits of n)` (via
`Nat.bits`), its
  recurrences `tm (2n) = tm n`, `tm (2n+1) = ¬ tm n`, and the bridge
  `expand_iterate_eq` showing the
  approximant strings are precisely the Thue–Morse parity prefixes `tmList (2ⁿ)`.
* **Property (a) — the digit characterization.** `tElt_mem_cone_iff`: a finite
string `σ` is a prefix
  of `t` **iff** `σ` is the length-`σ.length` Thue–Morse prefix (`σ = tmList
  σ.length`); and the
  digit reading `tElt_digit : (tmList n ++ [tm n])⊥ ≤ t`, i.e. the `n`-th digit of
  `t` is `tm n`,
  the parity of the binary digits of `n` (Lambek).

The `tElt` *data* is choice-free; the `Prop`-level digit facts may use
`Classical.choice` (through the
project's `eq_of_toElementMap_principal` and the truth-domain primitives), exactly
like the existing
uniqueness lemmas. Overlap-freeness (property (b)) is a self-contained
word-combinatorics theorem and
lives in its own module.
-/


-- @@ L67-67 verbatim
@[expose] public section


-- @@ L69-69 verbatim
namespace Domain.Neighborhood.Exercise516


-- @@ L71-71 verbatim
open Domain.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


-- @@ L73-73 verbatim
/-! ### The Thue–Morse morphism `expand` (`0 ↦ 01`, `1 ↦ 10`). -/


-- @@ L75-79 verbatim
/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b
(¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ


-- @@ L81-81 verbatim
@[simp] theorem expand_nil : expand [] = [] := rfl


-- @@ L83-83 verbatim
@[simp] theorem expand_cons (b : Bool) (σ : Str) : expand (b :: σ) = b :: (!b) :: expand σ := rfl


-- @@ L85-89 verbatim
/-- `expand` distributes over append (it is a monoid morphism `Σ* → Σ*`). -/
theorem expand_append (σ τ : Str) : expand (σ ++ τ) = expand σ ++ expand τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]


-- @@ L91-91 verbatim
/-! ### `Φ` on a partial element computes by interleaving — and equals `expand`. -/


-- @@ L93-100 verbatim
/-- The second (total/partial-flag) component of an interleaving with a partial
first input is
always
`false`: a partial input keeps the output partial. -/
theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁


-- @@ L102-111 verbatim
/-- The interleaving of `h :: flip ρ` with `ρ` (both starting after a common head
`h`) is
`h :: expand ρ`. This is the heart of why `Φ` *is* the Thue–Morse morphism on the
trajectory. -/
theorem weave_head : ∀ (h : Bool) (
  ρ : Str), (mergeVal (h :: flip ρ) false ρ false).1 = h :: expand ρ
  | h, [] => rfl
  | h, c :: ρ => by
    simp only [flip_cons, mergeVal_cons_cons, expand_cons]
    rw [weave_head (!c) ρ]


-- @@ L113-116 verbatim
/-- **Exercise 5.16 (the operator `Φ`).** `Φ(x) = 0·merge(neg x, tail x)` as an
approximable map. -/
def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))


-- @@ L118-128 verbatim
/-- The value of `Φ` on a partial element `σ⊥` is `(0 · weave σ)⊥`, the leading
`0` prepended to the
interleaving of `(flip σ)⊥` and `(tail σ)⊥`. -/
theorem tmOp_strBot (σ : Str) :
    tmOp.toElementMap (strBot σ)
      = strBot (false :: (mergeVal (flip σ) false σ.tail false).1) := by
  unfold tmOp
  rw [toElementMap_comp, toElementMap_comp, toElementMap_paired, negMap_strBot, tailMap_strBot,
    show (strBot (flip σ)) = shapeElem false (flip σ) from rfl,
    show (strBot σ.tail) = shapeElem false σ.tail from rfl, mergeMap_pair, mergeElem,
    mergeVal_snd_false, shapeElem_false, consMap_strBot]


-- @@ L130-138 verbatim
/-- **The Thue–Morse trajectory.** On a partial element whose string starts with
`0`, `Φ` acts
as the
Thue–Morse morphism `expand`. -/
theorem tmOp_strBot_expand (ρ : Str) :
    tmOp.toElementMap (strBot (false :: ρ)) = strBot (expand (false :: ρ)) := by
  rw [tmOp_strBot]
  simp only [flip_cons, List.tail_cons, expand_cons]
  rw [weave_head (!false) ρ]


-- @@ L140-141 verbatim
/-! ### The finite approximants of the least fixed point are the morphism
iterates. -/


-- @@ L143-146 verbatim
/-- The base of the iterated bottom element: `f⁰(⊥) = ⊥`. -/
theorem iterElem_zero' {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) :
    f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]


-- @@ L148-152 verbatim
/-- A one-step unfolding of the iterated bottom element: `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate]
  exact Function.iterate_succ_apply' f.toElementMap n V.bot


-- @@ L154-161 verbatim
/-- Every iterate of `expand` from `[0]` starts with `0` (so `Φ` keeps acting as
`expand`). -/
theorem iterate_expand_cons (k : ℕ) : ∃ ρ, (expand^[k] [false] : Str) = false :: ρ := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨true :: expand ρ, by rw [Function.iterate_succ_apply', hρ]; rfl⟩


-- @@ L163-169 verbatim
/-- `⊥ = []⊥` in `C` (the cone of `Λ` is the master). -/
theorem strBot_nil : strBot [] = C.bot := by
  apply Element.ext
  intro Y
  rw [strBot, mem_principal, mem_bot, cone_nil, C_master]
  exact ⟨fun h => Set.Subset.antisymm (Set.subset_univ _) h.2,
    fun h => ⟨h ▸ C.master_mem, h ▸ Set.Subset.refl _⟩⟩


-- @@ L171-183 verbatim
/-- **Exercise 5.16 (the approximants).** The `(k+1)`-st approximant of the least
fixed point is the
partial element of the `k`-fold Thue–Morse morphism iterate of `[0]`:
`Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`. -/
theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero', ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']


-- @@ L185-185 verbatim
/-! ### The parity bit-function `tm` and its prefixes. -/


-- @@ L187-190 verbatim
/-- The Thue–Morse bit-function: `tm n = ⊕(binary digits of n)`, the parity of the
number of `1`s in
the binary expansion of `n` (Lambek's description). -/
def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false


-- @@ L192-192 verbatim
@[simp] theorem tm_zero : tm 0 = false := by simp [tm, Nat.zero_bits]


-- @@ L194-199 verbatim
/-- The even recurrence `tm (2n) = tm n` (appending a `0`-digit does not change
the parity). -/
theorem tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp only [tm, Nat.bit0_bits n (by omega : n ≠ 0), List.foldr_cons, Bool.false_xor]


-- @@ L201-204 verbatim
/-- The odd recurrence `tm (2n+1) = ¬ tm n` (appending a `1`-digit flips the
parity). -/
theorem tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = !tm n := by
  simp only [tm, Nat.bit1_bits n, List.foldr_cons, Bool.true_xor]


-- @@ L206-207 verbatim
/-- The length-`n` Thue–Morse prefix `[tm 0, tm 1, …, tm (n-1)]`. -/
def tmList (n : ℕ) : Str := (List.range n).map tm


-- @@ L209-209 verbatim
@[simp] theorem tmList_zero : tmList 0 = [] := rfl


-- @@ L211-212 verbatim
theorem tmList_succ (n : ℕ) : tmList (n + 1) = tmList n ++ [tm n] := by
  simp only [tmList, List.range_succ, List.map_append, List.map_cons, List.map_nil]


-- @@ L214-215 verbatim
theorem tmList_length (n : ℕ) : (tmList n).length = n := by
  rw [tmList, List.length_map, List.length_range]


-- @@ L217-224 verbatim
/-- Thue–Morse prefixes are nested in the prefix order. -/
theorem tmList_prefix {n m : ℕ} (h : n ≤ m) : tmList n <+: tmList m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]; exact List.prefix_rfl
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [tmList_succ]; exact List.prefix_append _ _)
    · exact List.prefix_rfl


-- @@ L226-239 verbatim
/-- **The morphism step on prefixes.** `expand (tmList m) = tmList (2m)`: applying
the Thue–Morse
morphism to a length-`m` prefix yields the length-`2m` prefix — this is exactly
the even/odd parity
recurrence in disguise. -/
theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]


-- @@ L241-248 verbatim
/-- **The bridge.** The `k`-fold morphism iterate of `[0]` is the Thue–Morse
parity prefix of length
`2ᵏ`: `expandᵏ[0] = tmList (2ᵏ)`. -/
theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]


-- @@ L250-250 verbatim
/-! ### Step 0 — the element `t` and its unfolding. -/


-- @@ L252-255 verbatim
/-- **Exercise 5.16 (Scott 1981, PRG-19).** Scott's Thue–Morse element `t =
0·merge(neg t, tail t)`,
the least fixed point of `Φ`. -/
def tElt : C.Element := tmOp.fixElement


-- @@ L257-264 verbatim
/-- **Exercise 5.16 — the defining unfolding.** `t = 0·merge(neg t, tail t)`. -/
theorem tElt_unfold :
    (consMap false).toElementMap
        (mergeMap.toElementMap (pair (negMap.toElementMap tElt) (tailMap.toElementMap tElt)))
      = tElt := by
  have h := toElementMap_fixElement tmOp
  rw [tmOp, toElementMap_comp, toElementMap_comp, toElementMap_paired] at h
  exact h


-- @@ L266-266 verbatim
/-! ### Property (a) — the digit characterization. -/


-- @@ L268-272 verbatim
/-- `(strBot τ)` has the cone of `σ` as a neighbourhood iff `σ` is a prefix of
`τ`. -/
theorem strBot_mem_cone {σ τ : Str} : (strBot τ).mem (cone σ) ↔ σ <+: τ := by
  rw [strBot, mem_principal]
  exact ⟨fun h => cone_subset_cone.mp h.2, fun h => ⟨memC_cone σ, cone_subset_cone.mpr h⟩⟩


-- @@ L274-279 verbatim
/-- `σΣ* = Σ*` iff `σ = Λ`. -/
theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil


-- @@ L281-287 verbatim
/-- Each approximant is below the least fixed point. -/
theorem iterElem_le_fixElement {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
    (n : ℕ) : f.iterElem n ≤ f.fixElement := by
  rw [f.fixElement_eq_iSupDirected]
  intro Z hZ
  rw [mem_iSupDirected]
  exact ⟨n, hZ⟩


-- @@ L289-298 verbatim
/-- **Property (a), prefix form.** Every Thue–Morse parity prefix is a prefix of
`t`:
`(tmList n)⊥ ⊑ t` for all `n`. -/
theorem tmList_le_tElt (n : ℕ) : strBot (tmList n) ≤ tElt := by
  have hpre : tmList n <+: expand^[n] [false] := by
    rw [expand_iterate_eq]; exact tmList_prefix (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc strBot (tmList n) ≤ strBot (expand^[n] [false]) :=
        strBot_le_strBot_iff.mpr hpre
    _ = tmOp.iterElem (n + 1) := (iterElem_succ_eq n).symm
    _ ≤ tElt := iterElem_le_fixElement tmOp (n + 1)


-- @@ L300-333 verbatim
/-- **Property (a) (Scott 1981, PRG-19; Lambek).** The finite-prefix
characterization of `t`: a
string `σ` is a prefix of `t` **iff** it is the length-`σ.length` Thue–Morse
parity prefix. Reading
off position `n`, the `n`-th digit of `t` is `tm n`, the parity of the binary
digits of `n`. -/
theorem tElt_mem_cone_iff (σ : Str) : tElt.mem (cone σ) ↔ σ = tmList σ.length := by
  constructor
  · intro hσ
    rw [show tElt = tmOp.fixElement from rfl, tmOp.fixElement_eq_iSupDirected,
      mem_iSupDirected] at hσ
    obtain ⟨n, hn⟩ := hσ
    -- `σ` is a prefix of some Thue–Morse prefix `tmList N`.
    obtain ⟨N, hpre⟩ : ∃ N, σ <+: tmList N := by
      cases n with
      | zero =>
        rw [iterElem_zero', mem_bot, C_master, cone_univ_iff] at hn
        exact ⟨0, by rw [hn]; exact List.nil_prefix⟩
      | succ k =>
        rw [iterElem_succ_eq, strBot_mem_cone, expand_iterate_eq] at hn
        exact ⟨2 ^ k, hn⟩
    -- Both `σ` and `tmList σ.length` are the length-`σ.length` prefix of `tmList
    -- N`.
    have hlen : σ.length ≤ N := hpre.length_le.trans_eq (tmList_length _)
    have h1 : σ = (tmList N).take σ.length := List.prefix_iff_eq_take.mp hpre
    have h2 : tmList σ.length = (tmList N).take σ.length := by
      have := List.prefix_iff_eq_take.mp (tmList_prefix hlen)
      rwa [tmList_length] at this
    exact h1.trans h2.symm
  · intro hσ
    have h := tmList_le_tElt σ.length
    have hmem : (strBot (tmList σ.length)).mem (cone σ) :=
      strBot_mem_cone.mpr (hσ ▸ List.prefix_rfl)
    exact h _ hmem


-- @@ L335-340 verbatim
/-- **Property (a), digit form.** The `n`-th digit of `t` is `tm n` (the parity of
the binary digits
of `n`): the length-`(n+1)` prefix of `t` is `tmList n ++ [tm n]`. -/
theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h


-- @@ L342-342 verbatim
end Domain.Neighborhood.Exercise516
