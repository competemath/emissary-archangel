/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-28 verbatim
/-!
# Piecewise C¹ Curve API

General-purpose API for proving properties of piecewise C¹ curves by checking each
consecutive segment defined by the partition.

## Main results

* `PiecewiseC1Curve.sortedPartition` - the partition points as a sorted list
* `PiecewiseC1Curve.consecutivePairs` - consecutive pairs (pᵢ, pᵢ₊₁) from the sorted partition
* `PiecewiseC1Curve.sortedPartition_head` - the first element of the sorted partition is `γ.a`
* `PiecewiseC1Curve.sortedPartition_last` - the last element of the sorted partition is `γ.b`
* `PiecewiseC1Curve.consecutivePairs_cover` - union of [pᵢ, pᵢ₊₁] covers [a,b]
* `PiecewiseC1Curve.forall_Icc_of_forall_consecutive` - prove a property on [a,b] from
  each consecutive interval [pᵢ, pᵢ₊₁]
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
open Set MeasureTheory Complex


-- @@ L34-34 verbatim
namespace PiecewiseC1Curve


-- @@ L36-36 verbatim
/-! ### Definitions -/


-- @@ L38-40 verbatim
/-- The sorted partition points as a list. -/
noncomputable def sortedPartition (γ : PiecewiseC1Curve) : List ℝ :=
  γ.partition.sort (· ≤ ·)


-- @@ L42-45 verbatim
/-- Consecutive pairs of partition points: [(p₀,p₁), (p₁,p₂), ...]. -/
noncomputable def consecutivePairs (γ : PiecewiseC1Curve) : List (ℝ × ℝ) :=
  let pts := γ.sortedPartition
  pts.zip pts.tail


-- @@ L47-47 verbatim
/-! ### Basic properties of `sortedPartition` -/


-- @@ L49-53 verbatim
/-- Membership in `sortedPartition` is equivalent to membership in the original partition. -/
@[simp]
theorem mem_sortedPartition (γ : PiecewiseC1Curve) (x : ℝ) :
    x ∈ γ.sortedPartition ↔ x ∈ γ.partition :=
  Finset.mem_sort (· ≤ ·)


-- @@ L55-58 verbatim
/-- The `sortedPartition` is sorted with respect to `≤`. -/
theorem sortedPartition_sorted (γ : PiecewiseC1Curve) :
    γ.sortedPartition.Pairwise (· ≤ ·) := by
  simp only [sortedPartition]; exact Finset.pairwise_sort γ.partition (· ≤ ·)


-- @@ L60-62 verbatim
/-- The `sortedPartition` has no duplicates. -/
theorem sortedPartition_nodup (γ : PiecewiseC1Curve) :
    γ.sortedPartition.Nodup := by simp only [sortedPartition, Finset.sort_nodup]


-- @@ L64-70 verbatim
/-- The `sortedPartition` is nonempty (contains at least `a` and `b`). -/
theorem sortedPartition_nonempty (γ : PiecewiseC1Curve) :
    γ.sortedPartition ≠ [] := by
  intro h
  have ha := γ.endpoints_in_partition.1
  rw [← mem_sortedPartition] at ha
  simp [h] at ha


-- @@ L72-75 verbatim
/-- Every element of the `sortedPartition` lies in `[a, b]`. -/
theorem sortedPartition_mem_Icc (γ : PiecewiseC1Curve) (x : ℝ)
    (hx : x ∈ γ.sortedPartition) : x ∈ Icc γ.a γ.b :=
  γ.partition_subset ((mem_sortedPartition γ x).mp hx)


-- @@ L77-77 verbatim
/-! ### Head and last of `sortedPartition` -/


-- @@ L79-89 verbatim
/-- The first element of the sorted partition equals `γ.a`.

  Proof sketch: `head ∈ [a,b]` so `a ≤ head`; all elements ≥ head from sorted, and
  `a ∈ sortedPartition`, so `head ≤ a`. Together: `head = a`. -/
theorem sortedPartition_head (γ : PiecewiseC1Curve) :
    γ.sortedPartition.head (sortedPartition_nonempty γ) = γ.a := by
  have hne := sortedPartition_nonempty γ
  have h_a_mem : γ.a ∈ γ.sortedPartition :=
    (mem_sortedPartition γ γ.a).mpr γ.endpoints_in_partition.1
  linarith [(sortedPartition_mem_Icc γ _ (List.head_mem hne)).1,
    (sortedPartition_sorted γ).rel_head h_a_mem]


-- @@ L91-104 verbatim
/-- Helper: in a sorted list, every element is ≤ the last element. -/
private theorem pairwise_le_getLast : ∀ (l : List ℝ) (_hl : l.Pairwise (· ≤ ·))
    (hne : l ≠ []) (elem : ℝ) (_hmem : elem ∈ l), elem ≤ l.getLast hne
  | [], _, hne, _, _ => absurd rfl hne
  | [hd], _, _, elem, hmem => by
      simpa only [List.getLast_singleton] using List.eq_of_mem_singleton hmem ▸ le_refl _
  | hd :: hd2 :: tl2, hl, _, elem, hmem => by
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil hd2 tl2
      rw [show (hd :: hd2 :: tl2).getLast (List.cons_ne_nil hd (hd2 :: tl2)) =
          (hd2 :: tl2).getLast htl_ne from List.getLast_cons_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · linarith [(List.pairwise_cons.mp hl).1 hd2 List.mem_cons_self,
          pairwise_le_getLast _ (List.pairwise_cons.mp hl).2 htl_ne hd2 List.mem_cons_self]
      · exact pairwise_le_getLast _ (List.pairwise_cons.mp hl).2 htl_ne elem hmem'


-- @@ L106-116 verbatim
/-- The last element of the sorted partition equals `γ.b`.

  Proof sketch: `getLast ∈ [a,b]` so `getLast ≤ b`; all elements ≤ getLast from sorted,
  and `b ∈ sortedPartition`, so `b ≤ getLast`. Together: `getLast = b`. -/
theorem sortedPartition_last (γ : PiecewiseC1Curve) :
    γ.sortedPartition.getLast (sortedPartition_nonempty γ) = γ.b := by
  have hne := sortedPartition_nonempty γ
  have h_b_mem : γ.b ∈ γ.sortedPartition :=
    (mem_sortedPartition γ γ.b).mpr γ.endpoints_in_partition.2
  linarith [(sortedPartition_mem_Icc γ _ (List.getLast_mem hne)).2,
    (sortedPartition_sorted γ).rel_getLast h_b_mem]


-- @@ L118-118 verbatim
/-! ### Consecutive pairs cover `[a, b]` -/


-- @@ L120-157 verbatim
/-- A sorted list whose head is `lo` and last is `hi` has consecutive Icc's covering `[lo, hi]`.
    Uses a structural induction on the list length, handling the base case (2 elements)
    and inductive case (>2 elements) separately. -/
private theorem pairwise_consecutive_union :
    ∀ (pts : List ℝ) (_hsorted : pts.Pairwise (· ≤ ·)) (hne : pts ≠ [])
      (_htail_ne : pts.tail ≠ []) (lo hi : ℝ)
      (_hhead : pts.head hne = lo) (_hlast : pts.getLast hne = hi),
    Icc lo hi ⊆ ⋃ p ∈ pts.zip pts.tail, Icc p.1 p.2 := by
  intro pts
  induction pts with
  | nil => intro _ hne _ _ _ _ _; exact absurd rfl hne
  | cons x xs ih =>
    intro hsorted hne htail_ne lo hi hhead hlast
    simp only [List.tail_cons] at htail_ne
    have hxlo : x = lo := hhead
    subst hxlo
    cases xs with
    | nil => exact absurd rfl htail_ne
    | cons y ys =>
      simp only [List.zip_cons_cons, List.tail_cons]
      have hys_sorted : (y :: ys).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hsorted).2
      have hys_ne : y :: ys ≠ [] := List.cons_ne_nil y ys
      rw [List.getLast_cons_cons] at hlast
      cases ys with
      | nil =>
        simp_all
      | cons z zs =>
        have htail_ne' : (y :: z :: zs).tail ≠ [] := List.cons_ne_nil z zs
        intro t ht
        simp only [List.mem_cons, Set.mem_iUnion]
        by_cases htxy : t ≤ y
        · exact ⟨(x, y), Or.inl rfl, ht.1, htxy⟩
        · push Not at htxy
          have ht_sub : t ∈ Icc y hi := ⟨le_of_lt htxy, ht.2⟩
          obtain ⟨p, hp_mem, hp_t⟩ :=
            Set.mem_iUnion₂.mp (ih hys_sorted hys_ne htail_ne' y hi rfl hlast ht_sub)
          exact ⟨p, Or.inr hp_mem, hp_t⟩


-- @@ L159-172 verbatim
/-- The sorted partition has at least two elements (since `a ≠ b` are both in the partition). -/
theorem sortedPartition_tail_nonempty (γ : PiecewiseC1Curve) :
    γ.sortedPartition.tail ≠ [] := by
  have hcard : 1 < γ.partition.card :=
    Finset.one_lt_card.mpr ⟨γ.a, γ.endpoints_in_partition.1, γ.b,
      γ.endpoints_in_partition.2, ne_of_lt γ.hab⟩
  have hlen : 2 ≤ γ.sortedPartition.length := by
    simp only [sortedPartition, Finset.length_sort]
    omega
  intro h
  have hlen2 : γ.sortedPartition.length ≤ 1 := by
    rcases List.exists_cons_of_ne_nil (sortedPartition_nonempty γ) with ⟨hd, tl, heq⟩
    simp_all
  linarith


-- @@ L174-180 verbatim
/-- The union of `Icc p.1 p.2` over all `p ∈ consecutivePairs γ` covers `[a, b]`. -/
theorem consecutivePairs_cover (γ : PiecewiseC1Curve) :
    Icc γ.a γ.b ⊆ ⋃ p ∈ γ.consecutivePairs, Icc p.1 p.2 :=
  pairwise_consecutive_union γ.sortedPartition
    (sortedPartition_sorted γ) (sortedPartition_nonempty γ)
    (sortedPartition_tail_nonempty γ)
    γ.a γ.b (sortedPartition_head γ) (sortedPartition_last γ)


-- @@ L182-182 verbatim
/-! ### Properties of consecutive pairs -/


-- @@ L184-196 verbatim
/-- For any sorted list, consecutive pairs in `l.zip l.tail` satisfy `p.1 ≤ p.2`. -/
private theorem pairwise_zip_tail_le {l : List ℝ} (hl : l.Pairwise (· ≤ ·))
    {p : ℝ × ℝ} (hp : p ∈ l.zip l.tail) : p.1 ≤ p.2 := by
  induction l with
  | nil => simp only [List.zip_nil_left, List.not_mem_nil] at hp
  | cons x xs ih =>
    cases xs with
    | nil => simp only [List.tail_cons, List.zip_nil_right, List.not_mem_nil] at hp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.tail_cons, List.mem_cons] at hp
      rcases hp with rfl | h
      · exact (List.pairwise_cons.mp hl).1 y List.mem_cons_self
      · exact ih ((List.pairwise_cons.mp hl).2) h


-- @@ L198-201 verbatim
/-- For each consecutive pair `(p, q)`, we have `p ≤ q`. -/
theorem consecutivePairs_le (γ : PiecewiseC1Curve) (p : ℝ × ℝ)
    (hp : p ∈ γ.consecutivePairs) : p.1 ≤ p.2 :=
  pairwise_zip_tail_le (sortedPartition_sorted γ) hp


-- @@ L203-210 verbatim
/-- Both components of a consecutive pair lie in `[a, b]`. -/
theorem consecutivePairs_subset (γ : PiecewiseC1Curve) (p : ℝ × ℝ)
    (hp : p ∈ γ.consecutivePairs) :
    p.1 ∈ Icc γ.a γ.b ∧ p.2 ∈ Icc γ.a γ.b := by
  simp only [consecutivePairs] at hp
  have h12 := List.of_mem_zip hp
  exact ⟨sortedPartition_mem_Icc γ _ h12.1,
         sortedPartition_mem_Icc γ _ (List.mem_of_mem_tail h12.2)⟩


-- @@ L212-212 verbatim
/-! ### Main theorems -/


-- @@ L214-221 verbatim
/-- **Main theorem**: to prove a property `P` on `[a, b]`, it suffices to prove `P` on each
    consecutive segment `[pᵢ, pᵢ₊₁]` of the partition. -/
theorem forall_Icc_of_forall_consecutive {P : ℝ → Prop}
    (γ : PiecewiseC1Curve)
    (h : ∀ p ∈ γ.consecutivePairs, ∀ t ∈ Icc p.1 p.2, P t) :
    ∀ t ∈ Icc γ.a γ.b, P t := fun t ht => by
  obtain ⟨p, hp_mem, hp_t⟩ := Set.mem_iUnion₂.mp (consecutivePairs_cover γ ht)
  exact h p hp_mem t hp_t


-- @@ L223-230 verbatim
/-- **Image variant**: if the image of each consecutive segment lies in `S`,
    then the image of `[a, b]` lies in `S`. -/
theorem image_subset_of_consecutive_images {S : Set ℂ}
    (γ : PiecewiseC1Curve)
    (h : ∀ p ∈ γ.consecutivePairs, γ.toFun '' Icc p.1 p.2 ⊆ S) :
    γ.toFun '' Icc γ.a γ.b ⊆ S := fun z ⟨t, ht, hz⟩ => by
  obtain ⟨p, hp_mem, hp_t⟩ := Set.mem_iUnion₂.mp (consecutivePairs_cover γ ht)
  exact h p hp_mem ⟨t, hp_t, hz⟩


-- @@ L232-232 verbatim
end PiecewiseC1Curve
