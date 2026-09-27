/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Data.Stream.Init
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L18-22 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.InfLists

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L24-24 verbatim
@[expose] public section



-- @@ L27-27 verbatim
namespace Stream'

-- @@ L28-28 verbatim
attribute [simp_lengths] length_take

-- @@ L29-30 verbatim
variable {A B : Type*} (f : A → B) (m n : ℕ) (a b : Stream' A) (x y : List A)
--compare PiNat, CantorScheme


-- @@ L32-32 verbatim
namespace Discrete

-- @@ L33-35 verbatim
@[simp] lemma append_inf_compose (x y : List A) :
  (x ++ₛ ·) ∘ (y ++ₛ ·) = ((x ++ y) ++ₛ ·) := by
  ext1; simp

-- @@ L36-37 verbatim
@[simp] lemma subAtInf_append (T : Set (Stream' A)) (x y : List A) :
  (y ++ₛ ·)⁻¹' ((x ++ₛ ·)⁻¹' T) = ((x ++ y) ++ₛ ·)⁻¹' T := by simp [← Set.preimage_comp]


-- @@ L39-40 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def principalOpen : Set (Stream' A) := Set.range (x ++ₛ ·)

-- @@ L41-41 verbatim
@[simp] lemma principalOpen_nil : @principalOpen A [] = Set.univ := by simp [principalOpen]

-- @@ L42-43 verbatim
@[simp] lemma principalOpen_append :
  x ++ₛ a ∈ principalOpen (x ++ y) ↔ a ∈ principalOpen y := by simp [principalOpen]

-- @@ L44-45 verbatim
@[simp] lemma principalOpen_append_nil : x ++ₛ a ∈ principalOpen x := by
  simpa using principalOpen_append a x []

-- @@ L46-47 verbatim
@[simp] lemma principalOpen_cons_nil (a : A) (as : Stream' A) : as.cons a ∈ principalOpen [a] := by
  apply principalOpen_append_nil

-- @@ L48-49 verbatim
@[simp] lemma extend_sub : a ∈ principalOpen (a.take n) := by
  use a.drop n; simp

-- @@ L50-53 verbatim
lemma principalOpen_iff_restrict : a ∈ principalOpen x ↔ x = a.take x.length := by
  constructor
  · rintro ⟨b, _, rfl⟩; simp [take_append_of_le_length]
  · rintro h; rw [h]; exact extend_sub _ _

-- @@ L54-58 verbatim
lemma principalOpen_cons {as : Stream' A} {x : List A} {a : A} :
  as ∈ principalOpen (a :: x) ↔ as.get 0 = a ∧ tail as ∈ principalOpen x := by
  simp_rw [principalOpen, Set.mem_range]
  nth_rw 1 [← exists_and_left, ← cons_head_tail as]
  simp_rw [cons_append_stream, cons_injective2.eq_iff, Eq.comm]

-- @@ L59-63 verbatim
lemma principalOpen_index : a ∈ principalOpen x ↔ ∀ (n) (_ : n < x.length), a.get n = x[n] := by
  rw [principalOpen_iff_restrict]; constructor <;> intro h
  · intro n h'; simp_rw (config := {singlePass := true}) [h, take_get]
  · symm; apply List.ext_getElem (by simp)
    simp; tauto --simpa using h --fails since mathlib update

-- @@ L64-69 verbatim
lemma principalOpen_concat {as : Stream' A} {x : List A} {a : A} :
  as ∈ principalOpen (x ++ [a]) ↔ as ∈ principalOpen x ∧ as.get x.length = a := by
  induction x generalizing as with
  | nil => simp [principalOpen_cons]
  | cons x xs ih =>
    simp [principalOpen_cons, @ih (tail as), and_assoc]

-- @@ L70-71 verbatim
lemma principalOpen_restrict : a ∈ principalOpen (b.take n) ↔ ∀ m < n, a.get m = b.get m := by
  rw [principalOpen_index]; simp (config := {contextual := true})

-- @@ L72-73 verbatim
@[simp] lemma principalOpen_sub : principalOpen (x ++ y) ⊆ principalOpen x := by
  intro _ ⟨z, h⟩; use y ++ₛ z; dsimp only; rwa [← append_append_stream]

-- @@ L74-75 verbatim
@[gcongr] lemma principalOpen_mono {x y : List A} (h : x <+: y) :
  principalOpen y ⊆ principalOpen x := by obtain ⟨z, rfl⟩ := h; apply principalOpen_sub


-- @@ L77-85 verbatim
lemma principalOpen_complement : (principalOpen x)ᶜ
  = ⋃ (y) (_ : x.length = y.length ∧ x ≠ y), principalOpen y := by
  ext a; constructor <;> simp only [Set.mem_iUnion]
  · intro h; use a.take x.length
    conv => simp
    intro h'; apply h; rw [h']; simp
  · intro ⟨x', ⟨hl, hne⟩, ⟨a1, h1⟩⟩ ⟨a2, h2⟩
    exact hne (append_left_injective (x := x) (y := x') (a := a2) (b := a1) (by
      simp_all) hl)

-- @@ L86-88 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
scoped instance prodDisc A : TopologicalSpace (Stream' A) :=
  Pi.topologicalSpace (t₂ := fun _ ↦ ⊥)


-- @@ L90-90 verbatim
section «Section1»

-- @@ L91-92 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
local instance instTopologicalSpaceLeanPool : TopologicalSpace A := ⊥

-- @@ L93-93 verbatim
local instance : DiscreteTopology A := ⟨rfl⟩

-- @@ L94-96 verbatim
lemma continuous_pi' {X} [TopologicalSpace X] {f : X → Stream' A}
  (h : ∀ i, Continuous fun a => (f a).get i) : Continuous f :=
  continuous_pi_iff.2 h

-- @@ L97-97 verbatim
lemma drop_con : Continuous (@drop A n) := continuous_pi' fun i ↦ continuous_apply (i + n)

-- @@ L98-98 verbatim
lemma tail_con : Continuous (@tail A) := drop_con 1

-- @@ L99-105 verbatim
lemma append_con : Continuous (x ++ₛ ·) := by
  apply continuous_pi'; intro i; rcases lt_or_ge i x.length with h | h
  · simp_rw [get_append_left _ _ _ h]; exact continuous_const
  · obtain ⟨i, rfl⟩ := le_iff_exists_add.mp h
    simp_rw [get_append_right]
    change @Continuous (∀ _ : ℕ, A) A Pi.topologicalSpace ⊥ (fun a ↦ a i)
    exact continuous_apply i

-- @@ L106-121 verbatim
/-- The principal opens form a neighborhood basis for the product topology. -/
lemma hasBasis_principalOpen : (nhds a).HasBasis
  (fun x ↦ a ∈ principalOpen x) (fun x ↦ principalOpen x) := by
  rw [show @nhds (Stream' A) (prodDisc A) a =
      Filter.pi (fun i : ℕ ↦ Pure.pure (f := Filter) (a i)) from
    (@nhds_pi ℕ (fun _ ↦ A) _ a).trans (by simp [nhds_discrete])]
  apply Filter.HasBasis.to_hasBasis (Filter.hasBasis_pi_pure (fun i : ℕ ↦ a i))
  · intro I hI
    have ⟨N, hN⟩ := hI.bddAbove
    refine ⟨a.take (N + 1), extend_sub _ _, fun b hb n hn ↦ ?_⟩
    exact (principalOpen_restrict (a := (b : Stream' A)) (b := a) (n := N + 1)).mp hb
      n <| lt_of_le_of_lt (hN hn) (Nat.lt_succ_self _)
  · intro x hx
    refine ⟨(Finset.range x.length : Set ℕ), Finset.finite_toSet _, fun b hb ↦ ?_⟩
    exact (principalOpen_index (a := (b : Stream' A)) (x := x)).mpr fun n hn ↦
      (hb n (by simp [hn])).trans ((principalOpen_index (a := a) (x := x)).mp hx n hn)

-- @@ L122-122 verbatim
end «Section1»


-- @@ L124-129 verbatim
lemma hasBasis_principalOpen' : (nhds a).HasBasis
  (fun n ↦ n ≥ m) (fun n ↦ principalOpen (a.take n)) := by
  apply Filter.HasBasis.to_hasBasis (hasBasis_principalOpen a)
  · intro x hx; rw [principalOpen_iff_restrict] at hx; rw [hx]
    use m + x.length; simp [principalOpen_mono]
  · intro n _; use a.take n; simp

-- @@ L130-131 verbatim
@[simp] lemma principalOpen_isOpen : IsOpen (principalOpen x) :=
  isOpen_iff_mem_nhds.mpr fun a h ↦ (hasBasis_principalOpen a).mem_iff.mpr ⟨x, h, subset_rfl⟩

-- @@ L132-134 verbatim
@[simp] lemma principalOpen_isClosed : IsClosed (principalOpen x) := by
  rw [← isOpen_compl_iff, principalOpen_complement]
  exact isOpen_biUnion fun i _ ↦ principalOpen_isOpen i

-- @@ L135-135 verbatim
end Discrete

-- @@ L136-136 verbatim
end Stream'
