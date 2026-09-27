/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import LeanPool.Koethe.Mortality.FormalWord
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L18-24 verbatim
/-!
# Periodic masks and independent connector holes

Free positions are enumerated as a finite subtype of *occurrences*, not as
residue classes.  In particular a connector of length `m * period` has
`m * holes` distinct projective blocks.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open scoped BigOperators


-- @@ L32-32 verbatim
namespace KoetheCounterexample.Mortality


-- @@ L34-34 verbatim
variable {k : Type*} [Field k]


-- @@ L36-41 verbatim
theorem lookup_add_of_dvd (M : PeriodicMask k) (a b : ℕ) (ha : M.period ∣ a) :
    M.lookup (a + b) = M.lookup b := by
  unfold PeriodicMask.lookup
  congr 1
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd ha]


-- @@ L43-60 verbatim
theorem compatible_append (M : PeriodicMask k) {u v : List (Triple k)}
    (hu : M.Compatible u) (hv : M.Compatible v) (hlen : M.period ∣ u.length) :
    M.Compatible (u ++ v) := by
  intro i z hz
  rw [List.get_eq_getElem]
  by_cases hi : i.val < u.length
  · rw [List.getElem_append_left hi]
    exact hu ⟨i.val, hi⟩ z hz
  · have hle : u.length ≤ i.val := Nat.le_of_not_gt hi
    have hiv : i.val - u.length < v.length := by
      have h := i.isLt
      simp only [List.length_append] at h
      omega
    rw [List.getElem_append_right hle]
    apply hv ⟨i.val - u.length, hiv⟩ z
    rw [← lookup_add_of_dvd M u.length (i.val - u.length) hlen,
      Nat.add_sub_of_le hle]
    exact hz


-- @@ L62-67 verbatim
theorem compatible_ofFn (M : PeriodicMask k) {L : ℕ} (f : Fin L → Triple k)
    (hf : ∀ i z, M.lookup i.val = some z → f i = z) :
    M.Compatible (List.ofFn f) := by
  intro i z hz
  rw [List.get_ofFn]
  exact hf (Fin.cast (by simp) i) z hz


-- @@ L69-71 verbatim
/-- Actual unassigned occurrences in a finite interval. -/
abbrev FreePos (M : PeriodicMask k) (L : ℕ) :=
  {i : Fin L // M.lookup i.val = none}


-- @@ L73-75 verbatim
instance freePosFintype (M : PeriodicMask k) (L : ℕ) : Fintype (FreePos M L) := by
  classical
  exact Subtype.fintype _


-- @@ L77-78 verbatim
/-- The number of free positions in the initial interval of length `L`. -/
def freeCount (M : PeriodicMask k) (L : ℕ) : ℕ := Fintype.card (FreePos M L)


-- @@ L80-82 verbatim
/-- An enumeration of the free positions in the initial interval of length `L`. -/
def freeIndex (M : PeriodicMask k) (L : ℕ) : FreePos M L ≃ Fin (freeCount M L) :=
  Fintype.equivFin _


-- @@ L84-91 verbatim
theorem lookup_finProd (M : PeriodicMask k) {m : ℕ}
    (a : Fin m) (b : Fin M.period) :
    M.lookup (finProdFinEquiv (a, b)).val = M.value b := by
  unfold PeriodicMask.lookup
  congr 1
  apply Fin.ext
  change (b.val + M.period * a.val) % M.period = b.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]


-- @@ L93-103 verbatim
/-- Exact independent-hole count, including zero repetitions. -/
theorem freeCount_mul_period (M : PeriodicMask k) (m : ℕ) :
    freeCount M (m * M.period) = m * M.holes := by
  classical
  unfold freeCount
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin M.period ≃ Fin (m * M.period))]
  simp only [Fintype.sum_prod_type, lookup_finProd]
  simp only [← Finset.card_filter]
  change (∑ _ : Fin m, M.holes) = m * M.holes
  simp


-- @@ L105-110 verbatim
/-- A fixed letter at assigned positions; a distinct variable block at each hole. -/
def connectorLetter (M : PeriodicMask k) (L : ℕ) (i : Fin L) :
    FormalLetter k (freeCount M L) :=
  match h : M.lookup i.val with
  | none => .inr (freeIndex M L ⟨i, h⟩)
  | some z => .inl z


-- @@ L112-115 verbatim
/-- The formal word of length `L` reading the mask: its fixed letter at each assigned position
and a distinct hole at each free position. -/
def formalConnector (M : PeriodicMask k) (L : ℕ) :
    List (FormalLetter k (freeCount M L)) := List.ofFn (connectorLetter M L)


-- @@ L117-118 verbatim
@[simp] theorem formalConnector_length (M : PeriodicMask k) (L : ℕ) :
    (formalConnector M L).length = L := by simp [formalConnector]


-- @@ L120-124 verbatim
theorem connectorLetter_of_none (M : PeriodicMask k) (L : ℕ) (i : Fin L)
    (h : M.lookup i.val = none) :
    connectorLetter M L i = .inr (freeIndex M L ⟨i, h⟩) := by
  unfold connectorLetter
  split <;> simp_all


-- @@ L126-130 verbatim
theorem connectorLetter_of_some (M : PeriodicMask k) (L : ℕ) (i : Fin L)
    (z : Triple k) (h : M.lookup i.val = some z) :
    connectorLetter M L i = .inl z := by
  unfold connectorLetter
  split <;> simp_all


-- @@ L132-156 verbatim
/-- Each enumerated hole contributes exactly one copy of its block degree. -/
theorem formalConnector_degree (M : PeriodicMask k) (L : ℕ) :
    ((formalConnector M L).map letterDegree).sum = fun _ => 1 := by
  classical
  ext b
  simp only [formalConnector, List.map_ofFn, List.sum_ofFn, Finset.sum_apply,
    Function.comp_apply]
  let t : FreePos M L := (freeIndex M L).symm b
  rw [Finset.sum_eq_single t.val]
  · rw [connectorLetter_of_none M L t.val t.property, letterDegree_inr]
    simp [blockUnit, t]
  · intro i _ hi
    cases h : M.lookup i.val with
    | some z => simp [connectorLetter_of_some M L i z h]
    | none =>
      rw [connectorLetter_of_none M L i h, letterDegree_inr]
      have hne : b ≠ freeIndex M L ⟨i, h⟩ := by
        intro heq
        apply hi
        have ht : (⟨i, h⟩ : FreePos M L) = t := by
          apply (freeIndex M L).injective
          exact heq.symm.trans ((freeIndex M L).apply_symm_apply b).symm
        exact congrArg Subtype.val ht
      simp [blockUnit, hne]
  · simp


-- @@ L158-171 verbatim
theorem specialized_connector_nonzero (M : PeriodicMask k) (L : ℕ)
    (x : (Fin (freeCount M L) × Fin 3) → k)
    (hx : ∀ b : Fin (freeCount M L), (fun j : Fin 3 => x (b, j)) ≠ 0) :
    ∀ z ∈ (formalConnector M L).map (specializeLetter x), z ≠ 0 := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  cases h : M.lookup i.val with
  | none =>
    rw [connectorLetter_of_none M L i h]
    exact hx _
  | some a =>
    rw [connectorLetter_of_some M L i a h]
    exact M.nonzero _ a h


-- @@ L173-180 verbatim
theorem specialized_connector_compatible (M : PeriodicMask k) (L : ℕ)
    (x : (Fin (freeCount M L) × Fin 3) → k) :
    M.Compatible ((formalConnector M L).map (specializeLetter x)) := by
  simp only [formalConnector, List.map_ofFn]
  apply compatible_ofFn
  intro i z hz
  rw [Function.comp_apply, connectorLetter_of_some M L i z hz]
  rfl


-- @@ L182-194 verbatim
/-- There is an initial compatible, nonzero word of exactly one mask period. -/
theorem exists_compatible_block (M : PeriodicMask k) :
    ∃ w : List (Triple k), w.length = M.period ∧
      (∀ z ∈ w, z ≠ 0) ∧ M.Compatible w := by
  let x : (Fin (freeCount M M.period) × Fin 3) → k := fun _ => 1
  have hx : ∀ b : Fin (freeCount M M.period), (fun j : Fin 3 => x (b, j)) ≠ 0 := by
    intro b h
    have h0 := congrFun h 0
    exact one_ne_zero h0
  refine ⟨(formalConnector M M.period).map (specializeLetter x), ?_,
    specialized_connector_nonzero M M.period x hx,
    specialized_connector_compatible M M.period x⟩
  simp


-- @@ L196-196 verbatim
end KoetheCounterexample.Mortality


-- @@ L198-198 verbatim
end
