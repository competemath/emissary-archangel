/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
module

public import LeanPool.SetTheory.Ordinals
import Mathlib.Tactic.FinCases
import Std.Tactic.BVDecide.Normalize.Prop


-- @@ L12-17 verbatim
/-!
# The first infinite ordinal in models of ZF

This module develops the theory of `ω` and the natural numbers inside a von Neumann model
of ZF, providing the infinitary tools needed for the Kunen inconsistency argument.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open SetTheory Ordinal Cardinal ZFSet Function


-- @@ L25-26 verbatim
variable {M M₀} [ZFStructure M] [ZFStructure M₀]
    [hM : IsVonNeumann M] [hM₀ : IsVonNeumannWithOmega M₀]


-- @@ L28-30 verbatim
/-- The `toZFSet` declaration. -/
def Set.toZFSet {A : ZFSet} (B : Set A) : ZFSet :=
  ZFSet.sep (fun x => ∃ hx : x ∈ A, ⟨x, hx⟩ ∈ B) A


-- @@ L32-34 verbatim
@[simp] lemma Set.mem_toZFSet {A : ZFSet} (B : Set A) (x : ZFSet) :
    x ∈ B.toZFSet ↔ ∃ hx : x ∈ A, ⟨x, hx⟩ ∈ B := by
  simp [Set.toZFSet]


-- @@ L36-36 verbatim
namespace SetTheory


-- @@ L38-39 expanded
/-- The `IsWellFoundedRevMem` declaration. -/
@[realize]
def IsWellFoundedRevMem (x : M) :=
  ∀ S ∈ powerset x, S ≠ ∅ → ∃ y ∈ S, ∀ z ∈ S, y ∉ z


-- @@ L40-41 verbatim
/-- The `MemOmega` declaration. -/
@[realize] def MemOmega (x : M) := IsOrdinal x ∧ IsWellFoundedRevMem x

-- @@ L42-44 expanded
@[toV_simps]
lemma IsWellFoundedRevMem.toV (x : M) : IsWellFoundedRevMem (toV x) ↔ IsWellFoundedRevMem x := by
  simp only [IsWellFoundedRevMem, toV_simps, empty.toV (M := M)]


-- @@ L46-52 verbatim
@[toZFSet_simps] lemma forall_set {x : ZFSet} {p : Set x → Prop} :
    (∀ y : Set x, p y) ↔ (∀ y ⊆ x, p {z : x | z.1 ∈ y}) := by
  refine ⟨fun h _ _ => h _, fun h y => ?_⟩
  convert h y.toZFSet ?_
  · simp_all
  · intro z
    simpa using fun hz _ => hz


-- @@ L54-69 expanded
@[toZFSet_simps]
lemma IsWellFoundedRevMem.toZFSet (x : M) :
    IsWellFoundedRevMem x ↔ WellFounded fun a b : toZFSet x => b ∈ a :=
  by
  rw [← IsWellFoundedRevMem.toV]
  simp only [IsWellFoundedRevMem, WellFounded.wellFounded_iff_has_min, powerset.spec, toZFSet_simps,
    Subtype.forall, Subtype.exists, Set.mem_ofPred_eq, mem_inside_ZFSet, exists_and_left,
    exists_prop]
  conv =>
    enter [2, y, hy, ne, 1, z]
    rw [← and_assoc, and_iff_left_of_imp (@hy z)]
    enter [2, u]
    rw [← and_imp, and_iff_right_of_imp (@hy u)]
  congr! 4 with y hy sub
  simp only [ne_eq, ZFSet.ext_iff, notMem_empty, iff_false, not_forall, not_not, Set.Nonempty,
    Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  simp_all
  aesop


-- @@ L71-72 verbatim
/-- The `ωₛ` declaration. -/
def ωₛ := Ordinal.toZFSet ω


-- @@ L74-80 expanded
instance instNatCastM : NatCast M where
  natCast
    (n : ℕ) := by
    (rcases hM with ⟨μ, hμ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; have _ := Fact.mk hμ)
    · refine ⟨Ordinal.toZFSet n, ?_⟩
      erw [mem_vonNeumann, rank_toZFSet]
      exact natCast_lt_of_isSuccLimit hμ _
    · exact toV (Ordinal.toZFSet n)


-- @@ L82-83 verbatim
instance instOfNatM {n} : OfNat M n where
  ofNat := (n : M)


-- @@ L85-86 expanded
@[toZFSet_simps]
lemma NatCast.natCast.toZFSet {n : ℕ} : toZFSet (n : M) = Ordinal.toZFSet n := by
  (rcases hM with ⟨μ, hμ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; have _ := Fact.mk hμ) <;> rfl


-- @@ L88-88 verbatim
lemma ofNat_eq_natCast (n : ℕ) : (OfNat.ofNat n : M) = n := rfl


-- @@ L90-90 verbatim
lemma natCast_zero : (0 : M) = ∅ := by simp [toZFSet_simps, ofNat_eq_natCast]


-- @@ L92-92 verbatim
lemma natCast_succ {n : ℕ} : ((n + 1 : ℕ) : M) = succ (n : M) := by simp [toZFSet_simps]


-- @@ L94-95 verbatim
lemma toZFSet_nat_mem_ωₛ {n : ℕ} : Ordinal.toZFSet n ∈ ωₛ := by
  simpa only [ωₛ] using toZFSet_mem_toZFSet_iff.mpr <| natCast_lt_omega0 _


-- @@ L97-100 verbatim
lemma eq_natCast_of_mem_ωₛ {α} (hα : α ∈ ωₛ) : ∃ n : ℕ, α = Ordinal.toZFSet n := by
  have ord_α := (isOrdinal_toZFSet _).mem hα
  obtain ⟨α, ⟨_⟩⟩ := isOrdinal_iff_mem_range_toZFSet.mp ord_α
  simpa [ωₛ, toZFSet_mem_toZFSet_iff, lt_omega0, toZFSet_strictMono.injective.eq_iff] using hα


-- @@ L102-106 verbatim
lemma nwf_rev_of_ωₛ_le {α} (hα : ωₛ ≤ α) : ¬WellFounded (fun x y : α => y ∈ x) := by
  intro h
  rw [wellFounded_iff_isEmpty_descending_chain] at h
  refine h.false ⟨fun n => ⟨Ordinal.toZFSet n, hα toZFSet_nat_mem_ωₛ⟩, ?_⟩
  simpa only [mem_inside_ZFSet] using fun n => toZFSet_mem_toZFSet_iff.mpr (by simp)


-- @@ L108-118 verbatim
lemma wf_rev_of_lt_ωₛ {α} (hα : α ∈ ωₛ) : WellFounded (fun x y : α => y ∈ x) := by
  refine @Finite.wellFounded_of_trans_of_irrefl _ ?_  _ ?_ ?_
  · obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_mem_ωₛ hα
    erw [← mk_lt_aleph0_iff, cardinalMk_coe_sort]
    simp only [card_toZFSet, lift_lt_aleph0, card_lt_aleph0, natCast_lt_omega0]
  · have ord_α := (isOrdinal_toZFSet _).mem hα
    refine ⟨fun x y z hy hz => ?_⟩
    simp only [mem_inside_ZFSet] at *
    exact ord_α.2 hz hy x.2
  · refine ⟨fun x => ?_⟩
    simp [mem_inside_ZFSet, mem_irrefl]


-- @@ L120-121 expanded
@[toV_simps]
lemma MemOmega.toV (n : M) : MemOmega (toV n) ↔ MemOmega n := by simp only [MemOmega, toV_simps]


-- @@ L123-132 expanded
@[toZFSet_simps]
lemma MemOmega.toZFSet (n : M) : MemOmega n ↔ toZFSet n ∈ ωₛ :=
  by
  rw [← MemOmega.toV, MemOmega]
  conv_rhs => rw [← ToZFSet.toZFSet_toV]
  generalize toV n = n
  refine
    ⟨fun
      | ⟨ord, wf_rev⟩ => ?_, fun sub => ?_⟩
  · simp only [toZFSet_simps] at ord wf_rev
    exact
      (ord.mem_or_subset (isOrdinal_toZFSet _)).resolve_right fun sub => nwf_rev_of_ωₛ_le sub wf_rev
  · simpa only [toZFSet_simps] using ⟨(isOrdinal_toZFSet _).mem sub, wf_rev_of_lt_ωₛ sub⟩


-- @@ L134-136 verbatim
lemma eq_natCast_of_memOmega {α : M} (hα : MemOmega α) : ∃ n : ℕ, α = n := by
  simp only [toZFSet_simps] at hα ⊢
  exact eq_natCast_of_mem_ωₛ hα


-- @@ L138-139 verbatim
lemma memOmega_natCast {n : ℕ} : MemOmega (n : M) := by
  simp only [toZFSet_simps, toZFSet_nat_mem_ωₛ]


-- @@ L141-151 expanded
@[realize]
lemma ωₘ.eu : IsSet {n : M₀ | MemOmega n} :=
  by
  rw [isSet_iff]
  (rcases hM₀ with ⟨μ, hμ, omega_lt_μ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; have _ := Fact.mk hμ)
  · refine ⟨⟨ωₛ, by simpa [ωₛ, mem_vonNeumann]⟩, ?_⟩
    intro y hy
    rw [Set.mem_ofPred_eq, MemOmega.toZFSet] at hy
    rwa [ToZFSet.mem, ToZFSet.toZFSet_vonNeumann]
  · refine ⟨toV ωₛ, ?_⟩
    intro y hy
    rw [Set.mem_ofPred_eq, MemOmega.toZFSet] at hy
    rwa [ToZFSet.mem, ToZFSet.toV_ZFSet, ToZFSet.toZFSet_V]


-- @@ L153-154 verbatim
@[simp] lemma natCast_mem_ωₘ {n : ℕ} : (n : M₀) ∈ (ωₘ : M₀) := by
  simp only [ωₘ.spec, memOmega_natCast]


-- @@ L156-163 expanded
@[toV_simps]
lemma ωₘ.toV : ωₘ = toV (ωₘ : M₀) :=
  by
  rw [ωₘ.eq_iff, ToV.forall_mem_toV_iff]
  · simpa only [toV_simps] using ωₘ.spec
  · intro α hα
    simp only [toZFSet_simps] at hα ⊢
    generalize α.val = α at *
    obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_mem_ωₛ hα
    exact ⟨n, by simp only [toZFSet_simps]⟩


-- @@ L165-168 expanded
@[toZFSet_simps]
lemma ωₘ.toZFSet : toZFSet (ωₘ : M₀) = ωₛ :=
  by
  rw [← ToZFSet.toZFSet_toV, ← ωₘ.toV]
  have (x : V) : x ∈ (ωₘ : V) ↔ toZFSet x ∈ ωₛ := by rw [ωₘ.spec, MemOmega.toZFSet]
  simpa [ZFSet.ext_iff, toZFSet_simps] using this


-- @@ L170-172 verbatim
@[simp] lemma isOrdinal_ωₘ : IsOrdinal (ωₘ : M₀) := by
  rw [IsOrdinal.toZFSet, ωₘ.toZFSet, ωₛ]
  exact isOrdinal_toZFSet _


-- @@ L174-181 verbatim
/-- The `omegaEquiv` declaration. -/
def omegaEquiv : (ωₘ : M₀) ≃ ℕ :=
  Equiv.symm <| Equiv.ofBijective (fun n => ⟨Nat.cast n, natCast_mem_ωₘ⟩) <| by
    simp only [Bijective, Injective, Surjective, toZFSet_simps, Subtype.forall,
      Subtype.mk.injEq, toZFSet_strictMono.injective.eq_iff]
    refine ⟨fun m n eq => ?_, fun α hα => ?_⟩
    · simp_all
    · simpa only [eq_comm] using eq_natCast_of_mem_ωₛ hα


-- @@ L183-184 verbatim
instance {n : ℕ} : OfNat (Ordinals M) n where
  ofNat := ⟨(n : M), memOmega_natCast.1⟩


-- @@ L186-186 verbatim
end SetTheory
