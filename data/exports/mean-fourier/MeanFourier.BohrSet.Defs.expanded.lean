/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.UnitaryDual

import Mathlib.LinearAlgebra.Complex.FiniteDimensional


-- @@ L12-14 verbatim
/-!
# Bohr sets
-/


-- @@ L16-16 verbatim
public section


-- @@ L18-18 verbatim
open scoped ENNReal NNReal Finset


-- @@ L20-20 verbatim
variable {G : Type*}


-- @@ L22-38 verbatim
variable (G) in
/-- A *Bohr set* `B` on a group `G` is a finite set of unitary representations of `G`, called the
*frequencies*, along with an extended non-negative real number for each frequency `ψ`, called the
*width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`. This is
the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B` (in particular, it does not uniquely
determine either `B.frequencies` or `B.width`). -/
@[ext]
structure BohrSet [Group G] where
  frequencies : Finset (UnitaryDual ℂ G)
  /-- The width of a Bohr set at a frequency. Note that this width corresponds to chord-length. -/
  ewidth : UnitaryDual ℂ G → ℝ≥0∞
  mem_frequencies : ∀ ψ, ψ ∈ frequencies ↔ ewidth ψ < ⊤


-- @@ L40-40 verbatim
namespace BohrSet

-- @@ L41-41 verbatim
section Group

-- @@ L42-42 verbatim
variable [Group G] {B : BohrSet G} {ψ : UnitaryDual ℂ G} {x y : G}


-- @@ L44-44 verbatim
def width (B : BohrSet G) (ψ : UnitaryDual ℂ G) : ℝ≥0 := (B.ewidth ψ).toNNReal


-- @@ L46-48 verbatim
lemma coe_width (hψ : ψ ∈ B.frequencies) : B.width ψ = B.ewidth ψ := by
  refine ENNReal.coe_toNNReal ?_
  rwa [← lt_top_iff_ne_top, ← B.mem_frequencies]


-- @@ L50-51 verbatim
lemma ewidth_eq_top_iff : ψ ∉ B.frequencies ↔ B.ewidth ψ = ⊤ := by
  simp [B.mem_frequencies]


-- @@ L53-53 verbatim
alias ⟨ewidth_eq_top_of_not_mem_frequencies, _⟩ := ewidth_eq_top_iff


-- @@ L55-56 verbatim
lemma width_eq_zero_of_not_mem_frequencies (hψ : ψ ∉ B.frequencies) : B.width ψ = 0 := by
  rw [width, ewidth_eq_top_of_not_mem_frequencies hψ, ENNReal.toNNReal_top]


-- @@ L58-62 verbatim
lemma ewidth_injective : Function.Injective (BohrSet.ewidth (G := G)) := by
  intro B₁ B₂ h
  ext ψ
  case ewidth => rw [h]
  case frequencies => rw [B₁.mem_frequencies, B₂.mem_frequencies, h]


-- @@ L64-68 verbatim
/-- Construct a Bohr set on a finite group given an extended width function. -/
noncomputable def ofEwidth [Finite G] (ρ : UnitaryDual ℂ G → ℝ≥0∞) : BohrSet G where
  frequencies := {ψ | ρ ψ < ⊤}
  ewidth := ρ
  mem_frequencies ψ := by simp


-- @@ L70-75 verbatim
/-- Construct a Bohr set on a finite group given a width function and a frequency set. -/
noncomputable def ofWidth (Γ : Finset (UnitaryDual ℂ G)) (ρ : UnitaryDual ℂ G → ℝ≥0) :
    BohrSet G where
  frequencies := Γ
  ewidth ψ := open scoped Classical in if ψ ∈ Γ then ρ ψ else ⊤
  mem_frequencies ψ := by simp [lt_top_iff_ne_top]


-- @@ L77-90 verbatim
@[ext]
lemma ext_width {B B' : BohrSet G} (freq : B.frequencies = B'.frequencies)
    (width : ∀ ψ : UnitaryDual ℂ G, ψ ∈ B.frequencies → B.width ψ = B'.width ψ) :
    B = B' := by
  ext
  case frequencies => rw [freq]
  case ewidth ψ =>
    by_cases hψ : ψ ∈ B.frequencies
    case pos =>
      rw [← coe_width hψ, width _ hψ, coe_width]
      rwa [← freq]
    case neg =>
      rw [ewidth_eq_top_of_not_mem_frequencies hψ, ewidth_eq_top_of_not_mem_frequencies]
      rwa [← freq]


-- @@ L92-92 verbatim
/-! ### Coercion, membership -/


-- @@ L94-100 verbatim
/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`.
This is the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B`. -/
@[coe] def chordSet (B : BohrSet G) : Set G :=
  {x | ∀ ψ, ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ ≤ B.ewidth ψ}


-- @@ L102-102 verbatim
scoped notation3 "Bohr(" Γ", " ρ ")" => (ofWidth Γ ρ).chordSet


-- @@ L104-105 verbatim
/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe] abbrev Elem (B : BohrSet G) : Type _ := B.chordSet


-- @@ L107-107 verbatim
instance instCoe : Coe (BohrSet G) (Set G) := ⟨chordSet⟩

-- @@ L108-108 verbatim
instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩


-- @@ L110-111 verbatim
lemma mem_chordSet_iff_nnnorm_ewidth :
    x ∈ B.chordSet ↔ ∀ ψ, ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ ≤ B.ewidth ψ := .rfl


-- @@ L113-127 verbatim
lemma mem_chordSet_iff_nnnorm_width :
    x ∈ B.chordSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ ≤ B.width ψ := by
  refine forall_congr' fun ψ => ?_
  constructor
  case mpr =>
    intro h
    rcases eq_top_or_lt_top (B.ewidth ψ) with h₁ | h₁
    case inl => simp [h₁]
    case inr =>
      have : ψ ∈ B.frequencies := by simp [mem_frequencies, h₁]
      specialize h this
      rwa [← ENNReal.coe_le_coe, coe_width this] at h
  case mp =>
    intro h₁ h₂
    rwa [← ENNReal.coe_le_coe, coe_width h₂]


-- @@ L129-131 verbatim
lemma mem_chordSet_iff_norm_width :
    x ∈ B.chordSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖ ≤ B.width ψ :=
  mem_chordSet_iff_nnnorm_width


-- @@ L133-133 verbatim
@[simp, norm_cast] lemma coeSort_coe (B : BohrSet G) : ↥(B : Set G) = B := rfl


-- @@ L135-135 verbatim
@[simp] lemma one_mem_chordSet : 1 ∈ B.chordSet := by simp [mem_chordSet_iff_nnnorm_width]


-- @@ L137-141 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma inv_mem_chordSet : x⁻¹ ∈ B.chordSet ↔ x ∈ B.chordSet := by
  refine forall_congr' fun ψ ↦ ?_
  rw [← nnnorm_map ContinuousLinearMap.adjoint]
  simp [-LinearIsometryEquiv.toContinuousLinearEquiv_symm, LinearIsometryEquiv.inv_def]


-- @@ L143-143 verbatim
@[simp] lemma inv_chordSet : B.chordSet⁻¹ = B.chordSet := by ext; simp


-- @@ L145-152 verbatim
@[simp] lemma conj_mem_chordSet : y * x * y⁻¹ ∈ B.chordSet ↔ x ∈ B.chordSet := by
  simp only [mem_chordSet_iff_nnnorm_ewidth]
  congr! 3 with ψ
  calc
    ‖1 - (ψ.ρ (y * x * y⁻¹) : ψ.E →L[ℂ] ψ.E)‖₊
    _ = ‖ψ.ρ y * (1 - ψ.ρ x : ψ.E →L[ℂ] ψ.E) * ψ.ρ y⁻¹‖₊ := by
      simp [mul_sub, sub_mul, ← ContinuousLinearEquiv.toContinuousLinearMap_mul]
    _ = ‖1 - (ψ.ρ x : ψ.E →L[ℂ] ψ.E)‖₊ := by simp [-map_inv]


-- @@ L154-154 verbatim
/-! ### Lattice structure -/


-- @@ L156-161 verbatim
noncomputable instance : Max (BohrSet G) where
  max B₁ B₂ := {
    frequencies := B₁.frequencies ∩ B₂.frequencies,
    ewidth ψ := B₁.ewidth ψ ⊔ B₂.ewidth ψ,
    mem_frequencies ψ := by simp [mem_frequencies]
  }


-- @@ L163-168 verbatim
noncomputable instance : Min (BohrSet G) where
  min B₁ B₂ := {
    frequencies := B₁.frequencies ∪ B₂.frequencies,
    ewidth ψ := B₁.ewidth ψ ⊓ B₂.ewidth ψ,
    mem_frequencies ψ := by simp [mem_frequencies]
  }


-- @@ L170-173 verbatim
noncomputable instance [Finite G] : Bot (BohrSet G) where
  bot.frequencies := .univ
  bot.ewidth := 0
  bot.mem_frequencies := by simp


-- @@ L175-178 verbatim
noncomputable instance : Top (BohrSet G) where
  top.frequencies := ∅
  top.ewidth := ⊤
  top.mem_frequencies := by simp


-- @@ L180-180 verbatim
instance : Preorder (BohrSet G) := .lift ewidth


-- @@ L182-183 verbatim
noncomputable instance : DistribLattice (BohrSet G) :=
  ewidth_injective.distribLattice BohrSet.ewidth .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)


-- @@ L185-185 verbatim
lemma le_iff_ewidth {B₁ B₂ : BohrSet G} : B₁ ≤ B₂ ↔ ∀ ⦃ψ⦄, B₁.ewidth ψ ≤ B₂.ewidth ψ := .rfl


-- @@ L187-191 verbatim
@[gcongr]
lemma frequencies_anti {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) : B₂.frequencies ⊆ B₁.frequencies := by
  intro ψ hψ
  simp only [mem_frequencies] at hψ ⊢
  exact (h ψ).trans_lt hψ


-- @@ L193-193 verbatim
lemma frequencies_antitone : Antitone (frequencies : BohrSet G → _) := fun _ _ ↦ frequencies_anti


-- @@ L195-208 verbatim
lemma le_iff_width {B₁ B₂ : BohrSet G} :
    B₁ ≤ B₂ ↔
      B₂.frequencies ⊆ B₁.frequencies ∧ ∀ ⦃ψ⦄, ψ ∈ B₂.frequencies → B₁.width ψ ≤ B₂.width ψ where
  mp h := by
    refine ⟨frequencies_anti h, fun ψ hψ => ?_⟩
    rw [← ENNReal.coe_le_coe, coe_width hψ, coe_width (frequencies_anti h hψ)]
    exact h ψ
  mpr := by
    rintro ⟨h₁, h₂⟩ ψ
    by_cases ψ ∈ B₂.frequencies
    case neg h' => simp [ewidth_eq_top_of_not_mem_frequencies h']
    case pos h' =>
      rw [← coe_width h', ← coe_width (h₁ h'), ENNReal.coe_le_coe]
      exact h₂ h'


-- @@ L210-214 verbatim
@[gcongr]
lemma width_le_width {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) (hψ : ψ ∈ B₂.frequencies) :
    B₁.width ψ ≤ B₂.width ψ := by
  rw [le_iff_width] at h
  exact h.2 hψ


-- @@ L216-216 verbatim
noncomputable instance : OrderTop (BohrSet G) := .lift BohrSet.ewidth (fun _ _ h => h) rfl


-- @@ L218-224 verbatim
open scoped Classical in
noncomputable instance [Finite G] : SupSet (BohrSet G) where
  sSup B := {
    frequencies := {ψ | ⨆ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨆ i ∈ B, ewidth i ψ
    mem_frequencies := by simp
  }


-- @@ L226-228 verbatim
lemma iInf_lt_top {α β : Type*} [CompleteLattice β] {S : Set α} {f : α → β} :
    (⨅ i ∈ S, f i) < ⊤ ↔ ∃ i ∈ S, f i < ⊤ := by
  simp [lt_top_iff_ne_top]


-- @@ L230-236 verbatim
open scoped Classical in
noncomputable instance [Finite G] : InfSet (BohrSet G) where
  sInf B := {
    frequencies := {ψ | ∃ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨅ i ∈ B, ewidth i ψ
    mem_frequencies := by simp
  }


-- @@ L238-243 verbatim
noncomputable instance [Finite G] : CompleteLattice (BohrSet G) :=
  ewidth_injective.completeLattice BohrSet.ewidth .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun B ↦ by ext ψ; simp only [iSup_apply]; rfl)
    (fun B ↦ by ext ψ; simp only [iInf_apply]; rfl)
    rfl
    rfl


-- @@ L245-247 verbatim
noncomputable instance [Finite G] : CompletelyDistribLattice (BohrSet G) := by
  refine .ofMinimalAxioms <| ewidth_injective.completelyDistribLatticeMinimalAxioms .of ewidth ?_ ?_
    <;> · intros; ext; simp only [iSup_apply, iInf_apply]; rfl


-- @@ L249-249 verbatim
/-! ### Width, frequencies, rank -/


-- @@ L251-252 verbatim
/-- The cardinality rank of a Bohr set is its number of frequencies. -/
def cardRank (B : BohrSet G) : ℕ := #B.frequencies


-- @@ L254-254 verbatim
@[simp] lemma card_frequencies (B : BohrSet G) : #B.frequencies = B.cardRank := by rfl


-- @@ L256-257 verbatim
/-- The dimension rank of a Bohr set is the sum of the dimensions of its frequencies. -/
noncomputable def dimRank (B : BohrSet G) : ℕ := ∑ ψ ∈ B.frequencies, Module.finrank ℂ ψ.E


-- @@ L259-261 verbatim
/-- The squared dimension rank of a Bohr set is the sum of the squares of the dimensions of its
frequencies. -/
noncomputable def dimSqRank (B : BohrSet G) : ℕ := ∑ ψ ∈ B.frequencies, Module.finrank ℂ ψ.E ^ 2


-- @@ L263-267 verbatim
lemma cardRank_le_dimRank : B.cardRank ≤ B.dimRank := by
  rw [← card_frequencies, Finset.card_eq_sum_ones, dimRank]
  gcongr with ψ
  rw [Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, Module.finrank_pos_iff]
  infer_instance


-- @@ L269-269 verbatim
/-! ### Dilation -/


-- @@ L271-271 verbatim
section smul

-- @@ L272-272 verbatim
variable {ρ : ℝ}


-- @@ L274-275 verbatim
lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ :=
  ENNReal.mul_lt_top (by simp) hy


-- @@ L277-285 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma nnreal_smul_lt_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y < ⊤ ↔ y < ⊤ := by
  constructor
  case mpr => exact nnreal_smul_lt_top
  case mp =>
    intro h
    by_contra hy
    simp only [top_le_iff, not_lt] at hy
    simp [hy, ENNReal.smul_top, hx] at h


-- @@ L287-288 verbatim
lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) hy


-- @@ L290-297 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma nnreal_smul_ne_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y ≠ ⊤ ↔ y ≠ ⊤ := by
  constructor
  case mpr => exact nnreal_smul_ne_top
  case mp =>
    intro h
    by_contra hy
    simp [hy, ENNReal.smul_top, hx] at h


-- @@ L299-305 verbatim
noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := BohrSet.mk B.frequencies
      (fun ψ => if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤) fun ψ => by
        simp only [lt_top_iff_ne_top, ite_ne_right_iff, iff_self_and]
        intro hψ
        refine ENNReal.mul_ne_top (by simp) ?_
        rwa [← lt_top_iff_ne_top, ← mem_frequencies]


-- @@ L307-307 verbatim
@[simp] lemma frequencies_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).frequencies = B.frequencies := rfl

-- @@ L308-308 verbatim
@[simp] lemma cardRank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).cardRank = B.cardRank := by rfl

-- @@ L309-309 verbatim
@[simp] lemma dimRank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).dimRank = B.dimRank := by rfl


-- @@ L311-312 verbatim
@[simp] lemma ewidth_smul (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).ewidth ψ = if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤ := rfl


-- @@ L314-316 verbatim
@[simp] lemma width_smul_apply (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).width ψ = Real.nnabs ρ * B.width ψ := by
  rw [width, ewidth_smul]; split <;> simp [← coe_width, width_eq_zero_of_not_mem_frequencies, *]


-- @@ L318-320 verbatim
lemma width_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).width = Real.nnabs ρ • B.width := by
  ext ψ
  simp [width_smul_apply]


-- @@ L322-324 verbatim
noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := by ext <;> simp
  mul_smul ρ φ B := by ext <;> simp [mul_assoc]


-- @@ L326-328 verbatim
end smul

-- Note it is not sufficient to say B.width = 0.

-- @@ L329-345 verbatim
lemma eq_singleton_one_of_ewidth_eq_zero {B : BohrSet G} (h : B.ewidth = 0) :
    B.chordSet = {1} := by
  rw [Set.eq_singleton_iff_unique_mem]
  simp only [mem_chordSet_iff_nnnorm_width, map_one,
    LinearIsometryEquiv.toContinuousLinearEquiv_one,
    ContinuousLinearEquiv.toContinuousLinearMap_one, sub_self, nnnorm_zero, zero_le, implies_true,
    true_and]
  intro x hx
  by_contra!
  sorry
  -- rw [←AddChar.exists_apply_ne_zero] at this
  -- obtain ⟨ψ, hψ⟩ := this
  -- apply hψ
  -- have hψ' : ψ ∈ B.frequencies := by simp [B.mem_frequencies, h]
  -- specialize hx hψ'
  -- rwa [B.width_def, h, Pi.zero_apply, ENNReal.toNNReal_zero, nonpos_iff_eq_zero, nnnorm_eq_zero,
  --   sub_eq_zero, eq_comm] at hx


-- @@ L347-352 verbatim
lemma chordSet_eq_top_of_two_le_width {B : BohrSet G} (h : ∀ ψ, 2 ≤ B.width ψ) :
    B.chordSet = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_chordSet_iff_nnnorm_width]
  intro i ψ _
  grw [nnnorm_sub_le, ← h]
  norm_num


-- @@ L354-355 verbatim
@[gcongr] lemma chordSet_mono {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) : B₁.chordSet ⊆ B₂.chordSet :=
  fun _ hx ψ => (hx ψ).trans (h ψ)


-- @@ L357-357 verbatim
lemma chordSet_monotone : Monotone (chordSet : BohrSet G → Set G) := fun _ _ => chordSet_mono


-- @@ L359-359 verbatim
open Pointwise


-- @@ L361-370 verbatim
lemma chordSet_mul_chordSet_subset {B₁ B₂ B₃ : BohrSet G} (h : B₁.ewidth + B₂.ewidth ≤ B₃.ewidth) :
    B₁.chordSet * B₂.chordSet ⊆ B₃.chordSet := by
  intro x
  simp only [mem_chordSet_iff_nnnorm_ewidth, Set.mem_mul, forall_exists_index, and_imp]
  rintro x hx y hy rfl ψ
  rw [map_mul]
  have : ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E) * ψ y‖₊ ≤ ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ + _ :=
    nnnorm_sub_mul_le (by simp)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_add] at this
  exact this.trans <| (h _).trans' <| add_le_add (hx _) (hy _)


-- @@ L372-375 verbatim
lemma chordSet_smul_add_chordSet_smul_subset {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    (ρ₁ • B).chordSet * (ρ₂ • B).chordSet ⊆ ((ρ₁ + ρ₂) • B).chordSet :=
  chordSet_mul_chordSet_subset fun ψ => by
    simp only [Pi.add_apply, ewidth_smul]; split <;> simp [add_nonneg, add_mul, *]


-- @@ L377-383 verbatim
lemma chordSet_pow_subset : ∀ {n : ℕ}, B.chordSet ^ n ⊆ ((n : ℝ) • B).chordSet
  | 0 => by simp
  | n + 1 => by
    grw [pow_succ, chordSet_pow_subset]
    refine chordSet_mul_chordSet_subset fun ψ ↦ ?_
    simp [add_nonneg, add_one_mul]
    split <;> simp


-- @@ L385-385 verbatim
end Group


-- @@ L387-387 verbatim
section CommGroup

-- @@ L388-388 verbatim
variable [CommGroup G] {B : BohrSet G}


-- @@ L390-391 verbatim
variable (B) in
@[simp] lemma dimRank_eq_cardRank : B.dimRank = B.cardRank := by simp [dimRank]


-- @@ L393-394 verbatim
variable (B) in
@[simp] lemma dimSqRank_eq_cardRank : B.dimSqRank = B.cardRank := by simp [dimSqRank]


-- @@ L396-396 verbatim
end CommGroup

-- @@ L397-397 verbatim
end BohrSet
