/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.IntrinsicDegree


-- @@ L8-12 verbatim
/-! # Uniqueness and fixed-word injectivity of signed crystal residues

These proofs use the original PBW preimages and their actual bilinear form.
They do not assert independence of the reduced word or existence of global basis lifts.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open LieLean LieLean.QuantumGroup LusztigF GrandLoop

-- @@ L16-16 verbatim
open scoped Pointwise

-- @@ L17-17 verbatim
namespace PBWSignedCrystal

-- @@ L18-18 verbatim
local notation "K" => RatFunc ℚ

-- @@ L19-19 verbatim
local notation "v" => (RatFunc.X : K)

-- @@ L20-20 verbatim
local notation "A" => InfinityLocalRing

-- @@ L21-21 verbatim
local notation "π" => InfinityLocalRing.uniformizer

-- @@ L22-22 verbatim
attribute [local instance] neZero_ratFunc_X

-- @@ L23-23 verbatim
variable {I : Type*} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}

-- @@ L24-24 verbatim
local notation "L" => latInf (D := D) transcendental_ratFunc_X A

-- @@ L25-25 verbatim
local notation "P" => π • L

-- @@ L26-26 verbatim
local notation "B" => fWi (D := D) transcendental_ratFunc_X

-- @@ L27-27 verbatim
local notation "F" => formU (D := D) (pow_ne_one_of_transcendental' transcendental_ratFunc_X)


-- @@ L29-37 verbatim
/-- An integer cannot disappear into the uniformizer ideal unless it is zero. -/
lemma int_eq_zero_of_uniformizer (n : ℤ) (a : A)
    (h : (n : K) = algebraMap A K (π * a)) : n = 0 := by
  have he : (n : A) = π * a := InfinityLocalRing.injective_algebraMap (by simpa using h)
  have hr := congrArg Sl2.RankOne.residue he
  change Sl2.RankOne.residue (n : Sl2.RankOne.LocalRing) =
    Sl2.RankOne.residue (Sl2.RankOne.localX * (show Sl2.RankOne.LocalRing from a)) at hr
  rw [map_mul, Sl2.RankOne.residue_localX, zero_mul, map_intCast] at hr
  exact_mod_cast hr


-- @@ L39-46 verbatim
/-- The actual form pairs the lattice with its uniformizer multiple into `π A`. -/
lemma form_mem_uniformizer {x y : Um D v} (hx : x ∈ L) (hy : y ∈ P) :
    ∃ a : A, F x y = algebraMap A K (π * a) := by
  let := Fintype.ofFinite I
  exact formU_mem_smul (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hx hy


-- @@ L48-54 verbatim
/-- Every word gives a nonzero crystal residue. -/
theorem word_not_mem_uniformizer (u : List I) : B u ∉ P := by
  let := Fintype.ofFinite I
  exact fWi_notMem (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum u


-- @@ L56-65 verbatim
open scoped Classical in
/-- Distinct unsigned crystal classes are orthogonal; equal ones have norm residue one. -/
lemma word_pairing (u t : List I) :
    ∃ a : A, F (B u) (B t) = (if B u - B t ∈ P then 1 else 0) +
      algebraMap A K (π * a) := by
  let := Fintype.ofFinite I
  exact formU_fWi_fWi (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum u t


-- @@ L67-88 verbatim
/-- No word residue is the negative of another word residue. -/
theorem word_add_not_mem_uniformizer (u t : List I) : B u + B t ∉ P := by
  intro h
  obtain ⟨a, ha⟩ := word_pairing (D := D) u u
  obtain ⟨b, hb⟩ := word_pairing (D := D) u t
  obtain ⟨c, hc⟩ := form_mem_uniformizer
    (NegativePart.fWord_mem_latticeInf _ _ u) h
  simp only [sub_self, Submodule.zero_mem, ite_true] at ha
  rw [map_add, ha, hb] at hc
  by_cases ht : B u - B t ∈ P
  · rw [ite_eq_left ht] at hc
    have he : (2 : K) = algebraMap A K (π * (c - a - b)) := by
      simp only [mul_sub, map_sub]
      linear_combination hc
    have := int_eq_zero_of_uniformizer 2 (c - a - b) he
    norm_num at this
  · rw [ite_eq_right ht] at hc
    have he : (1 : K) = algebraMap A K (π * (c - a - b)) := by
      simp only [mul_sub, map_sub]
      linear_combination hc
    have := int_eq_zero_of_uniformizer 1 (c - a - b) (by simpa using he)
    norm_num at this


-- @@ L90-105 verbatim
/-- A signed word representative has a unique sign and a unique unsigned word class. -/
theorem signed_residue_unique {x : Um D v} {e f : ℤ} {u t : List I}
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hx : x - (e : K) • B u ∈ P) (hy : x - (f : K) • B t ∈ P) :
    e = f ∧ B u - B t ∈ P := by
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · refine ⟨rfl, ?_⟩
    simpa using sub_mem hy hx
  · exfalso
    apply word_add_not_mem_uniformizer u t
    simpa [add_comm] using sub_mem hy hx
  · exfalso
    apply word_add_not_mem_uniformizer u t
    simpa using sub_mem hx hy
  · refine ⟨rfl, ?_⟩
    simpa using sub_mem hx hy


-- @@ L107-107 verbatim
section PBW

-- @@ L108-108 verbatim
open Modified

-- @@ L109-109 verbatim
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

-- @@ L110-111 verbatim
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

-- @@ L112-114 verbatim
/-- The original PBW preimage viewed in the actual Serre quotient. -/
abbrev pbwNegative {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) : Um D v :=
  (negativeQuotientEquiv D).symm (integralPBWPreimage R hw c)

-- @@ L115-115 verbatim
local notation "X" => pbwNegative R


-- @@ L117-134 verbatim
/-- Unequal exponents in a fixed reduced word cannot have scalar-proportional residues.
The proof uses actual PBW orthogonality, not a word-independence hypothesis. -/
theorem pbw_sub_smul_not_mem_uniformizer {w : List I} (hw : cs.IsReduced w)
    (c d : Fin w.length → ℕ) (hcd : c ≠ d) (s : K) :
    X hw c - s • X hw d ∉ P := by
  intro h
  obtain ⟨a, ha⟩ := PBWProductNorm.norm_residue R hw c
  have ho := PBWProductNorm.orthogonal R hw c d hcd
  change F (X hw c) (X hw c) = _ at ha
  change F (X hw c) (X hw d) = 0 at ho
  obtain ⟨b, hb⟩ := form_mem_uniformizer (PBWProductNorm.mem_lattice_degree R hw c) h
  rw [map_sub, map_smul, ho, smul_zero, sub_zero, ha] at hb
  have he : (1 : K) = algebraMap A K (π * (b - a)) := by
    simp only [mul_sub, map_sub]
    simp only [map_add, _root_.map_one] at hb
    linear_combination hb
  have := int_eq_zero_of_uniformizer 1 (b - a) (by simpa using he)
  norm_num at this


-- @@ L136-160 verbatim
/-- Unsigned residues of signed representatives of different fixed-word PBW monomials differ. -/
theorem pbw_unsigned_residue_injective {w : List I} (hw : cs.IsReduced w)
    (c d : Fin w.length → ℕ) {e f : ℤ} {u t : List I}
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hc : X hw c - (e : K) • B u ∈ P)
    (hd : X hw d - (f : K) • B t ∈ P)
    (hut : B u - B t ∈ P) : c = d := by
  by_contra hcd
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · apply pbw_sub_smul_not_mem_uniformizer R hw c d hcd 1
    convert add_mem (sub_mem hc hd) hut using 1
    simp
    abel
  · apply pbw_sub_smul_not_mem_uniformizer R hw c d hcd (-1)
    convert add_mem (add_mem hc hd) hut using 1
    simp
    abel
  · apply pbw_sub_smul_not_mem_uniformizer R hw c d hcd (-1)
    convert sub_mem (add_mem hc hd) hut using 1
    simp
    abel
  · apply pbw_sub_smul_not_mem_uniformizer R hw c d hcd 1
    convert sub_mem (sub_mem hc hd) hut using 1
    simp
    abel

-- @@ L161-161 verbatim
end PBW

-- @@ L162-162 verbatim
end PBWSignedCrystal
