/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.Crystal.Signed


-- @@ L8-14 verbatim
/-! # Original arbitrary PBW preimages have unique signed crystal residues

All integral, lattice, and norm conditions are discharged for the actual PBW preimages.
Uniqueness is of sign and crystal residue class, never of the representing word.
Fixed-reduced-word injectivity follows from actual PBW orthogonality. No global basis
or reduced-word independence assertion is made.
-/

-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
open LieLean LieLean.QuantumGroup LusztigF GrandLoop

-- @@ L17-17 verbatim
open scoped Pointwise

-- @@ L18-18 verbatim
namespace PBWSignedCrystal

-- @@ L19-19 verbatim
local notation "K" => RatFunc ℚ

-- @@ L20-20 verbatim
local notation "v" => (RatFunc.X : K)

-- @@ L21-21 verbatim
local notation "A" => InfinityLocalRing

-- @@ L22-22 verbatim
local notation "π" => InfinityLocalRing.uniformizer

-- @@ L23-23 verbatim
attribute [local instance] neZero_ratFunc_X

-- @@ L24-24 verbatim
variable {I : Type*} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}

-- @@ L25-25 verbatim
local notation "L" => latInf (D := D) transcendental_ratFunc_X A

-- @@ L26-26 verbatim
local notation "P" => π • L

-- @@ L27-27 verbatim
local notation "B" => fWi (D := D) transcendental_ratFunc_X


-- @@ L29-30 verbatim
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}


-- @@ L32-48 verbatim
/-- Unique signed crystal residue of every original arbitrary integral PBW preimage.
There are no additional integral, lattice, norm, homogeneous, finite-Weyl-group,
longest-word, root-independence, or regularity premises. -/
theorem original_PBW_unique_signed {w : List I} (hw : cs.IsReduced w)
    (c : Fin w.length → ℕ) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P ∧ B u ∉ P ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) ∉ P ∧
      ∀ (t : List I) (f : ℤ), (f = 1 ∨ f = -1) →
        (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
          (f : K) • B t ∈ P → e = f ∧ B u - B t ∈ P := by
  apply unique_signed_crystal_residue D
  · simpa only [LinearEquiv.apply_symm_apply] using
      (Modified.integralPBWPreimage R hw c).property
  · exact PBWProductNorm.mem_lattice_degree R hw c
  · exact PBWProductNorm.norm_residue R hw c


-- @@ L50-56 verbatim
/-- Actual PBW residues for one fixed reduced word distinguish all exponent tuples. -/
theorem original_PBW_residue_injective {w : List I} (hw : cs.IsReduced w)
    (c d : Fin w.length → ℕ)
    (h : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw d) ∈ P) : c = d := by
  by_contra hcd
  exact pbw_sub_smul_not_mem_uniformizer R hw c d hcd 1 (by simpa using h)


-- @@ L58-68 verbatim
/-- Unsigned crystal classes selected from the signed PBW residues are injective for a
fixed reduced word, even when the two signs differ. -/
theorem original_PBW_unsigned_injective {w : List I} (hw : cs.IsReduced w)
    (c d : Fin w.length → ℕ) {e f : ℤ} {u t : List I}
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hc : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
      (e : K) • B u ∈ P)
    (hd : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw d) -
      (f : K) • B t ∈ P)
    (hut : B u - B t ∈ P) : c = d :=
  pbw_unsigned_residue_injective R hw c d he hf hc hd hut


-- @@ L70-76 verbatim
/-- Empty reduced words are included, with no nonempty or positive-degree premise. -/
theorem original_PBW_empty_signed (hw : cs.IsReduced []) (c : Fin [].length → ℕ) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P := by
  obtain ⟨u, e, he, hx, -⟩ := original_PBW_unique_signed R hw c
  exact ⟨u, e, he, hx⟩


-- @@ L78-84 verbatim
/-- The all-zero exponent tuple is included for every reduced word. -/
theorem original_PBW_zero_signed {w : List I} (hw : cs.IsReduced w) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw (fun _ ↦ 0)) -
        (e : K) • B u ∈ P := by
  obtain ⟨u, e, he, hx, -⟩ := original_PBW_unique_signed R hw (fun _ ↦ 0)
  exact ⟨u, e, he, hx⟩

-- @@ L85-85 verbatim
end PBWSignedCrystal
