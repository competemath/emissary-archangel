/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/
module

public import ArkLib.Data.CodingTheory.Basic.RelativeDistance


-- @@ L11-16 verbatim
/-!
# Decoding Radius for Codes

This module contains absolute and relative unique decoding radius definitions and the
standard lemmas relating decoding-radius bounds to code distance.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Code


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open NNReal

-- @@ L25-25 verbatim
open scoped NNReal

-- @@ L26-26 verbatim
section DecodingRadius


-- @@ L28-30 expanded
/-- The unique decoding radius: `≤ ⌊(d-1)/2⌋` for any code `C`. -/
noncomputable def uniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) : ℕ :=
  (hammingNorm C - 1) /
    2 -- Nat.division instead of Nat.floor


-- @@ L32-32 verbatim
alias UDR := uniqueDecodingRadius


-- @@ L34-39 expanded
/-- The relative unique decoding radius, obtained from the absolute radius by normalizing with the
block length. This also works with `≤`. -/
noncomputable def relativeUniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) : NNReal :=
  (((hammingNorm C : NNReal) - 1) / 2) /
    (Fintype.card ι : NNReal)
      -- TODO: define `Johnson bound` radius, capacity bounds, etc for generic code `C`


-- @@ L41-41 verbatim
alias relUDR := relativeUniqueDecodingRadius


-- @@ L43-66 expanded
@[simp]
lemma uniqueDecodingRadius_eq_floor_div_2 {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) :
    Code.uniqueDecodingRadius C = Nat.floor (((hammingNorm C - 1) : NNReal) / 2) :=
  by
  rw [uniqueDecodingRadius]
  apply Eq.symm
  set d := hammingNorm C
  set x_nat : NNReal := ((d - 1 : ℕ) : NNReal)
  set x_nnreal : NNReal :=
    (((d : NNReal) - 1) : NNReal)
      -- 5. These two real numbers are actually equal
      
  have h_eq : x_nat = x_nnreal := by
    -- rw [NNReal.sub_eq_cast_sub, NNReal.coe_nat_cast]
    
    dsimp only [x_nat, x_nnreal]
    by_cases h_d_ge_1 : d ≥ 1
    · simp only [Nat.cast_tsub, Nat.cast_one]
    · have h_d_eq_0 : d = 0 := by omega
      rw [h_d_eq_0]
      simp only [zero_tsub, CharP.cast_eq_zero]
  rw [← h_eq]; dsimp [x_nat];
  let res := Nat.floor_div_eq_div (K := NNReal) (m := (hammingNorm C - 1)) (n := 2)
  rw [Nat.cast_ofNat] at res
  exact res


-- @@ L68-75 expanded
/-- Given an error/proximity parameter `e` within the unique decoding radius of a code `C` where
`‖C‖₀ > 0`, this lemma proves the standard bound `2 * e < d`
(i.e. condition of `Code.eq_of_lt_dist`). -/
lemma UDRClose_iff_two_mul_proximity_lt_d_UDR {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) [NeZero (hammingNorm C)] {e : ℕ} :
    e ≤ Code.uniqueDecodingRadius (C := C) ↔ 2 * e < hammingNorm C :=
  (Nat.two_mul_lt_iff_le_half_of_sub_one (a := e) (b := hammingNorm C) (h_b_pos := by
      exact Nat.pos_of_neZero (hammingNorm C))).symm


-- @@ L77-105 expanded
/-- A stronger version of `distFromCode_eq_of_lt_half_dist`:
If two codewords `v` and `w` are both within the `uniqueDecodingRadius` of
`u` (i.e. `2 * Δ₀(u, v) < ‖C‖₀ and 2 * Δ₀(u, w) < ‖C‖₀`), then they must be equal. -/
theorem eq_of_le_uniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) (u : ι → F) {v w : ι → F} (hv : v ∈ C) (hw : w ∈ C)
    (huv : hammingDist u v ≤ Code.uniqueDecodingRadius C)
    (huw : hammingDist u w ≤ Code.uniqueDecodingRadius C) : v = w := by
  -- Handle the edge case where distance is 0 (trivial code)
  
  by_cases hd : hammingNorm C = 0
  · simp only [uniqueDecodingRadius] at huv huw
    simp only [hd, zero_tsub, Nat.zero_div, nonpos_iff_eq_zero, hammingDist_eq_zero] at huv huw
    rw [← huv, ← huw]
  · -- Main Case: d > 0
    
    apply eq_of_lt_dist hv hw
    calc
      hammingDist v w ≤ hammingDist v u + hammingDist u w := by exact hammingDist_triangle v u w
      _ = hammingDist u v + hammingDist u w := by simp only [hammingDist_comm]
      _ ≤ Code.uniqueDecodingRadius C + Code.uniqueDecodingRadius C := by gcongr
      _ < hammingNorm C := by
        -- Proof that 2 * ⌊(d-1)/2⌋ < d
        
        simp only [uniqueDecodingRadius]
          -- 2 * ((d - 1) / 2) ≤ d - 1
          
        have h_div : 2 * ((hammingNorm C - 1) / 2) ≤ hammingNorm C - 1 :=
          by
          rw [mul_comm]
          apply
            Nat.div_mul_le_self (m := hammingNorm C - 1) (n := 2)
              -- Since d ≠ 0, d - 1 < d
              
        have h_sub : hammingNorm C - 1 < hammingNorm C := Nat.pred_lt hd
        omega


-- @@ L107-187 expanded
/-- A word `u` is within the `uniqueDecodingRadius` of a code `C` if and only if
there exists *exactly one* codeword `v` in `C` that is that close.
-/
theorem UDR_close_iff_exists_unique_close_codeword {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    hammingDist u C ≤ Code.uniqueDecodingRadius C ↔
      ∃! v ∈ C, hammingDist u v ≤ Code.uniqueDecodingRadius C :=
  by
  -- 1. Define t (radius) and d (distance) for brevity
  
  set t := Code.uniqueDecodingRadius C
  set d := hammingNorm C
  constructor
  · -- (→) Direction 1: "Close" implies "Uniquely Close"
    
    intro h_dist_le_t
    let v := pickClosestCodeword_of_Nonempty_Code (C := C) (u := u)
    have h_close_to_v : hammingDist u v ≤ t :=
      by
      rw [distFromPickClosestCodeword_of_Nonempty_Code (C := C) (u := u)] at h_dist_le_t
      simp only [Nat.cast_le] at h_dist_le_t
      exact h_dist_le_t
    have h_exists : ∃ v, v ∈ C ∧ hammingDist u v ≤ t :=
      by
      use v
      simp only [Subtype.coe_prop, true_and]
      exact h_close_to_v
    have h_uniq :
      ∀ (v₁ : ι → F) (v₂ : ι → F),
        v₁ ∈ C → v₂ ∈ C → hammingDist u v₁ ≤ t → hammingDist u v₂ ≤ t → v₁ = v₂ :=
      by
      intro v₁ v₂ hv₁_mem hv₂_mem h_dist_v₁ h_dist_v₂
      have h_dist_v1_v2 : hammingDist v₁ v₂ ≤ hammingDist v₁ u + hammingDist u v₂ := by
        exact hammingDist_triangle v₁ u v₂
      rw [hammingDist_comm v₁ u] at h_dist_v1_v2
      have h_le_2t : hammingDist v₁ v₂ ≤ t + t :=
        h_dist_v1_v2.trans (Nat.add_le_add h_dist_v₁ h_dist_v₂)
      rw [← Nat.two_mul] at h_le_2t
      by_cases h_d_ge_2 : d ≥ 2
      · -- Case 1: d ≥ 2 (the standard case)
                -- We have t = ⌊(d-1)/2⌋. We know 2 * ⌊(d-1)/2⌋ ≤ d-1
        
        have h_2t_le_d_minus_1 : 2 * t ≤ d - 1 :=
          by
          dsimp only [d, t, uniqueDecodingRadius]
          rw [mul_comm]
          exact
            Nat.div_mul_le_self (hammingNorm C - 1)
              2
                -- Since d ≥ 2, we know d-1 < d
                
        have h_d_minus_1_lt_d : d - 1 < d :=
          by
          apply Nat.sub_lt_of_pos_le
          ·
            linarith -- d > 0
              
          ·
            linarith -- 1 > 0
                      -- Chain the inequalities: Δ₀(v₁, v₂) ≤ 2*t ≤ d-1 < d
              
        have h_dist_lt_d : hammingDist v₁ v₂ < d := by
          omega
            -- By `eq_of_lt_dist`, if two codewords have a distance less than
                    -- the minimum distance of the code, they must be equal.
            
        exact eq_of_lt_dist hv₁_mem hv₂_mem h_dist_lt_d
      · -- Case 2: d < 2 (i.e., d = 0 or d = 1)
                -- This means the code is trivial or has min distance 1
        
        have h_d_le_1 : d ≤ 1 := by
          omega
            -- If d ≤ 1, then t = ⌊(1-1)/2⌋ = 0 or ⌊(0-1)/2⌋ = 0
            
        have h_t_eq_0 : t = 0 := by
          dsimp only [t, d, uniqueDecodingRadius]
          apply Nat.le_zero.mp
          omega
            -- Our assumption `Δ₀(u, v₁) ≤ t` becomes `Δ₀(u, v₁) ≤ 0`
            
        rw [h_t_eq_0] at h_dist_v₁ h_dist_v₂
        rw [Nat.le_zero] at h_dist_v₁ h_dist_v₂
        have h_u_eq_v1 : u = v₁ := by rw [← hammingDist_eq_zero]; exact h_dist_v₁
        have h_u_eq_v2 : u = v₂ := by rw [← hammingDist_eq_zero]; exact h_dist_v₂
        rw [← h_u_eq_v1, h_u_eq_v2]
          -- 5. Combine existence and uniqueness
              -- apply ExistsUnique.intro h_exists
          
    refine existsUnique_of_exists_of_unique h_exists ?_
    intro v₁ v₂ ⟨hv₁_mem, h_dist_v₁⟩ ⟨hv₂_mem, h_dist_v₂⟩
    exact h_uniq v₁ v₂ hv₁_mem hv₂_mem h_dist_v₁ h_dist_v₂
  · -- (←) Direction 2: "Uniquely Close" implies "Close"
    
    intro h_exists_unique
    rcases h_exists_unique with ⟨v, hv_mem, h_dist_le⟩
    rw [closeToCode_iff_closeToCodeword_of_minDist]
    use v


-- @@ L189-208 expanded
/-- A word `u` is close to a code `C` within the absolute unique decoding radius
if and only if it is close within the relative unique decoding radius.
-/
theorem UDR_close_iff_relURD_close {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] [Nonempty ι]
    (C : Set (ι → F)) (u : ι → F) :
    hammingDist u C ≤ uniqueDecodingRadius C ↔
      relHammingDist u C ≤ relativeUniqueDecodingRadius C :=
  by
  rw [closeToCode_iff_closeToCodeword_of_minDist, relCloseToCode_iff_relCloseToCodeword_of_minDist]
    -- Goal: (∃ v ∈ C, Δ₀(u, v) ≤ t) ↔ (∃ v ∈ C, δᵣ(u, v) ≤ τ)
    
  apply exists_congr
  intro v
  simp only [and_congr_right_iff]
  intro hv_mem
  rw [pairRelDist_le_iff_pairDist_le]
  set n := (Fintype.card ι : NNReal)
  have h_n_pos : 0 < n := by exact NeZero.pos n
  conv_lhs => rw [uniqueDecodingRadius_eq_floor_div_2 (C := C)]
  dsimp only [relativeUniqueDecodingRadius]
  conv_rhs => rw [div_mul_cancel₀ (h := by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)]


-- @@ L210-222 expanded
@[simp]
theorem dist_le_UDR_iff_relDist_le_relUDR {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    [Nonempty ι] (C : Set (ι → F)) (e : ℕ) :
    e ≤ uniqueDecodingRadius C ↔
      (e : NNReal) / (Fintype.card ι : NNReal) ≤ relativeUniqueDecodingRadius C :=
  by
  rw [uniqueDecodingRadius_eq_floor_div_2]
  unfold relativeUniqueDecodingRadius
  conv_rhs =>
    rw [div_le_iff₀ (b := e) (c := Fintype.card ι) (a :=
        ((hammingNorm C : NNReal) - 1) / 2 / (Fintype.card ι : NNReal)) (hc := by
        simp only [Nat.cast_pos, Fintype.zero_lt_card])]
  simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [Nat.le_floor_iff (ha := by simp only [zero_le])]


-- @@ L224-224 verbatim
end DecodingRadius


-- @@ L226-226 verbatim
end


-- @@ L228-228 verbatim
end Code
