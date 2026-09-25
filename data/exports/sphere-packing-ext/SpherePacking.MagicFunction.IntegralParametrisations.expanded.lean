/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic



-- @@ L14-25 verbatim
/-!
# Integral parametrisations

This file defines explicit complex-valued parametrisations used to rewrite contour integrals in
the magic function argument.

## Main definitions
* `MagicFunction.Parametrisations.z₁`, `MagicFunction.Parametrisations.z₂`,
  `MagicFunction.Parametrisations.z₃`, `MagicFunction.Parametrisations.z₄`,
  `MagicFunction.Parametrisations.z₅`, `MagicFunction.Parametrisations.z₆`
* Their extensions `z₁'`--`z₆'` to all real parameters.
-/


-- @@ L27-27 verbatim
namespace MagicFunction.Parametrisations


-- @@ L29-29 verbatim
open Set Complex Real


-- @@ L31-31 verbatim
local notation "ℍ₀" => UpperHalfPlane.upperHalfPlaneSet


-- @@ L33-33 verbatim
noncomputable section Parametrisations


-- @@ L35-36 verbatim
/-- Parametrisation `t ↦ -1 + i t` of the vertical segment from `-1` to `-1 + i`. -/
@[expose] public def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 + I * t


-- @@ L38-42 verbatim
/-- Extension of `z₁` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.
-/
@[expose] public def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t


-- @@ L44-45 verbatim
/-- Parametrisation `t ↦ -1 + t + i` of the horizontal segment from `-1 + i` to `i`. -/
@[expose] public def z₂ (t : Icc (0 : ℝ) 1) : ℂ := -1 + t + I


-- @@ L47-51 verbatim
/-- Extension of `z₂` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.
-/
@[expose] public def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t


-- @@ L53-54 verbatim
/-- Parametrisation `t ↦ 1 + i t` of the vertical segment from `1` to `1 + i`. -/
@[expose] public def z₃ (t : Icc (0 : ℝ) 1) : ℂ := 1 + I * t


-- @@ L56-60 verbatim
/-- Extension of `z₃` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.
-/
@[expose] public def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t


-- @@ L62-63 verbatim
/-- Parametrisation `t ↦ 1 - t + i` of the horizontal segment from `1 + i` to `i`. -/
@[expose] public def z₄ (t : Icc (0 : ℝ) 1) : ℂ := 1 - t + I


-- @@ L65-69 verbatim
/-- Extension of `z₄` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.
-/
@[expose] public def z₄' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₄ t


-- @@ L71-72 verbatim
/-- Parametrisation `t ↦ i t` of the vertical segment from `0` to `i`. -/
@[expose] public def z₅ (t : Icc (0 : ℝ) 1) : ℂ := I * t


-- @@ L74-78 verbatim
/-- Extension of `z₅` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.
-/
@[expose] public def z₅' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₅ t


-- @@ L80-81 verbatim
/-- Parametrisation `t ↦ i t` of the ray `i * Ici 1`. -/
@[expose] public def z₆ (t : Ici (1 : ℝ)) : ℂ := I * t


-- @@ L83-87 verbatim
/-- Extension of `z₆` to a map `ℝ → ℂ` via `IciExtend`.

The prime indicates we have extended a parametrisation on `Ici 1` to all real `t`.
-/
@[expose] public def z₆' (t : ℝ) : ℂ := IciExtend z₆ t


-- @@ L89-91 verbatim
/-- The imaginary part of `z₂'` is always positive (in fact, it is equal to `1`). -/
public lemma im_z₂'_pos_all (t : ℝ) : 0 < (z₂' t).im := by
  simp [z₂', Set.IccExtend_apply, z₂]


-- @@ L93-95 verbatim
/-- The imaginary part of `z₄'` is always positive (in fact, it is equal to `1`). -/
public lemma im_z₄'_pos_all (t : ℝ) : 0 < (z₄' t).im := by
  simp [z₄', Set.IccExtend_apply, z₄]


-- @@ L97-99 verbatim
/-- The imaginary part of `z₂'` is constantly equal to `1`. -/
public lemma im_z₂'_eq_one (t : ℝ) : (z₂' t).im = (1 : ℝ) := by
  simp [z₂', Set.IccExtend_apply, z₂]


-- @@ L101-103 verbatim
/-- The imaginary part of `z₄'` is constantly equal to `1`. -/
public lemma im_z₄'_eq_one (t : ℝ) : (z₄' t).im = (1 : ℝ) := by
  simp [z₄', Set.IccExtend_apply, z₄]


-- @@ L105-111 verbatim
/-- The extended parametrisation `z₅'` stays in the closed unit disk. -/
public lemma norm_z₅'_le_one (t : ℝ) : ‖z₅' t‖ ≤ 1 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu1 : u ≤ 1 := by simp [hu]
  have hnorm : ‖z₅' t‖ = u := by
    simp [z₅', Set.IccExtend_apply, z₅, hu, Complex.norm_real]
  simpa [hnorm] using hu1


-- @@ L113-129 verbatim
/-- The extended parametrisation `z₁'` stays in the closed ball of radius `2` centered at `0`. -/
public lemma norm_z₁'_le_two (t : ℝ) : ‖z₁' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu0 : 0 ≤ u := by simp [hu]
  have hu1 : u ≤ 1 := by simp [hu]
  have huabs : |u| ≤ 1 := by
    simpa [abs_of_nonneg hu0] using hu1
  have hz : z₁' t = (-1 : ℂ) + (I : ℂ) * (u : ℂ) := by
    simp [z₁', Set.IccExtend_apply, z₁, hu]
  calc
    ‖z₁' t‖ = ‖(-1 : ℂ) + (I : ℂ) * (u : ℂ)‖ := by simp [hz]
    _ ≤ ‖(-1 : ℂ)‖ + ‖(I : ℂ) * (u : ℂ)‖ := norm_add_le _ _
    _ = (1 : ℝ) + ‖(u : ℂ)‖ := by simp
    _ = 1 + |u| := by simp [Complex.norm_real]
    _ ≤ 1 + 1 := by
          simpa [add_comm] using add_le_add_right huabs 1
    _ = 2 := by ring


-- @@ L131-149 verbatim
/-- The extended parametrisation `z₂'` stays in the closed ball of radius `2` centered at `0`. -/
public lemma norm_z₂'_le_two (t : ℝ) : ‖z₂' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu0 : 0 ≤ u := by simp [hu]
  have hu1 : u ≤ 1 := by simp [hu]
  have habs : |u - 1| ≤ 1 := by
    grind only [= max_def, = min_def, = abs.eq_1]
  have hnorm : ‖(-1 : ℂ) + (u : ℂ)‖ ≤ 1 := by
    have : ‖(-1 : ℂ) + (u : ℂ)‖ = |u - 1| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Complex.norm_real (u - 1))
    simpa [this] using habs
  have hz : z₂' t = ((-1 : ℂ) + (u : ℂ)) + (I : ℂ) := by
    simp [z₂', Set.IccExtend_apply, z₂, hu]
  calc
    ‖z₂' t‖ = ‖((-1 : ℂ) + (u : ℂ)) + (I : ℂ)‖ := by simp [hz]
    _ ≤ ‖(-1 : ℂ) + (u : ℂ)‖ + ‖(I : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 : ℝ) + 1 := add_le_add hnorm (by simp)
    _ = 2 := by ring


-- @@ L151-170 verbatim
/-- The extended parametrisation `z₄'` stays in the closed ball of radius `2` centered at `0`. -/
public lemma norm_z₄'_le_two (t : ℝ) : ‖z₄' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu0 : 0 ≤ u := by simp [hu]
  have hu1 : u ≤ 1 := by simp [hu]
  have habs : |1 - u| ≤ 1 := by
    have hle : 0 ≤ 1 - u := sub_nonneg.mpr hu1
    have habs_eq : |1 - u| = 1 - u := abs_of_nonneg hle
    simpa [habs_eq] using sub_le_self (1 : ℝ) hu0
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ ≤ 1 := by
    have : ‖(1 : ℂ) - (u : ℂ)‖ = |1 - u| := by
      simpa using Complex.norm_real (1 - u)
    simpa [this] using habs
  have hz : z₄' t = ((1 : ℂ) - (u : ℂ)) + (I : ℂ) := by
    simp [z₄', Set.IccExtend_apply, z₄, hu, sub_eq_add_neg]
  calc
    ‖z₄' t‖ = ‖((1 : ℂ) - (u : ℂ)) + (I : ℂ)‖ := by simp [hz]
    _ ≤ ‖(1 : ℂ) - (u : ℂ)‖ + ‖(I : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 : ℝ) + 1 := add_le_add hnorm (by simp)
    _ = 2 := by ring


-- @@ L172-172 verbatim
end Parametrisations


-- @@ L174-174 verbatim
section UpperHalfPlane


-- @@ L176-176 verbatim
open scoped UpperHalfPlane


-- @@ L178-180 verbatim
private lemma im_pos_of_mapsto {s : Set ℝ} {f : ℝ → ℂ} (hf : MapsTo f s ℍ₀) {t : ℝ} (ht : t ∈ s) :
    0 < (f t).im := by
  simpa [UpperHalfPlane.upperHalfPlaneSet] using hf ht


-- @@ L182-185 verbatim
/-- The map `z₁'` sends `Ioc 0 1` into the upper half-plane. -/
public lemma z₁'_mapsto : MapsTo z₁' (Ioc 0 1) ℍ₀ := by
  intro t ht
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₁', IccExtend_of_mem, mem_Icc_of_Ioc ht, z₁] using ht.1


-- @@ L187-189 verbatim
/-- For `t ∈ Ioc 0 1`, the point `z₁' t` has positive imaginary part. -/
public lemma im_z₁'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₁' t).im := by
  simpa using im_pos_of_mapsto z₁'_mapsto ht


-- @@ L191-194 verbatim
/-- The map `z₂'` sends `Icc 0 1` into the upper half-plane. -/
public lemma z₂'_mapsto : MapsTo z₂' (Icc 0 1) ℍ₀ := by
  intro t ht
  simp [UpperHalfPlane.upperHalfPlaneSet, z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]


-- @@ L196-198 verbatim
/-- For `t ∈ Icc 0 1`, the point `z₂' t` has positive imaginary part. -/
public lemma im_z₂'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₂' t).im := by
  simpa using im_pos_of_mapsto z₂'_mapsto ht


-- @@ L200-203 verbatim
/-- The map `z₃'` sends `Ioc 0 1` into the upper half-plane. -/
public lemma z₃'_mapsto : MapsTo z₃' (Ioc 0 1) ℍ₀ := by
  intro t ht
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₃', IccExtend_of_mem, mem_Icc_of_Ioc ht, z₃] using ht.1


-- @@ L205-207 verbatim
/-- For `t ∈ Ioc 0 1`, the point `z₃' t` has positive imaginary part. -/
public lemma im_z₃'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₃' t).im := by
  simpa using im_pos_of_mapsto z₃'_mapsto ht


-- @@ L209-212 verbatim
/-- The map `z₄'` sends `Icc 0 1` into the upper half-plane. -/
public lemma z₄'_mapsto : MapsTo z₄' (Icc 0 1) ℍ₀ := by
  intro t ht
  simp [UpperHalfPlane.upperHalfPlaneSet, z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]


-- @@ L214-216 verbatim
/-- For `t ∈ Icc 0 1`, the point `z₄' t` has positive imaginary part. -/
public lemma im_z₄'_pos {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < (z₄' t).im := by
  simpa using im_pos_of_mapsto z₄'_mapsto ht


-- @@ L218-221 verbatim
/-- The map `z₅'` sends `Ioc 0 1` into the upper half-plane. -/
public lemma z₅'_mapsto : MapsTo z₅' (Ioc 0 1) ℍ₀ := by
  intro t ht
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₅', IccExtend_of_mem, mem_Icc_of_Ioc ht, z₅] using ht.1


-- @@ L223-225 verbatim
/-- For `t ∈ Ioc 0 1`, the point `z₅' t` has positive imaginary part. -/
public lemma im_z₅'_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < (z₅' t).im := by
  simpa using im_pos_of_mapsto z₅'_mapsto ht


-- @@ L227-231 verbatim
/-- The map `z₆'` sends `Ici 1` into the upper half-plane. -/
public lemma z₆'_mapsto : MapsTo z₆' (Ici 1) ℍ₀ := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  simpa [UpperHalfPlane.upperHalfPlaneSet, z₆', IciExtend_of_mem, ht, z₆] using ht0


-- @@ L233-233 verbatim
end UpperHalfPlane


-- @@ L235-235 verbatim
section eq_of_mem


-- @@ L237-239 verbatim
/-- On `Icc 0 1`, the extension `z₁'` agrees with the original parametrisation `z₁`. -/
public lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 + I * t := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht, z₁]


-- @@ L241-243 verbatim
/-- On `Icc 0 1`, the extension `z₂'` agrees with the original parametrisation `z₂`. -/
public lemma z₂'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₂' t = -1 + t + I := by
  rw [z₂', IccExtend_of_mem zero_le_one z₂ ht, z₂]


-- @@ L245-247 verbatim
/-- On `Icc 0 1`, the extension `z₃'` agrees with the original parametrisation `z₃`. -/
public lemma z₃'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = 1 + I * t := by
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht, z₃]


-- @@ L249-251 verbatim
/-- On `Icc 0 1`, the extension `z₄'` agrees with the original parametrisation `z₄`. -/
public lemma z₄'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₄' t = 1 - t + I := by
  rw [z₄', IccExtend_of_mem zero_le_one z₄ ht, z₄]


-- @@ L253-255 verbatim
/-- On `Icc 0 1`, the extension `z₅'` agrees with the original parametrisation `z₅`. -/
public lemma z₅'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = I * t := by
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht, z₅]


-- @@ L257-259 verbatim
/-- On `Ici 1`, the extension `z₆'` agrees with the original parametrisation `z₆`. -/
public lemma z₆'_eq_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = I * t := by
  rw [z₆', IciExtend_of_mem z₆ ht, z₆]


-- @@ L261-263 verbatim
/-- On `Icc 0 1`, the points `z₃' t` and `z₅' t` differ by the translation `+ 1`. -/
public lemma z₃'_eq_z₅'_add_one {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = z₅' t + 1 := by
  simp [z₃'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht, add_comm]


-- @@ L265-265 verbatim
end eq_of_mem


-- @@ L267-267 verbatim
end MagicFunction.Parametrisations
