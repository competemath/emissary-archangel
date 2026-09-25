/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Norm


-- @@ L11-33 verbatim
/-!

# States are bounded by the order-unit norm

## i. Overview

A state assigns real numbers to observables with no continuity assumed anywhere — `𝓢[ℝ, E]` is
built purely from positivity and unitality. It turns out to be bounded
regardless: `|ω x| ≤ ‖x‖`, the order-unit norm of `OrderUnit/Norm.lean`. Physically, a state can
never predict an expectation value bigger than the biggest an observable can actually read, and
this is exactly that fact, with the tightest possible constant.

## ii. Key results

- `UnitalPositiveLinearMap.apply_le_orderUnitNorm`
- `UnitalPositiveLinearMap.abs_apply_le_orderUnitNorm`

## iii. Table of contents

- A. The one-sided bound
- B. The absolute-value bound

-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
open IsArchimedeanOrderUnit


-- @@ L39-40 verbatim
variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]


-- @@ L42-42 verbatim
namespace UnitalPositiveLinearMap


-- @@ L44-44 verbatim
/-! ## A. The one-sided bound -/


-- @@ L46-53 expanded
/-- A state never overshoots the order-unit norm. -/
lemma apply_le_orderUnitNorm (ω : UnitalPositiveLinearMap ℝ E ℝ) (x : E) : ω x ≤ orderUnitNorm x :=
  by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := exists_orderUnitBound_lt_orderUnitNorm_add x hε
  have hpos : 0 ≤ ω (r • (1 : E) - x) := ω.map_nonneg (sub_nonneg.mpr hr.2.2)
  simp only [map_sub, map_smul, smul_eq_mul, map_one, mul_one] at hpos
  linarith


-- @@ L55-55 verbatim
/-! ## B. The absolute-value bound -/


-- @@ L57-63 expanded
/-- A state's values are squeezed within the order-unit norm on both sides: it can never predict
an expectation value bigger, in either direction, than an observable's own order-unit norm. -/
lemma abs_apply_le_orderUnitNorm (ω : UnitalPositiveLinearMap ℝ E ℝ) (x : E) :
    |ω x| ≤ orderUnitNorm x :=
  by
  have h1 : ω x ≤ orderUnitNorm x := apply_le_orderUnitNorm ω x
  have h2 : ω (-x) ≤ orderUnitNorm (-x) := apply_le_orderUnitNorm ω (-x)
  rw [_root_.map_neg, orderUnitNorm_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩


-- @@ L65-65 verbatim
end UnitalPositiveLinearMap
