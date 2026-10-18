/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio


-- @@ L8-34 verbatim
/-!
# Pentagon Lucas Sequence

We define a Lucas-like sequence arising from the regular pentagon:

  `T n = (2 cos(π/10))ⁿ + (2 sin(π/10))ⁿ`

where the roots α = 2 cos(π/10) and β = 2 sin(π/10) satisfy the characteristic
quadratic x² - (α + β)x + αβ = 0, with:

  αβ = 2 sin(π/5)   (by the double-angle identity)

## Main results

* `pentagonSeq` — the sequence definition
* `pentagonSeq_zero` — T₀ = 2
* `pentagonSeq_two` — T₂ = 4  (Pythagorean identity)
* `pentagonSeq_recurrence` — T_{n+2} = (α + β) T_{n+1} - αβ · T_n
* `cos_pi_div_five_eq_goldenRatio_div_two` — cos(π/5) = φ/2
* `two_sin_pi_div_ten_eq_inv_goldenRatio` — 2 sin(π/10) = φ⁻¹ = -ψ
* `pentagonSeq_product` — αβ = 2 sin(π/5)

## References

The sequence bridges the golden ratio φ and pentagon trigonometry through
the exact identity cos(π/5) = φ/2, equivalently sin(π/10) = φ⁻¹/2 = -ψ/2.
-/


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
open Real


-- @@ L40-40 verbatim
namespace LeanCert.Engine.PentagonLucas


-- @@ L42-42 verbatim
/-! ### Pentagon trig constants -/


-- @@ L44-45 verbatim
/-- The larger root: α = 2 cos(π/10). -/
def α : ℝ := 2 * cos (π / 10)


-- @@ L47-48 verbatim
/-- The smaller root: β = 2 sin(π/10). -/
def β : ℝ := 2 * sin (π / 10)


-- @@ L50-50 verbatim
/-! ### Sequence definition -/


-- @@ L52-53 verbatim
/-- The pentagon Lucas sequence: `T n = αⁿ + βⁿ`. -/
def pentagonSeq (n : ℕ) : ℝ := α ^ n + β ^ n


-- @@ L55-55 verbatim
/-! ### Base cases -/


-- @@ L57-59 verbatim
@[simp]
theorem pentagonSeq_zero : pentagonSeq 0 = 2 := by
  unfold pentagonSeq; norm_num


-- @@ L61-63 verbatim
@[simp]
theorem pentagonSeq_one : pentagonSeq 1 = α + β := by
  unfold pentagonSeq; ring


-- @@ L65-72 verbatim
/-- T₂ = 4: this is the Pythagorean identity in disguise, since
    (2 cos θ)² + (2 sin θ)² = 4(cos² θ + sin² θ) = 4. -/
theorem pentagonSeq_two : pentagonSeq 2 = 4 := by
  unfold pentagonSeq α β
  have h : (2 * cos (π / 10)) ^ 2 + (2 * sin (π / 10)) ^ 2
      = 4 * (cos (π / 10) ^ 2 + sin (π / 10) ^ 2) := by ring
  rw [h, cos_sq_add_sin_sq]
  norm_num


-- @@ L74-74 verbatim
/-! ### Product of roots: αβ = 2 sin(π/5) -/


-- @@ L76-83 verbatim
/-- The product of the roots equals 2 sin(π/5), by the double-angle identity
    2 sin θ cos θ = sin(2θ). -/
theorem pentagonSeq_product : α * β = 2 * sin (π / 5) := by
  unfold α β
  have h : 2 * cos (π / 10) * (2 * sin (π / 10))
      = 2 * (2 * sin (π / 10) * cos (π / 10)) := by ring
  rw [h, ← sin_two_mul]
  ring_nf


-- @@ L85-85 verbatim
/-! ### Recurrence relation -/


-- @@ L87-94 verbatim
/-- The fundamental recurrence: T_{n+2} = (α + β) · T_{n+1} - αβ · T_n.

This follows from α and β being roots of x² - (α+β)x + αβ = 0,
i.e., α² = (α+β)α - αβ and β² = (α+β)β - αβ. -/
theorem pentagonSeq_recurrence (n : ℕ) :
    pentagonSeq (n + 2) = (α + β) * pentagonSeq (n + 1) - α * β * pentagonSeq n := by
  simp only [pentagonSeq]
  ring


-- @@ L96-96 verbatim
/-! ### Golden ratio bridge -/


-- @@ L98-104 verbatim
/-- cos(π/5) = φ/2, linking the golden ratio to pentagon geometry.
    This follows directly from Mathlib's `cos_pi_div_five`. -/
theorem cos_pi_div_five_eq_goldenRatio_div_two :
    cos (π / 5) = goldenRatio / 2 := by
  rw [cos_pi_div_five]
  unfold goldenRatio
  ring


-- @@ L106-135 verbatim
/-- sin(π/10) = (√5 - 1) / 4.
    We derive this from cos(π/5) = (1 + √5)/4 via cos(2θ) = 1 - 2sin²(θ). -/
theorem sin_pi_div_ten :
    sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
  -- Use cos(π/5) = 1 - 2sin²(π/10)
  have hcos : cos (π / 5) = 1 - 2 * sin (π / 10) ^ 2 := by
    have h : π / 5 = 2 * (π / 10) := by ring
    rw [h, cos_two_mul]
    have := sin_sq (π / 10)
    linarith
  rw [cos_pi_div_five] at hcos
  -- sin(π/10) ≥ 0
  have hsin_nn : 0 ≤ sin (π / 10) := by
    apply sin_nonneg_of_nonneg_of_le_pi
    · linarith [pi_pos]
    · linarith [pi_pos]
  -- sin²(π/10) = (3 - √5)/8
  have hsq : sin (π / 10) ^ 2 = (3 - Real.sqrt 5) / 8 := by linarith
  -- target² = (3 - √5)/8
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have htarget_sq : ((Real.sqrt 5 - 1) / 4) ^ 2 = (3 - Real.sqrt 5) / 8 := by nlinarith
  -- target ≥ 0
  have htarget_nn : 0 ≤ (Real.sqrt 5 - 1) / 4 := by
    apply div_nonneg _ (by norm_num)
    have : 1 ≤ Real.sqrt 5 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  -- Both nonneg with same square → equal
  nlinarith [sq_nonneg (sin (π / 10) - (Real.sqrt 5 - 1) / 4)]


-- @@ L137-143 verbatim
/-- The golden ratio bridge: 2 sin(π/10) = φ⁻¹ = -ψ.
    This means β = 1/φ, connecting the pentagon sequence root to the golden ratio. -/
theorem two_sin_pi_div_ten_eq_inv_goldenRatio :
    2 * sin (π / 10) = goldenRatio⁻¹ := by
  rw [sin_pi_div_ten, inv_goldenRatio]
  unfold goldenConj
  ring


-- @@ L145-148 verbatim
/-- β = φ⁻¹: the smaller root of the pentagon sequence is the reciprocal
    of the golden ratio. -/
theorem β_eq_inv_goldenRatio : β = goldenRatio⁻¹ := by
  exact two_sin_pi_div_ten_eq_inv_goldenRatio


-- @@ L150-151 verbatim
/-- α expressed in terms of the golden ratio. -/
theorem α_eq : α = 2 * cos (π / 10) := rfl


-- @@ L153-153 verbatim
/-! ### Recurrence with golden ratio -/


-- @@ L155-161 verbatim
/-- The recurrence in terms of concrete constants:
    T_{n+2} = (α + β) · T_{n+1} - 2sin(π/5) · T_n -/
theorem pentagonSeq_recurrence' (n : ℕ) :
    pentagonSeq (n + 2) =
      (α + β) * pentagonSeq (n + 1) - 2 * sin (π / 5) * pentagonSeq n := by
  rw [← pentagonSeq_product]
  exact pentagonSeq_recurrence n


-- @@ L163-163 verbatim
/-! ### Asymptotic dominance -/


-- @@ L165-168 verbatim
/-- β < 1, so βⁿ → 0. The sequence is asymptotically dominated by αⁿ. -/
theorem β_lt_one : β < 1 := by
  rw [β_eq_inv_goldenRatio]
  exact (inv_lt_one₀ goldenRatio_pos).mpr one_lt_goldenRatio


-- @@ L170-172 verbatim
theorem β_pos : 0 < β := by
  rw [β_eq_inv_goldenRatio]
  exact inv_pos.mpr goldenRatio_pos


-- @@ L174-174 verbatim
/-! ### The characteristic quadratic -/


-- @@ L176-178 verbatim
/-- α and β are the two roots of x² - (α+β)x + αβ = 0. -/
theorem α_is_root_char_poly :
    α ^ 2 - (α + β) * α + α * β = 0 := by ring


-- @@ L180-181 verbatim
theorem β_is_root_char_poly :
    β ^ 2 - (α + β) * β + α * β = 0 := by ring


-- @@ L183-183 verbatim
/-! ### Separation: Binet-like formula -/


-- @@ L185-186 verbatim
/-- The anti-symmetric companion: U_n = αⁿ - βⁿ. -/
def pentagonSeqU (n : ℕ) : ℝ := α ^ n - β ^ n


-- @@ L188-189 verbatim
theorem pentagonSeqU_zero : pentagonSeqU 0 = 0 := by
  unfold pentagonSeqU; norm_num


-- @@ L191-192 verbatim
theorem pentagonSeqU_one : pentagonSeqU 1 = α - β := by
  unfold pentagonSeqU; ring


-- @@ L194-197 verbatim
theorem pentagonSeqU_recurrence (n : ℕ) :
    pentagonSeqU (n + 2) = (α + β) * pentagonSeqU (n + 1) - α * β * pentagonSeqU n := by
  simp only [pentagonSeqU]
  ring


-- @@ L199-202 verbatim
/-- Recovery: αⁿ = (T_n + U_n) / 2 -/
theorem alpha_pow_eq (n : ℕ) :
    α ^ n = (pentagonSeq n + pentagonSeqU n) / 2 := by
  unfold pentagonSeq pentagonSeqU; ring


-- @@ L204-207 verbatim
/-- Recovery: βⁿ = (T_n - U_n) / 2 -/
theorem beta_pow_eq (n : ℕ) :
    β ^ n = (pentagonSeq n - pentagonSeqU n) / 2 := by
  unfold pentagonSeq pentagonSeqU; ring


-- @@ L209-209 verbatim
end LeanCert.Engine.PentagonLucas
