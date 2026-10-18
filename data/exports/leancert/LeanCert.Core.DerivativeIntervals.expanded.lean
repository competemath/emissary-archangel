/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.MeanValue


-- @@ L14-55 verbatim
/-!
# Derivative Interval Library

This file provides a systematic collection of derivative interval facts for basic functions.
These lemmas establish that derivatives of common functions lie within specified intervals,
which feeds into:
- Monotonicity analysis
- Lipschitz/contractivity bounds
- Newton method analysis
- Global optimization pruning

## Main theorems

### Exp (derivative = exp, always positive)
* `exp_deriv_pos` - exp' x > 0 for all x
* `exp_deriv_interval` - exp' x ∈ [exp a, exp b] for x ∈ [a, b]

### Log (derivative = 1/x on (0, ∞))
* `log_deriv_interval` - log' x ∈ [1/b, 1/a] for x ∈ [a, b] with 0 < a

### Arctan (derivative = 1/(1+x²) ∈ (0, 1])
* `arctan_deriv_interval` - arctan' x ∈ (0, 1] for all x
* `arctan_deriv_mem_Icc` - arctan' x ∈ [0, 1] for all x

### Arsinh (derivative = 1/√(1+x²) ∈ (0, 1])
* `arsinh_deriv_interval` - arsinh' x ∈ (0, 1] for all x
* `arsinh_deriv_mem_Icc` - arsinh' x ∈ [0, 1] for all x

### Sin/Cos (derivatives bounded by 1)
* `sin_deriv_interval` - |sin' x| = |cos x| ≤ 1
* `cos_deriv_interval` - |cos' x| = |sin x| ≤ 1

### Sinh/Cosh (derivative relationships)
* `sinh_deriv_eq_cosh` - sinh' = cosh
* `cosh_deriv_eq_sinh` - cosh' = sinh
* `cosh_deriv_interval` - cosh' x = sinh x, monotonicity facts

## Design notes

These lemmas are independent of any specific algorithm; they're just facts about functions.
They're designed to be composable with the chain rule for AD correctness proofs.
-/


-- @@ L57-57 verbatim
namespace LeanCert.Core.DerivativeIntervals


-- @@ L59-59 verbatim
open Real Set


-- @@ L61-61 verbatim
/-! ### Exp derivative intervals -/


-- @@ L63-66 verbatim
/-- The derivative of exp is positive everywhere -/
theorem exp_deriv_pos (x : ℝ) : 0 < deriv exp x := by
  rw [Real.deriv_exp]
  exact Real.exp_pos x


-- @@ L68-69 verbatim
/-- exp is strictly increasing (follows from positive derivative) -/
theorem exp_strictMono : StrictMono exp := Real.exp_strictMono


-- @@ L71-75 verbatim
/-- For x ∈ [a, b], we have exp' x = exp x ∈ [exp a, exp b] -/
theorem exp_deriv_interval {a b x : ℝ} (hx : x ∈ Icc a b) :
    deriv exp x ∈ Icc (exp a) (exp b) := by
  rw [Real.deriv_exp]
  exact ⟨exp_le_exp.mpr hx.1, exp_le_exp.mpr hx.2⟩


-- @@ L77-77 verbatim
/-! ### Log derivative intervals -/


-- @@ L79-81 verbatim
/-- The derivative of log at x > 0 is x⁻¹ -/
theorem log_deriv_eq_inv {x : ℝ} (_hx : 0 < x) : deriv log x = x⁻¹ :=
  Real.deriv_log x


-- @@ L83-91 verbatim
/-- For x ∈ [a, b] with 0 < a ≤ b, we have log' x = 1/x ∈ [1/b, 1/a] -/
theorem log_deriv_interval {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Icc a b) :
    deriv log x ∈ Icc (b⁻¹) (a⁻¹) := by
  have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
  rw [log_deriv_eq_inv hx_pos]
  constructor
  · exact inv_anti₀ hx_pos hx.2
  · have ha_le_x : a ≤ x := hx.1
    exact inv_anti₀ ha ha_le_x


-- @@ L93-94 verbatim
/-- log is strictly increasing on (0, ∞) -/
theorem log_strictMonoOn : StrictMonoOn log (Ioi 0) := Real.strictMonoOn_log


-- @@ L96-96 verbatim
/-! ### Arctan derivative intervals -/


-- @@ L98-100 verbatim
/-- The derivative of arctan at x is 1/(1+x²) -/
theorem arctan_deriv_eq (x : ℝ) : deriv arctan x = (1 + x ^ 2)⁻¹ :=
  (Real.hasDerivAt_arctan' x).deriv


-- @@ L102-105 verbatim
/-- 1/(1+x²) is always positive -/
theorem arctan_deriv_pos (x : ℝ) : 0 < deriv arctan x := by
  rw [arctan_deriv_eq]
  exact inv_pos.mpr (by nlinarith [sq_nonneg x])


-- @@ L107-111 verbatim
/-- 1/(1+x²) ≤ 1 for all x -/
theorem arctan_deriv_le_one (x : ℝ) : deriv arctan x ≤ 1 := by
  rw [arctan_deriv_eq]
  have h : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  exact inv_le_one_of_one_le₀ h


-- @@ L113-115 verbatim
/-- arctan' x ∈ (0, 1] for all x -/
theorem arctan_deriv_interval (x : ℝ) : deriv arctan x ∈ Ioc 0 1 :=
  ⟨arctan_deriv_pos x, arctan_deriv_le_one x⟩


-- @@ L117-119 verbatim
/-- arctan' x ∈ [0, 1] for all x (closed interval version for interval arithmetic) -/
theorem arctan_deriv_mem_Icc (x : ℝ) : deriv arctan x ∈ Icc 0 1 :=
  ⟨le_of_lt (arctan_deriv_pos x), arctan_deriv_le_one x⟩


-- @@ L121-122 verbatim
/-- arctan is strictly increasing (follows from positive derivative) -/
theorem arctan_strictMono : StrictMono arctan := Real.arctan_strictMono


-- @@ L124-124 verbatim
/-! ### Arsinh derivative intervals -/


-- @@ L126-129 verbatim
/-- The derivative of arsinh at x is (√(1+x²))⁻¹ -/
theorem arsinh_deriv_eq (x : ℝ) : deriv arsinh x = (sqrt (1 + x ^ 2))⁻¹ := by
  have h := Real.hasDerivAt_arsinh x
  rw [h.deriv]


-- @@ L131-135 verbatim
/-- √(1+x²) ≥ 1 for all x -/
theorem sqrt_one_add_sq_ge_one (x : ℝ) : 1 ≤ sqrt (1 + x ^ 2) := by
  have h : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  calc sqrt (1 + x ^ 2) ≥ sqrt 1 := sqrt_le_sqrt h
    _ = 1 := sqrt_one


-- @@ L137-140 verbatim
/-- √(1+x²) > 0 for all x -/
theorem sqrt_one_add_sq_pos (x : ℝ) : 0 < sqrt (1 + x ^ 2) := by
  apply sqrt_pos.mpr
  nlinarith [sq_nonneg x]


-- @@ L142-145 verbatim
/-- arsinh' x > 0 for all x -/
theorem arsinh_deriv_pos (x : ℝ) : 0 < deriv arsinh x := by
  rw [arsinh_deriv_eq]
  exact inv_pos.mpr (sqrt_one_add_sq_pos x)


-- @@ L147-150 verbatim
/-- arsinh' x ≤ 1 for all x -/
theorem arsinh_deriv_le_one (x : ℝ) : deriv arsinh x ≤ 1 := by
  rw [arsinh_deriv_eq]
  exact inv_le_one_of_one_le₀ (sqrt_one_add_sq_ge_one x)


-- @@ L152-154 verbatim
/-- arsinh' x ∈ (0, 1] for all x -/
theorem arsinh_deriv_interval (x : ℝ) : deriv arsinh x ∈ Ioc 0 1 :=
  ⟨arsinh_deriv_pos x, arsinh_deriv_le_one x⟩


-- @@ L156-158 verbatim
/-- arsinh' x ∈ [0, 1] for all x (closed interval version) -/
theorem arsinh_deriv_mem_Icc (x : ℝ) : deriv arsinh x ∈ Icc 0 1 :=
  ⟨le_of_lt (arsinh_deriv_pos x), arsinh_deriv_le_one x⟩


-- @@ L160-161 verbatim
/-- arsinh is strictly increasing -/
theorem arsinh_strictMono : StrictMono arsinh := Real.arsinh_strictMono


-- @@ L163-163 verbatim
/-! ### Sin derivative intervals -/


-- @@ L165-168 verbatim
/-- The derivative of sin is cos -/
theorem sin_deriv_eq (x : ℝ) : deriv sin x = cos x := by
  have h := Real.deriv_sin
  exact congrFun h x


-- @@ L170-173 verbatim
/-- |sin' x| = |cos x| ≤ 1 -/
theorem sin_deriv_abs_le_one (x : ℝ) : |deriv sin x| ≤ 1 := by
  rw [sin_deriv_eq]
  exact abs_cos_le_one x


-- @@ L175-178 verbatim
/-- sin' x ∈ [-1, 1] for all x -/
theorem sin_deriv_mem_Icc (x : ℝ) : deriv sin x ∈ Icc (-1) 1 := by
  rw [sin_deriv_eq]
  exact ⟨neg_one_le_cos x, cos_le_one x⟩


-- @@ L180-180 verbatim
/-! ### Cos derivative intervals -/


-- @@ L182-185 verbatim
/-- The derivative of cos is -sin -/
theorem cos_deriv_eq (x : ℝ) : deriv cos x = -sin x := by
  have h := Real.deriv_cos'
  exact congrFun h x


-- @@ L187-190 verbatim
/-- |cos' x| = |sin x| ≤ 1 -/
theorem cos_deriv_abs_le_one (x : ℝ) : |deriv cos x| ≤ 1 := by
  rw [cos_deriv_eq, abs_neg]
  exact abs_sin_le_one x


-- @@ L192-197 verbatim
/-- cos' x ∈ [-1, 1] for all x -/
theorem cos_deriv_mem_Icc (x : ℝ) : deriv cos x ∈ Icc (-1) 1 := by
  rw [cos_deriv_eq]
  constructor
  · simp only [neg_le_neg_iff]; exact sin_le_one x
  · have h := neg_one_le_sin x; linarith


-- @@ L199-199 verbatim
/-! ### Sinh derivative intervals -/


-- @@ L201-204 verbatim
/-- The derivative of sinh is cosh -/
theorem sinh_deriv_eq (x : ℝ) : deriv sinh x = cosh x := by
  have h := Real.deriv_sinh
  exact congrFun h x


-- @@ L206-209 verbatim
/-- sinh' x = cosh x ≥ 1 for all x -/
theorem sinh_deriv_ge_one (x : ℝ) : 1 ≤ deriv sinh x := by
  rw [sinh_deriv_eq]
  exact Real.one_le_cosh x


-- @@ L211-214 verbatim
/-- sinh' x > 0 for all x -/
theorem sinh_deriv_pos (x : ℝ) : 0 < deriv sinh x := by
  have h := sinh_deriv_ge_one x
  linarith


-- @@ L216-217 verbatim
/-- sinh is strictly increasing -/
theorem sinh_strictMono : StrictMono sinh := Real.sinh_strictMono


-- @@ L219-219 verbatim
/-! ### Cosh derivative intervals -/


-- @@ L221-224 verbatim
/-- The derivative of cosh is sinh -/
theorem cosh_deriv_eq (x : ℝ) : deriv cosh x = sinh x := by
  have h := Real.deriv_cosh
  exact congrFun h x


-- @@ L226-228 verbatim
/-- cosh' 0 = sinh 0 = 0 -/
theorem cosh_deriv_zero : deriv cosh 0 = 0 := by
  rw [cosh_deriv_eq, Real.sinh_zero]


-- @@ L230-233 verbatim
/-- For x > 0, cosh' x = sinh x > 0 -/
theorem cosh_deriv_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < deriv cosh x := by
  rw [cosh_deriv_eq]
  exact Real.sinh_pos_iff.mpr hx


-- @@ L235-238 verbatim
/-- For x < 0, cosh' x = sinh x < 0 -/
theorem cosh_deriv_neg_of_neg {x : ℝ} (hx : x < 0) : deriv cosh x < 0 := by
  rw [cosh_deriv_eq]
  exact Real.sinh_neg_iff.mpr hx


-- @@ L240-252 verbatim
/-- cosh is strictly decreasing on (-∞, 0] -/
theorem cosh_strictAntiOn_nonpos : StrictAntiOn cosh (Iic 0) := by
  intro x hx y hy hxy
  simp only [mem_Iic] at hx hy
  -- Use that cosh is even and decreasing on negative reals
  calc cosh y = cosh (-(-y)) := by ring_nf
    _ = cosh (-y) := by rw [Real.cosh_neg]
    _ < cosh (-x) := by
        apply Real.cosh_strictMonoOn
        · simp only [mem_Ici]; linarith
        · simp only [mem_Ici]; linarith
        · linarith
    _ = cosh x := by rw [Real.cosh_neg]


-- @@ L254-256 verbatim
/-- cosh is strictly increasing on [0, ∞) -/
theorem cosh_strictMonoOn_nonneg : StrictMonoOn cosh (Ici 0) :=
  Real.cosh_strictMonoOn


-- @@ L258-258 verbatim
end LeanCert.Core.DerivativeIntervals


-- @@ L260-268 verbatim
/-! ## One-Sided Taylor Bounds

For convex functions, the Taylor polynomial provides a one-sided bound.
For exp on [0, ∞), the n-th Taylor polynomial is a lower bound.
For concave functions, similar upper bounds hold.

These bounds are tighter than symmetric remainder bounds at endpoints,
which is important for verified numerics.
-/


-- @@ L270-270 verbatim
namespace LeanCert.Core.OneSidedTaylor


-- @@ L272-272 verbatim
open Real Set


-- @@ L274-274 verbatim
/-! ### Exp lower bounds (convexity gives Taylor poly ≤ function) -/


-- @@ L276-278 verbatim
/-- 1 ≤ exp x for x ≥ 0 (Taylor degree 0) -/
theorem one_le_exp_of_nonneg (x : ℝ) (hx : 0 ≤ x) : 1 ≤ exp x :=
  Real.one_le_exp hx


-- @@ L280-283 verbatim
/-- 1 + x ≤ exp x for all x (Taylor degree 1) -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ exp x := by
  have h := add_one_le_exp x
  linarith


-- @@ L285-287 verbatim
/-- x + 1 ≤ exp x for all x (alternate form) -/
theorem add_one_le_exp' (x : ℝ) : x + 1 ≤ exp x :=
  add_one_le_exp x


-- @@ L289-291 verbatim
/-! ### Monotonicity from derivative bounds

These wrap the Mathlib lemmas for convenience with our naming. -/


-- @@ L293-301 verbatim
/-- If f' ≥ 0 on [a, b], then f is monotone increasing on [a, b] -/
theorem monotoneOn_of_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) :
    MonotoneOn f (Icc a b) := by
  refine _root_.monotoneOn_of_deriv_nonneg (convex_Icc a b) hf ?_ ?_
  · rw [interior_Icc]; exact hf'
  · intro x hx; rw [interior_Icc] at hx; exact hderiv x hx


-- @@ L303-310 verbatim
/-- If f' > 0 on (a, b), then f is strictly monotone on [a, b] -/
theorem strictMonoOn_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (_hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    StrictMonoOn f (Icc a b) := by
  refine _root_.strictMonoOn_of_deriv_pos (convex_Icc a b) hf ?_
  intro x hx; rw [interior_Icc] at hx; exact hderiv x hx


-- @@ L312-320 verbatim
/-- If f' ≤ 0 on [a, b], then f is antitone (monotone decreasing) on [a, b] -/
theorem antitoneOn_of_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, deriv f x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  refine _root_.antitoneOn_of_deriv_nonpos (convex_Icc a b) hf ?_ ?_
  · rw [interior_Icc]; exact hf'
  · intro x hx; rw [interior_Icc] at hx; exact hderiv x hx


-- @@ L322-329 verbatim
/-- If f' < 0 on (a, b), then f is strictly antitone on [a, b] -/
theorem strictAntiOn_of_deriv_neg {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (_hf' : DifferentiableOn ℝ f (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, deriv f x < 0) :
    StrictAntiOn f (Icc a b) := by
  refine _root_.strictAntiOn_of_deriv_neg (convex_Icc a b) hf ?_
  intro x hx; rw [interior_Icc] at hx; exact hderiv x hx


-- @@ L331-331 verbatim
end LeanCert.Core.OneSidedTaylor
