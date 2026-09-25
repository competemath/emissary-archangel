module

public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Algebra.Group.Translate

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Positivity


-- @@ L9-11 verbatim
/-!
# Lp norms
-/


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
open Finset Function Real MeasureTheory

-- @@ L16-16 verbatim
open scoped ComplexConjugate ENNReal NNReal translate


-- @@ L18-18 verbatim
variable {α 𝕜 E : Type*} [MeasurableSpace α]


-- @@ L20-20 verbatim
/-! #### Weighted Lp norm -/


-- @@ L22-22 verbatim
section NormedAddCommGroup

-- @@ L23-23 verbatim
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {w : α → ℝ≥0} {f g h : α → E}


-- @@ L25-27 verbatim
/-- The weighted Lp norm of a function. -/
noncomputable def wLpNorm (p : ℝ≥0∞) (w : α → ℝ≥0) (f : α → E) : ℝ :=
  lpNorm f p <| .sum fun i ↦ w i • .dirac i


-- @@ L29-29 verbatim
notation "‖" f "‖_[" p ", " w "]" => wLpNorm p w f


-- @@ L31-31 expanded
@[simp]
lemma wLpNorm_nonneg : 0 ≤ wLpNorm p w f := by simp [wLpNorm]


-- @@ L33-33 expanded
@[simp]
lemma wLpNorm_zero (w : α → ℝ≥0) : wLpNorm p w (0 : α → E) = 0 := by simp [wLpNorm]


-- @@ L35-36 expanded
@[simp]
lemma wLpNorm_neg (w : α → ℝ≥0) (f : α → E) : wLpNorm p w (-f) = wLpNorm p w f := by simp [wLpNorm]


-- @@ L38-39 expanded
lemma wLpNorm_sub_comm (w : α → ℝ≥0) (f g : α → E) : wLpNorm p w (f - g) = wLpNorm p w (g - f) := by
  simp [wLpNorm, lpNorm_sub_comm]


-- @@ L41-45 expanded
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma wLpNorm_one_eq_dLpNorm (p : ℝ≥0∞) (f : α → E) : wLpNorm p 1 f = dLpNorm p f :=
  by
  simp only [wLpNorm, lpNorm, Pi.one_apply, one_smul, dLpNorm, Measure.count]
  congr!
  simp


-- @@ L47-48 expanded
@[simp]
lemma wLpNorm_fun_one_eq_dLpNorm (p : ℝ≥0∞) (f : α → E) : wLpNorm p (fun _ ↦ 1) f = dLpNorm p f :=
  wLpNorm_one_eq_dLpNorm ..


-- @@ L50-50 expanded
@[simp]
lemma wLpNorm_exponent_zero (w : α → ℝ≥0) (f : α → E) : wLpNorm 0 w f = 0 := by simp [wLpNorm]


-- @@ L52-54 expanded
@[simp]
lemma wLpNorm_norm (w : α → ℝ≥0) (hf : StronglyMeasurable f) :
    (wLpNorm p w fun i ↦ ‖f i‖) = wLpNorm p w f :=
  lpNorm_norm hf.aestronglyMeasurable _


-- @@ L56-57 expanded
lemma wLpNorm_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (f : α → E) (p : ℝ≥0∞) (w : α → ℝ≥0) :
    wLpNorm p w (c • f) = ‖c‖₊ * wLpNorm p w f :=
  lpNorm_const_smul ..


-- @@ L59-60 expanded
lemma wLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) (w : α → ℝ≥0) :
    wLpNorm p w (n • f) = n • wLpNorm p w f :=
  lpNorm_nsmul ..


-- @@ L62-62 verbatim
section RCLike

-- @@ L63-63 verbatim
variable {K : Type*} [RCLike K]


-- @@ L65-65 expanded
@[simp]
lemma wLpNorm_conj (f : α → K) : wLpNorm p w (conj f) = wLpNorm p w f :=
  lpNorm_conj ..


-- @@ L67-67 verbatim
end RCLike


-- @@ L69-69 verbatim
variable [Finite α]


-- @@ L71-76 expanded
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma wLpNorm_const_right (hp : p ≠ ∞) (w : ℝ≥0) (f : α → E) :
    wLpNorm p (const _ w) f = w ^ p.toReal⁻¹ * dLpNorm p f :=
  by
  cases nonempty_fintype α
  simp [wLpNorm, dLpNorm, ← Finset.smul_sum, lpNorm_smul_measure_of_ne_top hp, Measure.count,
    NNReal.smul_def]


-- @@ L78-82 expanded
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma wLpNorm_smul_right (hp : p ≠ ⊤) (c : ℝ≥0) (f : α → E) :
    wLpNorm p (c • w) f = c ^ p.toReal⁻¹ * wLpNorm p w f :=
  by
  cases nonempty_fintype α
  simp [wLpNorm, mul_smul, ← Finset.smul_sum, lpNorm_smul_measure_of_ne_top hp, NNReal.smul_def]


-- @@ L84-84 verbatim
variable [Fintype α] [DiscreteMeasurableSpace α]


-- @@ L86-89 expanded
lemma wLpNorm_eq_sum_norm (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) (f : α → E) :
    wLpNorm p w f = (∑ i, w i • ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [wLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, NNReal.smul_def,
    integral_finsetSum_measure]


-- @@ L91-93 expanded
lemma wLpNorm_toNNReal_eq_sum_norm {p : ℝ} (hp : 0 < p) (w : α → ℝ≥0) (f : α → E) :
    wLpNorm p.toNNReal w f = (∑ i, w i • ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [wLpNorm_eq_sum_norm] <;> simp [hp, hp.le, NNReal.smul_def]


-- @@ L95-100 expanded
lemma wLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    wLpNorm p w f ^ (p : ℝ) = ∑ i, w i • ‖f i‖ ^ (p : ℝ) :=
  by
  rw [wLpNorm_eq_sum_norm (mod_cast hp) (by simp), ENNReal.coe_toReal,
    Real.rpow_inv_rpow _ (mod_cast hp)]
  simp only [NNReal.smul_def, smul_eq_mul]
  positivity


-- @@ L102-104 expanded
lemma wLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    wLpNorm p w f ^ p = ∑ i, w i • ‖f i‖ ^ p := by
  simpa using wLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) w f


-- @@ L106-107 expanded
lemma wL1Norm_eq_sum_norm (w : α → ℝ≥0) (f : α → E) : wLpNorm 1 w f = ∑ i, w i • ‖f i‖ := by
  simp [wLpNorm_eq_sum_norm]


-- @@ L109-123 expanded
/-- Monotonicity of weighted `L^p` norms in the exponent, for probability weights. -/
@[gcongr]
lemma wLpNorm_mono_right (hw : ∑ i, (w i : ℝ≥0∞) = 1) (hpq : p ≤ q) (f : α → E) :
    wLpNorm p w f ≤ wLpNorm q w f :=
  by
  have : IsProbabilityMeasure (Measure.sum fun i ↦ (w i : ℝ≥0) • Measure.dirac (i : α)) :=
    by
    rw [isProbabilityMeasure_iff, Measure.sum_apply _ MeasurableSet.univ]
    simp [hw, ← Measure.coe_nnreal_smul]
  rw [wLpNorm, wLpNorm, ←
    toReal_eLpNorm (μ := Measure.sum fun i ↦ (w i : ℝ≥0) • Measure.dirac i)
      (MemLp.of_discrete (p := p)).aestronglyMeasurable,
    ←
    toReal_eLpNorm (μ := Measure.sum fun i ↦ (w i : ℝ≥0) • Measure.dirac i)
      (MemLp.of_discrete (p := q)).aestronglyMeasurable]
  exact
    ENNReal.toReal_mono (MemLp.of_discrete (p := q)).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hpq (MemLp.of_discrete (p := p)).aestronglyMeasurable)


-- @@ L125-125 verbatim
omit [Fintype α]


-- @@ L127-127 verbatim
section one_le


-- @@ L129-130 expanded
lemma wLpNorm_add_le (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    wLpNorm p w (f + g) ≤ wLpNorm p w f + wLpNorm p w g :=
  lpNorm_add_le .of_discrete hp


-- @@ L132-134 expanded
lemma wLpNorm_sub_le (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    wLpNorm p w (f - g) ≤ wLpNorm p w f + wLpNorm p w g := by
  simpa [sub_eq_add_neg] using wLpNorm_add_le hp w f (-g)


-- @@ L136-137 expanded
lemma wLpNorm_le_wLpNorm_add_wLpNorm_sub' (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    wLpNorm p w f ≤ wLpNorm p w g + wLpNorm p w (f - g) := by
  simpa using wLpNorm_add_le hp w g (f - g)


-- @@ L139-141 expanded
lemma wLpNorm_le_wLpNorm_add_wLpNorm_sub (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    wLpNorm p w f ≤ wLpNorm p w g + wLpNorm p w (g - f) := by rw [wLpNorm_sub_comm];
  exact wLpNorm_le_wLpNorm_add_wLpNorm_sub' hp ..


-- @@ L143-144 expanded
lemma wLpNorm_le_add_wLpNorm_add (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    wLpNorm p w f ≤ wLpNorm p w (f + g) + wLpNorm p w g := by
  simpa using wLpNorm_add_le hp w (f + g) (-g)


-- @@ L146-148 expanded
lemma wLpNorm_sub_le_wLpNorm_sub_add_wLpNorm_sub (hp : 1 ≤ p) (f g : α → E) :
    wLpNorm p w (f - h) ≤ wLpNorm p w (f - g) + wLpNorm p w (g - h) := by
  simpa using wLpNorm_add_le hp w (f - g) (g - h)


-- @@ L150-150 verbatim
end one_le


-- @@ L152-152 verbatim
end NormedAddCommGroup


-- @@ L154-154 verbatim
section Real

-- @@ L155-155 verbatim
variable [DiscreteMeasurableSpace α] {p : ℝ≥0∞} {w : α → ℝ≥0} {f g : α → ℝ}


-- @@ L157-160 expanded
@[simp]
lemma wLpNorm_one [Fintype α] (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) :
    wLpNorm p w (1 : α → ℝ) = (∑ i, w i) ^ p.toReal⁻¹ := by
  simp [wLpNorm_eq_sum_norm hp₀ hp, NNReal.smul_def]


-- @@ L162-163 expanded
lemma wLpNorm_mono [Finite α] (hf : 0 ≤ f) (hfg : f ≤ g) : wLpNorm p w f ≤ wLpNorm p w g :=
  lpNorm_mono_real .of_discrete (by simpa [abs_of_nonneg (hf _)])


-- @@ L165-165 verbatim
end Real


-- @@ L167-167 verbatim
section wLpNorm

-- @@ L168-168 verbatim
variable [Finite α] [DiscreteMeasurableSpace α] {p : ℝ≥0} {w : α → ℝ≥0}


-- @@ L170-170 verbatim
variable [AddCommGroup α]


-- @@ L172-176 expanded
@[simp]
lemma wLpNorm_translate [NormedAddCommGroup E] (a : α) (f : α → E) :
    wLpNorm p (τ a w) (τ a f) = wLpNorm p w f :=
  by
  cases nonempty_fintype α
  obtain rfl | hp := eq_or_ne p 0 <;>
    simp [wLpNorm_eq_sum_norm, *, NNReal.smul_def, ← sum_translate a fun x ↦ w x * ‖f x‖ ^ (_ : ℝ)]


-- @@ L178-178 verbatim
end wLpNorm


-- @@ L180-180 verbatim
namespace Mathlib.Meta.Positivity

-- @@ L181-181 verbatim
open Lean Meta Qq Function MeasureTheory


-- @@ L183-192 expanded
/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p, w]`. -/
@[positivity wLpNorm _ _ _]
meta def evalWLpNorm : PositivityExt where
  eval {u} R _z _p
    e :=
    match _p with
    | none => pure .none
    | some _ => do
      match u, R, e with
      | 0, ~q(ℝ), ~q(@wLpNorm $α $E $instαmeas $instEnorm $p $w $f) =>
        assumeInstancesCommute
        return .nonnegative q(wLpNorm_nonneg)
      | _ =>
        throwError"not wLpNorm"


-- @@ L194-194 verbatim
end Mathlib.Meta.Positivity
