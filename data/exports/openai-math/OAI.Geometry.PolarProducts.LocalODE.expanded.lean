import OAI.Geometry.PolarProducts.SmoothPaths


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u3 u4 u5 u6


-- @@ L7-7 verbatim
section LowerBoundInline

-- @@ L8-8 verbatim
open Set Filter Function

-- @@ L9-9 verbatim
open scoped Topology ContDiff NNReal

-- @@ L10-10 verbatim
open Set Filter Metric

-- @@ L11-11 verbatim
open scoped Topology ContDiff


-- @@ L13-13 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L14-14 verbatim
open scoped Topology ContDiff NNReal


-- @@ L16-16 verbatim
namespace SmoothODE


-- @@ L18-18 verbatim
abbrev Time := Icc (0 : ℝ) 1


-- @@ L20-20 verbatim
variable {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
def extend (u : C(Time, E)) : ℝ → E := fun t => u (projIcc 0 1 zero_le_one t)


-- @@ L26-28 verbatim
omit [NormedSpace ℝ E] in
theorem continuous_extend (u : C(Time, E)) : Continuous (extend u) :=
  u.continuous.comp continuous_projIcc


-- @@ L30-32 verbatim
omit [NormedSpace ℝ E] in
@[simp] theorem extend_coe (u : C(Time, E)) (t : Time) : extend u t = u t := by
  simp [extend]


-- @@ L34-37 verbatim
def primitive (u : C(Time, E)) : C(Time, E) :=
  ⟨fun t => ∫ s in 0..(t : ℝ), extend u s,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_extend u).intervalIntegrable a b) 0).comp continuous_subtype_val⟩


-- @@ L39-40 verbatim
@[simp] theorem primitive_apply (u : C(Time, E)) (t : Time) :
    primitive u t = ∫ s in 0..(t : ℝ), extend u s := rfl


-- @@ L42-51 verbatim
theorem norm_primitive_le (u : C(Time, E)) : ‖primitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := ‖u‖)
    (fun s _ => u.norm_coe_le_norm (projIcc 0 1 zero_le_one s))
  change ‖∫ s in 0..(t : ℝ), extend u s‖ ≤ ‖u‖
  refine h.trans ?_
  rw [sub_zero, abs_of_nonneg t.2.1]
  exact mul_le_of_le_one_right (norm_nonneg _) t.2.2


-- @@ L53-70 verbatim
def primitiveCLM : C(Time, E) →L[ℝ] C(Time, E) := by
  let L : C(Time, E) →ₗ[ℝ] C(Time, E) :=
    { toFun := primitive
      map_add' := by
        intro u v
        ext t
        change (∫ s in 0..(t : ℝ), extend u s + extend v s) = _
        exact intervalIntegral.integral_add
          ((continuous_extend u).intervalIntegrable _ _)
          ((continuous_extend v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        exact intervalIntegral.integral_smul c (extend u) }
  exact L.mkContinuous 1 (by
    intro u
    change ‖primitive u‖ ≤ 1 * ‖u‖
    simpa using norm_primitive_le u)


-- @@ L72-72 verbatim
@[simp] theorem primitiveCLM_apply (u : C(Time, E)) : primitiveCLM u = primitive u := rfl


-- @@ L74-76 verbatim
theorem primitiveCLM_norm_le : ‖primitiveCLM (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_primitive_le u


-- @@ L78-78 verbatim
end

-- @@ L79-79 verbatim
end SmoothODE


-- @@ L81-81 verbatim
namespace SmoothODE


-- @@ L83-83 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L84-84 verbatim
open scoped Topology ContDiff NNReal


-- @@ L86-87 verbatim
variable {E : Type u4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]


-- @@ L89-89 verbatim
noncomputable section


-- @@ L91-93 verbatim
def picard {V : E → E} (hV : Continuous V) (h : ℝ) (x : E)
    (u : C(Time, E)) : C(Time, E) :=
  ContinuousMap.const Time x + h • primitive (SmoothPaths.superpose hV u)


-- @@ L95-104 verbatim
omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem lipschitz_superpose {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) :
    LipschitzWith K (SmoothPaths.superpose (X := Time) hV.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (ContinuousMap.dist_le (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro t
  exact (hV.dist_le_mul (u t) (v t)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist (f := u) (g := v) t) K.coe_nonneg)


-- @@ L106-115 verbatim
omit [CompleteSpace E] in
theorem lipschitz_picard {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (x : E) : LipschitzWith (‖h‖₊ * K) (picard hV.continuous h x) := by
  have hp : LipschitzWith 1 (primitive (E := E)) := by
    change LipschitzWith 1 (primitiveCLM (E := E))
    exact ContinuousLinearMap.opNorm_le_iff_lipschitz.mp primitiveCLM_norm_le
  have hi := (lipschitzWith_smul h).comp (hp.comp (lipschitz_superpose hV))
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa [picard] using hi.dist_le_mul u v


-- @@ L117-126 verbatim
omit [CompleteSpace E] in

theorem contDiff_picard [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V) (h : ℝ) :
    ContDiff ℝ ∞ (fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : E × C(Time, E) => ContinuousMap.const Time p.1) :=
    (ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)).contDiff.comp contDiff_fst
  have hp : ContDiff ℝ ∞ (fun p : E × C(Time, E) =>
      primitive (SmoothPaths.superpose hV.continuous p.2)) :=
    primitiveCLM.contDiff.comp ((SmoothPaths.contDiff_superpose hV).comp contDiff_snd)
  exact hc.add (hp.const_smul h)


-- @@ L128-130 verbatim
def trajectory {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : C(Time, E) :=
  SmoothContraction.fixedPoint (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) hh (lipschitz_picard hV h) x


-- @@ L132-135 verbatim
theorem trajectory_eq {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    picard hV.continuous h x (trajectory hV h hh x) = trajectory hV h hh x :=
  SmoothContraction.fixedPoint_eq (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) hh (lipschitz_picard hV h) x


-- @@ L137-140 verbatim
theorem contDiff_trajectory [ProperSpace E] {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) :
    ContDiff ℝ ∞ (trajectory hV h hh) :=
  SmoothContraction.contDiff_fixedPoint (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) (contDiff_picard hVs h) hh (lipschitz_picard hV h)


-- @@ L142-144 verbatim
def curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : ℝ) : E :=
  x + h • ∫ s in 0..t, V (extend (trajectory hV h hh x) s)


-- @@ L146-149 verbatim
@[simp] theorem curve_coe {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : Time) :
    curve hV h hh x t = trajectory hV h hh x t :=
  congrArg (fun u : C(Time, E) => u t) (trajectory_eq hV h hh x)


-- @@ L151-153 verbatim
@[simp] theorem curve_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : curve hV h hh x 0 = x := by
  simp [curve]


-- @@ L155-159 verbatim
theorem continuous_curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : Continuous (curve hV h hh x) := by
  have hc := hV.continuous.comp (continuous_extend (trajectory hV h hh x))
  exact continuous_const.add
    ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).const_smul h)


-- @@ L161-172 verbatim
theorem hasDerivAt_curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : Time) :
    HasDerivAt (curve hV h hh x) (h • V (curve hV h hh x t)) (t : ℝ) := by
  have hc := hV.continuous.comp (continuous_extend (trajectory hV h hh x))
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 (t : ℝ)))
      hc.continuousAt
  rw [curve_coe]
  change HasDerivAt (fun s : ℝ =>
    x + h • ∫ r in 0..s, V (extend (trajectory hV h hh x) r)) _ (t : ℝ)
  simpa only [Pi.smul_apply, Function.comp_apply, extend_coe] using
    (hd.const_smul h).const_add x


-- @@ L174-176 verbatim
def step {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : E :=
  trajectory hV h hh x ⟨1, by constructor <;> norm_num⟩


-- @@ L178-182 verbatim
theorem contDiff_step [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) : ContDiff ℝ ∞ (step hV h hh) :=
  (ContinuousMap.evalCLM ℝ (M := E) (⟨1, by constructor <;> norm_num⟩ : Time)).contDiff.comp
    (contDiff_trajectory hV hVs h hh)


-- @@ L184-186 verbatim
@[simp] theorem curve_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : curve hV h hh x 1 = step hV h hh x :=
  curve_coe hV h hh x ⟨1, by constructor <;> norm_num⟩


-- @@ L188-188 verbatim
end

-- @@ L189-189 verbatim
end SmoothODE


-- @@ L191-191 verbatim
namespace SmoothODE


-- @@ L193-193 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L194-194 verbatim
open scoped Topology ContDiff NNReal


-- @@ L196-197 verbatim
variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]


-- @@ L199-199 verbatim
noncomputable section


-- @@ L201-218 verbatim
theorem curve_unique {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 1))
    (hf' : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f (h • V (f t)) (Ici t) t)
    (h0 : f 0 = x) : EqOn f (curve hV h hh x) (Icc 0 1) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ y => h • V y) (s := fun _ => univ)
    (K := ‖h‖₊ * K)
  · intro _ _
    exact ((lipschitzWith_smul h).comp hV).lipschitzOnWith
  · exact hf
  · exact hf'
  · intro _ _; trivial
  · exact (continuous_curve hV h hh x).continuousOn
  · intro t ht
    exact (hasDerivAt_curve hV h hh x ⟨t, ht.1, ht.2.le⟩).hasDerivWithinAt
  · intro _ _; trivial
  · simpa using h0


-- @@ L220-234 verbatim
theorem curve_reverse {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    EqOn (fun t => curve hV h hh x (1 - t))
      (curve hV (-h) (by simpa using hh) (step hV h hh x)) (Icc 0 1) := by
  apply curve_unique hV (-h) (by simpa using hh) (step hV h hh x)
  · exact ((continuous_curve hV h hh x).comp (continuous_const.sub continuous_id)).continuousOn
  · intro t ht
    have hr : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hd := (hasDerivAt_curve hV h hh x ⟨1 - t, hr⟩).scomp t
      ((hasDerivAt_id t).const_sub 1)
    have he : HasDerivAt (fun t => curve hV h hh x (1 - t))
        ((-h) • V (curve hV h hh x (1 - t))) t := by
      simpa only [Function.comp_def, id_eq, neg_smul, one_smul] using hd
    exact he.hasDerivWithinAt
  · simp


-- @@ L236-240 verbatim
theorem step_neg_step {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    step hV (-h) (by simpa using hh) (step hV h hh x) = x := by
  have he := curve_reverse hV h hh x (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he.symm


-- @@ L242-251 verbatim
def stepHomeomorph [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) : E ≃ₜ E where
  toFun := step hV h hh
  invFun := step hV (-h) (by simpa using hh)
  left_inv := step_neg_step hV h hh
  right_inv x := by
    simpa only [neg_neg] using step_neg_step hV (-h) (by simpa using hh) x
  continuous_toFun := (contDiff_step hV hVs h hh).continuous
  continuous_invFun := (contDiff_step hV hVs (-h) (by simpa using hh)).continuous


-- @@ L253-256 verbatim
@[simp] theorem stepHomeomorph_apply [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    stepHomeomorph hV hVs h hh x = step hV h hh x := rfl


-- @@ L258-265 verbatim
theorem curve_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    EqOn (curve hV h hh x) (fun _ => x) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x continuousOn_const
  · intro t _
    simpa only [hx, smul_zero] using (hasDerivWithinAt_const t (Ici t) x)
  · rfl


-- @@ L267-271 verbatim
@[simp] theorem step_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    step hV h hh x = x := by
  have he := curve_of_eq_zero hV h hh x hx (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he


-- @@ L273-273 verbatim
end

-- @@ L274-274 verbatim
end SmoothODE


-- @@ L276-276 verbatim
namespace SmoothODE


-- @@ L278-278 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L279-279 verbatim
open scoped Topology ContDiff NNReal


-- @@ L281-282 verbatim
variable {E : Type u6} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]


-- @@ L284-284 verbatim
noncomputable section


-- @@ L286-288 verbatim
def tangentPath {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) : C(Time, E) :=
  fderiv ℝ (trajectory hV h hh) x v


-- @@ L290-313 verbatim
theorem tangentPath_eq {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    tangentPath hV h hh x v =
      ContinuousMap.const Time v + h • primitive
        (SmoothPaths.applyField
          (SmoothPaths.superpose (hVs.continuous_fderiv (by simp)) (trajectory hV h hh x))
          (tangentPath hV h hh x v)) := by
  let Q := trajectory hV h hh
  let DQ := fderiv ℝ Q x
  let A := SmoothPaths.applyField
    (SmoothPaths.superpose (hVs.continuous_fderiv (by simp)) (Q x))
  have hQ : HasFDerivAt Q DQ x :=
    (contDiff_trajectory hV hVs h hh).differentiable (by simp) x |>.hasFDerivAt
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hVs.differentiable (by simp)) (hVs.continuous_fderiv (by simp)) (Q x)).comp x hQ
  have hP := (primitiveCLM (E := E)).hasFDerivAt.comp x hS
  have hC := (ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)).hasFDerivAt (x := x)
  have hD := hC.add (hP.const_smul h)
  have hD' : HasFDerivAt Q
      ((ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)) +
        h • primitiveCLM.comp (A.comp DQ)) x := by
    apply hD.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun y => (trajectory_eq hV h hh y).symm)
  exact congrArg (fun L : E →L[ℝ] C(Time, E) => L v) (hQ.unique hD')


-- @@ L315-315 verbatim
end

-- @@ L316-316 verbatim
end SmoothODE


-- @@ L318-318 verbatim
end LowerBoundInline


-- @@ L320-320 verbatim
end OAI
