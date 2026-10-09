import OAI.Geometry.PolarProducts.RegularizedMaximum


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u38 u39 u40


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

-- @@ L12-12 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L13-13 verbatim
open scoped Topology ContDiff NNReal

-- @@ L14-14 verbatim
open Set Filter Function

-- @@ L15-15 verbatim
open scoped Topology ContDiff

-- @@ L16-16 verbatim
open Set Filter Function

-- @@ L17-17 verbatim
open scoped Topology ContDiff NNReal

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology ContDiff

-- @@ L20-20 verbatim
open Set Filter Function

-- @@ L21-21 verbatim
open scoped Topology ContDiff

-- @@ L22-22 verbatim
open Set Filter Function

-- @@ L23-23 verbatim
open scoped ContDiff Topology

-- @@ L24-24 verbatim
open Set MeasureTheory

-- @@ L25-25 verbatim
open scoped ContDiff Interval Topology


-- @@ L27-27 verbatim
namespace RadialSymplectic


-- @@ L29-29 verbatim
open Set Filter Function TensorCalculus

-- @@ L30-30 verbatim
open scoped Topology ContDiff


-- @@ L32-32 verbatim
variable {E : Type u38} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

-- @@ L37-37 verbatim
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

-- @@ L38-38 verbatim
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

-- @@ L39-39 verbatim
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance


-- @@ L41-41 verbatim
def radialMap (α : E → ℝ) (x : E) : E := α x • x


-- @@ L43-44 verbatim
def radialPrimitive (B : TwoTensor E) (α : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  (α x ^ 2 / 2) • B x


-- @@ L46-52 verbatim
theorem fderiv_radialMap {α : E → ℝ} {x : E} (hα : DifferentiableAt ℝ α x) (a : E) :
    fderiv ℝ (radialMap α) x a = α x • a + (fderiv ℝ α x a) • x := by
  have hh := hα.hasFDerivAt.smul (hasFDerivAt_id x)
  have he := congrArg (fun L : E →L[ℝ] E => L a) hh.fderiv
  change fderiv ℝ (radialMap α) x a = _ at he
  simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, id_eq] using he


-- @@ L54-65 verbatim
theorem fderiv_radialPrimitive (B : TwoTensor E) {α : E → ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (a b : E) :
    fderiv ℝ (radialPrimitive B α) x a b =
      (α x ^ 2 / 2) * B a b + α x * fderiv ℝ α x a * B x b := by
  have hs : HasFDerivAt (fun y => α y ^ 2 / 2) (α x • fderiv ℝ α x) x := by
    convert! (hα.hasFDerivAt.pow 2).mul_const (1 / 2 : ℝ) using 1 <;>
      simp [div_eq_mul_inv, smul_smul]
  have hh := hs.smul B.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) hh.fderiv
  change fderiv ℝ (radialPrimitive B α) x a b = _ at he
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_assoc] using he


-- @@ L67-75 verbatim
theorem radial_pullback (B : TwoTensor E) (hsk : ∀ a b, B a b = -B b a)
    {α : E → ℝ} {x : E} (hα : DifferentiableAt ℝ α x) (a b : E) :
    B (fderiv ℝ (radialMap α) x a) (fderiv ℝ (radialMap α) x b) =
      exteriorD (radialPrimitive B α) x a b := by
  have hz : B x x = 0 := by have hh := hsk x x; linarith
  simp only [fderiv_radialMap hα, exteriorD_apply, fderiv_radialPrimitive B hα,
    map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
  rw [hsk a x, hsk b a]
  ring


-- @@ L77-77 verbatim
end

-- @@ L78-78 verbatim
end RadialSymplectic


-- @@ L80-80 verbatim
open Set

-- @@ L81-81 verbatim
open scoped Topology ContDiff


-- @@ L83-83 verbatim
namespace RadialSymplectic


-- @@ L85-85 verbatim
noncomputable section


-- @@ L87-87 verbatim
def radiusSq (μ δ s : ℝ) : ℝ := s + μ * (s / (s + δ))


-- @@ L89-90 verbatim
def inverseScaleSq (μ δ t : ℝ) : ℝ :=
  2 * δ / (μ + δ - t + Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t))


-- @@ L92-102 verbatim
theorem radiusSq_strictMonoOn {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    StrictMonoOn (radiusSq μ δ) (Ici 0) := by
  intro s hs t ht hst
  have hsδ : 0 < s + δ := add_pos_of_nonneg_of_pos hs hδ
  have htδ : 0 < t + δ := add_pos_of_nonneg_of_pos ht hδ
  have hf : s / (s + δ) ≤ t / (t + δ) := by
    apply (div_le_div_iff₀ hsδ htδ).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hf hμ
  dsimp only [radiusSq]
  linarith


-- @@ L104-106 verbatim
theorem radial_discriminant_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (t : ℝ) :
    0 < (μ + δ - t) ^ 2 + 4 * δ * t := by
  nlinarith [sq_nonneg (t + δ - μ), mul_pos hμ hδ]


-- @@ L108-117 verbatim
theorem inverseScaleSq_den_pos {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (_ht : 0 ≤ t) : 0 < μ + δ - t + Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) := by
  have hsq := Real.sq_sqrt (radial_discriminant_pos hμ hδ t).le
  have hr := Real.sqrt_nonneg ((μ + δ - t) ^ 2 + 4 * δ * t)
  by_contra hc
  have hc' : Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) ≤ -(μ + δ - t) := by
    linarith
  have htt : 0 < t := by linarith
  have hmul := mul_self_le_mul_self hr hc'
  nlinarith [mul_pos hδ htt]


-- @@ L119-121 verbatim
theorem inverseScaleSq_pos {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 < inverseScaleSq μ δ t :=
  div_pos (mul_pos (by norm_num) hδ) (inverseScaleSq_den_pos hμ hδ ht)


-- @@ L123-131 verbatim
theorem inverseScaleSq_quadratic {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    t * (inverseScaleSq μ δ t) ^ 2 + (μ + δ - t) * inverseScaleSq μ δ t - δ = 0 := by
  have hD := (inverseScaleSq_den_pos hμ hδ ht).ne'
  have hsq := Real.sq_sqrt (radial_discriminant_pos hμ hδ t).le
  unfold inverseScaleSq
  generalize Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) = R at hD hsq ⊢
  field_simp [hD]
  nlinarith


-- @@ L133-141 verbatim
theorem radiusSq_inverse {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    radiusSq μ δ (inverseScaleSq μ δ t * t) = t := by
  have hq := inverseScaleSq_pos hμ hδ ht
  have hquad := inverseScaleSq_quadratic hμ hδ ht
  have hd : 0 < inverseScaleSq μ δ t * t + δ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le ht) hδ
  unfold radiusSq
  field_simp [hd.ne']
  nlinarith [mul_eq_zero_of_left hquad t]


-- @@ L143-150 verbatim
theorem inverseScaleSq_factor {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    (1 + μ / (inverseScaleSq μ δ t * t + δ)) * inverseScaleSq μ δ t = 1 := by
  have hq := inverseScaleSq_pos hμ hδ ht
  have hquad := inverseScaleSq_quadratic hμ hδ ht
  have hd : 0 < inverseScaleSq μ δ t * t + δ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le ht) hδ
  field_simp [hd.ne']
  nlinarith


-- @@ L152-158 verbatim
theorem contDiffAt_inverseScaleSq {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (inverseScaleSq μ δ) t := by
  have hs : ContDiffAt ℝ ∞ (fun y => Real.sqrt ((μ + δ - y) ^ 2 + 4 * δ * y)) t :=
    (Real.contDiffAt_sqrt (radial_discriminant_pos hμ hδ t).ne').comp t
      (((contDiffAt_const.sub contDiffAt_id).pow 2).add (contDiffAt_const.mul contDiffAt_id))
  exact contDiffAt_const.div ((contDiffAt_const.sub contDiffAt_id).add hs)
    (inverseScaleSq_den_pos hμ hδ ht).ne'


-- @@ L160-160 verbatim
end

-- @@ L161-161 verbatim
end RadialSymplectic


-- @@ L163-163 verbatim
namespace RadialSymplectic


-- @@ L165-165 verbatim
open Set

-- @@ L166-166 verbatim
open scoped Topology ContDiff


-- @@ L168-168 verbatim
variable {E : Type u39} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L170-170 verbatim
noncomputable section


-- @@ L172-172 verbatim
def expansionScale (μ δ : ℝ) (x : E) : ℝ := Real.sqrt (1 + μ / (‖x‖ ^ 2 + δ))

-- @@ L173-173 verbatim
def radialExpansion (μ δ : ℝ) : E → E := radialMap (expansionScale μ δ)

-- @@ L174-175 verbatim
def contractionScale (μ δ : ℝ) (x : E) : ℝ :=
  Real.sqrt (inverseScaleSq μ δ (‖x‖ ^ 2))

-- @@ L176-176 verbatim
def radialContraction (μ δ : ℝ) : E → E := radialMap (contractionScale μ δ)


-- @@ L178-184 verbatim
omit [InnerProductSpace ℝ E] in
theorem expansionScale_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    0 < expansionScale μ δ x := by
  unfold expansionScale
  apply Real.sqrt_pos.mpr
  have hd : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  positivity


-- @@ L186-192 verbatim
omit [InnerProductSpace ℝ E] in
theorem expansionScale_sq {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    expansionScale μ δ x ^ 2 = 1 + μ / (‖x‖ ^ 2 + δ) := by
  unfold expansionScale
  apply Real.sq_sqrt
  have hd : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  positivity


-- @@ L194-199 verbatim
theorem norm_sq_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    ‖radialExpansion μ δ x‖ ^ 2 = radiusSq μ δ (‖x‖ ^ 2) := by
  simp only [radialExpansion, radialMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [expansionScale_sq hμ hδ]
  unfold radiusSq
  ring


-- @@ L201-212 verbatim
theorem radialExpansion_injective {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    Function.Injective (radialExpansion μ δ : E → E) := by
  intro x y h
  have hh := congrArg (fun z : E => ‖z‖ ^ 2) h
  rw [norm_sq_radialExpansion hμ hδ, norm_sq_radialExpansion hμ hδ] at hh
  have hnorm := (radiusSq_strictMonoOn hμ.le hδ).injOn (sq_nonneg ‖x‖) (sq_nonneg ‖y‖) hh
  have hscale : expansionScale μ δ x = expansionScale μ δ y := by
    unfold expansionScale
    rw [hnorm]
  dsimp only [radialExpansion, radialMap] at h
  rw [hscale] at h
  exact (smul_right_injective E (expansionScale_pos hμ hδ y).ne') h


-- @@ L214-217 verbatim
omit [InnerProductSpace ℝ E] in
theorem contractionScale_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    0 < contractionScale μ δ x :=
  Real.sqrt_pos.mpr (inverseScaleSq_pos hμ hδ (sq_nonneg _))


-- @@ L219-222 verbatim
theorem norm_sq_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    ‖radialContraction μ δ x‖ ^ 2 = inverseScaleSq μ δ (‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  simp only [radialContraction, radialMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [contractionScale, Real.sq_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg _)).le]


-- @@ L224-233 verbatim
theorem expansionScale_mul_contractionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : expansionScale μ δ (radialContraction μ δ x) * contractionScale μ δ x = 1 := by
  have hp := expansionScale_pos hμ hδ (radialContraction μ δ x)
  have hq := contractionScale_pos hμ hδ x
  have hsq : (expansionScale μ δ (radialContraction μ δ x) * contractionScale μ δ x)^2 = 1 := by
    rw [mul_pow, expansionScale_sq hμ hδ, contractionScale,
      Real.sq_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg _)).le,
      norm_sq_radialContraction hμ hδ]
    exact inverseScaleSq_factor hμ hδ (sq_nonneg _)
  nlinarith [mul_pos hp hq]


-- @@ L235-238 verbatim
theorem radialExpansion_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : radialExpansion μ δ (radialContraction μ δ x) = x := by
  change expansionScale μ δ (radialContraction μ δ x) • (contractionScale μ δ x • x) = x
  rw [smul_smul, expansionScale_mul_contractionScale hμ hδ, one_smul]


-- @@ L240-242 verbatim
theorem radialContraction_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : radialContraction μ δ (radialExpansion μ δ x) = x :=
  radialExpansion_injective hμ hδ (radialExpansion_radialContraction hμ hδ _)


-- @@ L244-251 verbatim
theorem contDiff_expansionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (expansionScale μ δ : E → ℝ) := by
  have hn : ContDiff ℝ ∞ (fun x : E => ‖x‖^2 + δ) := (contDiff_norm_sq ℝ).add contDiff_const
  have hd (x : E) : ‖x‖ ^ 2 + δ ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne'
  have hp (x : E) : 1 + μ / (‖x‖ ^ 2 + δ) ≠ 0 := by
    have hpp : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
    positivity
  exact (contDiff_const.add (contDiff_const.div hn hd)).sqrt hp


-- @@ L253-261 verbatim
theorem contDiff_contractionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (contractionScale μ δ : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hi : ContDiffAt ℝ ∞ (fun z : E => inverseScaleSq μ δ (‖z‖ ^ 2)) x :=
    (contDiffAt_inverseScaleSq hμ hδ (sq_nonneg ‖x‖)).comp (f := fun z : E => ‖z‖^2) x
      (contDiff_norm_sq ℝ).contDiffAt
  exact (Real.contDiffAt_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg ‖x‖)).ne').comp
    (f := fun z : E => inverseScaleSq μ δ (‖z‖ ^ 2)) x hi


-- @@ L263-265 verbatim
theorem contDiff_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (radialExpansion μ δ : E → E) :=
  (contDiff_expansionScale hμ hδ).smul contDiff_id


-- @@ L267-269 verbatim
theorem contDiff_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (radialContraction μ δ : E → E) :=
  (contDiff_contractionScale hμ hδ).smul contDiff_id


-- @@ L271-277 verbatim
def radialHomeomorph {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) : E ≃ₜ E where
  toFun := radialExpansion μ δ
  invFun := radialContraction μ δ
  left_inv := radialContraction_radialExpansion hμ hδ
  right_inv := radialExpansion_radialContraction hμ hδ
  continuous_toFun := (contDiff_radialExpansion hμ hδ).continuous
  continuous_invFun := (contDiff_radialContraction hμ hδ).continuous


-- @@ L279-289 verbatim
theorem radialContraction_mapsTo {μ δ a r : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (hbound : a ≤ radiusSq μ δ (r^2)) :
    MapsTo (radialContraction μ δ : E → E) {x | ‖x‖^2 < a} {x | ‖x‖^2 < r^2} := by
  intro x hx
  have hi := radiusSq_inverse hμ hδ (sq_nonneg ‖x‖)
  have hh : radiusSq μ δ (‖radialContraction μ δ x‖^2) < radiusSq μ δ (r^2) := by
    rw [norm_sq_radialContraction hμ hδ, hi]
    exact lt_of_lt_of_le hx hbound
  exact ((radiusSq_strictMonoOn hμ.le hδ).lt_iff_lt
    (show ‖radialContraction μ δ x‖^2 ∈ Ici (0 : ℝ) from sq_nonneg ‖radialContraction μ δ x‖)
    (show r^2 ∈ Ici (0 : ℝ) from sq_nonneg r)).mp hh


-- @@ L291-291 verbatim
end

-- @@ L292-292 verbatim
end RadialSymplectic


-- @@ L294-294 verbatim
namespace RadialSymplectic


-- @@ L296-296 verbatim
open ComplexPotential TensorCalculus

-- @@ L297-297 verbatim
open scoped ContDiff


-- @@ L299-299 verbatim
noncomputable section


-- @@ L301-301 verbatim
variable {E : Type u40} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L303-303 verbatim
def modelPotential (μ δ : ℝ) (x : E) : ℝ := ‖x‖^2 + μ * Real.log (‖x‖^2 + δ)


-- @@ L305-309 verbatim
theorem contDiff_modelPotential (μ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (modelPotential μ δ : E → ℝ) :=
  (contDiff_norm_sq ℝ).add (contDiff_const.mul
    (((contDiff_norm_sq ℝ).add contDiff_const).log
      (fun x => (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hδ).ne')))


-- @@ L311-326 verbatim
theorem dc_modelPotential (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    dc J (modelPotential μ δ) x = radialPrimitive (standardTensor J) (expansionScale μ δ) x := by
  let h : ℝ → ℝ := fun t => t + μ * Real.log (t + δ)
  have hp : ‖x‖^2 + δ ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne'
  have hd : HasDerivAt h (1 + μ * (‖x‖^2 + δ)⁻¹) (‖x‖^2) := by
    convert (hasDerivAt_id (‖x‖^2)).add
      ((((hasDerivAt_id (‖x‖^2)).add_const δ).log hp).const_mul μ) using 1 <;> first | rfl | simp [one_div]
  change dc J (h ∘ (fun y : E => ‖y‖^2)) x = _
  rw [dc_scalar_comp J ((contDiff_norm_sq ℝ).differentiable (show (∞ : ℕ∞ω) ≠ 0 by simp) x)
    hd.differentiableAt, hd.deriv, dc_norm_sq J hsk, smul_smul]
  unfold radialPrimitive
  rw [expansionScale_sq hμ hδ]
  congr 1
  ring


-- @@ L328-340 verbatim
theorem radialExpansion_pullback (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x a b : E) :
    standardTensor J (fderiv ℝ (radialExpansion μ δ : E → E) x a)
      (fderiv ℝ (radialExpansion μ δ : E → E) x b) = ddc J (modelPotential μ δ) x a b := by
  have hsk' (a b : E) : standardTensor J a b = -standardTensor J b a := by
    change inner (𝕜 := ℝ) (J a) b = -inner (𝕜 := ℝ) (J b) a
    rw [← real_inner_comm (J a) b, hsk]
  have he : dc J (modelPotential μ δ) = radialPrimitive (standardTensor J) (expansionScale μ δ) :=
    funext (dc_modelPotential J hsk hμ hδ)
  rw [ddc, he]
  exact radial_pullback (standardTensor J) hsk' ((contDiff_expansionScale hμ hδ).differentiable
    (by simp) x) a b


-- @@ L342-356 verbatim
theorem radialContraction_pullback (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x a b : E) :
    ddc J (modelPotential μ δ) (radialContraction μ δ x)
      (fderiv ℝ (radialContraction μ δ : E → E) x a)
      (fderiv ℝ (radialContraction μ δ : E → E) x b) = standardTensor J a b := by
  have hd (v : E) : fderiv ℝ (radialExpansion μ δ : E → E) (radialContraction μ δ x)
      (fderiv ℝ (radialContraction μ δ : E → E) x v) = v := by
    have he : (radialExpansion μ δ : E → E) ∘ radialContraction μ δ = id :=
      funext (radialExpansion_radialContraction hμ hδ)
    have hh := fderiv_comp x ((contDiff_radialExpansion hμ hδ).differentiable (by simp)
      (radialContraction μ δ x)) ((contDiff_radialContraction hμ hδ).differentiable (by simp) x)
    rw [he, fderiv_id] at hh
    exact (congrArg (fun L : E →L[ℝ] E => L v) hh).symm
  rw [← radialExpansion_pullback J hsk hμ hδ, hd, hd]


-- @@ L358-358 verbatim
end

-- @@ L359-359 verbatim
end RadialSymplectic


-- @@ L361-361 verbatim
end LowerBoundInline


-- @@ L363-363 verbatim
end OAI
