import OAI.Geometry.PolarProducts.PotentialForms


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u30 u31 u32 u33 u34 u35


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


-- @@ L23-23 verbatim
open Set Filter Function

-- @@ L24-24 verbatim
open scoped ContDiff Topology


-- @@ L26-26 verbatim
namespace CompactExtension

-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-30 verbatim
variable {E : Type u30} {F : Type u31} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L32-34 verbatim
def extend (U : Set E) (f : E → F) : E → F := by
  classical
  exact U.indicator f


-- @@ L36-41 verbatim
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem eventuallyEq_extend {U : Set E} (hU : IsOpen U) (f : E → F) {x : E} (hx : x ∈ U) :
    extend U f =ᶠ[𝓝 x] f := by
  classical
  filter_upwards [hU.mem_nhds hx] with y hy
  exact indicator_of_mem hy f


-- @@ L43-54 verbatim
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem tsupport_extend_subset {U C : Set E} (hC : IsClosed C) {f : E → F}
    (hf : ∀ x ∈ U, x ∉ C → f x = 0) : tsupport (extend U f) ⊆ C := by
  classical
  apply closure_minimal _ hC
  intro x hx
  by_contra hn
  have hh : extend U f x = 0 := by
    by_cases hU : x ∈ U
    · exact (indicator_of_mem hU f).trans (hf x hU hn)
    · exact indicator_of_notMem hU f
  exact hx hh


-- @@ L56-66 verbatim
theorem contDiff_extend {U C : Set E} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    {f : E → F} (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x)
    (hzero : ∀ x ∈ U, x ∉ C → f x = 0) : ContDiff ℝ ∞ (extend U f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf x hx).congr_of_eventuallyEq (eventuallyEq_extend hU f hx)
  · have hxc : x ∉ C := fun hc => hx (hCU hc)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hC.isOpen_compl.mem_nhds hxc] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun ht => hy (tsupport_extend_subset hC hzero ht))


-- @@ L68-71 verbatim
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem hasCompactSupport_extend {U C : Set E} (hC : IsCompact C) {f : E → F}
    (hzero : ∀ x ∈ U, x ∉ C → f x = 0) : HasCompactSupport (extend U f) :=
  hC.of_isClosed_subset (isClosed_tsupport _) (tsupport_extend_subset hC.isClosed hzero)


-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
end CompactExtension


-- @@ L76-76 verbatim
namespace ComplexPotential


-- @@ L78-78 verbatim
open TensorCalculus Set Filter Function

-- @@ L79-79 verbatim
open scoped ContDiff Topology


-- @@ L81-81 verbatim
noncomputable section


-- @@ L83-84 verbatim
variable {E : Type u32} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


-- @@ L86-86 verbatim
local instance moserOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

-- @@ L87-87 verbatim
local instance moserOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

-- @@ L88-88 verbatim
local instance moserTwoGroup : NormedAddCommGroup (TwoTensor E) := inferInstance

-- @@ L89-89 verbatim
local instance moserTwoSpace : NormedSpace ℝ (TwoTensor E) := inferInstance


-- @@ L91-94 verbatim
omit [FiniteDimensional ℝ E] in
theorem tsupport_dc_subset (J : E →L[ℝ] E) (φ : E → ℝ) :
    tsupport (dc J φ) ⊆ tsupport φ :=
  (tsupport_comp_subset (map_zero (dcOp J)) (fderiv ℝ φ)).trans (tsupport_fderiv_subset ℝ)


-- @@ L96-104 verbatim
omit [FiniteDimensional ℝ E] in
theorem fderiv_homeomorph_apply_symm (F : E ≃ₜ E)
    (hF : ContDiff ℝ ∞ (F : E → E)) (hFi : ContDiff ℝ ∞ (F.symm : E → E)) (x a : E) :
    fderiv ℝ (F : E → E) (F.symm x) (fderiv ℝ (F.symm : E → E) x a) = a := by
  have he : (F : E → E) ∘ (F.symm : E → E) = id := funext F.apply_symm_apply
  have hd := fderiv_comp x (hF.differentiable (by simp) (F.symm x))
    (hFi.differentiable (by simp) x)
  rw [he, fderiv_id] at hd
  exact (congrArg (fun L : E →L[ℝ] E => L a) hd).symm


-- @@ L106-170 verbatim
theorem exists_potential_transport (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖)
    {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {τ T : E → ℝ} (hτ : ∀ x ∈ U, IsPSHAt J τ x) (hT : ∀ x ∈ U, IsPSHAt J T x)
    (heq : ∀ x ∈ U, x ∉ C → T x = τ x) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        ddc J (fun y => ‖y‖^2 + τ y) (F x) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = ddc J (fun y => ‖y‖^2 + T y) x a b := by
  let g := CompactExtension.extend U (fun y => T y - τ y)
  have hz : ∀ x ∈ U, x ∉ C → T x - τ x = 0 := by
    intro x hx hxc
    rw [heq x hx hxc, sub_self]
  have hg : ContDiff ℝ ∞ g := CompactExtension.contDiff_extend hU hC.isClosed hCU
    (fun x hx => (hT x hx).1.sub (hτ x hx).1) hz
  have hgs : tsupport g ⊆ C := CompactExtension.tsupport_extend_subset hC.isClosed hz
  let γ := dc J g
  let W := ddc J (fun y => ‖y‖^2 + τ y)
  have hγ : ContDiff ℝ ∞ γ := contDiff_dc J hg
  have hsγ : tsupport γ ⊆ C := (tsupport_dc_subset J g).trans hgs
  have hcγ : HasCompactSupport γ := hC.of_isClosed_subset (isClosed_tsupport _) hsγ
  have hdiff (x : E) (hx : x ∈ U) :
      exteriorD γ x = ddc J T x - ddc J τ x := by
    change ddc J g x = _
    rw [ddc_congr J (CompactExtension.eventuallyEq_extend hU _ hx)]
    exact ddc_sub J (hT x hx).1 (hτ x hx).1
  have hnorm (x : E) (hx : x ∈ U) : W x = standardTensor J + ddc J τ x := by
    dsimp [W]
    rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt (hτ x hx).1, ddc_norm_sq J hsk]
  have hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x := fun x hx =>
    contDiffAt_ddc J ((contDiff_norm_sq ℝ).contDiffAt.add (hτ x hx).1)
  have hWi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible := by
    intro x hx s hs
    apply isInvertible_of_positive_complex_line _ J
    intro a ha
    rw [hnorm x hx, hdiff x hx]
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul,
      standardTensor_complex_line J hJ]
    have hn : 0 < ‖a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
    have h₀ := mul_nonneg (sub_nonneg.mpr hs.2) ((hτ x hx).2 a)
    have h₁ := mul_nonneg hs.1 ((hT x hx).2 a)
    nlinarith
  obtain ⟨F, hF, hFi, hout, hmap, hpull⟩ := Moser.compactlySupported_deformation hU hW
    (fun x _ a b => ddc_skew J _ x a b)
    (fun x hx a b c => ddc_closed J ((contDiff_norm_sq ℝ).contDiffAt.add (hτ x hx).1) a b c)
    hγ hcγ (hsγ.trans hCU) hWi
  refine ⟨F.symm, hFi, hF, ?_, ?_, ?_⟩
  · intro x hx
    exact (F.symm_apply_eq.mpr (hout x hx).symm)
  · intro x
    simpa using (hmap (F.symm x)).symm
  · intro x hx a b
    have hix : F.symm x ∈ U := (hmap (F.symm x)).mp (by simpa using hx)
    have hh := hpull (F.symm x) hix (fderiv ℝ (F.symm : E → E) x a)
      (fderiv ℝ (F.symm : E → E) x b)
    rw [F.apply_symm_apply, fderiv_homeomorph_apply_symm F hF hFi,
      fderiv_homeomorph_apply_symm F hF hFi, hnorm x hx, hdiff x hx] at hh
    have hend : standardTensor J + ddc J τ x + (ddc J T x - ddc J τ x) =
        ddc J (fun y => ‖y‖^2 + T y) x := by
      rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt (hT x hx).1, ddc_norm_sq J hsk]
      abel
    rw [hend] at hh
    exact hh.symm


-- @@ L172-172 verbatim
end

-- @@ L173-173 verbatim
end ComplexPotential


-- @@ L175-175 verbatim
namespace ComplexPotential


-- @@ L177-177 verbatim
open TensorCalculus Set Filter

-- @@ L178-178 verbatim
open scoped ContDiff Topology


-- @@ L180-180 verbatim
variable {E : Type u33} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L182-182 verbatim
noncomputable section


-- @@ L184-191 verbatim
theorem dc_scalar_comp (J : E →L[ℝ] E) {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h (φ x)) :
    dc J (h ∘ φ) x = deriv h (φ x) • dc J φ x := by
  have hd := (hh.hasDerivAt.comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  ext a
  rw [dc_apply, hd]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring


-- @@ L193-199 verbatim
theorem exteriorD_smul_one {γ : E → E →L[ℝ] ℝ} {s : E → ℝ} {x : E}
    (hs : DifferentiableAt ℝ s x) (hγ : DifferentiableAt ℝ γ x) (a b : E) :
    exteriorD (fun y => s y • γ y) x a b = s x * exteriorD γ x a b +
      fderiv ℝ s x a * γ x b - fderiv ℝ s x b * γ x a := by
  simp only [exteriorD_apply, fderiv_fun_smul hs hγ, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring


-- @@ L201-227 verbatim
theorem ddc_scalar_comp (J : E →L[ℝ] E) {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hh : ContDiffAt ℝ ∞ h (φ x)) (a b : E) :
    ddc J (h ∘ φ) x a b = deriv h (φ x) * ddc J φ x a b +
      deriv (deriv h) (φ x) *
        (fderiv ℝ φ x b * fderiv ℝ φ x (J a) -
          fderiv ℝ φ x a * fderiv ℝ φ x (J b)) / 4 := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (h ∘ φ) =ᶠ[𝓝 x] fun y => deriv h (φ y) • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      hφ.continuousAt ((hh.of_le h1).eventually (by simp))] with y hy hz
    exact dc_scalar_comp J (hy.differentiableAt one_ne_zero)
      ((show ContDiffAt ℝ (1 : ℕ∞ω) h (φ y) from hz).differentiableAt one_ne_zero)
  have hdh := (hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => deriv h (φ y)) x :=
    hdh.comp x (hφ.differentiableAt (by simp))
  have hd : fderiv ℝ (fun y => deriv h (φ y)) x =
      deriv (deriv h) (φ x) • fderiv ℝ φ x :=
    (hdh.hasDerivAt.comp_hasFDerivAt x (hφ.differentiableAt (by simp)).hasFDerivAt).fderiv
  have heD : exteriorD (dc J (h ∘ φ)) x =
      exteriorD (fun y => deriv h (φ y) • dc J φ y) x := by
    unfold exteriorD
    rw [he.fderiv_eq]
  rw [ddc, heD, exteriorD_smul_one hs ((contDiffAt_dc J hφ).differentiableAt (by simp))]
  rw [hd]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  change _ = deriv h (φ x) * exteriorD (dc J φ) x a b + _
  ring


-- @@ L229-235 verbatim
theorem ddc_scalar_comp_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hh : ContDiffAt ℝ ∞ h (φ x)) (a : E) :
    ddc J (h ∘ φ) x a (J a) = deriv h (φ x) * ddc J φ x a (J a) +
      deriv (deriv h) (φ x) * ((fderiv ℝ φ x a)^2 + (fderiv ℝ φ x (J a))^2) / 4 := by
  rw [ddc_scalar_comp J hφ hh, hJ, map_neg]
  ring


-- @@ L237-244 verbatim
theorem IsPSHAt.scalar_comp (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {h : ℝ → ℝ} {x : E} (hφ : IsPSHAt J φ x)
    (hh : ContDiffAt ℝ ∞ h (φ x)) (hmono : 0 ≤ deriv h (φ x))
    (hconv : 0 ≤ deriv (deriv h) (φ x)) : IsPSHAt J (h ∘ φ) x := by
  refine ⟨hh.comp x hφ.1, fun a => ?_⟩
  rw [ddc_scalar_comp_complex_line J hJ hφ.1 hh]
  exact add_nonneg (mul_nonneg hmono (hφ.2 a))
    (div_nonneg (mul_nonneg hconv (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num))


-- @@ L246-246 verbatim
end

-- @@ L247-247 verbatim
end ComplexPotential


-- @@ L249-249 verbatim
namespace ComplexPotential


-- @@ L251-251 verbatim
variable {E : Type u34} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L253-283 verbatim
theorem complex_line_inner_sq_le (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (x a : E) :
    (inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2 ≤ ‖x‖^2 * ‖a‖^2 := by
  let p := inner (𝕜 := ℝ) x a
  let q := inner (𝕜 := ℝ) x (J a)
  have hxa : inner (𝕜 := ℝ) (J x) a = -q := by
    dsimp [q]
    linarith [hsk x a]
  have hxj : inner (𝕜 := ℝ) x (J x) = 0 := by
    linarith [hsk x x, real_inner_comm x (J x)]
  have hjx : inner (𝕜 := ℝ) (J x) x = 0 := by rw [real_inner_comm, hxj]
  let w := p • x - q • J x
  have hw : inner (𝕜 := ℝ) w a = p^2 + q^2 := by
    dsimp [w]
    simp only [inner_sub_left, real_inner_smul_left, hxa]
    change p * p - q * (-q) = _
    ring
  have hww : inner (𝕜 := ℝ) w w = (p^2 + q^2) * ‖x‖^2 := by
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hxj, hjx]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hJ]
    ring
  have hcs := real_inner_mul_inner_self_le w a
  rw [hw, hww, real_inner_self_eq_norm_sq] at hcs
  change p^2 + q^2 ≤ ‖x‖^2 * ‖a‖^2
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg p) (sq_nonneg q)) with hs | hs
  · rw [← hs]
    positivity
  · exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith [hcs])


-- @@ L285-285 verbatim
end ComplexPotential


-- @@ L287-287 verbatim
namespace ComplexPotential


-- @@ L289-289 verbatim
open Set Filter

-- @@ L290-290 verbatim
open scoped ContDiff Topology


-- @@ L292-292 verbatim
noncomputable section


-- @@ L294-296 verbatim
@[simp] theorem deriv_log_add (δ t : ℝ) :
    deriv (fun s => Real.log (s + δ)) t = (t + δ)⁻¹ := by
  rw [deriv_comp_add_const, Real.deriv_log]


-- @@ L298-303 verbatim
theorem second_deriv_log_add (δ t : ℝ) (ht : t + δ ≠ 0) :
    deriv (deriv (fun s => Real.log (s + δ))) t = -1 / (t + δ)^2 := by
  have he : deriv (fun s => Real.log (s + δ)) = fun t => (t + δ)⁻¹ :=
    funext (deriv_log_add δ)
  rw [he]
  exact ((hasDerivAt_id t).add_const δ |>.inv ht).deriv


-- @@ L305-305 verbatim
variable {E : Type u35} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L307-307 verbatim
def logNormSq (δ : ℝ) (x : E) : ℝ := Real.log (‖x‖^2 + δ)


-- @@ L309-311 verbatim
theorem contDiffAt_logNormSq (δ : ℝ) {x : E} (hx : ‖x‖^2 + δ ≠ 0) :
    ContDiffAt ℝ ∞ (logNormSq δ) x :=
  ((contDiff_norm_sq ℝ).contDiffAt.add contDiffAt_const).log hx


-- @@ L313-327 verbatim
theorem ddc_logNormSq_complex_line (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    (δ : ℝ) {x : E} (hx : ‖x‖^2 + δ ≠ 0) (a : E) :
    ddc J (logNormSq δ) x a (J a) = ‖a‖^2 / (‖x‖^2 + δ) -
      ((inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2) / (‖x‖^2 + δ)^2 := by
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => Real.log (t + δ)) (‖x‖^2) :=
    (contDiffAt_id.add contDiffAt_const).log hx
  have he := ddc_scalar_comp_complex_line J hJJ (contDiff_norm_sq ℝ).contDiffAt hl a
  rw [ddc_norm_sq J hsk, standardTensor_complex_line J hJ,
    deriv_log_add, second_deriv_log_add δ _ hx, fderiv_norm_sq_apply] at he
  simp only [smul_apply, innerSL_apply_apply] at he
  change ddc J (logNormSq δ) x a (J a) = _ at he
  rw [he]
  ring


-- @@ L329-342 verbatim
theorem isPSHAt_logNormSq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    {δ : ℝ} (hδ : 0 ≤ δ) {x : E} (hx : 0 < ‖x‖^2 + δ) :
    IsPSHAt J (logNormSq δ) x := by
  refine ⟨contDiffAt_logNormSq δ hx.ne', fun a => ?_⟩
  rw [ddc_logNormSq_complex_line J hsk hJ hJJ δ hx.ne']
  have hineq := complex_line_inner_sq_le J hsk hJ x a
  have hnum : (inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2 ≤
      ‖a‖^2 * (‖x‖^2 + δ) := by
    nlinarith [mul_nonneg (sq_nonneg ‖a‖) hδ]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (sq_pos_of_pos hx) hx).mpr
  nlinarith [mul_le_mul_of_nonneg_right hnum hx.le]


-- @@ L344-344 verbatim
end

-- @@ L345-345 verbatim
end ComplexPotential


-- @@ L347-347 verbatim
end LowerBoundInline


-- @@ L349-349 verbatim
end OAI
