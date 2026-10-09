import OAI.Geometry.PolarProducts.StripMaps


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u61 u62 u63 u64 u65 u66 u67 u68 u69


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

-- @@ L26-26 verbatim
open Set

-- @@ L27-27 verbatim
open scoped Topology ContDiff

-- @@ L28-28 verbatim
open Set

-- @@ L29-29 verbatim
open Set MeasureTheory

-- @@ L30-30 verbatim
open scoped ContDiff Interval Topology

-- @@ L31-31 verbatim
open Set Filter Complex

-- @@ L32-32 verbatim
open scoped Topology ContDiff

-- @@ L33-33 verbatim
open MeasureTheory intervalIntegral Set

-- @@ L34-34 verbatim
open scoped Real


-- @@ L36-36 verbatim
namespace PolarStrips

-- @@ L37-37 verbatim
open Set ComplexCoordinates

-- @@ L38-38 verbatim
open scoped ContDiff

-- @@ L39-39 verbatim
noncomputable section

-- @@ L40-40 verbatim
variable {ι : Type u61} {κ : Type u62} [Fintype ι] [Fintype κ]


-- @@ L42-43 verbatim
def phase (b : κ → R ι) (k : ℕ) (z : C ι) : R ι × R ι :=
  (im z, -re z - ∑ j, PlanarLens.primitive k (functional (b j) z) • b j)


-- @@ L45-53 verbatim
theorem contDiffAt_phase (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) : ContDiffAt ℝ ∞ (phase b k) z := by
  change ContDiffAt ℝ ∞ (fun z : C ι => (ComplexCoordinates.im z, -ComplexCoordinates.re z - ∑ j, PlanarLens.primitive k (functional (b j) z) • b j)) z
  refine (ComplexCoordinates.im : C ι →L[ℝ] R ι).contDiff.contDiffAt.prodMk
    ((ComplexCoordinates.re : C ι →L[ℝ] R ι).contDiff.contDiffAt.neg.sub ?_)
  apply ContDiffAt.sum
  intro j _
  exact ((PlanarLens.contDiffAt_primitive (hz j) k).comp z
    ((functional (b j)).restrictScalars ℝ).contDiff.contDiffAt).smul contDiffAt_const


-- @@ L55-77 verbatim
theorem momentum_monotonic (b : κ → R ι) (k : ℕ) {z w : C ι}
    (hz : z ∈ domain (fun j => functional (b j)))
    (hw : w ∈ domain (fun j => functional (b j))) (hx : im z = im w) :
    inner (𝕜 := ℝ) ((phase b k w).2-(phase b k z).2) (re w-re z) ≤ -‖re w-re z‖^2 := by
  have hj (j : κ) : 0 ≤
      (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) *
      inner (𝕜 := ℝ) (b j) (re w-re z) := by
    have ht : (functional (b j) z).im = (functional (b j) w).im := by rw [im_functional, im_functional, hx]
    have hv : (((functional (b j) z).re : ℂ)+((functional (b j) w).im : ℂ)*Complex.I) ∈ PlanarLens.D := by
      rw [← ht, Complex.re_add_im]; exact hz j
    have hh := PlanarLens.J_product_nonneg (w := (functional (b j) w).re) hv (by simpa only [Complex.re_add_im] using hw j) k
    simpa only [PlanarLens.primitive, ht, inner_sub_right, ← re_functional] using hh
  have he : (phase b k w).2-(phase b k z).2 = -(re w-re z) -
      ∑ j, (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) • b j := by
    simp only [phase, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [he, inner_sub_left, inner_neg_left, real_inner_self_eq_norm_sq]
  have hsum : 0 ≤ inner (𝕜 := ℝ)
      (∑ j, (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) • b j)
      (re w-re z) := by
    simp only [sum_inner, real_inner_smul_left]
    exact Finset.sum_nonneg (fun j _ => hj j)
  linarith


-- @@ L79-88 verbatim
theorem injOn_phase (b : κ → R ι) (k : ℕ) :
    InjOn (phase b k) (domain (fun j => functional (b j))) := by
  intro z hz w hw he
  have hx : im z = im w := congrArg Prod.fst he
  have hp : (phase b k w).2-(phase b k z).2 = 0 := sub_eq_zero.mpr (congrArg Prod.snd he).symm
  have hh := momentum_monotonic b k hz hw hx
  rw [hp, inner_zero_left] at hh
  have hr : re w = re z := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (re w-re z)]))
  apply parts.injective
  exact Prod.ext hr.symm hx


-- @@ L90-90 verbatim
end

-- @@ L91-91 verbatim
end PolarStrips


-- @@ L93-93 verbatim
namespace ComplexPotential

-- @@ L94-94 verbatim
open ComplexCoordinates Set Filter

-- @@ L95-95 verbatim
open scoped Topology ContDiff

-- @@ L96-96 verbatim
noncomputable section


-- @@ L98-99 verbatim
variable {E : Type u63} {F : Type u64} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


-- @@ L101-115 verbatim
theorem ddc_holomorphic_norm_sq {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : AnalyticOnNhd ℂ f U) {z : E} (hz : z ∈ U) (v w : E) :
    let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    ddc (complexStructure E) (fun x => ‖f x‖^2) z v w =
      standardTensor (complexStructure F) (fderiv ℝ f z v) (fderiv ℝ f z w) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have he := ddc_comp (complexStructure E) (complexStructure F)
    ((hf z hz).contDiffAt.restrict_scalars ℝ) (contDiff_norm_sq ℝ).contDiffAt
    (show ∀ᶠ x in 𝓝 z, ∀ a, fderiv ℝ f x (complexStructure E a) = complexStructure F (fderiv ℝ f x a) by
      filter_upwards [hU.mem_nhds hz] with x hx
      exact fderiv_commutes_complexStructure (hf x hx).differentiableAt) v w
  rw [ddc_norm_sq (complexStructure F) complexStructure_skew] at he
  exact he


-- @@ L117-117 verbatim
variable {ι : Type u65} [Fintype ι]


-- @@ L119-120 verbatim
def phaseForm (v w : R ι × R ι) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2-inner (𝕜 := ℝ) w.1 v.2


-- @@ L122-130 verbatim
theorem standardTensor_parts (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    standardTensor (complexStructure (C ι)) v w = phaseForm (parts v) (parts w) := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  dsimp only
  rw [standardTensor_apply, complexStructure_apply, real_inner_parts]
  simp only [re_I_smul, im_I_smul, inner_neg_left, phaseForm, parts_apply]
  rw [real_inner_comm (im v) (re w)]
  ring


-- @@ L132-138 verbatim
theorem standardTensor_coordinates (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    standardTensor (complexStructure (C ι)) v w =
      ∑ i, ((v i).re*(w i).im-(w i).re*(v i).im) := by
  dsimp only
  rw [standardTensor_parts]
  simp [phaseForm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_sub_distrib, mul_comm]


-- @@ L140-145 verbatim
theorem scalar_wedge_mul (c v w : ℂ) :
    (c*v).re*(c*w).im-(c*w).re*(c*v).im =
      ‖c‖^2*(v.re*w.im-w.re*v.im) := by
  rw [Complex.sq_norm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring


-- @@ L147-147 verbatim
end

-- @@ L148-148 verbatim
end ComplexPotential


-- @@ L150-150 verbatim
namespace PolarStrips

-- @@ L151-151 verbatim
open Set Filter ComplexCoordinates ComplexPotential

-- @@ L152-152 verbatim
open scoped Topology ContDiff

-- @@ L153-153 verbatim
noncomputable section

-- @@ L154-154 verbatim
variable {ι : Type u66} {κ : Type u67} [Fintype ι] [Fintype κ]


-- @@ L156-168 verbatim
theorem fderiv_tuple_apply (ℓ : κ → C ι →L[ℂ] ℂ) (k : ℕ) {z : C ι}
    (hz : z ∈ domain ℓ) (v : C ι) (j : κ) :
    fderiv ℝ (tuple ℓ k) z v j =
      (k : ℂ)*PlanarLens.g (ℓ j z)^(k-1)*deriv PlanarLens.g (ℓ j z)*ℓ j v := by
  have ht := ((analyticOnNhd_tuple ℓ k z hz).differentiableAt.restrictScalars ℝ).hasFDerivAt
  have hp := (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : κ => ℂ) j).restrictScalars ℝ).hasFDerivAt.comp z ht)
  have hg := ((PlanarLens.analyticOnNhd_g _ (hz j)).differentiableAt.hasDerivAt.pow k).hasFDerivAt
  have hc := (hg.comp z (ℓ j).hasFDerivAt).restrictScalars ℝ
  have he := hc.unique hp
  have hh := congrArg (fun L : C ι →L[ℝ] ℂ => L v) he
  change (ℓ j v)*((k : ℂ)*PlanarLens.g (ℓ j z)^(k-1)*deriv PlanarLens.g (ℓ j z)) =
    fderiv ℝ (tuple ℓ k) z v j at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh.symm


-- @@ L170-176 verbatim
theorem norm_coefficient (k : ℕ) (w : ℂ) :
    ‖(k : ℂ)*PlanarLens.g w^(k-1)*deriv PlanarLens.g w‖^2 =
      (k : ℝ)^2*PlanarLens.density k w := by
  simp only [norm_mul, norm_pow, Complex.norm_natCast, mul_pow, ← pow_mul, PlanarLens.density]
  have he : (k-1)*2 = 2*k-2 := by omega
  rw [he]
  ring


-- @@ L178-198 verbatim
theorem fderiv_phase_apply (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v : C ι) :
    fderiv ℝ (phase b k) z v = (im v, -re v - ∑ j,
      fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) • b j) := by
  let L : κ → C ι →L[ℝ] R ι := fun j =>
    ((fderiv ℝ (PlanarLens.primitive k) (functional (b j) z)).comp
      ((functional (b j)).restrictScalars ℝ)).smulRight (b j)
  have hj (j : κ) : HasFDerivAt (fun x : C ι => PlanarLens.primitive k (functional (b j) x) • b j) (L j) z :=
    (((PlanarLens.contDiffAt_primitive (hz j) k).differentiableAt (by simp)).hasFDerivAt.comp z
      ((functional (b j)).restrictScalars ℝ).hasFDerivAt).smul_const (b j)
  have hs : HasFDerivAt (fun x : C ι => ∑ j, PlanarLens.primitive k (functional (b j) x) • b j)
      (∑ j, L j) z := by
    simpa only [Finset.sum_fn] using (HasFDerivAt.sum (u := Finset.univ) (fun j _ => hj j))
  have hd : HasFDerivAt (phase b k)
      ((im : C ι →L[ℝ] R ι).prod (-(re : C ι →L[ℝ] R ι)-∑ j, L j)) z :=
    im.hasFDerivAt.prodMk (re.hasFDerivAt.neg.sub hs)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, sub_apply,
    neg_apply, sum_apply, L,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  rfl


-- @@ L200-227 verbatim
theorem phase_form_formula (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v w : C ι) :
    phaseForm (fderiv ℝ (phase b k) z v) (fderiv ℝ (phase b k) z w) =
      phaseForm (parts v) (parts w) + ∑ j,
        (k : ℝ)^2*PlanarLens.density k (functional (b j) z) *
          ((functional (b j) v).re*(functional (b j) w).im -
            (functional (b j) w).re*(functional (b j) v).im) := by
  rw [fderiv_phase_apply b k hz, fderiv_phase_apply b k hz]
  have he (a : C ι) (j : κ) : inner (𝕜 := ℝ) (im a) (b j) = (functional (b j) a).im := by
    rw [real_inner_comm, im_functional]
  have hf : phaseForm (im v, -re v - ∑ j,
        fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) • b j)
      (im w, -re w - ∑ j,
        fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) w) • b j) =
      phaseForm (parts v) (parts w) + ∑ j,
        (fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) * (functional (b j) w).im -
         fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) w) * (functional (b j) v).im) := by
    simp only [phaseForm, parts_apply, inner_sub_right, inner_neg_right, inner_sum,
      real_inner_smul_right, he, Finset.sum_sub_distrib]
    rw [real_inner_comm (im v) (re w), real_inner_comm (im w) (re v)]
    ring
  rw [hf]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [PlanarLens.fderiv_primitive_apply (hz j) k (functional (b j) v),
    PlanarLens.fderiv_primitive_apply (hz j) k (functional (b j) w)]
  ring


-- @@ L229-250 verbatim
theorem phase_pullback (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    phaseForm (fderiv ℝ (phase b k) z v) (fderiv ℝ (phase b k) z w) =
      ddc (complexStructure (C ι)) (fun x => ‖x‖^2 + ‖tuple (fun j => functional (b j)) k x‖^2) z v w := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ (C κ) := InnerProductSpace.complexToReal
  let ℓ := fun j => functional (b j)
  have hτ : ContDiffAt ℝ ∞ (fun x => ‖tuple ℓ k x‖^2) z :=
    ((analyticOnNhd_tuple ℓ k z hz).contDiffAt.restrict_scalars ℝ).norm_sq ℂ
  dsimp only
  rw [ddc_add _ (contDiff_norm_sq ℝ).contDiffAt hτ,
    add_apply, add_apply,
    ddc_norm_sq _ complexStructure_skew,
    ddc_holomorphic_norm_sq (isOpen_domain ℓ) (analyticOnNhd_tuple ℓ k) hz,
    standardTensor_parts v w,
    standardTensor_coordinates (fderiv ℝ (tuple ℓ k) z v) (fderiv ℝ (tuple ℓ k) z w),
    phase_form_formula b k hz]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_tuple_apply ℓ k hz v j, fderiv_tuple_apply ℓ k hz w j, scalar_wedge_mul, norm_coefficient]


-- @@ L252-252 verbatim
end

-- @@ L253-253 verbatim
end PolarStrips


-- @@ L255-255 verbatim
namespace ConvexPolar

-- @@ L256-256 verbatim
open Set Filter

-- @@ L257-257 verbatim
open scoped Topology

-- @@ L258-258 verbatim
noncomputable section

-- @@ L259-259 verbatim
variable {E : Type u68} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L261-261 verbatim
def polar (K : Set E) : Set E := {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}


-- @@ L263-264 verbatim
theorem polar_antitone {K L : Set E} (h : K ⊆ L) : polar L ⊆ polar K :=
  fun _ hp q hq => hp q (h hq)


-- @@ L266-283 verbatim
theorem mem_interior_polar_of_bound {K : Set E} {p : E} {B r : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ q ∈ K, ‖q‖ ≤ B) (hr : r < 1)
    (hp : ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ r) : p ∈ interior (polar K) := by
  let δ := (1-r)/(B+1)
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (Metric.ball_mem_nhds p hδ)
  intro w hw q hq
  have hw' : ‖w-p‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hinner := real_inner_le_norm q (w-p)
  have hbq := hbound q hq
  have hmul : ‖q‖*‖w-p‖ ≤ (B+1)*δ := by
    calc
      ‖q‖*‖w-p‖ ≤ B*δ := mul_le_mul hbq hw'.le (norm_nonneg _) hB
      _ ≤ (B+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have hδeq : (B+1)*δ = 1-r := by dsimp [δ]; field_simp
  rw [inner_sub_right] at hinner
  linarith [hp q hq]


-- @@ L285-285 verbatim
variable {κ : Type u69}


-- @@ L287-287 verbatim
def stripBody (b : κ → E) : Set E := {x | ∀ j, |inner (𝕜 := ℝ) (b j) x| ≤ 1}


-- @@ L289-289 verbatim
variable [Fintype κ]


-- @@ L291-301 verbatim
theorem mem_interior_stripBody (b : κ → E) {x : E}
    (hx : ∀ j, |inner (𝕜 := ℝ) (b j) x| < 1) : x ∈ interior (stripBody b) := by
  let U : Set E := {y | ∀ j, |inner (𝕜 := ℝ) (b j) y| < 1}
  have hopen : IsOpen U := by
    have he : U = ⋂ j, {y | |inner (𝕜 := ℝ) (b j) y| < 1} := by ext y; simp [U]
    rw [he]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (by fun_prop) continuous_const
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hopen.mem_nhds hx) (fun y hy j => (hy j).le))


-- @@ L303-304 verbatim
theorem zero_mem_interior_stripBody (b : κ → E) : (0 : E) ∈ interior (stripBody b) :=
  mem_interior_stripBody b (by intro j; simp)


-- @@ L306-306 verbatim
variable [FiniteDimensional ℝ E]


-- @@ L308-319 verbatim
omit [Fintype κ] in
theorem isCompact_stripBody (b : κ → E)
    (hb : Function.Injective (fun x : E => fun j => inner (𝕜 := ℝ) (b j) x)) :
    IsCompact (stripBody b) := by
  let L : E →L[ℝ] (κ → ℝ) := ContinuousLinearMap.pi (fun j => innerSL ℝ (b j))
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hb)
  have hc := hL.isCompact_preimage (isCompact_pi_infinite (fun _ : κ => isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
  convert hc using 1
  ext x
  simp only [stripBody, mem_ofPred_eq, mem_preimage, ContinuousLinearMap.pi_apply, innerSL_apply_apply,
    mem_Icc, ← abs_le, L]


-- @@ L321-321 verbatim
end

-- @@ L322-322 verbatim
end ConvexPolar


-- @@ L324-324 verbatim
end LowerBoundInline


-- @@ L326-326 verbatim
end OAI
