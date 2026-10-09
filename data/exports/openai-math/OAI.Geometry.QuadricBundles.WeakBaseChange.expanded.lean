import OAI.Geometry.QuadricBundles.PointwiseRepresentative


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace QuadricCounterexample

-- @@ L10-10 verbatim
open Set Filter Topology MeasureTheory

-- @@ L11-11 verbatim
open scoped ENNReal

-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
section Composition

-- @@ L15-18 verbatim
variable {α : Type u1} {β : Type u2} {E : Type u3} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {T : α → β} {c : ℝ≥0∞}


-- @@ L20-23 verbatim
def boundedCompositionLp (hT : Measurable T) (hc : c ≠ ∞)
    (hdom : Measure.map T μ ≤ c • ν) : Lp E p ν →L[ℝ] Lp E p μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ T (⟨hT,rfl⟩ : MeasurePreserving T μ (Measure.map T μ))).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hc hdom)


-- @@ L25-31 verbatim
lemma boundedCompositionLp_coe (hT : Measurable T) (hc : c ≠ ∞)
    (hdom : Measure.map T μ ≤ c • ν) (f : Lp E p ν) :
    boundedCompositionLp hT hc hdom f =ᵐ[μ] fun x ↦ f (T x) := by
  have hpres : MeasurePreserving T μ (Measure.map T μ) := ⟨hT,rfl⟩
  have he := hpres.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul hc hdom f)
  exact (Lp.coeFn_compMeasurePreserving _ hpres).trans he

-- @@ L32-32 verbatim
end Composition


-- @@ L34-34 verbatim
section Weak

-- @@ L35-36 verbatim
variable {E : Type u4} {F : Type u5} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]


-- @@ L38-38 verbatim
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

-- @@ L39-39 verbatim
local instance : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F


-- @@ L41-47 verbatim
omit [CompleteSpace E] in
lemma complex_weak_implies_real {u : ℕ → E} {w : E}
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (u k) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ v, Tendsto (fun k ↦ inner ℝ (u k) v) atTop (𝓝 (inner ℝ w v)) := by
  intro v
  simpa only [real_inner_eq_re_inner ℂ, RCLike.re_eq_complex_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp (hw v)


-- @@ L49-53 verbatim
lemma real_weakLimit_map (A : E →L[ℝ] F) {u : ℕ → E} {w : E}
    (hw : ∀ v, Tendsto (fun k ↦ inner ℝ (u k) v) atTop (𝓝 (inner ℝ w v))) :
    ∀ v, Tendsto (fun k ↦ inner ℝ (A (u k)) v) atTop (𝓝 (inner ℝ (A w) v)) := by
  intro v
  simpa only [← ContinuousLinearMap.adjoint_inner_right] using hw (A.adjoint v)


-- @@ L55-68 verbatim
lemma real_weakLimit_approximate_graph (A : E →L[ℝ] F)
    {u : ℕ → E} {v : ℕ → F} {w : E} {z : F}
    (hw : ∀ e, Tendsto (fun k ↦ inner ℂ (u k) e) atTop (𝓝 (inner ℂ w e)))
    (hz : ∀ f, Tendsto (fun k ↦ inner ℂ (v k) f) atTop (𝓝 (inner ℂ z f)))
    (herr : Tendsto (fun k ↦ ‖v k-A (u k)‖) atTop (𝓝 0)) : z=A w := by
  have he := tendsto_zero_iff_norm_tendsto_zero.mpr herr
  have hweak (f : F) := (complex_weak_implies_real hz f).sub
    (real_weakLimit_map A (complex_weak_implies_real hw) f)
  have hzero (f : F) : Tendsto (fun k ↦ inner ℝ (v k-A (u k)) f) atTop (𝓝 0) := by
    simpa only [inner_zero_left] using he.inner tendsto_const_nhds
  have heq (f : F) : inner ℝ (z-A w) f=0 := by
    apply tendsto_nhds_unique _ (hzero f)
    simpa only [inner_sub_left] using hweak f
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (heq (z-A w)))

-- @@ L69-69 verbatim
end Weak


-- @@ L71-71 verbatim
section Jacobian

-- @@ L72-74 verbatim
variable {X : Type u6} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]


-- @@ L76-103 verbatim
lemma map_restrict_involution_le {T : X → X} {K : Set X} {C : ℝ}
    (hT : Measurable T) (hi : Function.Involutive T)
    (hTK : MeasurableSet (T '' K)) {T' : X → X →L[ℝ] X}
    (hd : ∀ x ∈ T '' K, HasFDerivWithinAt T (T' x) (T '' K) x)
    (hb : ∀ x ∈ T '' K, |(T' x).det| ≤ C) :
    Measure.map T (μ.restrict K) ≤ ENNReal.ofReal C • μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hT hs,Measure.restrict_apply (hT hs),Measure.smul_apply]
  have he : T ⁻¹' s ∩ K = T '' (s ∩ T '' K) := by
    ext x
    constructor
    · rintro ⟨hxs,hxK⟩
      exact ⟨T x,⟨hxs,⟨x,hxK,rfl⟩⟩,hi x⟩
    · rintro ⟨y,⟨hys,⟨z,hzK,hzy⟩⟩,hyx⟩
      have hTx : T x=y := by rw [← hyx,hi]
      refine ⟨by simpa only [mem_preimage,hTx] using hys,?_⟩
      have hxz : x=z := by rw [← hyx,← hzy,hi]
      simpa only [hxz] using hzK
  rw [he]
  calc
    μ (T '' (s ∩ T '' K)) ≤ ∫⁻ x in s ∩ T '' K, ENNReal.ofReal |(T' x).det| ∂μ :=
      addHaar_image_le_lintegral_abs_det_fderiv μ (hs.inter hTK)
        (fun x hx ↦ (hd x hx.2).mono inter_subset_right)
    _ ≤ ∫⁻ _x in s ∩ T '' K, ENNReal.ofReal C ∂μ :=
      setLIntegral_mono measurable_const (fun x hx ↦ ENNReal.ofReal_le_ofReal (hb x hx.2))
    _ = ENNReal.ofReal C * μ (s ∩ T '' K) := by simp
    _ ≤ ENNReal.ofReal C • μ s := by simpa only [smul_eq_mul] using mul_le_mul_right (measure_mono inter_subset_left) (ENNReal.ofReal C)

-- @@ L104-104 verbatim
end Jacobian

-- @@ L105-105 verbatim
end

-- @@ L106-106 verbatim
end QuadricCounterexample


-- @@ L108-108 verbatim
namespace QuadricCounterexample

-- @@ L109-109 verbatim
open Set Filter Topology MeasureTheory

-- @@ L110-110 verbatim
open scoped ENNReal

-- @@ L111-111 verbatim
noncomputable section

-- @@ L112-112 verbatim
section Multiplier

-- @@ L113-117 verbatim
variable {α : Type u7} {E : Type u8} {F : Type u9} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {A : α → E →L[ℝ] F} {C : ℝ}


-- @@ L119-128 verbatim
omit [Fact (1 ≤ p)] in
lemma boundedMultiplier_memLp (hA : AEStronglyMeasurable A μ)
    (_hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (f : Lp E p μ) :
    MemLp (fun x ↦ A x (f x)) p μ := by
  apply (((Lp.memLp f).norm).const_smul C).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable f)))
  filter_upwards [hb] with x hx
  simpa only [Pi.smul_apply,smul_eq_mul] using
    (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))


-- @@ L130-156 verbatim
def boundedMultiplierLp (hA : AEStronglyMeasurable A μ)
    (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : Lp E p μ →L[ℝ] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (boundedMultiplier_memLp hA hC hb f).toLp (fun x ↦ A x (f x))
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [(boundedMultiplier_memLp hA hC hb (f+g)).coeFn_toLp,
          (boundedMultiplier_memLp hA hC hb f).coeFn_toLp,
          (boundedMultiplier_memLp hA hC hb g).coeFn_toLp,
          Lp.coeFn_add f g,
          Lp.coeFn_add ((boundedMultiplier_memLp hA hC hb f).toLp _)
            ((boundedMultiplier_memLp hA hC hb g).toLp _)] with x hfg hf hg hadd hsum
        simp only [hfg,hf,hg,hadd,map_add,hsum,Pi.add_apply]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [(boundedMultiplier_memLp hA hC hb (c • f)).coeFn_toLp,
          (boundedMultiplier_memLp hA hC hb f).coeFn_toLp,
          Lp.coeFn_smul c f, Lp.coeFn_smul c ((boundedMultiplier_memLp hA hC hb f).toLp _)]
          with x hcf hf hsmul hout
        simp only [hcf,hf,hsmul,map_smul,hout,RingHom.id_apply,Pi.smul_apply] }
    C (fun f ↦ by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(boundedMultiplier_memLp hA hC hb f).coeFn_toLp,hb] with x hx hbx
      change ‖((boundedMultiplier_memLp hA hC hb f).toLp (fun x ↦ A x (f x))) x‖ ≤ C * ‖f x‖
      rw [hx]
      exact (A x).le_opNorm (f x) |>.trans
        (mul_le_mul_of_nonneg_right hbx (norm_nonneg _)))


-- @@ L158-161 verbatim
lemma boundedMultiplierLp_coe (hA : AEStronglyMeasurable A μ)
    (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (f : Lp E p μ) :
    boundedMultiplierLp hA hC hb f =ᵐ[μ] fun x ↦ A x (f x) :=
  (boundedMultiplier_memLp hA hC hb f).coeFn_toLp

-- @@ L162-162 verbatim
end Multiplier

-- @@ L163-163 verbatim
end

-- @@ L164-164 verbatim
end QuadricCounterexample


-- @@ L166-166 verbatim
namespace QuadricCounterexample

-- @@ L167-167 verbatim
open Set Filter Topology MeasureTheory

-- @@ L168-168 verbatim
noncomputable section


-- @@ L170-189 verbatim
lemma compact_involution_map_bound {X : Type u10} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {T : X → X} {U K : Set X}
    (hT : Measurable T) (hi : Function.Involutive T) (hU : IsOpen U)
    (hd : ContDiffOn ℝ 1 T U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hTU : MapsTo T U U) :
    ∃ C : ℝ, 0 ≤ C ∧ Measure.map T (μ.restrict K) ≤ ENNReal.ofReal C • μ := by
  have hTK : IsCompact (T '' K) := hK.image_of_continuousOn (hd.continuousOn.mono hKU)
  have hTKU : T '' K ⊆ U := by rintro _ ⟨x,hx,rfl⟩; exact hTU (hKU hx)
  have hc : ContinuousOn (fun x ↦ |(fderiv ℝ T x).det|) (T '' K) :=
    (continuous_abs.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn
        (hd.continuousOn_fderiv_of_isOpen hU le_rfl))).mono hTKU
  obtain ⟨C,hC⟩ := hTK.bddAbove_image hc
  refine ⟨max C 0,le_max_right _ _,map_restrict_involution_le (T' := fderiv ℝ T) hT hi hTK.measurableSet ?_ ?_⟩
  · intro x hx
    exact ((hd.differentiableOn_one x (hTKU hx)).differentiableAt
      (hU.mem_nhds (hTKU hx))).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)


-- @@ L191-191 verbatim
end

-- @@ L192-192 verbatim
end QuadricCounterexample


-- @@ L194-194 verbatim
namespace QuadricCounterexample

-- @@ L195-195 verbatim
open Set Filter Topology MeasureTheory Metric Matrix

-- @@ L196-196 verbatim
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

-- @@ L197-197 verbatim
noncomputable section

-- @@ L198-198 verbatim
abbrev MatrixCoefficients := EuclideanSpace ℂ (Fin 2 × Fin 2)


-- @@ L200-204 verbatim
lemma matrix_eq_of_quadratic_eq {H K : TwoMatrix} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (h : ∀ v : FiberCoordinates, quadraticValue H v=quadraticValue K v) : H=K := by
  rw [← matrixFromQuadratic_value hH,← matrixFromQuadratic_value hK]
  congr 1
  exact funext h


-- @@ L206-210 verbatim
def congruenceCoefficients (A : TwoMatrix) : MatrixCoefficients →L[ℂ] MatrixCoefficients :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c ↦ matrixToCoefficients (A.conjTranspose*coefficientsToMatrix c*A)
      map_add' := fun c d ↦ by simp only [map_add,mul_add,add_mul]
      map_smul' := fun t c ↦ by simp only [map_smul,Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }


-- @@ L212-213 verbatim
lemma congruenceCoefficients_apply (A : TwoMatrix) (c : MatrixCoefficients) :
    coefficientsToMatrix (congruenceCoefficients A c)=A.conjTranspose*coefficientsToMatrix c*A := rfl


-- @@ L215-220 verbatim
lemma continuous_congruenceCoefficients : Continuous congruenceCoefficients := by
  apply continuous_clm_apply.mpr
  intro c
  change Continuous (fun A : TwoMatrix ↦ matrixToCoefficients (A.conjTranspose*coefficientsToMatrix c*A))
  have hm : Continuous (matrixToCoefficients (n := Fin 2)) := LinearMap.continuous_of_finiteDimensional _
  exact hm.comp (by fun_prop)


-- @@ L222-233 verbatim
lemma TwistedPshForm.matrix_compatible {D : EqualizerData} {m : ℕ} (P : TwistedPshForm D m)
    (i j : StandardChart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j) :
    P.matrix i z= traceScalar m i j z •
      ((D.coordinateTransition i j z).transpose.conjTranspose *
        P.matrix j (coordinateChange i j z)*(D.coordinateTransition i j z).transpose) := by
  apply matrix_eq_of_quadratic_eq (P.positive i z).isHermitian
    ((Matrix.isHermitian_conjTranspose_mul_mul _ (P.positive j (coordinateChange i j z)).isHermitian).smul (by simp [IsSelfAdjoint]))
  intro v
  rw [P.compatible i j z hz,← quadraticValue_congruence]
  change _=(quadraticValueCLM v) (_ • _)
  rw [map_smul,smul_eq_mul]
  rfl


-- @@ L235-237 verbatim
lemma coordinateChange_symm (i j : StandardChart) : coordinateChange i j=coordinateChange j i := by
  funext z
  simp only [coordinateChange,scalarCoordinateChange,eq_comm]


-- @@ L239-242 verbatim
lemma coordinateChange_involutive (i j : StandardChart) : Function.Involutive (coordinateChange i j) := by
  intro z
  rw [coordinateChange_symm i j] at *
  simpa only [← coordinateChange_symm i j] using coordinateChange_inv i j z


-- @@ L244-246 verbatim
lemma coordinateChange_measurable (i j : StandardChart) : Measurable (coordinateChange i j) := by
  unfold coordinateChange scalarCoordinateChange
  split_ifs <;> fun_prop


-- @@ L248-260 verbatim
lemma coordinateChange_contDiffOn (i j : StandardChart) :
    ContDiffOn ℝ 1 (coordinateChange i j) (coordinateOverlap i j) := by
  apply ContDiffOn.prodMk
  · by_cases h : i.1=j.1
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact contDiffOn_fst.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).1.resolve_left h)
  · by_cases h : i.2=j.2
    · simp only [scalarCoordinateChange,ite_eq_left h]
      fun_prop
    · simp only [scalarCoordinateChange,ite_eq_right h]
      exact contDiffOn_snd.inv (fun z hz ↦ ((coordinateOverlap_iff i j z).mp hz).2.resolve_left h)


-- @@ L262-276 verbatim
lemma coordinateChange_mapsTo_overlap (i j : StandardChart) :
    MapsTo (coordinateChange i j) (coordinateOverlap i j) (coordinateOverlap i j) := by
  intro z hz
  rw [coordinateOverlap_iff] at hz ⊢
  constructor
  · rcases hz.1 with h|h
    · exact Or.inl h
    · right
      simp only [coordinateChange,scalarCoordinateChange]
      split_ifs <;> simpa using h
  · rcases hz.2 with h|h
    · exact Or.inl h
    · right
      simp only [coordinateChange,scalarCoordinateChange]
      split_ifs <;> simpa using h


-- @@ L278-285 verbatim
lemma coordinateChange_compact_bound (i j : StandardChart) {K : Set BaseCoordinates}
    (hK : IsCompact K) (hKU : K ⊆ coordinateOverlap i j) :
    ∃ C : ℝ, 0≤C ∧ Measure.map (coordinateChange i j) (volume.restrict K) ≤ ENNReal.ofReal C • volume := by
  let : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
    inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
  exact compact_involution_map_bound (coordinateChange_measurable i j)
    (coordinateChange_involutive i j) (coordinateOverlap_open i j)
    (coordinateChange_contDiffOn i j) hK hKU (coordinateChange_mapsTo_overlap i j)

-- @@ L286-286 verbatim
end

-- @@ L287-287 verbatim
end QuadricCounterexample


-- @@ L289-289 verbatim
namespace QuadricCounterexample

-- @@ L290-290 verbatim
open Set Filter Topology MeasureTheory

-- @@ L291-291 verbatim
open scoped ENNReal

-- @@ L292-292 verbatim
noncomputable section


-- @@ L294-314 verbatim
lemma L2_norm_tendsto_zero_of_bounded_ae {α : Type u11} {E : Type u12} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α} [IsFiniteMeasure μ]
    (f : ℕ → Lp E 2 μ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ k, ∀ᵐ x ∂μ, ‖f k x‖≤C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k ↦ f k x) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖f k‖) atTop (𝓝 0) := by
  have hn (k : ℕ) : (∫ x, ‖f k x‖^2 ∂μ)=‖f k‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    exact (real_inner_self_eq_norm_sq (f k x)).symm
  have hh := tendsto_integral_of_dominated_convergence
    (F := fun k x ↦ ‖f k x‖^2) (f := fun _ ↦ (0:ℝ)) (fun _ : α ↦ C^2)
    (fun k ↦ ((Lp.aestronglyMeasurable (f k)).norm.pow 2))
    (integrable_const (C^2))
    (fun k ↦ (hb k).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f k x‖)] using
        pow_le_pow_left₀ (norm_nonneg _) hx 2)
    (hlim.mono fun x hx ↦ by simpa using hx.norm.pow 2)
  simp only [integral_zero,hn] at hh
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh.sqrt


-- @@ L316-316 verbatim
section Weak

-- @@ L317-319 verbatim
variable {E : Type u13} {F : Type u14} {G : Type u15} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [InnerProductSpace ℂ G] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

-- @@ L320-320 verbatim
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

-- @@ L321-321 verbatim
local instance : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F

-- @@ L322-322 verbatim
local instance : InnerProductSpace ℝ G := InnerProductSpace.rclikeToReal ℂ G

-- @@ L323-336 verbatim
lemma real_weakLimit_two_maps (A : E →L[ℝ] G) (B : F →L[ℝ] G)
    {u : ℕ → E} {v : ℕ → F} {w : E} {z : F}
    (hw : ∀ e, Tendsto (fun k ↦ inner ℂ (u k) e) atTop (𝓝 (inner ℂ w e)))
    (hz : ∀ f, Tendsto (fun k ↦ inner ℂ (v k) f) atTop (𝓝 (inner ℂ z f)))
    (herr : Tendsto (fun k ↦ ‖B (v k)-A (u k)‖) atTop (𝓝 0)) : B z=A w := by
  have he := tendsto_zero_iff_norm_tendsto_zero.mpr herr
  have hweak (g : G) := (real_weakLimit_map B (complex_weak_implies_real hz) g).sub
    (real_weakLimit_map A (complex_weak_implies_real hw) g)
  have hzero (g : G) : Tendsto (fun k ↦ inner ℝ (B (v k)-A (u k)) g) atTop (𝓝 0) := by
    simpa only [inner_zero_left] using he.inner tendsto_const_nhds
  have heq (g : G) : inner ℝ (B z-A w) g=0 := by
    apply tendsto_nhds_unique _ (hzero g)
    simpa only [inner_sub_left] using hweak g
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (heq (B z-A w)))

-- @@ L337-337 verbatim
end Weak

-- @@ L338-338 verbatim
end

-- @@ L339-339 verbatim
end QuadricCounterexample


-- @@ L341-341 verbatim
end


-- @@ L343-343 verbatim
end OAI
