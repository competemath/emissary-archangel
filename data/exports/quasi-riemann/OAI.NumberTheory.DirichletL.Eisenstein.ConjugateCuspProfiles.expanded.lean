import OAI.NumberTheory.DirichletL.Eisenstein.ArbitraryCuspPullback
import OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace CubicEisenstein


-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open MulChar AddChar

-- @@ L12-12 verbatim
open scoped BigOperators

-- @@ L13-13 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open MeasureTheory Real

-- @@ L16-16 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L17-17 verbatim
open Finset Complex

-- @@ L18-18 verbatim
open scoped Classical

-- @@ L19-19 verbatim
open scoped Classical

-- @@ L20-20 verbatim
open Filter Real Asymptotics

-- @@ L21-21 verbatim
open ActualEisensteinCubic

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L24-24 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L25-25 verbatim
open Filter

-- @@ L26-26 verbatim
open scoped Topology

-- @@ L27-27 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L28-28 verbatim
open MulChar AddChar

-- @@ L29-29 verbatim
open Filter Asymptotics

-- @@ L30-30 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L31-31 verbatim
open Filter

-- @@ L32-32 verbatim
open MulChar AddChar

-- @@ L33-33 verbatim
open MulChar AddChar

-- @@ L34-34 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L35-35 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L36-36 verbatim
open scoped Topology

-- @@ L37-37 verbatim
open Filter Asymptotics

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L42-42 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L43-43 verbatim
open Filter Asymptotics

-- @@ L44-44 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L45-45 verbatim
open scoped Topology

-- @@ L46-46 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L47-47 verbatim
open Filter

-- @@ L48-48 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L49-49 verbatim
open scoped Topology

-- @@ L50-50 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L51-51 verbatim
open scoped Topology

-- @@ L52-52 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L53-53 verbatim
open scoped Topology

-- @@ L54-54 verbatim
open MeasureTheory Real

-- @@ L55-55 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L61-61 verbatim
open scoped BigOperators Classical

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L67-67 verbatim
open scoped BigOperators Classical

-- @@ L68-68 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L69-69 verbatim
open MeasureTheory Set

-- @@ L70-70 verbatim
open scoped BigOperators

-- @@ L71-71 verbatim
open scoped BigOperators Classical

-- @@ L72-72 verbatim
open scoped BigOperators Classical

-- @@ L73-73 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L74-74 verbatim
open scoped BigOperators

-- @@ L75-75 verbatim
open scoped BigOperators

-- @@ L76-76 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L77-77 verbatim
open scoped BigOperators Classical


-- @@ L79-79 verbatim
section

-- @@ L80-80 verbatim
open Filter MeasureTheory Asymptotics

-- @@ L81-81 verbatim
open scoped BigOperators Classical Topology MatrixGroups

-- @@ L82-82 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L84-99 verbatim
theorem cuspBarProfile_conjugate_reflection (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (CubicKubota.complexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) (-g 1 1/g 1 0)) v := by
  have hdual : 0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he := cubicSourceConjugateFunction_cuspDerivative G g H hfactor hc v hv
  have hpow : (v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hpow]
  simp only [one_div] at he
  rw [he]
  ring


-- @@ L101-122 verbatim
theorem conjugateSource_principal_cusp_mellin_entire (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0≠0) :
    (∀s : ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (complexMatrix G 0 0/complexMatrix G 1 0)) s) ∧
    Differentiable ℂ
      (mellin (cuspBarProfile cubicSourceConjugateFunction (complexMatrix G 0 0/complexMatrix G 1 0))) := by
  let g := complexMatrix G
  apply cusp_mellin_entire
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile cubicSourceConjugateFunction (-g 1 1/g 1 0))
    (-star (CubicKubota.complexCharacter G)/(g 1 0)^2) (‖g 1 0‖^2)
    residualCuspDecayRate residualCuspDecayRate
  · change 0<‖complexMatrix G 1 0‖^2
    positivity
  · exact residualCuspDecayRate_pos
  · exact residualCuspDecayRate_pos
  · exact cuspBarProfile_conjugate_continuousOn _
  · exact cuspZProfile_conjugate_continuousOn _
  · exact cuspBarProfile_conjugate_isBigO _
  · exact cuspZProfile_conjugate_isBigO _
  · intro v hv
    simpa only [one_smul] using cuspBarProfile_conjugate_reflection G g 1 (by simp [g]) hc v hv


-- @@ L124-131 verbatim
theorem conjugateSource_cusp_mellin_reflection (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0) (s : ℂ) :
    mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) (2*s)=
      (-star (CubicKubota.complexCharacter G)/(g 1 0)^2)*(‖g 1 0‖^2:ℝ)^(2-2*s:ℂ)*
        mellin (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) (-g 1 1/g 1 0)) (2-2*s) := by
  apply cusp_mellin_reflection_of_identity _ _ _ _ _ (by positivity)
  intro v hv
  exact cuspBarProfile_conjugate_reflection G g H hfactor hc v hv


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
section

-- @@ L136-136 verbatim
open Filter MeasureTheory

-- @@ L137-137 verbatim
open scoped BigOperators Classical Topology

-- @@ L138-138 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L140-140 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L142-162 verbatim
lemma cubicBesselIntegralDeriv_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt (fun y : ℝ=>∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv y t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  apply continuousAt_of_dominated («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (bound:=fun t : ℝ=>(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)))
  · exact Eventually.of_forall (fun y=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
  · filter_upwards [Ioi_mem_nhds (show delta<x by dsimp [delta];linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hyp : 0<y := hdelta.trans hy
    have htp : 0<t := ht
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  · exact cubicBesselDerivativeMajorant_integrable.const_mul (4/delta)
  · exact Eventually.of_forall (fun t=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)


-- @@ L164-173 verbatim
lemma schlafliBesselK_cubic_derivative_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt schlafliBesselK_cubic_derivative x := by
  have hp4 : ContinuousAt (fun y : ℝ=>(y/2)^(-(4:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hp1 : ContinuousAt (fun y : ℝ=>(y/2)^(-(1:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hI := (cubicBesselIntegral_hasDerivAt x hx).continuousAt
  have hD := cubicBesselIntegralDeriv_continuousAt x hx
  apply Complex.continuous_ofReal.continuousAt.comp
  exact ((continuousAt_const.mul hp4).mul hI).add ((continuousAt_const.mul hp1).mul hD)


-- @@ L175-175 verbatim
namespace SubexponentialBesselCoefficients

-- @@ L176-176 verbatim
variable (coeff : SubexponentialBesselCoefficients)


-- @@ L178-188 verbatim
lemma amplitudeDeriv_continuousAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    ContinuousAt (fun y : ℝ=>coeff.amplitudeDeriv y h) v := by
  by_cases hh : h=0
  · simpa only [amplitudeDeriv,ite_eq_left hh] using (continuousAt_const (y:=(0:ℂ)) (x:=v))
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hK : ContinuousAt (fun y : ℝ=>schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_hasDerivAt _ (by positivity)).continuousAt.comp (by fun_prop)
  have hD : ContinuousAt (fun y : ℝ=>schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_derivative_continuousAt _ (by positivity)).comp (by fun_prop)
  simp only [amplitudeDeriv,ite_eq_right hh]
  exact continuousAt_const.mul (hK.add ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).mul hD))


-- @@ L190-216 verbatim
lemma termFDeriv_continuousAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContinuousAt (coeff.termFDeriv h) p := by
  by_cases hh : h=0
  · have he : coeff.termFDeriv h=fun _=>(0:(ℝ × ℂ)→L[ℝ]ℂ) := by
      funext q
      simp only [termFDeriv,ite_eq_left hh]
    rw [he]
    exact continuousAt_const
  have hA := (coeff.amplitudeDeriv_continuousAt p.1 hp h).comp continuousAt_fst
  have hphase : ContinuousAt (fun q : ℝ × ℂ=>ShortDraftTrace.breveE (cuspFrequency h*q.2)) p := by
    change ContinuousAt (fun q : ℝ × ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2)))) p
    fun_prop
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.continuousAt.comp (hA.mul hphase)
  have hterm := (coeff.term_continuousOn h).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have hsecond := hterm.smul (continuousAt_const
    (y:=(horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  have he : coeff.termFDeriv h=(fun q : ℝ × ℂ=>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (coeff.amplitudeDeriv q.1 h*ShortDraftTrace.breveE (cuspFrequency h*q.2))+
      coeff.term h q • (horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) := by
    funext q
    simp only [termFDeriv,ite_eq_right hh]
  rw [he]
  exact hfirst.add hsecond


-- @@ L218-226 verbatim
lemma seriesFDeriv_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun p : ℝ × ℂ=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p)
      {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*((1+‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h p hp
    exact (coeff.termFDeriv_continuousAt h p (ha.trans_le hp.1)).continuousWithinAt
  · exact (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound


-- @@ L228-235 verbatim
lemma series_contDiffAt_one (p : ℝ × ℂ) (hp : 0<p.1) : ContDiffAt ℝ 1 coeff.series p := by
  apply contDiffAt_one_iff.mpr
  refine ⟨(fun q=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h q),
    {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)},?_,?_,?_⟩
  · exact continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  · exact coeff.seriesFDeriv_continuousOn_slab _ _ (by linarith) (by linarith)
  · intro q hq
    exact coeff.series_hasFDerivAt q (by change p.1/2≤q.1 ∧ q.1≤2*p.1 at hq;linarith [hq.1])


-- @@ L237-237 verbatim
end SubexponentialBesselCoefficients

-- @@ L238-238 verbatim
end


-- @@ L240-240 verbatim
section

-- @@ L241-241 verbatim
open Filter MeasureTheory

-- @@ L242-242 verbatim
open scoped BigOperators Classical Topology MatrixGroups

-- @@ L243-243 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L245-245 verbatim
def cuspSpatialInput (q : ℝ × ℂ) : SpatialCoordinates := ![q.2.re,q.2.im,q.1]

-- @@ L246-246 verbatim
def cuspSpatialOutput (p : SpatialCoordinates) : ℝ × ℂ := (p 2,spatialHorizontal p)


-- @@ L248-257 verbatim
lemma cuspSpatialInput_contDiff : ContDiff ℝ 1 cuspSpatialInput := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.re)
    exact Complex.reCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.im)
    exact Complex.imCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.1)
    fun_prop


-- @@ L259-260 verbatim
lemma cuspSpatialOutput_contDiff : ContDiff ℝ 1 cuspSpatialOutput :=
  (contDiff_apply ℝ ℝ 2).prodMk (spatialHorizontal_contDiff.of_le (by simp))


-- @@ L262-263 verbatim
lemma cuspSpatialInput_horizontal (q : ℝ × ℂ) : spatialHorizontal (cuspSpatialInput q)=q.2 :=
  Complex.re_add_im q.2


-- @@ L265-280 verbatim
lemma cuspSpatialAction_lift (g : SL(2,ℂ)) (q : ℝ × ℂ) (hq : 0<q.1) :
    cuspCoordinateLift (cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput q)))=
      g•cuspCoordinateLift q := by
  have hin : hyperbolicSpatialCoordinates (cuspCoordinateLift q)=cuspSpatialInput q := by
    rw [show q=(q.1,q.2) from rfl,cuspCoordinateLift_positive q.1 q.2 hq]
    simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,cuspSpatialInput]
  have he := mobiusSpatial_coordinates_global g (cuspCoordinateLift q)
  rw [hin] at he
  have hr := hyperbolicSpatialCoordinates_reconstruct (g•cuspCoordinateLift q)
  have hp : 0<mobiusSpatial g (cuspSpatialInput q) 2 := mobiusSpatial_positive g _ hq
  rw [cuspSpatialOutput,cuspCoordinateLift_positive _ _ hp]
  refine Eq.trans ?_ hr
  apply upperPoint_congr
  · rw [he]
    rfl
  · rw [he]


-- @@ L282-282 verbatim
namespace SubexponentialBesselCoefficients

-- @@ L283-283 verbatim
variable (coeff : SubexponentialBesselCoefficients)


-- @@ L285-300 verbatim
lemma fullFunction_cusp_contDiffAt_one (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>q.1^(2/3:ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>(q.1:ℂ)^(2/3:ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (coeff.series_contDiffAt_one p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq


-- @@ L302-314 verbatim
lemma fullFunction_translate_cusp_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (g•cuspCoordinateLift q)) p := by
  have hmid : ContDiffAt ℝ 1 (fun q=>mobiusSpatial g (cuspSpatialInput q)) p :=
    ((mobiusSpatial_contDiffAt g (cuspSpatialInput p) hp).of_le (by simp)).comp p
      cuspSpatialInput_contDiff.contDiffAt
  have hact := cuspSpatialOutput_contDiff.contDiffAt.comp p hmid
  have hpos : 0<(cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput p))).1 :=
    mobiusSpatial_positive g _ hp
  have hfull := (coeff.fullFunction_cusp_contDiffAt_one constant _ hpos).comp p hact
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact congrArg (coeff.fullFunction constant) (cuspSpatialAction_lift g q hq).symm


-- @@ L316-320 verbatim
lemma fullFunction_translate_split_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>coeff.fullFunction constant (g•cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>(q.2,q.1)) p := by fun_prop
  exact (coeff.fullFunction_translate_cusp_contDiffAt_one constant g (p.2,p.1) hp).comp p hswap


-- @@ L322-322 verbatim
end SubexponentialBesselCoefficients


-- @@ L324-328 verbatim
lemma cubicSourceResidualFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceResidualFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_contDiffAt_one _ g p hp


-- @@ L330-334 verbatim
lemma cubicSourceConjugateFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceConjugateFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  exact Complex.conjCLE.contDiff.contDiffAt.comp p
    (cubicSourceResidualFunction_translate_split_contDiffAt_one g p hp)


-- @@ L336-350 verbatim
lemma horizontalWirtingerBar_eq_fderiv (F : ℂ × ℝ→ℂ) (A : (ℂ × ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerBar (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)+Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar,h1,hI]


-- @@ L352-370 verbatim
lemma cuspBarProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspBarProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)+Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.add (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerBar_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt


-- @@ L372-390 verbatim
lemma cuspZProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspZProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)-Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.sub (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerZ_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt


-- @@ L392-395 verbatim
lemma cuspBarProfile_source_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w=>cubicSourceResidualFunction (H•w)) z) (Set.Ioi 0) :=
  cuspBarProfile_continuousOn_of_contDiff _
    (cubicSourceResidualFunction_translate_split_contDiffAt_one H) z


-- @@ L397-400 verbatim
lemma cuspZProfile_source_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceResidualFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceResidualFunction_translate_split_contDiffAt_one H) z


-- @@ L402-405 verbatim
lemma cuspBarProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspBarProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspBarProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z


-- @@ L407-410 verbatim
lemma cuspZProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z


-- @@ L412-412 verbatim
end


-- @@ L414-414 verbatim
section

-- @@ L415-415 verbatim
open Filter MeasureTheory

-- @@ L416-416 verbatim
open scoped BigOperators Classical


-- @@ L418-418 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicRamified

-- @@ L419-419 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L421-426 verbatim
lemma ninth_trace_character_period (c x : Eis) :
    ShortDraftTrace.breveE ((eisEmbedding c/(9*eisLam))*(9*eisEmbedding x))=1 := by
  have he : (eisEmbedding c/(9*eisLam))*(9*eisEmbedding x)=eisEmbedding (c*x)/eisLam := by
    rw [map_mul]
    ring
  rw [he,breveE_embedding_div_traceLambda]


-- @@ L428-438 verbatim
lemma ramifiedSource_scaled_periodic10 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction omega (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction omega (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift10,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift10*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift10,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (omega-1) x
  rw [hp,one_mul]


-- @@ L440-450 verbatim
lemma ramifiedSource_scaled_periodic19 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction (omega^2) (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift19,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift19*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift19,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (-2-omega) x
  rw [hp,one_mul]


-- @@ L452-460 verbatim
lemma periodic_integral_zero_of_eigen_translation (f : ℂ→ℂ)
    (hf : ∀x:Eis,∀z,f (z+3*eisEmbedding x)=f z) (b c : ℂ)
    (hc : c≠1) (he : ∀z,f (b+z)=c*f z) :
    (∫z in periodDomain,f z)=0 := by
  have hi := period_integral_translation f hf b
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hzero : (c-1)*(∫z in periodDomain,f z)=0 := by linear_combination hi
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)


-- @@ L462-472 verbatim
theorem ramifiedSource_zero_mode10 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction omega (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic10 v hv) 1 (eisEmbedding omega)
  · exact fun h => omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa using h))
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift10,ramifiedShift10_period]
    norm_num [cubicExp]


-- @@ L474-490 verbatim
theorem ramifiedSource_zero_mode19 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic19 v hv) 1 (eisEmbedding (omega^2))
  · intro h
    have he : omega^2=(1:Eis) := eisEmbedding_injective (by simpa using h)
    have hpoly := ramified_omega_relation
    rw [he] at hpoly
    have hw : omega=(-2:Eis) := by linear_combination hpoly
    rw [hw] at he
    norm_num at he
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift19,ramifiedShift19_period]
    norm_num [cubicExp]


-- @@ L492-492 verbatim
end


-- @@ L494-494 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L496-496 verbatim
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal

-- @@ L497-497 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L499-499 verbatim
abbrev UnitLowerData := Σa:PrimaryLower,{d:PrimaryLower//IsCoprime a.val d.val}


-- @@ L501-511 verbatim
def unitLowerToPrimitive (u : Eisˣ) (p : UnitLowerData) : PrimitiveRow := by
  refine ⟨![(u:Eis)*(p.1.val-p.2.val.val),p.2.val.val],?_,?_,p.2.val.2⟩
  · change IsCoprime ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd p.2.val.val (p.1.val-p.2.val.val) p.1.val
      ⟨-1,by ring⟩).mpr
    exact p.2.2.symm
  · have hd : (3:Eis)∣p.1.val-p.2.val.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub p.1.2 p.2.val.2
    exact hd.mul_left (u:Eis)


-- @@ L513-545 verbatim
lemma unitLowerToPrimitive_bijective (u : Eisˣ) :
    Function.Bijective (unitLowerToPrimitive u) := by
  constructor
  · rintro ⟨a,d,hd⟩ ⟨b,e,he⟩ h
    have hrow := congrArg Subtype.val h
    have hde : d=e := Subtype.ext (congrFun hrow 1)
    subst e
    have hab : a=b := by
      apply Subtype.ext
      have hh := congrFun hrow 0
      change (u:Eis)*(a.val-d.val)=(u:Eis)*(b.val-d.val) at hh
      have hcancel := u.isUnit.mul_left_cancel hh
      linear_combination hcancel
    subst b
    rfl
  · intro r
    let d : PrimaryLower := ⟨r.val 1,r.2.2.2⟩
    let a : PrimaryLower := ⟨(↑u⁻¹:Eis)*r.val 0+r.val 1,by
      have hc := r.2.2.1.mul_left (↑u⁻¹:Eis)
      have hh := dvd_add hc r.2.2.2
      convert hh using 1 ;ring⟩
    have hcop : IsCoprime a.val d.val := by
      apply IsCoprime.symm
      apply (isCoprime_right_congr_of_dvd d.val a.val ((↑u⁻¹:Eis)*r.val 0)
        ⟨1,by dsimp [a,d];ring⟩).mpr
      exact (isCoprime_mul_unit_left_right u⁻¹.isUnit _ _).mpr r.2.1.symm
    refine ⟨⟨a,d,hcop⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change (u:Eis)*((↑u⁻¹:Eis)*r.val 0+r.val 1-r.val 1)=r.val 0
      rw [add_sub_cancel_right,←mul_assoc]
      simp
    · rfl


-- @@ L547-548 verbatim
def unitLowerEquiv (u : Eisˣ) : UnitLowerData≃PrimitiveRow :=
  Equiv.ofBijective _ (unitLowerToPrimitive_bijective u)


-- @@ L550-557 verbatim
lemma rowOperator_lowerCusp (t : Eis) (v : Fin 2→ℂ) :
    rowOperator (integralComplexMatrix (lowerCuspMatrix t)) v=
      ![v 0+eisEmbedding t*v 1,v 1] := by
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,integralComplexMatrix_apply]
  fin_cases i <;>
    simp [lowerCuspMatrix,mul_comm]


-- @@ L559-571 verbatim
lemma unitLower_row_phase (u : Eisˣ) (p : UnitLowerData) :
    (cosetCharacter (primitiveRowEquiv.symm (unitLowerEquiv u p)))⁻¹=
      eisEmbedding (symbol (u:Eis) p.2.val.val)*
        eisEmbedding (symbol p.2.val.val p.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val)=_
  have hh : symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val=
      symbol ((u:Eis)*p.1.val) p.2.val.val := by
    exact symbol_congr ⟨-(u:Eis),by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.val),
    symbol_reciprocity p.1.val p.2.val.val (primaryLower_ne_zero p.1)
      (primaryLower_ne_zero p.2.val) (primaryLower_primary p.1)
        (primaryLower_primary p.2.val),map_mul]


-- @@ L573-576 verbatim
def unitLowerTerm (u : Eisˣ) (z : ℂ) (v : ℝ) (s : ℂ) (a d : Eis) : ℂ :=
  (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s


-- @@ L578-601 verbatim
lemma unitLower_summand (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (p : UnitLowerData) :
    summand (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerEquiv u p))=
      unitLowerTerm u z v s p.1.val p.2.val.val := by
  let r : Fin 2→ℂ := ![eisEmbedding ((u:Eis)*p.1.val),eisEmbedding p.2.val.val]
  have hr : rowOperator (integralComplexMatrix (lowerCuspMatrix (u:Eis)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerEquiv u p)))=r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [unitLowerEquiv, Equiv.ofBijective_apply, unitLowerToPrimitive, r, map_mul, map_sub, mul_sub]
  have hr0 : r≠0 := by
    intro hh
    have he := congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.val) he
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,unitLower_row_phase]
  change _=(eisEmbedding (symbol (u:Eis) p.2.val.val)*eisEmbedding (symbol p.2.val.val p.1.val))*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi : ((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹ := by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]


-- @@ L603-607 verbatim
theorem unitLowerEisenstein_eq_rows (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v) (s : ℂ) :
    eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s=
      ∑'p:UnitLowerData,unitLowerTerm u z v s p.1.val p.2.val.val := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq,←(unitLowerEquiv u).tsum_eq]
  exact tsum_congr (unitLower_summand u z v hv s)


-- @@ L609-609 verbatim
end CubicEisenstein


-- @@ L611-611 verbatim
end


-- @@ L613-613 verbatim
end OAI
