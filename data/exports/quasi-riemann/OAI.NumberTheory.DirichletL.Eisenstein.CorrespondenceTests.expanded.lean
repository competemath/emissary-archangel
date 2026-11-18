import OAI.NumberTheory.DirichletL.Eisenstein.InverseCorrespondence


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace CubicEisenstein


-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open MulChar AddChar

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
open MeasureTheory Real

-- @@ L15-15 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L16-16 verbatim
open Finset Complex

-- @@ L17-17 verbatim
open scoped Classical

-- @@ L18-18 verbatim
open scoped Classical

-- @@ L19-19 verbatim
open Filter Real Asymptotics

-- @@ L20-20 verbatim
open ActualEisensteinCubic

-- @@ L21-21 verbatim
open Filter

-- @@ L22-22 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L23-23 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L24-24 verbatim
open Filter

-- @@ L25-25 verbatim
open scoped Topology

-- @@ L26-26 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L27-27 verbatim
open MulChar AddChar

-- @@ L28-28 verbatim
open Filter Asymptotics

-- @@ L29-29 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L30-30 verbatim
open Filter

-- @@ L31-31 verbatim
open MulChar AddChar

-- @@ L32-32 verbatim
open MulChar AddChar

-- @@ L33-33 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L34-34 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L35-35 verbatim
open scoped Topology

-- @@ L36-36 verbatim
open Filter Asymptotics

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L42-42 verbatim
open Filter Asymptotics

-- @@ L43-43 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L44-44 verbatim
open scoped Topology

-- @@ L45-45 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L46-46 verbatim
open Filter

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L52-52 verbatim
open scoped Topology

-- @@ L53-53 verbatim
open MeasureTheory Real

-- @@ L54-54 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical

-- @@ L58-58 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open scoped BigOperators Classical

-- @@ L67-67 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L68-68 verbatim
open MeasureTheory Set

-- @@ L69-69 verbatim
open scoped BigOperators

-- @@ L70-70 verbatim
open scoped BigOperators Classical

-- @@ L71-71 verbatim
open scoped BigOperators Classical

-- @@ L72-72 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L73-73 verbatim
open scoped BigOperators

-- @@ L74-74 verbatim
open scoped BigOperators

-- @@ L75-75 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L76-76 verbatim
open scoped BigOperators Classical


-- @@ L78-78 verbatim
section


-- @@ L80-80 verbatim
open scoped Classical MatrixGroups BigOperators

-- @@ L81-81 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L82-82 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L84-91 verbatim
lemma cubeAverageMatrix_translate_lattice (p:Eis) (hp:p≠0) (q n:Eis) :
    cubeAverageMatrix p hp q*complexTranslation (3*eisEmbedding n)=cubeAverageMatrix p hp (q+n) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries, cubeAverageMatrix_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, map_add]
  ring


-- @@ L93-118 verbatim
lemma cubeAverage_period_three (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (n:Eis) (w:HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation (3*eisEmbedding n) • w)=cubeAverage p hp F w := by
  let a:(Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}):=
    { toFun:=fun r=>r+Ideal.Quotient.mk _ n
      invFun:=fun r=>r-Ideal.Quotient.mk _ n
      left_inv:=fun r=>add_sub_cancel_right r _
      right_inv:=fun r=>sub_add_cancel r _ }
  let f (r:Eis⧸Ideal.span {p^3}):=
    F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
        (complexTranslation (3*eisEmbedding n) • w))=f (a r) := by
    rw [←mul_smul,cubeAverageMatrix_translate_lattice]
    apply cubeAverage_summand_congr p hp F hF
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_add,GaussianShiftedPartition.representative_spec,
      GaussianShiftedPartition.representative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r,f (a r):=tsum_congr hpoint
    _ = ∑' r,f r:=a.tsum_eq f


-- @@ L120-120 verbatim
end


-- @@ L122-122 verbatim
section


-- @@ L124-124 verbatim
open MeasureTheory

-- @@ L125-125 verbatim
open scoped Classical MatrixGroups BigOperators


-- @@ L127-127 verbatim
section

-- @@ L128-128 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree

-- @@ L129-129 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L131-137 verbatim
lemma cubicSource_period_three (n:Eis) (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation (3*eisEmbedding n) • w)=
      cubicSourceResidualFunction w := by
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  simp only [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_period v hv z n


-- @@ L139-143 verbatim
lemma cubicSource_period_one (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation 1 • w)=cubicSourceResidualFunction w := by
  have h:=cubicSourceResidualFunction_rational_invariant ModularGroup.T w
  change cubicSourceResidualFunction (rationalComplex ModularGroup.T • w)=_ at h
  rwa [rationalComplex_T_eq] at h


-- @@ L145-153 verbatim
lemma cubicSource_period_finTwo (t:Fin 2) (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation (t.val:ℂ) • w)=cubicSourceResidualFunction w := by
  fin_cases t
  · have hz:complexTranslation 0=1:=by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [complexTranslation]
    simp only [Nat.cast_zero,hz,one_smul]
  · simpa using cubicSource_period_one w


-- @@ L155-166 verbatim
lemma cubicSource_cube_period_finTwo (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1)
    (t:Fin 2) (w:HyperbolicSpace) :
    cubeAverage p hp cubicSourceResidualFunction (complexTranslation (t.val:ℂ) • w)=
      cubeAverage p hp cubicSourceResidualFunction w := by
  fin_cases t
  · have hz:complexTranslation 0=1:=by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [complexTranslation]
    simp only [Nat.cast_zero,hz,one_smul]
  · simpa using cubeAverage_period_one p hp hprimary cubicSourceResidualFunction
      cubicSource_period_three cubicSource_period_one w


-- @@ L168-185 verbatim
theorem cubeSource_summand_average {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (cubeAverageMatrix p hp q •
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨d.matrix*M⁻¹,d.congruent⟩*sourceCuspConstant M*
        (v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  have hpoint (z:ℂ):cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)=
        integralComplexMatrix d.matrix •
          (cubeCuspTriangular d hp • upperPoint (3*(eisEmbedding (p^3)*z)) v hv):=by
    rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul]
  simp_rw [hpoint]
  rw [sourceCusp_average_complex_upper d.matrix (cubeCuspTriangular d hp)
    (cubeCuspTriangular_entries d hp).2.1 (p^3) (p^(2*d.exponent.val))
    (pow_ne_zero _ hp) (cubeCuspTriangular_integral_scale d hp) v hv,
    cubeCuspTriangular_height d hp v hv,sourceCuspConstant_congruent M d.matrix d.congruent]
  ring


-- @@ L187-202 verbatim
theorem cubeSource_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hM:sourceCuspConstant M=0) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=0 := by
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous M (p^3) v hv]
  have hz (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=0:=by
    rw [cubeSource_summand_average
      (actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary)
      hp.ne_zero v hv,hM]
    ring
  simp_rw [hz]
  simp


-- @@ L204-241 verbatim
theorem cubeSource_primary_upper_average (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous ((A:SL(2,Eis))*T) (p^3) v hv]
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average ((d r).right_upper T hT) hp.ne_zero v hv,
      CubeCuspData.right_upper_character,CubeCuspData.right_upper_exponent]
  simp_rw [hpoint]
  have hsum:(∑' r:Eis⧸Ideal.span {p^3},
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent)=
      (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
        actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p):=by
    unfold actualCubeCuspPhaseSum
    rw [←tsum_mul_left]
    apply tsum_congr
    intro r
    change _=(sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
      (cubeCuspHeightWeight p (d r).exponent*complexCharacter
        ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩)
    ring
  rw [hsum]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p))*
        (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)):=by ring
    _=_:=by rw [actualCubeCuspPhaseSum_normalized A p hp hprimary hA];ring


-- @@ L243-243 verbatim
end


-- @@ L245-245 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree

-- @@ L246-246 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L248-269 verbatim
theorem cubeSource_levelTwo_upper_average (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨B,hB,t,ht⟩:=exists_primary_cusp_shift A
  have hm (w:HyperbolicSpace):integralComplexMatrix ((B:SL(2,Eis))*T) • w=
      complexTranslation (t.val:ℂ) • (integralComplexMatrix ((A:SL(2,Eis))*T) • w):=by
    simp only [map_mul,mul_smul]
    exact ht (integralComplexMatrix T • w)
  have hc:sourceCuspConstant ((B:SL(2,Eis))*T)=sourceCuspConstant ((A:SL(2,Eis))*T):=by
    unfold sourceCuspConstant
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hm,cubicSource_period_finTwo]
  calc
    _=∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
        (integralComplexMatrix ((B:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv):=by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hm,cubicSource_cube_period_finTwo p hp.ne_zero hprimary]
    _=_:=by rw [cubeSource_primary_upper_average B T hT p hp hprimary hB v hv,hc]


-- @@ L271-286 verbatim
theorem cubeSource_average_all_cusps (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  by_cases hz:sourceCuspConstant M=0
  · rw [cubeSource_average_zero M p hp hprimary hz v hv,hz]
    ring
  · obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
    have hj:j=0:=by
      by_contra h
      exact hz ((sourceCuspConstant_zero_iff M G j T hT hM).mpr h)
    have he:M=(G:SL(2,Eis))*T:=by
      simpa [hj,cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using hM
    rw [he]
    exact cubeSource_levelTwo_upper_average G T hT p hp hprimary v hv


-- @@ L288-314 verbatim
theorem cubeSource_difference_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,
      (cubeAverage p hp.ne_zero cubicSourceResidualFunction
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=0 := by
  let c:ℂ→UpperCoordinates:=fun z=>⟨(3*(eisEmbedding (p^3)*z),v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.mul continuous_id)).prodMk continuous_const
  have hcoord:= (continuous_translatedUpperCoordinates (integralComplexMatrix M)).comp hc
  have h0:Continuous (fun z=>cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)):=by
    simpa only [Function.comp_def,c] using cubicSourceResidualFunction_continuous.comp hcoord
  have h1:Continuous (fun z=>cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)):=by
    simpa only [Function.comp_def,c] using
      (cubeAverage_continuous p hp.ne_zero cubicSourceResidualFunction cubicSourceResidualFunction_continuous).comp hcoord
  have h2:Continuous (fun z:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)):=
    continuous_const.mul h0
  rw [integral_sub (periodDomain_integrable_of_continuous _ h1)
    (periodDomain_integrable_of_continuous _ h2),integral_const_mul,
    cubeSource_average_all_cusps M p hp hprimary v hv,
    sourceCusp_average_enlarged M (p^3) (pow_ne_zero 3 hp.ne_zero) v hv]
  ring


-- @@ L316-316 verbatim
end


-- @@ L318-318 verbatim
section

-- @@ L319-319 verbatim
open Filter MeasureTheory

-- @@ L320-320 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise

-- @@ L321-321 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L323-323 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L325-332 verbatim
lemma integralCoverFiberPoint_continuous (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) : Continuous (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (continuous_integralOrbitProjection H).comp
    (continuous_hyperbolic_action (integralComplexMatrix ((integralCoverRep H K q)⁻¹:SL(2,ActualEisensteinCubic.O))))


-- @@ L334-352 verbatim
lemma integralCoverMap_fiber {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (w : HyperbolicSpace) :
    (integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w}=
      Set.range (fun q : IntegralCoverCosets H K=>integralCoverFiberPoint H K q w) := by
  ext u
  constructor
  · intro hu
    induction u using Quotient.inductionOn with
    | _ z =>
      have he : integralOrbitProjection K z=integralOrbitProjection K w := hu
      obtain ⟨k,hk⟩ := Quotient.exact he
      refine ⟨(k : IntegralCoverCosets H K),?_⟩
      change integralCoverFiberPoint H K (k : IntegralCoverCosets H K) w=integralOrbitProjection H z
      rw [integralCoverFiberPoint_mk]
      congr 1
      rw [←hk]
      exact inv_smul_smul k z
  · rintro ⟨q,rfl⟩
    exact integralCoverMap_fiberPoint hHK q w


-- @@ L354-367 verbatim
lemma integralCoverMap_preimage_image {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (S : Set (IntegralOrbitQuotient H)) :
    (integralOrbitProjection K) ⁻¹' (integralCoverMap hHK '' S)=
      ⋃q : IntegralCoverCosets H K,(integralCoverFiberPoint H K q) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨u,hu,huw⟩
    have hh : u∈(integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w} := huw
    rw [integralCoverMap_fiber hHK w] at hh
    obtain ⟨q,rfl⟩ := hh
    exact Set.mem_iUnion.mpr ⟨q,hu⟩
  · intro hw
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hw
    exact ⟨integralCoverFiberPoint H K q w,hq,integralCoverMap_fiberPoint hHK q w⟩


-- @@ L369-376 verbatim
theorem integralCoverMap_isClosedMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsClosedMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  intro S hS
  have hq : Topology.IsQuotientMap (integralOrbitProjection K) := isQuotientMap_quotient_mk'
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [integralCoverMap_preimage_image]
  exact isClosed_iUnion_of_finite (fun q=>hS.preimage (integralCoverFiberPoint_continuous H K q))


-- @@ L378-388 verbatim
theorem integralCoverMap_isProperMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsProperMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨integralCoverMap_continuous hHK,integralCoverMap_isClosedMap hHK,?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change IsCompact ((integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w})
    rw [integralCoverMap_fiber hHK w]
    exact (Set.finite_range _).isCompact


-- @@ L390-394 verbatim
theorem integralCoverMap_compact_preimage {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K]
    (S : Set (IntegralOrbitQuotient K)) (hS : IsCompact S) :
    IsCompact ((integralCoverMap hHK) ⁻¹' S) :=
  (integralCoverMap_isProperMap hHK).isCompact_preimage hS


-- @@ L396-396 verbatim
end


-- @@ L398-398 verbatim
section


-- @@ L400-400 verbatim
open MeasureTheory

-- @@ L401-401 verbatim
open scoped Classical MatrixGroups BigOperators


-- @@ L403-403 verbatim
section

-- @@ L404-404 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree

-- @@ L405-405 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L407-410 verbatim
lemma cubeCuspTriangular_norm_sq_pos {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) : 0<‖cubeCuspTriangular d hp 1 1‖^2 := by
  rw [cubeCuspTriangular_norm_sq]
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) _


-- @@ L412-416 verbatim
def cubeReducedRemainder {M:SL(2,Eis)} {p q:Eis} (d:CubeCuspData M p q) (hp:p≠0)
    (z:ℂ) (v:ℝ) (hv:0<v) : ℂ :=
  sourceCuspRemainder d.matrix
    ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/‖cubeCuspTriangular d hp 1 1‖^2) (div_pos hv (cubeCuspTriangular_norm_sq_pos d hp))


-- @@ L418-427 verbatim
lemma cubeSource_remainder_summand {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder d hp z v hv+
        sourceCuspLeadingCoefficient d.matrix*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
    complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  unfold cubeReducedRemainder sourceCuspRemainder
  rw [cubeCuspTriangular_height d hp v hv]
  ring


-- @@ L429-459 verbatim
lemma cubeSource_leading_sum (M:SL(2,Eis)) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        sourceCuspLeadingCoefficient d.matrix*cubeCuspHeightWeight p d.exponent)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have h:=cubeSource_average_all_cusps M p hp hprimary 1 (by norm_num)
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous M (p^3) 1 (by norm_num)] at h
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) 1 (by norm_num))))=
      sourceCuspConstant (d r).matrix*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average (d r) hp.ne_zero 1 (by norm_num),
      ←sourceCuspConstant_congruent M (d r).matrix (d r).congruent]
    simp only [Complex.ofReal_one,Complex.one_cpow,mul_one]
  rw [tsum_congr hpoint] at h
  simp only [Complex.ofReal_one,Complex.one_cpow,mul_one] at h
  change (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3}, sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)=_
  unfold sourceCuspLeadingCoefficient
  simp_rw [div_mul_eq_mul_div]
  rw [tsum_div_const]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},sourceCuspConstant (d r).matrix*cubeCuspHeightWeight p (d r).exponent)) /
        ((9*Real.sqrt 3/2:ℝ):ℂ):=by ring
    _=_:=by rw [h];ring


-- @@ L461-497 verbatim
theorem cubeSource_difference_eq_remainders (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        cubeReducedRemainder d hp.ne_zero z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      cubicSourceResidualFunction (cubeAverageMatrix p hp.ne_zero
        (GaussianShiftedPartition.representative (p^3) r) • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder (d r) hp.ne_zero z v hv+(v:ℂ)^(2/3:ℂ)*
        (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent):=by
    rw [cubeSource_remainder_summand (d r) hp.ne_zero z v hv]
    ring
  have hu:cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
        (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M*(v:ℂ)^(2/3:ℂ):=by
    unfold cubeAverage
    have hs1:Summable (fun r:Eis⧸Ideal.span {p^3}=>cubeReducedRemainder (d r) hp.ne_zero z v hv):=Summable.of_finite
    have hs2:Summable (fun r:Eis⧸Ideal.span {p^3}=>(v:ℂ)^(2/3:ℂ)*
      (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=Summable.of_finite
    rw [tsum_congr hpoint,hs1.tsum_add hs2,tsum_mul_left]
    calc
      _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
        (v:ℂ)^(2/3:ℂ)*((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=by ring
      _=_:=by rw [cubeSource_leading_sum M p hp hprimary];ring
  rw [hu]
  unfold sourceCuspRemainder
  ring


-- @@ L499-499 verbatim
end


-- @@ L501-501 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree

-- @@ L502-502 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L504-510 verbatim
lemma cubePrime_norm_ge_one (p:Eis) (hp:p≠0) : 1≤‖eisEmbedding p‖ := by
  have hn:1≤‖eisEmbedding p‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    have hq:Ideal.absNorm (Ideal.span {p})≠0:=
      (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  nlinarith [norm_nonneg (eisEmbedding p)]


-- @@ L512-548 verbatim
lemma cubeReducedRemainder_bound {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp
  have hd:D≤‖eisEmbedding p‖^3:=by
    rw [show D=‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)) from cubeCuspTriangular_norm_sq d hp]
    rw [←Real.rpow_natCast ‖eisEmbedding p‖ 3]
    apply Real.rpow_le_rpow_of_exponent_le hr1
    norm_num only [Nat.cast_ofNat]
    have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
    linarith
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_nonneg hr.le 3))
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hb:=sourceCuspRemainder_bound_all K (‖eisEmbedding p‖^3)⁻¹ hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) ha
  change ‖cubeReducedRemainder d hp z v hv‖≤K/(v/D)^3 at hb
  refine hb.trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hd 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)


-- @@ L550-569 verbatim
lemma cube_normalized_sum_bound (p:Eis) (hp:p≠0)
    (f:(Eis⧸Ideal.span {p^3})→ℂ) (B:ℝ) (_hB:0≤B) (hf:∀r,‖f r‖≤B) :
    ‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r,f r)‖≤B := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℝ)≠0:=by exact_mod_cast hqN
  have hs:‖∑' r,f r‖≤(Ideal.absNorm (Ideal.span {p}):ℝ)^3*B:=by
    calc
      _≤∑' r,‖f r‖:=norm_tsum_le_tsum_norm (Summable.of_finite)
      _≤∑' (_:Eis⧸Ideal.span {p^3}),B:=(Summable.of_finite).tsum_le_tsum hf Summable.of_finite
      _=_:=by
        rw [tsum_const,nsmul_eq_mul]
        change (Ideal.absNorm (Ideal.span {p^3}):ℝ)*B=_
        rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rw [norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
  calc
    _≤(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹^3*((Ideal.absNorm (Ideal.span {p}):ℝ)^3*B):=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3)
    _=B:=by field_simp


-- @@ L571-600 verbatim
theorem cubeSource_difference_decay_from_representatives (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)‖≤
    (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v:=by
    calc
      _≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
      _≤v:=hv1
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv ha
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound (d r) hp.ne_zero K hK hrep z v hv hv1)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring


-- @@ L602-602 verbatim
end


-- @@ L604-604 verbatim
open Filter MeasureTheory

-- @@ L605-605 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal

-- @@ L606-606 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L608-608 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L610-617 verbatim
lemma integralCoverMap_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient K→ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun q=>f (integralCoverMap hHK q)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (integralCoverMap_compact_preimage hHK (tsupport f) hf.isCompact)
  intro q hq
  exact subset_tsupport f hq


-- @@ L619-631 verbatim
lemma integralCoverTraceFunction_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply HasCompactSupport.of_support_subset_isCompact
    (hf.isCompact.image (integralCoverMap_continuous hHK))
  intro q hq
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))≠0 at hq
    obtain ⟨r,_,hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact ⟨integralCoverFiberPoint H K r w,subset_tsupport f hr,
      integralCoverMap_fiberPoint hHK r w⟩


-- @@ L633-636 verbatim
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)


-- @@ L638-640 verbatim
def kernelCorrespondenceFunction (f : KernelQuotient→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction H globalKubotaKernel
    (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)))


-- @@ L642-657 verbatim
omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_lift (f : KernelQuotient→ℂ) (w : HyperbolicSpace) :
    kernelCorrespondenceFunction hJK e g he f (integralOrbitProjection globalKubotaKernel w)=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        f (integralOrbitProjection globalKubotaKernel
          ((g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:
              globalKubotaKernel):SL(2,ActualEisensteinCubic.O)))•w)) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change (∑q : IntegralCoverCosets H globalKubotaKernel,
    f (integralCoverMap hJK (integralConjugateMap e g he
      (integralCoverFiberPoint H globalKubotaKernel q w))))=_
  apply Finset.sum_congr rfl
  intro q _
  rw [integralCoverFiberPoint_rep,integralSubgroup_smul,
    integralConjugateMap_projection,integralCoverMap_projection,mul_smul]


-- @@ L659-664 verbatim
include hHK in
lemma kernelCorrespondenceFunction_hasCompactSupport (f : KernelQuotient→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (kernelCorrespondenceFunction hJK e g he f) := by
  apply integralCoverTraceFunction_hasCompactSupport hHK
  exact (integralCoverMap_hasCompactSupport hJK f hf).comp_homeomorph
    (integralConjugateHomeomorph e g he)


-- @@ L666-677 verbatim
omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_contMDiff (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelCorrespondenceFunction hJK e g he f) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  apply kernel_contMDiff_of_lift
  simp_rw [kernelCorrespondenceFunction_lift]
  apply ContMDiff.sum
  intro q _
  exact (hf.comp kernelProjection_contMDiff).comp
    (hyperbolicAction_contMDiff (g*integralComplexMatrix
      (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))))


-- @@ L679-682 verbatim
def kernelCorrespondenceTest (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨kernelCorrespondenceFunction hJK e g he f.1,
    kernelCorrespondenceFunction_contMDiff hJK e g he f.1 f.2.1,
    kernelCorrespondenceFunction_hasCompactSupport hHK hJK e g he f.1 f.2.2⟩


-- @@ L684-684 verbatim
end CubicEisenstein


-- @@ L686-686 verbatim
end


-- @@ L688-688 verbatim
end OAI
