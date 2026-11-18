import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L74-74 verbatim
open scoped BigOperators Classical


-- @@ L76-76 verbatim
namespace CubicEisenstein


-- @@ L78-78 verbatim
section

-- @@ L79-79 verbatim
open scoped BigOperators Classical MatrixGroups

-- @@ L80-80 verbatim
open MeasureTheory

-- @@ L81-81 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L83-83 verbatim
open CubicKubota EisensteinCuspModThree ConcreteTraceCRT

-- @@ L84-84 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L86-87 verbatim
def sourceCuspCoefficients (j : Fin 3) : SubexponentialBesselCoefficients :=
  ![sourceBesselCoefficients,ramifiedBesselCoefficients false,ramifiedBesselCoefficients true] j


-- @@ L89-89 verbatim
def sourceCuspScale (j : Fin 3) : ℝ := ![1,3,3] j

-- @@ L90-90 verbatim
def sourceCuspBesselConstant (j : Fin 3) : ℂ := ![(3*Real.pi)*constantArithmeticResidue,0,0] j


-- @@ L92-93 verbatim
lemma sourceCuspScale_pos (j : Fin 3) : 0<sourceCuspScale j := by
  fin_cases j <;> norm_num [sourceCuspScale]


-- @@ L95-101 verbatim
lemma ramifiedSource_scaled_fullFunction (side : Bool) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).fullFunction 0
        (upperPoint (z/3) (v/3) (by positivity)) := by
  rw [ramifiedSource_eq_series]
  simp only [SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]


-- @@ L103-116 verbatim
theorem sourceCusp_bessel_expansion (j : Fin 3) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)=
      (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (z/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j)
          (div_pos hv (sourceCuspScale_pos j))) := by
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      lowerCuspMatrix_zero,sourceBesselFunction] using congrFun cubicSourceResidualFunction_eq_bessel (upperPoint z v hv)
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction false v hv z
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction true v hv z


-- @@ L118-119 verbatim
def sourceCuspZTerm (j : Fin 3) (z : ℂ) (v : ℝ) (h : Eis) : ℂ :=
  (sourceCuspCoefficients j).scaledConjugateZTerm (sourceCuspScale j) v z h


-- @@ L121-131 verbatim
theorem sourceCuspZFamily_series (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=∑'h:Eis,sourceCuspZTerm j z v h := by
  rw [sourceCuspZFamily,cuspZProfile_positive _ _ _ hv]
  have he : (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint w v hv))=
      fun w=>star ((sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (w/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j) (div_pos hv (sourceCuspScale_pos j)))) := by
    funext w
    exact congrArg star (sourceCusp_bessel_expansion j v hv w)
  rw [he]
  exact (sourceCuspCoefficients j).scaledConjugate_wirtingerZ (sourceCuspBesselConstant j)
    (sourceCuspScale j) (sourceCuspScale_pos j) v hv z


-- @@ L133-135 verbatim
theorem sourceCuspZTerm_summable (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    Summable (sourceCuspZTerm j z v) :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_summable (sourceCuspScale j) (sourceCuspScale_pos j) v hv z


-- @@ L137-138 verbatim
lemma sourceCuspZTerm_zero (j : Fin 3) (z : ℂ) (v : ℝ) : sourceCuspZTerm j z v 0=0 :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_zero _ _ _


-- @@ L140-147 verbatim
lemma sourceCuspZTerm_bessel (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v)
    (h : Eis) (hh : h≠0) :
    sourceCuspZTerm j z v h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(sourceCuspScale j:ℂ))*
        star ((sourceCuspCoefficients j).value h)*((v/sourceCuspScale j:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/sourceCuspScale j))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_bessel _ (sourceCuspScale_pos j) v hv z h hh


-- @@ L149-160 verbatim
theorem thetaTwistedCuspProfile_reflected_series (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((d h).multiplier/(v:ℂ)^2*
          ∑'n:Eis,sourceCuspZTerm (d h).index (d h).dualPoint (((d h).heightScale*v)⁻¹) n) := by
  rw [thetaTwistedCuspProfile_reflection_of_data Ψ c hc d hd v hv]
  apply Finset.sum_congr rfl
  intro h hh
  rw [sourceCuspZFamily_series _ _ _ (inv_pos.mpr (mul_pos (d h).heightScale_pos hv))]


-- @@ L162-167 verbatim
def finiteReflectedSourceTerm (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (v : ℝ) (h : Eis⧸Ideal.span {c}) (n : Eis) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
    ((d h).multiplier/(v:ℂ)^2*
      sourceCuspZTerm (d h).index (d h).dualPoint (((d h).heightScale*v)⁻¹) n)


-- @@ L169-173 verbatim
theorem finiteReflectedSourceTerm_summable (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (v : ℝ) (hv : 0<v) (h : Eis⧸Ideal.span {c}) :
    Summable (finiteReflectedSourceTerm Ψ c hc d v h) :=
  ((sourceCuspZTerm_summable _ _ _ (inv_pos.mpr (mul_pos (d h).heightScale_pos hv))).mul_left _).mul_left _


-- @@ L175-184 verbatim
theorem thetaTwistedCuspProfile_reflected_single_series (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑'n:Eis,∑h:Eis⧸Ideal.span {c},finiteReflectedSourceTerm Ψ c hc d v h n := by
  rw [thetaTwistedCuspProfile_reflected_series Ψ c hc d hd v hv,
    Summable.tsum_finsetSum (fun h hh=>finiteReflectedSourceTerm_summable Ψ c hc d v hv h)]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [finiteReflectedSourceTerm,tsum_mul_left]


-- @@ L186-186 verbatim
end


-- @@ L188-188 verbatim
open scoped BigOperators Classical

-- @@ L189-189 verbatim
open MeasureTheory

-- @@ L190-190 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L192-192 verbatim
open ConcreteTraceCRT

-- @@ L193-193 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L195-195 verbatim
def sourceCuspRadialLength (h : Eis) : ℝ := if h=0 then 1 else ‖eisEmbedding h‖^2

-- @@ L196-196 verbatim
def sourceCuspRadialScale (j : Fin 3) : ℝ := thetaBesselScale/sourceCuspScale j


-- @@ L198-200 verbatim
def sourceCuspRadialBaseCoefficient (j : Fin 3) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h)*star ((sourceCuspCoefficients j).value h)/
    ((sourceCuspScale j:ℂ)^2*(sourceCuspRadialLength h:ℂ))


-- @@ L202-204 verbatim
def sourceCuspRadialCoefficient (j : Fin 3) (z : ℂ) (h : Eis) : ℂ :=
  sourceCuspRadialBaseCoefficient j h*
    ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ)))


-- @@ L206-210 verbatim
lemma sourceCuspRadialLength_pos (h : Eis) : 0<sourceCuspRadialLength h := by
  by_cases hh:h=0
  · simp only [sourceCuspRadialLength,ite_eq_left hh,zero_lt_one]
  · rw [sourceCuspRadialLength,ite_eq_right hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))


-- @@ L212-213 verbatim
lemma sourceCuspRadialScale_pos (j : Fin 3) : 0<sourceCuspRadialScale j :=
  div_pos thetaBesselScale_pos (sourceCuspScale_pos j)


-- @@ L215-217 verbatim
lemma sourceCuspRadialCoefficient_norm (j : Fin 3) (z : ℂ) (h : Eis) :
    ‖sourceCuspRadialCoefficient j z h‖=‖sourceCuspRadialBaseCoefficient j h‖ := by
  rw [sourceCuspRadialCoefficient,norm_mul,breveE_norm,mul_one]


-- @@ L219-222 verbatim
lemma sourceCuspRadialCoefficient_zero (j : Fin 3) (z : ℂ) :
    sourceCuspRadialCoefficient j z 0=0 := by
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,cuspFrequency,
    map_zero,zero_div,mul_zero,zero_mul]


-- @@ L224-228 verbatim
lemma sourceCuspRadialLength_frequency (h : Eis) (hh : h≠0) :
    ‖cuspFrequency h‖=thetaBesselScale*Real.sqrt (sourceCuspRadialLength h) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,sourceCuspRadialLength,ite_eq_right hh,
    Real.sqrt_sq (norm_nonneg _)]
  rfl


-- @@ L230-247 verbatim
theorem sourceCuspZTerm_eq_radial (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) (h : Eis) :
    sourceCuspZTerm j z v h=
      (sourceCuspRadialCoefficient j z h*(sourceCuspRadialLength h:ℂ))*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v) := by
  by_cases hh:h=0
  · subst h
    rw [sourceCuspZTerm_zero,sourceCuspRadialCoefficient_zero]
    ring
  · rw [sourceCuspZTerm_bessel j z v hv h hh,sourceCuspRadialLength_frequency h hh]
    have ha : 4*Real.pi*(thetaBesselScale*Real.sqrt (sourceCuspRadialLength h))*(v/sourceCuspScale j)=
        4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v := by
      unfold sourceCuspRadialScale
      ring
    rw [ha]
    have hs0 : (sourceCuspScale j:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
    have hl0 : (sourceCuspRadialLength h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspRadialLength_pos h).ne'
    simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,Complex.ofReal_div]
    field_simp [hs0,hl0]


-- @@ L249-253 verbatim
theorem sourceCuspZFamily_eq_radialBesselProfile (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=
      radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient j z) (sourceCuspRadialScale j) v := by
  rw [sourceCuspZFamily_series j z v hv]
  exact tsum_congr (sourceCuspZTerm_eq_radial j z v hv)


-- @@ L255-268 verbatim
theorem thetaTwistedCuspProfile_reflected_radial (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((d h).multiplier/(v:ℂ)^2*
          radialBesselProfile sourceCuspRadialLength
            (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
            (sourceCuspRadialScale (d h).index) (((d h).heightScale*v)⁻¹)) := by
  rw [thetaTwistedCuspProfile_reflection_of_data Ψ c hc d hd v hv]
  apply Finset.sum_congr rfl
  intro h hh
  rw [sourceCuspZFamily_eq_radialBesselProfile _ _ _ (inv_pos.mpr (mul_pos (d h).heightScale_pos hv))]


-- @@ L270-270 verbatim
end CubicEisenstein


-- @@ L272-272 verbatim
open Filter MeasureTheory

-- @@ L273-273 verbatim
open scoped Classical BigOperators Topology


-- @@ L275-275 verbatim
namespace CompletedGauss


-- @@ L277-283 verbatim
lemma positive_nat_pow_cpow (x:ℝ) (hx:0≤x) (n:ℕ) (s:ℂ) :
    ((x^n:ℝ):ℂ)^s=((x:ℂ)^s)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx,
        hn,pow_succ]


-- @@ L285-320 verbatim
lemma positive_reflection_powers (Q u d X r:ℝ)
    (hQ:0<Q) (hu:0<u) (hd:0<d) (hX:0<X) (hr:0<r) (w:ℂ) :
    (Q:ℂ)^(1+2*w)*(u:ℂ)^(2-2*w)*(2:ℂ)^(4*w)/(d:ℂ)^(2+2*w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(u/d)^2:ℝ):ℂ)*((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^(-w) := by
  have hQ0:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hu0:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hu.ne'
  have hd0:(d:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hd.ne'
  have hX0:(X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hX.ne'
  have hr0:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hQp:(Q:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0)
  have hup:(u:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hu0)
  have hdp:(d:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have hXp:(X:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hX0)
  have hrp:(r:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hr0)
  have h2p:(2:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have h16:((16:ℝ):ℂ)^w=((2:ℂ)^w)^4 := by
    have hh:=positive_nat_pow_cpow 2 (by norm_num) 4 w
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hh
    exact hh
  have hy:((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^w=
      (((u:ℂ)^w)^2*((d:ℂ)^w)^2*(X:ℂ)^w*(r:ℂ)^w)/
        (((2:ℂ)^w)^4*((Q:ℂ)^w)^2) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity)]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hr.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hX.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    rw [positive_nat_pow_cpow u hu.le,positive_nat_pow_cpow d hd.le,
      positive_nat_pow_cpow Q hQ.le,h16]
  rw [Complex.cpow_add _ _ hQ0,Complex.cpow_one,
    Complex.cpow_sub _ _ hu0,Complex.cpow_add _ _ hd0]
  simp only [Complex.cpow_ofNat_mul,Complex.cpow_ofNat]
  rw [Complex.cpow_neg,Complex.cpow_neg,Complex.cpow_neg,hy]
  push_cast
  field_simp


-- @@ L322-338 verbatim
theorem bessel_reflection_scale (q d Q X r:ℝ)
    (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X) (hr:0<r) (w:ℂ) :
    (Q:ℂ)^(2-2*(1/2-w))*besselReflectionFactor q d (1/2-w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(q/d)^2:ℝ):ℂ)*
        ((CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2):ℝ):ℂ)^(-w) := by
  have he:=positive_reflection_powers Q (4*Real.pi*q) (4*Real.pi*d) X r
    hQ (by positivity) (by positivity) hX hr w
  have hp:Q*((4*Real.pi*q)/(4*Real.pi*d))^2=Q*(q/d)^2 := by
    field_simp
  have hy:(4*Real.pi*q)^2*(4*Real.pi*d)^2*X*r/(16*Q^2)=
      CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2) := by
    unfold CubicReflectionKernel.paperScale
    ring
  rw [hp,hy] at he
  unfold besselReflectionFactor
  convert he using 1 ; congr 2 ; ring_nf


-- @@ L340-340 verbatim
end CompletedGauss


-- @@ L342-342 verbatim
open Filter MeasureTheory

-- @@ L343-343 verbatim
open scoped Classical BigOperators Topology ContDiff


-- @@ L345-345 verbatim
namespace CubicReflectionKernel


-- @@ L347-364 verbatim
lemma paperKernel_three_halves (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    paperKernel V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change paperKernel V x=_
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he


-- @@ L366-382 verbatim
lemma paperKernel_three_halves_bound (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖paperKernel V x‖≤C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=mellinInv_euler_line_bound V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)


-- @@ L384-384 verbatim
end CubicReflectionKernel

-- @@ L385-385 verbatim
namespace CompletedGauss


-- @@ L387-387 verbatim
section

-- @@ L388-388 verbatim
open CubicReflectionKernel


-- @@ L390-407 verbatim
lemma paperKernel_weighted_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>a i*paperKernel V (c*r i)) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply Summable.of_norm
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring


-- @@ L409-440 verbatim
theorem paperKernel_weighted_mellin {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*paperKernel V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,inverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*paperKernel V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [paperKernel_three_halves V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM


-- @@ L442-442 verbatim
end


-- @@ L444-444 verbatim
open CubicEisenstein CubicReflectionKernel


-- @@ L446-477 verbatim
lemma besselSmoothingIntegrand_reflected_kernel_line {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (X:ℝ) (hX:0<X) (t:ℝ) :
    besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
      (A*((Q*(q/d)^2:ℝ):ℂ))*
        ((∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
          (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
            mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))) := by
  let s:ℂ:=(-1:ℂ)+(-t)*Complex.I
  let w:ℂ:=(3/2:ℂ)+t*Complex.I
  have hs:s.re-1/2=-(3/2:ℝ):=by dsimp [s];norm_num
  have hslt:s.re<4/3:=by dsimp [s];norm_num
  have hsum:Summable (fun i=>‖a i‖*(r i)^(s.re-1/2)):=by simpa only [hs] using has
  have hsw:1/2-w=s:=by dsimp [s,w];ring
  have hw:1/2-s=w:=by rw [←hsw];ring
  have hsw':s-1/2=-w:=by rw [←hsw];ring
  have hp:=bessel_reflection_scale q d Q X 1 hq hd hQ hX (by norm_num) w
  simp only [hsw,Complex.ofReal_one,Complex.one_cpow,mul_one] at hp
  have he:=continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect s hslt hsum
  change besselSmoothingIntegrand F q V X s=_
  rw [besselSmoothingIntegrand,he,hw,hsw']
  change _=(A*((Q*(q/d)^2:ℝ):ℂ))*
    ((∑'i,a i*(r i:ℂ)^(-w))*
      (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-w)*mellinEulerData V 0 w))
  rw [mellinEulerData,pow_zero,one_mul,mellinData]
  calc
    _=(A*mellin V (-w)*gammaMultiplier w*(∑'i,a i*(r i:ℂ)^(-w)))*
      ((Q:ℂ)^(2-2*s)*besselReflectionFactor q d s*(X:ℂ)^(-w)):=by ring
    _=_:=by rw [hp];ring


-- @@ L479-539 verbatim
theorem completedT_smoothed_reflection {α:Type*} [Countable α]
    (Ψ:ActualEisensteinCubic.O→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hF:∀s:ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe:Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (hreflect:∀v:ℝ,0<v→completedBesselProfile Ψ q v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=
      (A*(Q:ℂ)*((q/d:ℝ):ℂ)^2)*
        ∑'i,a i*paperKernel (Vstar W) (27*q^2*d^2*X*r i/Q^2) := by
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  have hl:=besselSmoothingIntegrand_reflected_integrable (completedBesselProfile Ψ q)
    r hr a q d Q hq hd hQ A hreflect has (Vstar W) v0 v1 hv0 hVs hV X hX
  have hlreal : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X
        (((-1:ℝ):ℂ)+t*Complex.I)) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hl
  have hshift:=completedT_mellin_shift Ψ hΨ q hq hF hFe W v0 v1 hv0 hWs hW X hX
    (-1) (by norm_num) hlreal
  let c:ℝ:=27*q^2*d^2*X/Q^2
  have hc:0<c:=by dsimp [c];positivity
  let M:ℝ→ℂ:=fun t=>(∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
    (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
      mellinEulerData (Vstar W) 0 ((3/2:ℂ)+t*Complex.I))
  have hk:=paperKernel_weighted_mellin r hr a has (Vstar W) v0 v1 hv0 hVs hV c hc
  have hpoint (t:ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((-1:ℂ)+(-t)*Complex.I)=
        (A*((Q*(q/d)^2:ℝ):ℂ))*M t :=
    besselSmoothingIntegrand_reflected_kernel_line (completedBesselProfile Ψ q)
      r hr a q d Q hq hd hQ A hreflect has (Vstar W) X hX t
  calc
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((-1:ℂ)+(-t)*Complex.I):=by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t:ℝ=>
          besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X
            ((-1:ℂ)+t*Complex.I)) volume).symm
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*((1/(2*Real.pi):ℂ)*∫t:ℝ,M t):=by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*(∑'i,a i*paperKernel (Vstar W) (c*r i)):=by rw [hk]
    _=_:=by
      push_cast
      congr 1
      · ring
      · apply tsum_congr
        intro i
        congr 2
        dsimp [c]
        ring


-- @@ L541-554 verbatim
theorem reflected_paperKernel_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (q d Q X:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W) :
    Summable (fun i=>a i*paperKernel (Vstar W) (27*q^2*d^2*X*r i/Q^2)) := by
  have h:=paperKernel_weighted_summable r hr a has (Vstar W) v0 v1 hv0
    (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (27*q^2*d^2*X/Q^2) (by positivity)
  apply h.congr
  intro i
  congr 2
  ring


-- @@ L556-556 verbatim
end CompletedGauss


-- @@ L558-558 verbatim
open Filter MeasureTheory

-- @@ L559-559 verbatim
open scoped Classical BigOperators Topology ContDiff


-- @@ L561-561 verbatim
namespace CompletedGauss

-- @@ L562-562 verbatim
open CubicEisenstein CubicReflectionKernel


-- @@ L564-606 verbatim
theorem besselSmoothingIntegral_reflected_kernel {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (X:ℝ) (hX:0<X) :
    (1/(2*Real.pi):ℂ)*∫t:ℝ,besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)=
      (A*(Q:ℂ)*((q/d:ℝ):ℂ)^2)*
        ∑'i,a i*paperKernel V (27*q^2*d^2*X*r i/Q^2) := by
  let c:ℝ:=27*q^2*d^2*X/Q^2
  have hc:0<c:=by dsimp [c];positivity
  let M:ℝ→ℂ:=fun t=>(∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
    (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
      mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))
  have hk:=paperKernel_weighted_mellin r hr a has V v0 v1 hv0 hVs hV c hc
  have hpoint (t:ℝ) :
      besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
        (A*((Q*(q/d)^2:ℝ):ℂ))*M t :=
    besselSmoothingIntegrand_reflected_kernel_line F
      r hr a q d Q hq hd hQ A hreflect has V X hX t
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I):=by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t:ℝ=>
          besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) volume).symm
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*((1/(2*Real.pi):ℂ)*∫t:ℝ,M t):=by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*(∑'i,a i*paperKernel V (c*r i)):=by rw [hk]
    _=_:=by
      push_cast
      congr 1
      · ring
      · apply tsum_congr
        intro i
        congr 2
        dsimp [c]
        ring


-- @@ L608-624 verbatim
theorem paperKernel_weighted_norm_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*paperKernel V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring


-- @@ L626-626 verbatim
end CompletedGauss


-- @@ L628-628 verbatim
end


-- @@ L630-630 verbatim
end OAI
