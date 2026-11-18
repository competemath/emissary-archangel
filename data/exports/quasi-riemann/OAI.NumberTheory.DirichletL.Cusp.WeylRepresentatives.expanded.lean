import OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays


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
namespace ShortDraftCusp

-- @@ L77-77 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L79-79 verbatim
section

-- @@ L80-80 verbatim
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal

-- @@ L81-81 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L83-84 verbatim
def A3WeylCusp (u : Eis) : SL(2,Eis) :=
  ⟨!![u,-1;1,0],by simp [Matrix.det_fin_two]⟩


-- @@ L86-92 verbatim
lemma A3_ramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![M 0 0-u*M 0 1,M 0 1;M 1 0-u*M 1 1,M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerCuspMatrix,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring


-- @@ L94-100 verbatim
lemma A3_unramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![-M 0 1,M 0 0+u*M 0 1;-M 1 1,M 1 0+u*M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A3WeylCusp,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring


-- @@ L102-107 verbatim
lemma A3_principal_mem_levelThree (M : SL(2,Eis))
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0) (hd : (3:Eis)∣M 1 1-1) : M∈levelThree := by
  apply (mem_levelThree_iff_entries M).mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simpa using (by assumption)


-- @@ L109-120 verbatim
lemma A3_ramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1) :
    M*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_ramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using hb
  · convert dvd_sub hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring
  · simpa using hd


-- @@ L122-133 verbatim
lemma A3_unramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1) :
    M*(A3WeylCusp u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_unramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert dvd_neg.mpr hb using 1 ; simp ; ring
  · convert dvd_add ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using dvd_neg.mpr hd
  · convert dvd_add hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring


-- @@ L135-135 verbatim
end


-- @@ L137-137 verbatim
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal

-- @@ L138-138 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L140-145 verbatim
lemma A3_principal_character (M : SL(2,Eis)) (hM : M∈levelThree)
    (c0 r : Eis) (hC : M 1 0=c0*r) (hr : lambda^2∣r-1) :
    complexCharacter ⟨M,hM⟩ =
      eisEmbedding (symbol c0 (M 0 0))*eisEmbedding (symbol (M 0 0) r) := by
  change eisEmbedding (symbol (M 1 0) (M 0 0))=_
  rw [hC,A3_principal_global _ _ _ (levelThree_primary ⟨M,hM⟩) hr,map_mul]


-- @@ L147-155 verbatim
lemma A3_ramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hM⟩ =
      eisEmbedding (symbol (M 1 0-u*M 1 1) (M 0 0-u*M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_ramified_relative_matrix]
  rfl


-- @@ L157-165 verbatim
lemma A3_unramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(A3WeylCusp u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hM⟩ =
      eisEmbedding (symbol (-M 1 1) (-M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_unramified_relative_matrix]
  rfl


-- @@ L167-183 verbatim
theorem A3_ramified_character (M : SL(2,Eis)) (u c0 r : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1)
    (hC : M 1 0=u*(c0*r)) (hr : lambda^2∣r-1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,
      A3_ramified_mem_levelThree M u ha hb hc hd⟩ =
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol c0 (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA : lambda^2∣(M 0 0-u*M 0 1)-1 := by
    apply lambda_sq_dvd_three.trans
    convert dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; ring
  have hdet : M 0 0*M 1 1-M 0 1*(u*(c0*r))=1 := by
    rw [←hC]
    simpa only [Matrix.det_fin_two] using M.property
  rw [A3_ramified_literal_character,hC,
    A3_ramified_global_factor _ _ _ _ _ _ hdet
      (lambda_sq_dvd_three.trans ha) hA hr,map_mul]


-- @@ L185-202 verbatim
theorem A3_unramified_character (M : SL(2,Eis)) (u c0 r : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1)
    (hC : M 1 0=c0*r) (h9 : (9:Eis)∣M 0 0*M 1 1) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,
      A3_unramified_mem_levelThree M u ha hb hc hd⟩ =
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb' : lambda^2∣(-M 0 1)-1 := by
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr hb using 1 ; ring
  have hc' : lambda^2∣c0*r-1 := by
    rw [←hC]
    exact lambda_sq_dvd_three.trans hc
  have hdet : M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    rw [←hC]
    simpa only [Matrix.det_fin_two] using M.property
  rw [A3_unramified_literal_character,
    A3_unramified_global_factor _ _ _ _ _ hdet hb' hc' h9,map_mul]


-- @@ L204-204 verbatim
end ShortDraftCusp


-- @@ L206-206 verbatim
namespace CubicEisenstein


-- @@ L208-208 verbatim
section

-- @@ L209-209 verbatim
open Filter MeasureTheory

-- @@ L210-210 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L212-212 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

-- @@ L213-213 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L215-218 verbatim
lemma fixedCuspArrayIndex_ne_zero (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayIndex u m I J≠0 :=
  mul_ne_zero (mul_ne_zero (ramifiedElement_ne_zero u m) hI) (pow_ne_zero _ hJ)


-- @@ L220-231 verbatim
lemma fixedCuspArrayIndex_norm_sq (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖^2=
      (3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hr:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=‖eisEmbedding (u.val*lambda^m)‖^2*‖eisEmbedding (primaryGenerator I)‖^2*
      (‖eisEmbedding (primaryGenerator J)‖^2)^3 := by
        simp only [fixedCuspArrayIndex,map_mul,map_pow,norm_mul,norm_pow]
        ring
    _=_ := by rw [hr,primaryGenerator_norm_sq I hI,primaryGenerator_norm_sq J hJ]


-- @@ L233-237 verbatim
lemma fixedCuspArrayIndex_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      Real.sqrt ((3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3) := by
  rw [←fixedCuspArrayIndex_norm_sq u m I J hI hJ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]


-- @@ L239-251 verbatim
lemma fixedCuspArrayWeight_div_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      1/((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hn:0<(Ideal.absNorm I:ℝ) := by
    rw [←primaryGenerator_norm_sq I hI]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hI))
  have hb:0<(Ideal.absNorm J:ℝ) := by
    rw [←primaryGenerator_norm_sq J hJ]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [fixedCuspArrayWeight,fixedCuspArrayIndex_norm u m I J hI hJ]
  simpa only [Real.rpow_natCast] using cusp_coefficient_normalization (m:ℝ)
    (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) hn hb


-- @@ L253-268 verbatim
theorem fixedConjugateCuspArray_div_norm (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))/
      (‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℂ)=
    (fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J/
      (((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [fixedConjugateCuspArray_reconstruct j u m I J h]
  calc
    _=(fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J*
      ((fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℝ):ℂ) := by
        push_cast
        ring
    _=_ := by
      rw [fixedCuspArrayWeight_div_norm u m I J h.2.1 h.2.2]
      push_cast
      ring


-- @@ L270-270 verbatim
end


-- @@ L272-272 verbatim
open Filter MeasureTheory

-- @@ L273-273 verbatim
open scoped BigOperators Classical Topology ContDiff MatrixGroups


-- @@ L275-275 verbatim
section

-- @@ L276-276 verbatim
open CompletedGauss CompletedDyadic ConcreteTraceCRT

-- @@ L277-277 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L279-280 verbatim
lemma thetaFullFrequency_eq_fixedCuspArrayIndex (p:ThetaFullIndex) :
    thetaFullFrequency p=fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val := rfl


-- @@ L282-287 verbatim
lemma sourceCuspRadialLength_full_index (p:ThetaFullIndex) :
    sourceCuspRadialLength (thetaFullFrequency p)=
      (3:ℝ)^p.2.1*(Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength,ite_eq_right (thetaFullFrequency_ne_zero p),thetaFullFrequency_eq_fixedCuspArrayIndex]
  exact fixedCuspArrayIndex_norm_sq p.1 p.2.1 p.2.2.1.val p.2.2.2.val
    p.2.2.1.property.2 p.2.2.2.property


-- @@ L289-294 verbatim
lemma thetaRamifiedScale_eq (m:ℕ) :
    ramifiedScale 1 completedRamifiedStep m=(3:ℝ)^((m:ℝ)/3) := by
  unfold ramifiedScale completedRamifiedStep
  rw [one_mul,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring


-- @@ L296-300 verbatim
lemma thetaRamifiedScale_cube (m:ℕ) :
    (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  rw [thetaRamifiedScale_eq,←Real.rpow_mul_natCast (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [show ((m:ℝ)/3)*(3:ℝ)=m by ring,Real.rpow_natCast]


-- @@ L302-307 verbatim
lemma sourceCusp_full_index_kernel_argument (p:ThetaFullIndex) (j:Fin 3) (Q X:ℝ) :
    X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2)=
      (X/(27*(sourceCuspScale j)^2*Q^2))*(ramifiedScale 1 completedRamifiedStep p.2.1)^3*
        (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength_full_index,thetaRamifiedScale_cube]
  ring


-- @@ L309-309 verbatim
def sourceFrequencyAngle (h:Eis) : ℂ := eisEmbedding h/(‖eisEmbedding h‖:ℂ)


-- @@ L311-313 verbatim
lemma sourceFrequencyAngle_norm (h:Eis) (hh:h≠0) : ‖sourceFrequencyAngle h‖=1 := by
  rw [sourceFrequencyAngle,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))


-- @@ L315-328 verbatim
lemma sourceCuspRadialCoefficient_angle (j:Fin 3) (z:ℂ) (h:Eis) (hh:h≠0) :
    sourceCuspRadialCoefficient j z h=
      ((-2*Real.pi*Complex.I*thetaFrequencyScale)/(sourceCuspScale j:ℂ)^2)*
        sourceFrequencyAngle h*
        (star ((sourceCuspCoefficients j).value h)/(‖eisEmbedding h‖:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) := by
  have hn:(‖eisEmbedding h‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))
  have hs:(sourceCuspScale j:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  rw [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,sourceCuspRadialLength,ite_eq_right hh]
  rw [cuspFrequency_eq_thetaFrequencyScale]
  unfold sourceFrequencyAngle
  push_cast
  field_simp [hn,hs]


-- @@ L330-331 verbatim
def fixedRadialCoefficientScalar : ℂ :=
  (-2*Real.pi*Complex.I)*thetaFrequencyScale*(fixedCuspCoefficientBound:ℂ)


-- @@ L333-348 verbatim
theorem sourceCuspRadialCoefficient_fixed_array
    (j:Fin 3) (z:ℂ) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) (h:fixedCuspArrayEligible I J) :
    sourceCuspRadialCoefficient j z (fixedCuspArrayIndex u m I J)=
      (fixedRadialCoefficientScalar/(sourceCuspScale j:ℂ)^2)*
        (fixedConjugateCuspArray j u m I J*
          sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
          ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
            (z/(sourceCuspScale j:ℂ))))/
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm I:ℝ)*
          (Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [sourceCuspRadialCoefficient_angle _ _ _
    (fixedCuspArrayIndex_ne_zero u m I J h.2.1 h.2.2),
    fixedConjugateCuspArray_div_norm j u m I J h,thetaRamifiedScale_eq]
  unfold fixedRadialCoefficientScalar
  push_cast
  ring


-- @@ L350-350 verbatim
end


-- @@ L352-352 verbatim
open CompletedGauss CompletedDyadic ConcreteTraceCRT

-- @@ L353-353 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L355-365 verbatim
lemma thetaFullIndex_denominator_pos (p:ThetaFullIndex) :
    0<ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ) := by
  have hI:0<(Ideal.absNorm p.2.2.1.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.1.property.2]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.1.property.2))
  have hJ:0<(Ideal.absNorm p.2.2.2.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.2.property]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.2.property))
  rw [thetaRamifiedScale_eq]
  positivity


-- @@ L367-370 verbatim
lemma SourceCuspDatum.smoothed_unit_phase_norm (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)‖=1 := by
  rw [norm_mul,d.multiplier_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos d.heightScale_pos,inv_mul_cancel₀ d.heightScale_pos.ne']


-- @@ L372-389 verbatim
theorem SourceCuspDatum.smoothedFullCoefficient_normalization (d:SourceCuspDatum) (p:ThetaFullIndex) :
    (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)=
    (fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency p)*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
          (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
      ((ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ) := by
  have hs:(sourceCuspScale d.index:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos _).ne'
  have hn:((ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (thetaFullIndex_denominator_pos p).ne'
  simp only [thetaFullFrequency_eq_fixedCuspArrayIndex]
  rw [sourceCuspRadialCoefficient_fixed_array _ _ _ _ _ _
    ⟨p.2.2.1.property.1,p.2.2.1.property.2,p.2.2.2.property⟩]
  field_simp [hs,hn]


-- @@ L391-406 verbatim
lemma SourceCuspDatum.smoothedFullCoefficient_norm_le (d:SourceCuspDatum) (p:ThetaFullIndex) :
    ‖(d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖≤
    ‖fixedRadialCoefficientScalar‖/
      (ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)) := by
  have ha:‖fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p)*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        (d.dualPoint/(sourceCuspScale d.index:ℂ)))‖≤1:=by
    rw [norm_mul,norm_mul,sourceFrequencyAngle_norm _ (thetaFullFrequency_ne_zero p),breveE_norm,mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  rw [d.smoothedFullCoefficient_normalization,norm_div,norm_mul,norm_mul,
    d.smoothed_unit_phase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg (thetaFullIndex_denominator_pos p).le]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) ha) (thetaFullIndex_denominator_pos p).le


-- @@ L408-425 verbatim
theorem SourceCuspDatum.smoothedKernel_fixed_array (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=(fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p)*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [d.smoothedKernel_full_index,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [←mul_assoc,d.smoothedFullCoefficient_normalization,sourceCusp_full_index_kernel_argument]
  ring


-- @@ L427-427 verbatim
end CubicEisenstein


-- @@ L429-429 verbatim
open scoped Classical BigOperators


-- @@ L431-431 verbatim
namespace CanonicalRowCompletion

-- @@ L432-432 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticAllOddCRT

-- @@ L433-433 verbatim
open UniqueFactorizationMonoid

-- @@ L434-434 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L436-452 verbatim
theorem idealRowHom_congr_mod (I:Ideal Eis) (x y:Eis) (hxy:x-y∈I) :
    idealRowHom x I=idealRowHom y I := by
  by_cases hI:I=0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _)=(if I=0 then 0 else _)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hle:I≤P:=((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  unfold localRowValue
  split_ifs with hp
  · let:P.IsMaximal:=hp.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl


-- @@ L454-457 verbatim
lemma sexticReciprocityPhase_congr_right (a x y:Eis) (hxy:(4:Eis)∣x-y) :
    sexticReciprocityPhase a x=sexticReciprocityPhase a y := by
  unfold sexticReciprocityPhase
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y hxy]


-- @@ L459-461 verbatim
lemma sexticReciprocityPhase_norm (a x:Eis) : ‖sexticReciprocityPhase a x‖≤1 := by
  unfold sexticReciprocityPhase quadraticRaySign
  split_ifs <;> norm_num


-- @@ L463-468 verbatim
def reciprocalRow (a:Eis) (ha:Supported (Ideal.span {a})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})
  map_one' := by rw [sexticReciprocityPhase_one_right a ha,idealRowHom_one_supported _ ha,one_mul]
  map_mul' x y := by
    rw [sexticReciprocityPhase_mul_right,idealRowHom_argument_mul]
    ring


-- @@ L470-475 verbatim
lemma reciprocalRow_norm (a:Eis) (ha:Supported (Ideal.span {a})) (n:Eis) :
    ‖reciprocalRow a ha n‖≤1 := by
  change ‖sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (sexticReciprocityPhase_norm a n)).trans (idealRowHom_norm _ _)


-- @@ L477-484 verbatim
lemma reciprocalRow_periodic (a:Eis) (ha:Supported (Ideal.span {a})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(4:Eis)}*Ideal.span {a}) (reciprocalRow a ha) := by
  intro x y hxy
  change sexticReciprocityPhase a x*idealRowHom x (Ideal.span {a})=
    sexticReciprocityPhase a y*idealRowHom y (Ideal.span {a})
  rw [sexticReciprocityPhase_congr_right a x y
    (Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)),
    idealRowHom_congr_mod _ x y (Ideal.mul_le_right hxy)]


-- @@ L486-495 verbatim
lemma reciprocalRow_eq_idealRowHom (a n:Eis)
    (ha:Supported (Ideal.span {a})) (hn:Supported (Ideal.span {n}))
    (hpa:lambda^2∣a-1) (hpn:lambda^2∣n-1) :
    reciprocalRow a ha n=idealRowHom a (Ideal.span {n}) := by
  have h:=idealRowHom_primary_reciprocity n a hpn hpa hn ha
  have hs:sexticReciprocityPhase n a=sexticReciprocityPhase a n := by
    exact congrArg (fun z:ℤ=>(z:ℂ)) (quadraticRaySign_symm _ _)
  change sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})=_
  rw [hs] at h
  exact h.symm


-- @@ L497-497 verbatim
end CanonicalRowCompletion


-- @@ L499-499 verbatim
namespace CubicEisenstein

-- @@ L500-500 verbatim
open scoped Classical BigOperators MatrixGroups Matrix


-- @@ L502-502 verbatim
open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic

-- @@ L503-503 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L504-504 verbatim
namespace FixedCuspShape

-- @@ L505-505 verbatim
variable {H:SL(2,Eis)} (s:FixedCuspShape H)


-- @@ L507-511 verbatim
def amplitude (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray s.index u m I J*
    sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))


-- @@ L513-520 verbatim
lemma amplitude_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ‖s.amplitude u m I J‖≤1 := by
  by_cases he:fixedCuspArrayEligible I J
  · rw [amplitude,norm_mul,norm_mul,breveE_norm,
      sourceFrequencyAngle_norm _ (fixedCuspArrayIndex_ne_zero u m I J he.2.1 he.2.2),mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  · simp only [amplitude,fixedConjugateCuspArray,
      fixedCuspArray_zero_of_ineligible _ _ _ _ _ he,star_zero,zero_mul,norm_zero]
    norm_num


-- @@ L522-552 verbatim
theorem smoothedKernel_fixed_shape (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0)
    (W:ℝ→ℂ) (X:ℝ) :
    (s.datum g hc).smoothedKernel W X=
      (fixedRadialCoefficientScalar*((s.datum g hc).multiplier*
        (‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ)))*
      ∑'p:ThetaFullIndex,
        ((s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*
            eisEmbedding (s.upper 0 0)^2*
            (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/
            (sourceCuspScale s.index:ℂ)))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^4))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [(s.datum g hc).smoothedKernel_fixed_array,s.datum_heightScale]
  have hi:(s.datum g hc).index=s.index:=rfl
  simp only [hi,←pow_mul,show (2:ℕ)*2=4 by norm_num]
  congr 1
  apply tsum_congr
  intro p
  have hp:=s.datum_additive_phase g hc (cuspFrequency (thetaFullFrequency p))
    (sourceCuspScale s.index:ℂ)
  rw [show -cuspFrequency (thetaFullFrequency p)*
      ((s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ))=
      -cuspFrequency (thetaFullFrequency p)*(s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ) by ring,hp]
  unfold amplitude
  rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
  ring


-- @@ L554-562 verbatim
lemma smoothed_row_factor (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g hc).multiplier*((s.datum g hc).heightScale:ℂ)=
      -star (levelTwoComplexCharacter g)*
        (star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*
        ((‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ):ℂ)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [s.datum_multiplier,s.datum_heightScale]
  push_cast
  ring


-- @@ L564-564 verbatim
end FixedCuspShape

-- @@ L565-565 verbatim
end CubicEisenstein


-- @@ L567-567 verbatim
open scoped BigOperators Classical Matrix MatrixGroups


-- @@ L569-569 verbatim
namespace ShortDraftCRT

-- @@ L570-570 verbatim
variable {R:Type*} [CommRing R]


-- @@ L572-576 verbatim
lemma exists_controlled_inverse (B c a:R) (ha:IsCoprime a (B*c)) :
    ∃d0:R,B*c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=ha
  refine ⟨x,-y,?_⟩
  linear_combination hxy


-- @@ L578-583 verbatim
lemma exists_controlled_zero_inverse (B c a:R)
    (hBc:IsCoprime B c) (hac:IsCoprime a c) :
    ∃d0:R,B∣d0 ∧ c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=hac.mul_left hBc
  refine ⟨B*x,⟨x,rfl⟩,-y,?_⟩
  linear_combination hxy


-- @@ L585-585 verbatim
variable [IsDomain R]


-- @@ L587-600 verbatim
lemma fixed_completion_upper_right_dvd (B M c r a d0 b d:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c))
    (hinv:B*c∣a*d0-1) (hdet:a*d-b*(c*r)=1) (hd:M*c∣d-d0) : B∣b := by
  have hBcM:B*c∣M*c:=mul_dvd_mul_right hBM c
  have hadd:B*c∣a*(d-d0):=dvd_mul_of_dvd_right (hBcM.trans hd) a
  have hfull:B*c∣a*d-1:=by
    convert dvd_add hadd hinv using 1 ; ring
  have hmul:B*c∣c*(b*r):=by
    convert hfull using 1
    linear_combination -hdet
  rw [mul_comm B c] at hmul
  have hbr:B∣b*r:=(mul_dvd_mul_iff_left hc).mp hmul
  have hBr:IsCoprime B r:=hr.of_mul_right_left.symm.of_isCoprime_of_dvd_left hBM
  exact hBr.dvd_of_dvd_mul_right hbr


-- @@ L602-608 verbatim
theorem exists_fixed_completion_upper_right (B M c r a d0:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hinv:B*c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0
    ((dvd_mul_left c B).trans hinv) hr har
  exact ⟨b,d,hdet,hd,fixed_completion_upper_right_dvd B M c r a d0 b d hc hBM hr hinv hdet hd⟩


-- @@ L610-622 verbatim
omit [IsDomain R] in
theorem exists_fixed_completion_lower_right (B M c r a d0:R)
    (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hzero:B∣d0) (hinv:c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣d ∧ B∣a*d ∧ B∣b*(c*r)+1 := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0 hinv hr har
  have hdd:B∣d-d0:=(hBM.trans (dvd_mul_right M c)).trans hd
  have hBd:B∣d:=by
    convert dvd_add hdd hzero using 1 ; ring
  have hBad:B∣a*d:=dvd_mul_of_dvd_right hBd a
  refine ⟨b,d,hdet,hd,hBd,hBad,?_⟩
  convert hBad using 1
  linear_combination -hdet


-- @@ L624-632 verbatim
theorem controlled_completion_matrix_congr (M c r r0 a a0 b b0 d d0 inverse:R)
    (hc:c≠0) (hr:IsCoprime M r)
    (hdet:a*d-b*(c*r)=1) (hdet0:a0*d0-b0*(c*r0)=1)
    (ha:M*c∣a-a0) (hd:M*c∣d-inverse) (hd0:M*c∣d0-inverse)
    (hrr:M∣r-r0) :
    (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (Ideal.span {M}))=
      (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (Ideal.span {M})) := by
  apply fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha _ hrr
  convert dvd_sub hd hd0 using 1 ; ring


-- @@ L634-634 verbatim
end ShortDraftCRT


-- @@ L636-636 verbatim
end


-- @@ L638-638 verbatim
end OAI
