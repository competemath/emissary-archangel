import OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierExpansion


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

-- @@ L79-79 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L81-81 verbatim
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal CubicRamified

-- @@ L82-82 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L84-87 verbatim
lemma ramified_omega_relation : omega^2+omega+1=(0:Eis) := by
  apply eisEmbedding_injective
  simp only [map_add,map_pow,map_one,map_zero,eisEmbedding_omega_actual]
  exact EisensteinEmbedding.omega3_sq


-- @@ L89-90 verbatim
def lowerCuspMatrix (t : Eis) : SL(2,Eis) :=
  ⟨!![1,0;t,1],by simp [Matrix.det_fin_two]⟩


-- @@ L92-103 verbatim
def ramifiedParabolic (t x : Eis) : levelThree := by
  let M : SL(2,Eis) := ⟨!![1-3*t*x,3*x;-3*t^2*x,1+3*t*x],by
    rw [Matrix.det_fin_two]
    change (1-3*t*x)*(1+3*t*x)-(3*x)*(-3*t^2*x)=1
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-t*x,by change 1-3*t*x-1=3*(-t*x);ring⟩
  · exact ⟨x,by change 3*x-0=3*x;ring⟩
  · exact ⟨-t^2*x,by change -3*t^2*x-0=3*(-t^2*x);ring⟩
  · exact ⟨t*x,by change 1+3*t*x-1=3*(t*x);ring⟩


-- @@ L105-115 verbatim
lemma ramifiedParabolic_mul_lower (t x : Eis) :
    (ramifiedParabolic t x : SL(2,Eis))*lowerCuspMatrix t=
      lowerCuspMatrix t*(upperTranslation x : SL(2,Eis)) := by
  apply Subtype.ext
  change (ramifiedParabolic t x : Matrix (Fin 2) (Fin 2) Eis) *
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) =
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) *
      (upperTranslation x : Matrix (Fin 2) (Fin 2) Eis)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic,lowerCuspMatrix,upperTranslation,Matrix.mul_apply,Fin.sum_univ_two] <;> ring


-- @@ L117-125 verbatim
lemma ramifiedParabolic_character (t x : Eis) :
    complexCharacter (ramifiedParabolic t x)=
      eisEmbedding (symbol (-t) (1-3*t*x)) := by
  simp only [complexCharacter,MonoidHom.comp_apply,character,ramifiedParabolic]
  apply congrArg eisEmbedding
  apply symbol_congr
  refine ⟨t,?_⟩
  change (-3*t^2*x)-(-t)=(1-3*t*x)*t
  ring


-- @@ L127-139 verbatim
lemma ramifiedParabolic_omega_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic omega (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (A+B)) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega*ActualEisensteinCoordinates.eval A B=primaryCoord B (B-A) := by
    rw [primaryCoord_eq]
    change 1-3*omega*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*(B:Eis)*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  congr 2
  ring


-- @@ L141-160 verbatim
lemma ramifiedParabolic_omega_sq_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic (omega^2) (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (-(A+B))) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega^2*ActualEisensteinCoordinates.eval A B=primaryCoord (A-B) A := by
    rw [primaryCoord_eq]
    change 1-3*omega^2*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*((A:Eis)+(B:Eis)*omega-(B:Eis))*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) 2,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  have he : cubicExp (2*((A-B)*2+(-1)*A))=cubicExp (-(A+B)) := by
    apply cubicExp_eq_of_dvd_sub
    exact ⟨A-B,by ring⟩
  have hs : cubicExp ((A-B)*2+(-1)*A)^2=cubicExp (2*((A-B)*2+(-1)*A)) := by
    rw [pow_two,←cubicExp_add]
    congr 1
    ring
  convert congrArg eisEmbedding (hs.trans he) using 1 ; congr 2 ; ring_nf


-- @@ L162-163 verbatim
def ramifiedSourceFunction (t : Eis) (w : HyperbolicSpace) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix (lowerCuspMatrix t) • w)


-- @@ L165-166 verbatim
lemma ramifiedSourceFunction_continuous (t : Eis) : Continuous (ramifiedSourceFunction t) :=
  cubicSourceResidualFunction_continuous.comp (continuous_const_smul _)


-- @@ L168-179 verbatim
lemma ramifiedSourceFunction_translate (t x : Eis) (w : HyperbolicSpace) :
    ramifiedSourceFunction t (complexMatrix (upperTranslation x) • w)=
      eisEmbedding (symbol (-t) (1-3*t*x))*ramifiedSourceFunction t w := by
  have he := cubicSourceResidualFunction_automorphy
    (sourceLevelInclusion (ramifiedParabolic t x))
    (integralComplexMatrix (lowerCuspMatrix t) • w)
  rw [sourceLevelInclusion_character,ramifiedParabolic_character] at he
  change cubicSourceResidualFunction
    (integralComplexMatrix (ramifiedParabolic t x : SL(2,Eis)) •
      (integralComplexMatrix (lowerCuspMatrix t) • w))=_ at he
  rw [←mul_smul,←map_mul,ramifiedParabolic_mul_lower,map_mul,mul_smul] at he
  exact he


-- @@ L181-186 verbatim
lemma ramifiedSourceFunction_omega_translate (A B : ℤ) (w : HyperbolicSpace) :
    ramifiedSourceFunction omega
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (A+B))*ramifiedSourceFunction omega w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_value]


-- @@ L188-193 verbatim
lemma ramifiedSourceFunction_omega_sq_translate (A B : ℤ) (w : HyperbolicSpace) :
    ramifiedSourceFunction (omega^2)
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (-(A+B)))*ramifiedSourceFunction (omega^2) w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_sq_value]


-- @@ L195-195 verbatim
end


-- @@ L197-197 verbatim
section

-- @@ L198-198 verbatim
open MeasureTheory Filter

-- @@ L199-199 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L201-201 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicRamified

-- @@ L202-202 verbatim
open EisensteinEmbedding (omega3)

-- @@ L203-203 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L205-221 verbatim
lemma embedding_cubicExp (n : ℤ) :
    eisEmbedding (cubicExp n)=Complex.exp (2*Real.pi*Complex.I*(n:ℂ)/3) := by
  have hw : omega3=Complex.exp (2*Real.pi*Complex.I/3) := by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨-1,by push_cast;ring⟩
  rw [cubicExp,map_pow,eisEmbedding_omega_actual,hw,←Complex.exp_nat_mul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(n/3),?_⟩
  have hn : (n%3).toNat=(n%3) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hnc : ((n%3).toNat:ℂ)=((n%3:ℤ):ℂ) := by exact_mod_cast hn
  have he : ((n%3:ℤ):ℂ)=(n:ℂ)-3*((n/3:ℤ):ℂ) := by
    have he0 : n%3=n-3*(n/3) := by omega
    exact_mod_cast he0
  rw [hnc,he]
  push_cast
  ring


-- @@ L223-223 verbatim
def ramifiedShift10 : ℂ := eisEmbedding (omega-1)/(9*eisLam)


-- @@ L225-225 verbatim
def ramifiedShift19 : ℂ := eisEmbedding (-2-omega)/(9*eisLam)


-- @@ L227-232 verbatim
lemma ramifiedShift10_explicit : ramifiedShift10=-(omega3^2)/9 := by
  unfold ramifiedShift10
  apply (div_eq_iff (mul_ne_zero (by norm_num : (9:ℂ)≠0) eisLam_ne_zero)).mpr
  rw [map_sub,eisEmbedding_omega_actual,map_one]
  change omega3-1=-(omega3^2)/9*(9*(1+2*omega3))
  linear_combination (2*omega3-1)*EisensteinEmbedding.omega3_sq


-- @@ L234-239 verbatim
lemma ramifiedShift19_explicit : ramifiedShift19=omega3/9 := by
  unfold ramifiedShift19
  apply (div_eq_iff (mul_ne_zero (by norm_num : (9:ℂ)≠0) eisLam_ne_zero)).mpr
  rw [map_sub,map_neg,map_ofNat,eisEmbedding_omega_actual]
  change -2-omega3=omega3/9*(9*(1+2*omega3))
  linear_combination -2*EisensteinEmbedding.omega3_sq


-- @@ L241-260 verbatim
lemma ramifiedShift10_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (A+B)) := by
  have he : ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((omega-1)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift10,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((omega-1)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((omega-1)*ActualEisensteinCoordinates.eval A B)).2=A-2*B := by
    have hw : omega-1=ActualEisensteinCoordinates.eval (-1) 1 := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,one_mul]
      change omega-1=-1+omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,←embedding_cubicExp]
  exact congrArg eisEmbedding (cubicExp_eq_of_dvd_sub ⟨-B,by ring⟩)


-- @@ L262-280 verbatim
lemma ramifiedShift19_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (-(A+B))) := by
  have he : ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((-2-omega)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift19,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((-2-omega)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((-2-omega)*ActualEisensteinCoordinates.eval A B)).2=-(A+B) := by
    have hw : -2-omega=ActualEisensteinCoordinates.eval (-2) (-1) := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,Int.cast_ofNat,neg_mul,one_mul]
      change -2-omega=-2+-omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,embedding_cubicExp]


-- @@ L282-294 verbatim
lemma ramifiedSourceFunction_upper_shift10 (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction omega (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding x))*
        ramifiedSourceFunction omega (upperPoint z v hv) := by
  let A := (ActualEisensteinCoordinates.coords x).1
  let B := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval A B := (ActualEisensteinCoordinates.eval_coords x).symm
  rw [hx,ramifiedShift10_period]
  have he : upperPoint (z+3*eisEmbedding (ActualEisensteinCoordinates.eval A B)) v hv=
      complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace))
      (upperTranslation_section (ActualEisensteinCoordinates.eval A B) z v hv).symm
  rw [he,ramifiedSourceFunction_omega_translate]


-- @@ L296-308 verbatim
lemma ramifiedSourceFunction_upper_shift19 (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (omega^2) (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding x))*
        ramifiedSourceFunction (omega^2) (upperPoint z v hv) := by
  let A := (ActualEisensteinCoordinates.coords x).1
  let B := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval A B := (ActualEisensteinCoordinates.eval_coords x).symm
  rw [hx,ramifiedShift19_period]
  have he : upperPoint (z+3*eisEmbedding (ActualEisensteinCoordinates.eval A B)) v hv=
      complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace))
      (upperTranslation_section (ActualEisensteinCoordinates.eval A B) z v hv).symm
  rw [he,ramifiedSourceFunction_omega_sq_translate]


-- @@ L310-325 verbatim
lemma trace_dephase_periodic (f : ℂ→ℂ) (shift : ℂ)
    (hf : ∀ x : Eis,∀z, f (z+3*eisEmbedding x)=
      ShortDraftTrace.breveE (shift*(3*eisEmbedding x))*f z) :
    ∀x:Eis,∀z,(f (z+3*eisEmbedding x)*ShortDraftTrace.breveE (-shift*(z+3*eisEmbedding x)))=
      f z*ShortDraftTrace.breveE (-shift*z) := by
  intro x z
  rw [hf,mul_add,AddChar.map_add_eq_mul]
  have hn : -shift*(3*eisEmbedding x)=-(shift*(3*eisEmbedding x)) := by ring
  rw [hn,AddChar.map_neg_eq_inv]
  have hne : ShortDraftTrace.breveE (shift*(3*eisEmbedding x))≠0 :=
    Complex.exp_ne_zero _
  calc
    _ = (ShortDraftTrace.breveE (shift*(3*eisEmbedding x))*
      (ShortDraftTrace.breveE (shift*(3*eisEmbedding x)))⁻¹)*
        (f z*ShortDraftTrace.breveE (-shift*z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne,one_mul]


-- @@ L327-332 verbatim
lemma ramifiedSourceFunction_dephase10_periodic (v : ℝ) (hv : 0<v) :
    ∀x:Eis,∀z,ramifiedSourceFunction omega (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ramifiedShift10*(z+3*eisEmbedding x))=
    ramifiedSourceFunction omega (upperPoint z v hv)*ShortDraftTrace.breveE (-ramifiedShift10*z) :=
  trace_dephase_periodic (fun z => ramifiedSourceFunction omega (upperPoint z v hv))
    ramifiedShift10 (fun x z=>ramifiedSourceFunction_upper_shift10 x z v hv)


-- @@ L334-339 verbatim
lemma ramifiedSourceFunction_dephase19_periodic (v : ℝ) (hv : 0<v) :
    ∀x:Eis,∀z,ramifiedSourceFunction (omega^2) (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ramifiedShift19*(z+3*eisEmbedding x))=
    ramifiedSourceFunction (omega^2) (upperPoint z v hv)*ShortDraftTrace.breveE (-ramifiedShift19*z) :=
  trace_dephase_periodic (fun z => ramifiedSourceFunction (omega^2) (upperPoint z v hv))
    ramifiedShift19 (fun x z=>ramifiedSourceFunction_upper_shift19 x z v hv)


-- @@ L341-341 verbatim
end


-- @@ L343-343 verbatim
section

-- @@ L344-344 verbatim
open Filter MeasureTheory

-- @@ L345-345 verbatim
open scoped BigOperators Classical Topology MatrixGroups ENNReal


-- @@ L347-348 verbatim
def arbitraryCuspCompact (M : SL(2,ℂ)) (a b : ℝ) : Set HyperbolicSpace :=
  (M • ·) '' cuspHeightCompact a b


-- @@ L350-352 verbatim
lemma arbitraryCuspCompact_isCompact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    IsCompact (arbitraryCuspCompact M a b) :=
  (cuspHeightCompact_isCompact a b ha).image (continuous_const_smul M)


-- @@ L354-358 verbatim
lemma arbitraryCusp_image_restrict_le (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)≤
      (1:ℝ≥0∞) • hyperbolicVolume.restrict (arbitraryCuspCompact M a b) := by
  simpa only [one_smul,arbitraryCuspCompact] using Measure.restrict_mono_set hyperbolicVolume
    (Set.image_mono (cuspPeriodStrip_subset_heightCompact a b ha))


-- @@ L360-364 verbatim
lemma arbitraryCusp_smul_measurePreserving (M : SL(2,ℂ)) (a b : ℝ) :
    MeasurePreserving (M • ·) (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)) :=
  (measurePreserving_smul M hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul M) _


-- @@ L366-372 verbatim
def arbitraryCuspPullback (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    KernelQuotientL2→L[ℂ]CuspHeightStripL2 a b :=
  (Lp.compMeasurePreservingₗᵢ ℂ (M • ·) (arbitraryCusp_smul_measurePreserving M a b)).toContinuousLinearMap.comp
    ((dominatedComplexL2 (by simp : (1:ℝ≥0∞)≠⊤)
      (arbitraryCusp_image_restrict_le M a b ha)).comp
      (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha)))


-- @@ L374-387 verbatim
lemma arbitraryCuspPullback_ae (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (F : KernelQuotientL2) :
    arbitraryCuspPullback M a b ha F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel (M • w)) := by
  have h1 := dominatedComplexL2_ae (by simp : (1:ℝ≥0∞)≠⊤)
    (arbitraryCusp_image_restrict_le M a b ha)
    (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
      (arbitraryCuspCompact_isCompact M a b ha) F)
  have h2 := (Measure.absolutelyContinuous_of_le_smul
    (arbitraryCusp_image_restrict_le M a b ha)).ae_eq
      (kernelCompactPullbackCLM_ae (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha) F)
  exact (Lp.coeFn_compMeasurePreserving _ (arbitraryCusp_smul_measurePreserving M a b)).trans
    ((arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving.ae_eq_comp (h1.trans h2))


-- @@ L389-405 verbatim
lemma arbitraryCusp_quasiMeasurePreserving (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    Measure.QuasiMeasurePreserving
      (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) := by
  have hcompact : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (arbitraryCuspCompact M a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨measurable_integralOrbitProjection _,Measure.absolutelyContinuous_of_le_smul
      (kernelCompactMultiplicity_spec _ (arbitraryCuspCompact_isCompact M a b ha))⟩
  have himage : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨hcompact.measurable,((Measure.absolutelyContinuous_of_le_smul
      (arbitraryCusp_image_restrict_le M a b ha)).map
        (measurable_integralOrbitProjection _)).trans hcompact.absolutelyContinuous⟩
  exact himage.comp (arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving


-- @@ L407-408 verbatim
def arbitraryCuspQuotientCompact (M : SL(2,ℂ)) (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' arbitraryCuspCompact M a b


-- @@ L410-412 verbatim
lemma arbitraryCuspQuotientCompact_isCompact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    IsCompact (arbitraryCuspQuotientCompact M a b) :=
  (arbitraryCuspCompact_isCompact M a b ha).image (continuous_integralOrbitProjection _)


-- @@ L414-417 verbatim
lemma arbitraryCusp_mem_compact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (w : HyperbolicSpace) (hw : w∈cuspPeriodStrip a b) :
    integralOrbitProjection globalKubotaKernel (M • w)∈arbitraryCuspQuotientCompact M a b :=
  ⟨M • w,⟨w,cuspPeriodStrip_subset_heightCompact a b ha hw,rfl⟩,rfl⟩


-- @@ L419-419 verbatim
end


-- @@ L421-421 verbatim
section

-- @@ L422-422 verbatim
open Filter MeasureTheory

-- @@ L423-423 verbatim
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace ENNReal


-- @@ L425-427 verbatim
def arbitraryCuspWeightedPhase (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*ShortDraftTrace.breveE (-freq*hyperbolicHorizontal w)


-- @@ L429-437 verbatim
lemma arbitraryCuspWeightedPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    Continuous (arbitraryCuspWeightedPhase ρ freq) := by
  unfold arbitraryCuspWeightedPhase
  apply (ρ.continuous.comp hyperbolicHeight_continuous).mul
  change Continuous (fun w : HyperbolicSpace =>
    Complex.exp (2*Real.pi*Complex.I*((-freq*hyperbolicHorizontal w)+
      starRingEnd ℂ (-freq*hyperbolicHorizontal w))))
  have hh := hyperbolicHorizontal_continuous
  fun_prop


-- @@ L439-442 verbatim
lemma arbitraryCuspWeightedPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ‖arbitraryCuspWeightedPhase ρ freq w‖≤‖ρ‖ := by
  rw [arbitraryCuspWeightedPhase,norm_mul,breveE_norm,mul_one]
  exact ρ.norm_coe_le_norm _


-- @@ L444-450 verbatim
lemma arbitraryCuspFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    MemLp (fun w => star (arbitraryCuspWeightedPhase ρ freq w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  let := cuspPeriodStripFiniteVolume a b ha
  apply MemLp.of_bound (arbitraryCuspWeightedPhase_continuous ρ freq).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star];exact arbitraryCuspWeightedPhase_bound ρ freq w)


-- @@ L452-455 verbatim
def arbitraryCuspFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : CuspHeightStripL2 a b :=
  (arbitraryCuspFourierTest_memLp a b ha ρ freq).toLp
    (fun w => star (arbitraryCuspWeightedPhase ρ freq w))


-- @@ L457-460 verbatim
def arbitraryCuspHeightFourier (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq)).comp
    (arbitraryCuspPullback M a b ha)


-- @@ L462-474 verbatim
lemma arbitraryCuspHeightFourier_integral (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ freq F=
      ∫w in cuspPeriodStrip a b,
        F (integralOrbitProjection globalKubotaKernel (M • w))*
          arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  change inner ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq) (arbitraryCuspPullback M a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (arbitraryCuspFourierTest_memLp a b ha ρ freq),
    arbitraryCuspPullback_ae M a b ha F] with w hw hp
  rw [RCLike.inner_apply,arbitraryCuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]


-- @@ L476-489 verbatim
lemma arbitraryCuspHeightFourier_restrict (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ freq
      (kernelMassRestrictionCLM (arbitraryCuspQuotientCompact M a b)
        (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)=
      arbitraryCuspHeightFourier M a b ha ρ freq F := by
  rw [arbitraryCuspHeightFourier_integral,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (kernelMassRestriction_coe (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z*arbitraryCuspWeightedPhase ρ freq w)
    (hw.trans (Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm) _))


-- @@ L491-495 verbatim
def arbitraryCuspHeightFamily (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (s : ℂ) : ℂ :=
  arbitraryCuspHeightFourier M a b ha ρ freq
    (kernelLocalCorrectedSeed (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)


-- @@ L497-504 verbatim
lemma arbitraryCuspHeightFamily_analyticAt (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (arbitraryCuspHeightFamily M a b ha ρ freq) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (arbitraryCuspHeightFourier M a b ha ρ freq) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _
        (arbitraryCuspQuotientCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl


-- @@ L506-513 verbatim
lemma arbitraryCuspHeightFamily_residue_limit (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*arbitraryCuspHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have hh := (arbitraryCuspHeightFourier M a b ha ρ freq).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (arbitraryCuspQuotientCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,arbitraryCuspHeightFourier_restrict,
    arbitraryCuspHeightFamily] using hh


-- @@ L515-527 verbatim
lemma arbitraryCuspHeightFamily_initial (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    arbitraryCuspHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (M • w)*
        arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFamily,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm),kernelQuotientEisenstein_mk]


-- @@ L529-529 verbatim
end


-- @@ L531-531 verbatim
open Filter MeasureTheory

-- @@ L532-532 verbatim
open scoped BigOperators Classical Topology InnerProductSpace


-- @@ L534-541 verbatim
private lemma inner_projection_sandwich {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] G) (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x y : G) :
    inner ℂ x (A (K.starProjection (A.adjoint y))) =
      inner ℂ (A (K.starProjection (A.adjoint x))) y := by
  rw [← A.adjoint_inner_left, ← A.adjoint_inner_right]
  exact (K.inner_starProjection_left_eq_right _ _).symm


-- @@ L543-545 verbatim
lemma kernelThetaMassProjection_symmetric (F D : KernelQuotientL2) :
    inner ℂ F (kernelThetaMassProjection D)=inner ℂ (kernelThetaMassProjection F) D :=
  inner_projection_sandwich kernelEnergyMass kernelThetaNull F D


-- @@ L547-568 verbatim
lemma kernelThetaMassProjection_eigenvector (F : KernelQuotientL2)
    (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    kernelThetaMassProjection F=(9/17:ℂ) • F := by
  let u : kernelEnergyLaplacian.domain := ⟨F,LinearPMap.mem_domain_of_mem_graph hF⟩
  have hu : kernelEnergyLaplacian u=(8/9:ℂ) • F :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph u) hF rfl
  let E : KernelEnergyGraph := kernelVariationalSolution (kernelEnergyLaplacian u+u)
  have hE : E∈kernelThetaNull := by
    change kernelSpectralFormOperator (8/9:ℂ) E=0
    dsimp only [E]
    rw [kernelSpectralFormOperator_of_domain,hu]
    change kernelVariationalSolution ((8/9:ℂ) • F-(8/9:ℂ) • F)=0
    rw [sub_self,map_zero]
  have hmass : kernelEnergyMass E=F := kernelEnergyLaplacian_resolvent_relation u
  have hscale : kernelEnergyMass.adjoint F=(9/17:ℂ) • E := by
    dsimp [E]
    rw [hu]
    change kernelVariationalSolution F=(9/17:ℂ) • kernelVariationalSolution ((8/9:ℂ) • F+F)
    rw [map_add,map_smul,smul_add,smul_smul]
    module
  change kernelEnergyMass (kernelThetaNull.starProjection (kernelEnergyMass.adjoint F))=_
  rw [hscale,map_smul,kernelThetaNull.starProjection_eq_self_iff.mpr hE,map_smul,hmass]


-- @@ L570-577 verbatim
theorem kernelEisensteinResidueVector_pairing (a b : ℝ) (ha : 0<a) (hab : a<b)
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab)=
      (3/2:ℂ)*inner ℂ F (kernelL2Defect a b ha hab (4/3)) := by
  rw [kernelEisensteinResidueVector,inner_smul_right,kernelThetaMassProjection_symmetric,
    kernelThetaMassProjection_eigenvector F hF,inner_smul_left]
  simp only [map_div₀,map_ofNat]
  ring


-- @@ L579-583 verbatim
theorem kernelEisensteinResidueVector_orthogonal_of_defect (a b : ℝ) (ha : 0<a) (hab : a<b)
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (hzero : inner ℂ F (kernelL2Defect a b ha hab (4/3))=0) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab)=0 := by
  rw [kernelEisensteinResidueVector_pairing a b ha hab F hF,hzero,mul_zero]


-- @@ L585-585 verbatim
open Filter MeasureTheory

-- @@ L586-586 verbatim
open scoped BigOperators Classical Topology InnerProductSpace


-- @@ L588-604 verbatim
lemma kernelLocalCorrectedSeed_initial_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelLocalCorrectedSeed S hS a b (by linarith) hab s=
      kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 := kernelLocalCorrectedSeed_ae_eq S hS a b (by linarith) hab s
  have h2 := kernelLocalCorrectedSeed_ae_eq S hS c d (by linarith) hcd s
  have h3 := kernelEisensteinL2Correction_initial_overlap a b ha hab s hs hi
  have h4 := kernelEisensteinL2Correction_initial_overlap c d hc hcd s hs hi
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with q hq1 hq2 hq3 hq4
  rw [hq1,hq2]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed,hq3,hq4]
    ring
  · simp only [Set.indicator_of_notMem hq]


-- @@ L606-630 verbatim
lemma kernelLocalCorrectedSeed_cutoff_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    ∀s∈cuspUpperParameterRegion,
      kernelLocalCorrectedSeed S hS a b (by linarith) hab s=
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 : AnalyticOnNhd ℂ
      (kernelLocalCorrectedSeed S hS a b (by linarith) hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelLocalCorrectedSeed_analyticAt_nonreal S hS a b (by linarith) hab s
      (by linarith [hs.1]) hs.2.ne'
  have h2 : AnalyticOnNhd ℂ
      (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) cuspUpperParameterRegion := by
    intro s hs
    exact kernelLocalCorrectedSeed_analyticAt_nonreal S hS c d (by linarith) hcd s
      (by linarith [hs.1]) hs.2.ne'
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have he : (kernelLocalCorrectedSeed S hS a b (by linarith) hab)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLocalCorrectedSeed_initial_eq S hS a b c d ha hab hc hcd s hs.1 hs.2
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) he


-- @@ L632-655 verbatim
lemma kernelEisensteinResidueVector_restrict_cutoff_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector a b (by linarith) hab)=
      kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector c d (by linarith) hcd) := by
  have h1 := (kernelLocalCorrectedSeed_residue_limit S hS a b (by linarith) hab).comp
    thetaApproach_tendsto_complex_punctured
  have h2 := (kernelLocalCorrectedSeed_residue_limit S hS c d (by linarith) hcd).comp
    thetaApproach_tendsto_complex_punctured
  have he : (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS a b (by linarith) hab
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    rw [kernelLocalCorrectedSeed_cutoff_eq S hS a b c d ha hab hc hcd _
      (by constructor <;> simp [] <;> linarith)]
  exact tendsto_nhds_unique h1 (h2.congr' he.symm)


-- @@ L657-676 verbatim
lemma kernelL2_eq_of_compact_restrictions (F G : KernelQuotientL2)
    (h : ∀S : Set KernelQuotient, ∀hS : IsCompact S,
      kernelMassRestrictionCLM S hS.measurableSet F=
        kernelMassRestrictionCLM S hS.measurableSet G) : F=G := by
  let S : ℕ→Set KernelQuotient := fun n => {q | kernelQuotientBarrier 2 3 q≤n}
  have hS (n : ℕ) : IsCompact (S n) := kernelBarrier_sublevel_isCompact n
  have he (n : ℕ) : ∀ᵐq∂integralQuotientVolume globalKubotaKernel, q∈S n → F q=G q := by
    have hi := h (S n) (hS n)
    have hf := kernelMassRestriction_coe (S n) (hS n).measurableSet F
    have hg := kernelMassRestriction_coe (S n) (hS n).measurableSet G
    filter_upwards [hf,hg] with q hf hg hq
    rw [Set.indicator_of_mem hq] at hf hg
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet F q=F q at hf
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet G q=G q at hg
    rw [hi] at hf
    exact hf.symm.trans hg
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with q hq
  obtain ⟨n,hn⟩ := exists_nat_ge (kernelQuotientBarrier 2 3 q)
  exact hq n hn


-- @@ L678-684 verbatim
theorem kernelEisensteinResidueVector_cutoff_independent
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    kernelEisensteinResidueVector a b (by linarith) hab=
      kernelEisensteinResidueVector c d (by linarith) hcd := by
  apply kernelL2_eq_of_compact_restrictions
  intro S hS
  exact kernelEisensteinResidueVector_restrict_cutoff_eq S hS a b c d ha hab hc hcd


-- @@ L686-686 verbatim
end CubicEisenstein


-- @@ L688-688 verbatim
end


-- @@ L690-690 verbatim
end OAI
