import OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceEnergy


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


-- @@ L80-80 verbatim
open scoped Classical MatrixGroups BigOperators

-- @@ L81-81 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L82-82 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L84-93 verbatim
lemma positive_cube_cpow_third (r:ℝ) (hr:0<r) :
    ((r^3:ℝ):ℂ)^(1/3:ℂ)=(r:ℂ) := by
  calc
    _=(((r^3)^(1/3:ℝ):ℝ):ℂ):=by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow (pow_nonneg hr.le 3) (1/3)).symm
    _=_:=by
      congr 1
      rw [←Real.rpow_natCast_mul hr.le 3]
      norm_num


-- @@ L95-110 verbatim
lemma cubicBesselNormalizer_mul_cube (h p:Eis) (hp:p≠0) :
    cubicBesselNormalizer (h*p^3)=(‖eisEmbedding p‖:ℂ)*cubicBesselNormalizer h := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have ha:0≤2*Real.pi*‖cuspFrequency h‖:=by positivity
  have he:(2*Real.pi*‖cuspFrequency (h*p^3)‖:ℂ)=
      ((‖eisEmbedding p‖^3:ℝ):ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by
    rw [hf]
    push_cast
    ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr.le 3) ha,
    positive_cube_cpow_third _ hr]
  push_cast
  ring


-- @@ L112-114 verbatim
lemma eisenstein_norm_eq_sqrt_norm (p:Eis) :
    ‖eisEmbedding p‖=Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]


-- @@ L116-123 verbatim
theorem sourceResidualFourierCoefficient_cube_sqrt (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ):ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh,
    eisenstein_norm_eq_sqrt_norm]


-- @@ L125-134 verbatim
theorem sourceArithmeticResidue_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) : sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h := by
  have ht:=sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh
  unfold sourceResidualFourierCoefficient at ht
  rw [cubicBesselNormalizer_mul_cube h p hp] at ht
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ (mul_ne_zero hr (cubicBesselNormalizer_ne_zero h hh))
  simpa only [mul_assoc] using ht


-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
open MeasureTheory

-- @@ L139-139 verbatim
open scoped Classical MatrixGroups BigOperators

-- @@ L140-140 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree

-- @@ L141-141 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L143-145 verbatim
def cubeSourceDifference (p:Eis) (hp:p≠0) (w:HyperbolicSpace) : ℂ :=
  cubeAverage p hp cubicSourceResidualFunction w-
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w


-- @@ L147-150 verbatim
lemma cubeSourceDifference_continuous (p:Eis) (hp:p≠0) :
    Continuous (cubeSourceDifference p hp) :=
  (cubeAverage_continuous p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous).sub
    (continuous_const.mul cubicSourceResidualFunction_continuous)


-- @@ L152-156 verbatim
lemma cubeSourceDifference_period_three (p:Eis) (hp:p≠0) (n:Eis) (w:HyperbolicSpace) :
    cubeSourceDifference p hp (complexTranslation (3*eisEmbedding n) • w)=cubeSourceDifference p hp w := by
  unfold cubeSourceDifference
  rw [cubeAverage_period_three p hp cubicSourceResidualFunction cubicSource_period_three,
    cubicSource_period_three]


-- @@ L158-162 verbatim
lemma cubeSourceDifference_period_one (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1) (w:HyperbolicSpace) :
    cubeSourceDifference p hp (complexTranslation 1 • w)=cubeSourceDifference p hp w := by
  unfold cubeSourceDifference
  rw [cubeAverage_period_one p hp hprimary cubicSourceResidualFunction cubicSource_period_three cubicSource_period_one,
    cubicSource_period_one]


-- @@ L164-170 verbatim
lemma sourceCusp_period_nine (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (z+9*eisEmbedding n) v hv)=
      cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv) := by
  have h:=sourceCusp_scaled_periodic M v hv n (z/3)
  have h1:3*(z/3+3*eisEmbedding n)=z+9*eisEmbedding n:=by ring
  have h0:3*(z/3)=z:=by ring
  simpa only [h1,h0] using h


-- @@ L172-201 verbatim
lemma cubeSource_summand_cusp_period {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv))=
    cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint z v hv)) := by
  let T:=cubeCuspTriangular d hp
  let V:=v/‖T 1 1‖^2
  have hV:0<V:=div_pos hv (cubeCuspTriangular_norm_sq_pos d hp)
  have he (x:ℂ):cubicSourceResidualFunction (cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint x v hv))=
    cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*x+T 0 1)/T 1 1) V hV):=by
    rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
      complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  have hx:(T 0 0*(z+9*eisEmbedding (p^3*n))+T 0 1)/T 1 1=
      (T 0 0*z+T 0 1)/T 1 1+9*eisEmbedding (p^(2*d.exponent.val)*n):=by
    calc
      _=(T 0 0*z+T 0 1)/T 1 1+9*((T 0 0/T 1 1)*eisEmbedding (p^3))*eisEmbedding n:=by
        rw [map_mul]
        ring
      _=_:=by rw [cubeCuspTriangular_integral_scale d hp,map_mul];ring
  calc
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*(z+9*eisEmbedding (p^3*n))+T 0 1)/T 1 1) V hV):=he _
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*z+T 0 1)/T 1 1+9*eisEmbedding (p^(2*d.exponent.val)*n)) V hV):=by rw [hx]
    _=cubicSourceResidualFunction (integralComplexMatrix d.matrix •
      upperPoint ((T 0 0*z+T 0 1)/T 1 1) V hV):=sourceCusp_period_nine d.matrix _ V hV _
    _=_:=(he z).symm


-- @@ L203-215 verbatim
lemma cubeSourceDifference_cusp_period (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) (n:Eis) :
    cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv)=
    cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv) := by
  have hU:cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (z+9*eisEmbedding (p^3*n)) v hv)=
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv):=by
    exact congrArg (fun t:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*t)
      (tsum_congr (fun r:Eis⧸Ideal.span {p^3}=>cubeSource_summand_cusp_period
        (actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary) hp.ne_zero z v hv n))
  exact congrArg₂ (fun a b:ℂ=>a-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*b)
    hU (sourceCusp_period_nine M z v hv (p^3*n))


-- @@ L217-221 verbatim
lemma cubeSourceDifference_cusp_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeSourceDifference p hp.ne_zero
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=0 :=
  cubeSource_difference_average_zero M p hp hprimary v hv


-- @@ L223-230 verbatim
lemma cubeSourceDifference_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤
      (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 :=
  cubeSource_difference_decay_from_representatives p hp hprimary K hK hrep M z v hv hv1


-- @@ L232-232 verbatim
end CubicEisenstein


-- @@ L234-234 verbatim
open scoped Classical


-- @@ L236-236 verbatim
namespace FiniteAutomorphismCover


-- @@ L238-238 verbatim
variable {G : Type*} [Group G] {ι : Type*}


-- @@ L240-241 verbatim
def common (K R : Subgroup G) (a : ι → G ≃* G) : Subgroup G :=
  K ⊓ ⨅i, R.comap (a i).toMonoidHom


-- @@ L243-244 verbatim
lemma common_le (K R : Subgroup G) (a : ι → G ≃* G) : common K R a ≤ K :=
  inf_le_left


-- @@ L246-248 verbatim
lemma common_le_preimage (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    common K R a ≤ R.comap (a i).toMonoidHom :=
  inf_le_right.trans (iInf_le _ i)


-- @@ L250-255 verbatim
instance common_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] : (common K R a).FiniteIndex := by
  let : (⨅i, R.comap (a i).toMonoidHom).FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun i => inferInstance)
  unfold common
  infer_instance


-- @@ L257-260 verbatim
def toSource (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : common K R a →* R where
  toFun h := ⟨a i (h : G), common_le_preimage K R a i h.property⟩
  map_one' := Subtype.ext (map_one (a i))
  map_mul' x y := Subtype.ext (map_mul (a i) (x : G) (y : G))


-- @@ L262-263 verbatim
@[simp] lemma toSource_coe (K R : Subgroup G) (a : ι → G ≃* G) (i : ι)
    (h : common K R a) : (toSource K R a i h : G) = a i (h : G) := rfl


-- @@ L265-269 verbatim
lemma toSource_injective (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    Function.Injective (toSource K R a i) := by
  intro x y hxy
  apply Subtype.ext
  exact (a i).injective (congrArg (fun r : R => (r : G)) hxy)


-- @@ L271-282 verbatim
lemma toSource_range (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    (toSource K R a i).range =
      (common K R a).comap ((a i).symm.toMonoidHom.comp R.subtype) := by
  ext r
  constructor
  · rintro ⟨h,rfl⟩
    change (a i).symm (a i (h : G)) ∈ common K R a
    simpa only [MulEquiv.symm_apply_apply] using h.property
  · intro hr
    refine ⟨⟨(a i).symm (r : G),hr⟩,?_⟩
    apply Subtype.ext
    exact (a i).apply_symm_apply (r : G)


-- @@ L284-287 verbatim
instance toSource_range_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] (i : ι) : (toSource K R a i).range.FiniteIndex := by
  rw [toSource_range]
  infer_instance


-- @@ L289-291 verbatim
def hom (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a →* G :=
  lengthScale.subtype.comp (e.toMonoidHom.comp (toSource K R a i))


-- @@ L293-295 verbatim
@[simp] lemma hom_apply (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    hom K R lengthScale a e i h = (e (toSource K R a i h) : G) := rfl


-- @@ L297-299 verbatim
lemma hom_injective (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    Function.Injective (hom K R lengthScale a e i) :=
  lengthScale.subtype_injective.comp (e.injective.comp (toSource_injective K R a i))


-- @@ L301-302 verbatim
def target (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) : Subgroup G :=
  (hom K R lengthScale a e i).range


-- @@ L304-307 verbatim
lemma target_le (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i ≤ lengthScale := by
  rintro x ⟨h,rfl⟩
  exact (e (toSource K R a i h)).property


-- @@ L309-311 verbatim
lemma target_le_common_ambient (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) (hLK : lengthScale ≤ K) (i : ι) : target K R lengthScale a e i ≤ K :=
  (target_le K R lengthScale a e i).trans hLK


-- @@ L313-315 verbatim
lemma target_eq_map (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i = ((toSource K R a i).range.map e.toMonoidHom).map lengthScale.subtype := by
  rw [target,hom,MonoidHom.range_comp,MonoidHom.range_comp]


-- @@ L317-324 verbatim
instance target_finiteIndex [Finite ι] (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) [K.FiniteIndex] [R.FiniteIndex] [lengthScale.FiniteIndex] (i : ι) :
    (target K R lengthScale a e i).FiniteIndex := by
  let : ((toSource K R a i).range.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective _ e.surjective
  constructor
  rw [target_eq_map,Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero


-- @@ L326-328 verbatim
def equiv (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a ≃* target K R lengthScale a e i :=
  MonoidHom.ofInjective (hom_injective K R lengthScale a e i)


-- @@ L330-332 verbatim
@[simp] lemma equiv_coe (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    (equiv K R lengthScale a e i h : G) = (e (toSource K R a i h) : G) := rfl


-- @@ L334-334 verbatim
end FiniteAutomorphismCover


-- @@ L336-336 verbatim
namespace CubicKubota

-- @@ L337-337 verbatim
open scoped BigOperators Classical MatrixGroups


-- @@ L339-339 verbatim
open CubicEisenstein ConcreteTraceCRT

-- @@ L340-340 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L342-381 verbatim
lemma literalCube_zero_pair (p : ActualEisensteinCubic.O) (hp : p≠0) (x : cubeKernelCorrespondence p) :
    cubeAverageMatrix p hp 0*integralComplexMatrix (cubeKernelRightGlobal p hp x)=
      integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0 := by
  let M := cubeKernelLeftGlobal p x
  let N := cubeKernelRightGlobal p hp x
  let z := cubeDilationRoot p
  have hz : z^2=eisEmbedding p^3 := cubeDilationRoot_sq p
  have hz0 : z≠0 := cubeDilationRoot_ne_zero p hp
  have he := cubeCorrespondence_entries p x.1
  change p^3*M 0 0=N 0 0*p^3 ∧ p^3*M 0 1=N 0 1 ∧
    M 1 0=N 1 0*p^3 ∧ M 1 1=N 1 1 at he
  have h00 : eisEmbedding (M 0 0)=eisEmbedding (N 0 0) :=
    congrArg eisEmbedding (mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _)))
  have h01 := congrArg eisEmbedding he.2.1
  have h10 := congrArg eisEmbedding he.2.2.1
  have h11 := congrArg eisEmbedding he.2.2.2
  simp only [map_mul,map_pow] at h01 h10
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      cubeAverageMatrix_entries,integralComplexMatrix_apply]
  · change z⁻¹*eisEmbedding (N 0 0)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 0)=
      eisEmbedding (M 0 0)*z⁻¹+eisEmbedding (M 0 1)*0
    rw [h00,map_zero]
    ring
  · change z⁻¹*eisEmbedding (N 0 1)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 1)=
      eisEmbedding (M 0 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 0 1)*z
    rw [←h01,←hz,map_zero]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 0)+z*eisEmbedding (N 1 0)=
      eisEmbedding (M 1 0)*z⁻¹+eisEmbedding (M 1 1)*0
    rw [h10,←hz]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 1)+z*eisEmbedding (N 1 1)=
      eisEmbedding (M 1 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 1 1)*z
    rw [h11,map_zero]
    ring


-- @@ L383-392 verbatim
theorem literalCube_zero_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp).symm (cubeAverageMatrix p hp 0) := by
  intro r
  let x := (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp)).symm r
  have hr : cubeKernelRightGlobal p hp x=(r:SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelRightGlobal_injective p hp) r
  change cubeAverageMatrix p hp 0*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0
  rw [←hr]
  exact literalCube_zero_pair p hp x


-- @@ L394-399 verbatim
lemma cubeTranslation_complex (q : ActualEisensteinCubic.O) :
    integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O))=complexTranslation (3*eisEmbedding q) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [integralComplexMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [upperTranslation, complexTranslation, map_ofNat]


-- @@ L401-409 verbatim
lemma cubeAverageMatrix_factor_zero (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O) :
    cubeAverageMatrix p hp q=cubeAverageMatrix p hp 0*
      integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
  rw [cubeTranslation_complex]
  have h0 : complexTranslation 0=1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  simp only [cubeAverageMatrix,map_zero,mul_zero,h0,mul_one]


-- @@ L411-419 verbatim
theorem literalCube_summand_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O)
    (A : SL(2,ActualEisensteinCubic.O)) (r : (cubeKernelRightGlobal p hp).range)
    (hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*A=(r:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix ((cubeKernelRangeEquiv p hp).symm r:SL(2,ActualEisensteinCubic.O))*cubeAverageMatrix p hp q := by
  have hAc := congrArg integralComplexMatrix hA
  simp only [map_mul] at hAc
  rw [cubeAverageMatrix_factor_zero,mul_assoc,hAc,←mul_assoc,
    literalCube_zero_intertwines p hp r,mul_assoc]


-- @@ L421-421 verbatim
end CubicKubota


-- @@ L423-423 verbatim
namespace CubicEisenstein

-- @@ L424-424 verbatim
open Filter MeasureTheory

-- @@ L425-425 verbatim
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace

-- @@ L426-426 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L428-428 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L430-437 verbatim
lemma integralCoverIntertwines_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) :
    IntegralCoverIntertwines (e.trans f) (h*g) := by
  intro x
  change (h*g)*integralComplexMatrix (x:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (f (e x):SL(2,ActualEisensteinCubic.O))*(h*g)
  rw [mul_assoc,he x,←mul_assoc,hf (e x),mul_assoc]


-- @@ L439-448 verbatim
lemma integralConjugateMap_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap f h hf (integralConjugateMap e g he q)=
      integralConjugateMap (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection K (h•(g•w))=integralOrbitProjection K ((h*g)•w)
    rw [mul_smul]


-- @@ L450-464 verbatim
lemma integralConjugatePullback_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (hK : K≤CubicKubota.levelThree) (F : IntegralQuotientL2 K) :
    integralConjugatePullback e g he hH hJ (integralConjugatePullback f h hf hJ hK F)=
      integralConjugatePullback (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) hH hK F := by
  apply Lp.ext
  have hinner := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp
    (integralConjugatePullback_ae f h hf hJ hK F)
  filter_upwards [integralConjugatePullback_ae e g he hH hJ (integralConjugatePullback f h hf hJ hK F),
    hinner,integralConjugatePullback_ae (e.trans f) (h*g)
      (integralCoverIntertwines_trans e f g h he hf) hH hK F] with q ho hi ht
  dsimp only [Function.comp_def] at hi
  rw [ho,hi,ht,integralConjugateMap_trans]


-- @@ L466-473 verbatim
def kernelCoverLeg {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 H :=
  (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree)


-- @@ L475-489 verbatim
lemma kernelCoverLeg_representative {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCoverLeg hHK hJK e g he F=ᵐ[integralQuotientVolume H]
      fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)) := by
  have hc := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  exact (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hc)


-- @@ L491-507 verbatim
lemma kernelCoverLeg_adjoint_apply {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : IntegralQuotientL2 H) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) F=
      integralCoverTrace hJK globalKubotaKernel_le_levelThree
        (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
          (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) F) := by
  apply ext_inner_right ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ F (integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))=_
  rw [integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm


-- @@ L509-531 verbatim
theorem kernelCoverLeg_adjoint_comp {H Ji Jj : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hiK : Ji≤globalKubotaKernel) (hjK : Jj≤globalKubotaKernel)
    [Ji.IsFiniteRelIndex globalKubotaKernel] [Jj.IsFiniteRelIndex globalKubotaKernel]
    (ei : H≃*Ji) (ej : H≃*Jj) (gi gj : SL(2,ℂ))
    (hei : IntegralCoverIntertwines ei gi) (hej : IntegralCoverIntertwines ej gj) :
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)).comp
      (kernelCoverLeg hHK hiK ei gi hei)=
        kernelCorrespondenceL2 hjK hiK (ej.symm.trans ei) (gi*gj⁻¹)
          (integralCoverIntertwines_trans ej.symm ei gj⁻¹ gi
            (integralCoverIntertwines_inverse ej gj hej) hei) := by
  apply ContinuousLinearMap.ext
  intro F
  change ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)
    (kernelCoverLeg hHK hiK ei gi hei F)=_
  rw [kernelCoverLeg_adjoint_apply]
  change integralCoverTrace hjK globalKubotaKernel_le_levelThree
    (integralConjugatePullback ej.symm gj⁻¹ (integralCoverIntertwines_inverse ej gj hej)
      (hjK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)
      (integralConjugatePullback ei gi hei
        (hHK.trans globalKubotaKernel_le_levelThree) (hiK.trans globalKubotaKernel_le_levelThree)
        (integralCoverPullback hiK globalKubotaKernel_le_levelThree F)))=_
  rw [integralConjugatePullback_trans]
  rfl


-- @@ L533-533 verbatim
end CubicEisenstein


-- @@ L535-535 verbatim
open scoped Classical MatrixGroups BigOperators


-- @@ L537-537 verbatim
namespace CubicKubota

-- @@ L538-538 verbatim
open CubicEisenstein ConcreteTraceCRT

-- @@ L539-539 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L541-541 verbatim
abbrev CubeResidues (p : ActualEisensteinCubic.O) := ActualEisensteinCubic.O ⧸ Ideal.span {p^3}


-- @@ L543-544 verbatim
def cubeCommonAutomorphism (p : ActualEisensteinCubic.O) (r : CubeResidues p) : SL(2,ActualEisensteinCubic.O) ≃* SL(2,ActualEisensteinCubic.O) :=
  MulAut.conj (upperTranslation (GaussianShiftedPartition.representative (p^3) r):SL(2,ActualEisensteinCubic.O))


-- @@ L546-548 verbatim
def cubeCommonCover (p : ActualEisensteinCubic.O) (hp : p≠0) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.common globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p)


-- @@ L550-551 verbatim
lemma cubeCommonCover_le (p : ActualEisensteinCubic.O) (hp : p≠0) : cubeCommonCover p hp≤globalKubotaKernel :=
  FiniteAutomorphismCover.common_le _ _ _


-- @@ L553-557 verbatim
lemma cubeCommonCover_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) : (cubeCommonCover p hp).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.common_finiteIndex _ _ _


-- @@ L559-562 verbatim
def cubeCommonTarget (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.target globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r


-- @@ L564-566 verbatim
lemma cubeCommonTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonTarget p hp r≤globalKubotaKernel :=
  FiniteAutomorphismCover.target_le_common_ambient _ _ _ _ _ (cubeKernelLeftGlobal_le p) r


-- @@ L568-574 verbatim
lemma cubeCommonTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    (cubeCommonTarget p hp r).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).1
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.target_finiteIndex _ _ _ _ _ r


-- @@ L576-580 verbatim
def cubeCommonEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonCover p hp≃*cubeCommonTarget p hp r :=
  FiniteAutomorphismCover.equiv globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r


-- @@ L582-595 verbatim
lemma cubeCommon_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    IntegralCoverIntertwines (cubeCommonEquiv p hp r)
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)) := by
  intro h
  let q := GaussianShiftedPartition.representative (p^3) r
  let rh := FiniteAutomorphismCover.toSource globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p) r h
  have hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      (rh:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
    change (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      ((upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))⁻¹)*
        (upperTranslation q:SL(2,ActualEisensteinCubic.O))
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  exact literalCube_summand_intertwines p hp q (h:SL(2,ActualEisensteinCubic.O)) rh hA


-- @@ L597-605 verbatim
def cubeCommonLeg (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 (cubeCommonCover p hp) := by
  letI := cubeCommonTarget_finiteIndex p hp r
  letI : (cubeCommonTarget p hp r).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p hp) (cubeCommonTarget_le p hp r)
    (cubeCommonEquiv p hp r)
    (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r))
    (cubeCommon_intertwines p hp r)


-- @@ L607-607 verbatim
end CubicKubota


-- @@ L609-609 verbatim
end


-- @@ L611-611 verbatim
end OAI
