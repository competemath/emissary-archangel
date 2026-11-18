import OAI.NumberTheory.DirichletL.Eisenstein.SourceQuotient


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
open scoped BigOperators Classical MatrixGroups Matrix

-- @@ L81-81 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

-- @@ L82-82 verbatim
open PrimaryIdealUnitReindex (GoodIdeal)

-- @@ L83-83 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L85-85 verbatim
abbrev PrimaryLower:={c:Eis//(3:Eis)∣c-1}

-- @@ L86-86 verbatim
abbrev OppositeData:=Σc:PrimaryLower,{x:Eis//IsCoprime c.val x}


-- @@ L88-88 verbatim
lemma primaryLower_primary (c:PrimaryLower):lambda^2∣c.val-1:=lambda_sq_dvd_three.trans c.2

-- @@ L89-89 verbatim
lemma primaryLower_ne_zero (c:PrimaryLower):c.val≠0:=primary_ne_zero c.val (primaryLower_primary c)


-- @@ L91-96 verbatim
def oppositeDataToPrimitive (p:OppositeData):PrimitiveRow:=
  ⟨![-3*p.2.val,p.1.val],by
    change IsCoprime (-3*p.2.val) p.1.val ∧ (3:Eis)∣-3*p.2.val ∧ (3:Eis)∣p.1.val-1
    refine ⟨?_,⟨-p.2.val,by ring⟩,p.1.2⟩
    simpa only [neg_mul] using
      ((primary_coprime_three p.1.val (primaryLower_primary p.1)).mul_right p.2.2).symm.neg_left⟩


-- @@ L98-123 verbatim
lemma oppositeDataToPrimitive_bijective:Function.Bijective oppositeDataToPrimitive:=by
  constructor
  · rintro ⟨c,x,hx⟩ ⟨d,y,hy⟩ h
    have hrow:=congrArg Subtype.val h
    have hcd:c=d:=by
      apply Subtype.ext
      exact congrFun hrow 1
    subst d
    have hxy:x=y:=by
      have he:-(3:Eis)*x=-(3:Eis)*y:=congrFun hrow 0
      exact mul_left_cancel₀ (by norm_num : -(3:Eis)≠0) he
    subst y
    rfl
  · intro r
    obtain ⟨t,ht⟩:=r.2.2.1
    let c:PrimaryLower:=⟨r.1 1,r.2.2.2⟩
    have hx:IsCoprime c.val (-t):=by
      have hh:IsCoprime c.val (3*t):=by simpa only [c,ht] using r.2.1.symm
      exact (hh.of_isCoprime_of_dvd_right (dvd_mul_left t 3)).neg_right
    refine ⟨⟨c,-t,hx⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change -3*(-t)=r.1 0
      rw [ht]
      ring
    · rfl


-- @@ L125-126 verbatim
def oppositeDataEquiv:OppositeData≃PrimitiveRow:=
  Equiv.ofBijective oppositeDataToPrimitive oppositeDataToPrimitive_bijective


-- @@ L128-128 verbatim
def oppositeMatrix:SL(2,ℂ):=⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩


-- @@ L130-133 verbatim
lemma rowOperator_opposite (v:Fin 2→ℂ):rowOperator oppositeMatrix v=![v 1,-v 0]:=by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [oppositeMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_two]


-- @@ L135-136 verbatim
def oppositeEisenstein (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):ℂ:=
  eisenstein (oppositeMatrix*upperSection z v hv) s


-- @@ L138-155 verbatim
lemma rowHeight_eq_shiftedHeightKernel (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c d:Eis) (hc:c≠0):
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s=
      ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z:=by
  have hc':=eisEmbedding_ne_zero hc
  have hnorm:0<‖eisEmbedding c‖^2:=sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac:eisEmbedding c*z+eisEmbedding d=eisEmbedding c*(z+eisEmbedding d/eisEmbedding c):=by field_simp
  have heq:v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2)=
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹:=by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ;ring
  unfold shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),←Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring


-- @@ L157-159 verbatim
def oppositeTerm (z:ℂ) (v:ℝ) (s:ℂ) (c x:Eis):ℂ:=
  eisEmbedding (symbol (3*x) c)*
    ((v/(‖eisEmbedding c*z+eisEmbedding (3*x)‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s


-- @@ L161-167 verbatim
lemma oppositeTerm_eq_shifted (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c x:Eis) (hc:c≠0):
    oppositeTerm z v s c x=
      (eisEmbedding (symbol (3*x) c)*((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s))*
        shiftedHeightKernel v s (eisEmbedding (3*x)/eisEmbedding c) z:=by
  rw [oppositeTerm,rowHeight_eq_shiftedHeightKernel z v hv s c (3*x) hc]
  ring


-- @@ L169-196 verbatim
lemma opposite_summand (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OppositeData):
    summand (oppositeMatrix*upperSection z v hv) s
      (primitiveRowEquiv.symm (oppositeDataEquiv p))=
      oppositeTerm z v s p.1.val p.2.val:=by
  let r:Fin 2→ℂ:=![eisEmbedding p.1.val,eisEmbedding (3*p.2.val)]
  have hr:rowOperator oppositeMatrix
      (embeddedRow (primitiveRowEquiv.symm (oppositeDataEquiv p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_opposite]
    funext i
    fin_cases i <;>
      simp [oppositeDataEquiv, Equiv.ofBijective_apply, oppositeDataToPrimitive, r, map_mul]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 0
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.1) he
  have hp:0<heightDenominator z v r:=heightDenominator_pos z v hv r hr0
  have hphase:(cosetCharacter (primitiveRowEquiv.symm (oppositeDataEquiv p)))⁻¹=
      eisEmbedding (symbol (3*p.2.val) p.1.val):=by
    rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (-3*p.2.val) p.1.val)=_
    rw [neg_mul,symbol_neg_numerator _ _ (primaryLower_primary p.1)]
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,hphase]
  change _=eisEmbedding (symbol (3*p.2.val) p.1.val)*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]


-- @@ L198-202 verbatim
theorem oppositeEisenstein_eq_rows (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):
    oppositeEisenstein z v hv s=∑'p:OppositeData,oppositeTerm z v s p.1.val p.2.val:=by
  rw [oppositeEisenstein,eisenstein,←primitiveRowEquiv.symm.tsum_eq,
    ←oppositeDataEquiv.tsum_eq]
  exact tsum_congr (opposite_summand z v hv s)


-- @@ L204-208 verbatim
theorem opposite_rows_summable_norm (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re):
    Summable (fun p:OppositeData=>‖oppositeTerm z v s p.1.val p.2.val‖):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).summable_iff.mpr
    (summable_norm_summand (oppositeMatrix*upperSection z v hv) s hs)
  exact hh.congr (fun p=>congrArg norm (opposite_summand z v hv s p))


-- @@ L210-214 verbatim
def primaryLowerIdealEquiv:PrimaryLower≃GoodIdeal where
  toFun c:=⟨Ideal.span {c.val},by rw [primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c)];exact primaryLower_ne_zero c⟩
  invFun I:=⟨primaryGenerator I.val,three_dvd_primary_sub_one _ (primaryGenerator_spec I.val I.2).2⟩
  left_inv c:=Subtype.ext (primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c))
  right_inv I:=Subtype.ext (primaryGenerator_spec I.val I.2).1


-- @@ L216-216 verbatim
end


-- @@ L218-218 verbatim
section


-- @@ L220-220 verbatim
open scoped BigOperators Classical

-- @@ L221-221 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

-- @@ L222-222 verbatim
open PrimaryIdealUnitReindex (GoodIdeal)

-- @@ L223-223 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L225-225 verbatim
abbrev CoprimeElement (c:Eis):={x:Eis//IsCoprime c x}


-- @@ L227-233 verbatim
def cubicResidueElementMap (c:Eis) (p:CubicUnitResidue c×Eis):CoprimeElement c:=
  ⟨GaussianShiftedPartition.representative c p.1.val+c*p.2,by
    apply (isUnit_quotient_span_iff c _).mp
    have hc:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [map_add,map_mul,hc,zero_mul,add_zero,
      GaussianShiftedPartition.representative_spec] using p.1.2⟩


-- @@ L235-264 verbatim
lemma cubicResidueElementMap_bijective (c:Eis) (hc:c≠0):
    Function.Bijective (cubicResidueElementMap c):=by
  have hmod (r:CubicUnitResidue c) (n:Eis):
      Ideal.Quotient.mk (Ideal.span {c})
        (GaussianShiftedPartition.representative c r.val+c*n)=r.val:=by
    have hzero:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add,map_mul,hzero,zero_mul,add_zero,GaussianShiftedPartition.representative_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ h
    have he:=congrArg Subtype.val h
    change GaussianShiftedPartition.representative c r.val+c*n=
      GaussianShiftedPartition.representative c t.val+c*m at he
    have hrt:r=t:=Subtype.ext (by
      simpa only [hmod] using congrArg (Ideal.Quotient.mk (Ideal.span {c})) he)
    subst t
    have hnm:n=m:=mul_left_cancel₀ hc (add_left_cancel he)
    subst m
    rfl
  · intro x
    let r:CubicUnitResidue c:=⟨Ideal.Quotient.mk (Ideal.span {c}) x.val,
      (isUnit_quotient_span_iff c x.val).mpr x.2⟩
    have hdiv:c∣x.val-GaussianShiftedPartition.representative c r.val:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact (GaussianShiftedPartition.representative_spec c r.val).symm
    obtain ⟨n,hn⟩:=hdiv
    refine ⟨(r,n),Subtype.ext ?_⟩
    change GaussianShiftedPartition.representative c r.val+c*n=x.val
    linear_combination -hn


-- @@ L266-268 verbatim
def cubicResidueElementEquiv (c:Eis) (hc:c≠0):
    CubicUnitResidue c×Eis≃CoprimeElement c:=
  Equiv.ofBijective (cubicResidueElementMap c) (cubicResidueElementMap_bijective c hc)


-- @@ L270-277 verbatim
lemma oppositeTerm_shift (z:ℂ) (v:ℝ) (s:ℂ) (c x n:Eis):
    oppositeTerm z v s c (x+c*n)=oppositeTerm (z+3*eisEmbedding n) v s c x:=by
  have hsym:symbol (3*(x+c*n)) c=symbol (3*x) c:=symbol_congr ⟨3*n,by ring⟩
  have harg:eisEmbedding c*z+eisEmbedding (3*(x+c*n))=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding (3*x):=by
    simp only [map_mul,map_add,map_ofNat]
    ring
  rw [oppositeTerm,oppositeTerm,hsym,harg]


-- @@ L279-282 verbatim
def oppositeGaussSum (h c:Eis):ℂ:=
  ∑'r:CubicUnitResidue c,
    eisEmbedding (symbol (3*GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive h c (3*GaussianShiftedPartition.representative c r.val)


-- @@ L284-305 verbatim
theorem oppositeGaussSum_eq (h:Eis) (c:PrimaryLower):
    oppositeGaussSum h c.val=cubicUnitGaussSum (9*h) c.val:=by
  have hp:=primaryLower_primary c
  have hc:=primaryLower_ne_zero c
  have he:oppositeGaussSum h c.val=
      eisEmbedding (symbol 3 c.val)*cubicUnitGaussSum h c.val:=by
    rw [oppositeGaussSum,cubicUnitGaussSum,←tsum_mul_left]
    apply tsum_congr
    intro r
    rw [symbol_mul_numerator _ _ _ hp,map_mul]
    have hadd:residueAdditive h c.val (3*GaussianShiftedPartition.representative c.val r.val)=
        residueAdditive (3*h) c.val (GaussianShiftedPartition.representative c.val r.val):=by
      unfold residueAdditive cuspFrequency
      simp only [map_mul,map_ofNat]
      congr 1
      ring
    rw [hadd]
    ring
  rw [he]
  have hs:=cubicUnitGaussSum_phase_shift h 1 c.val hc hp (by
    simpa only [mul_one] using (primary_coprime_three c.val hp).symm)
  simpa only [symbol_one_numerator c.val hp,map_one,one_mul,mul_one,mul_comm h 9] using hs


-- @@ L307-308 verbatim
def oppositeArithmeticSeries (s:ℂ) (h:Eis):ℂ:=
  ∑'c:PrimaryLower,((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val


-- @@ L310-319 verbatim
theorem oppositeArithmeticSeries_eq (s:ℂ) (h:Eis):
    oppositeArithmeticSeries s h=unramifiedCubicGaussSeries s (9*h):=by
  rw [oppositeArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  rw [oppositeGaussSum_eq]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (9*h) (primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]


-- @@ L321-321 verbatim
end


-- @@ L323-323 verbatim
section


-- @@ L325-325 verbatim
open MeasureTheory Set Filter Module

-- @@ L326-326 verbatim
open scoped BigOperators Classical ENNReal MatrixGroups Matrix

-- @@ L327-327 verbatim
open ActualEisensteinCubic ConcreteTraceCRT


-- @@ L329-336 verbatim
lemma continuous_inverse_fixed_left_operator (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    Continuous (fun z:ℂ=>rowOperator (a*upperSection z v hv)⁻¹):=by
  have he (z:ℂ):rowOperator (a*upperSection z v hv)⁻¹=
      (rowOperator a⁻¹).comp (rowOperator (upperSection z v hv)⁻¹):=by
    ext u
    simp only [mul_inv_rev,ContinuousLinearMap.comp_apply,rowOperator_mul]
  simp_rw [he]
  exact continuous_const.clm_comp (continuous_inverse_upper_operator v hv)


-- @@ L338-347 verbatim
lemma exists_fixed_left_rowBound (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    ∃C:ℝ,0<C ∧ ∀z∈periodDomain,rowBound (a*upperSection z v hv)≤C:=by
  have hc:Continuous (fun z:ℂ=>rowBound (a*upperSection z v hv)):=
    continuous_const.mul (continuous_const.add (continuous_inverse_fixed_left_operator a v hv).norm)
  let R:ℝ:=∑i:Fin 2,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:ℂ) R).bddAbove_image hc.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩


-- @@ L349-362 verbatim
lemma continuous_fixed_left_summand (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (x:CuspCosets):
    Continuous (fun z:ℂ=>summand (a*upperSection z v hv) s x):=by
  simp_rw [summand,←rowOperator_mul,rowEnergy_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    unfold heightDenominator
    fun_prop
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (heightDenominator_pos z v hv _
      (rowOperator_ne_zero a _ (embeddedRow_ne_zero x))) hv


-- @@ L364-379 verbatim
lemma fixed_left_summable_majorant (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (hs:2<s.re):
    ∃M:CuspCosets→ℝ,Summable M ∧ (∀x,0≤M x) ∧
      ∀z∈periodDomain,∀x,‖summand (a*upperSection z v hv) s x‖≤M x:=by
  obtain ⟨C,hC,hbound⟩:=exists_fixed_left_rowBound a v hv
  refine ⟨fun x=>C^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm:=summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj:Function.Injective (fun x:CuspCosets=>rowCoordinates (cosetRow x)):=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (a*upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)


-- @@ L381-401 verbatim
theorem hasSum_integral_fixed_left_Eisenstein (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s freq:ℂ) (hs:2<s.re):
    HasSum (fun x:CuspCosets=>∫z in periodDomain,
      summand (a*upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (a*upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)):=by
  let:Countable CuspCosets:=(rowCoordinates_injective.comp cosetRow_injective).countable
  let:=periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩:=fixed_left_summable_majorant a v hv s hs
  have hchar:Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-freq*z)):=by
    change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  exact hasSum_integral_of_dominated_convergence
    («μ»:=volume.restrict periodDomain)
    (fun (x:CuspCosets) (_:ℂ)=>M x)
    (fun x=>((continuous_fixed_left_summand a v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x=>(ae_restrict_mem periodDomain_measurable).mono fun z hz=>by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _=>hM)
    (integrable_const (∑'x,M x))
    (Eventually.of_forall fun z=>(summable_summand (a*upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))


-- @@ L403-403 verbatim
end


-- @@ L405-405 verbatim
section


-- @@ L407-407 verbatim
open MeasureTheory Set Filter

-- @@ L408-408 verbatim
open scoped BigOperators Classical ENNReal

-- @@ L409-409 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

-- @@ L410-410 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L412-413 verbatim
def oppositeIntegral (v:ℝ) (s freq:ℂ) (c x:Eis):ℂ:=
  ∫z in periodDomain,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z)


-- @@ L415-425 verbatim
theorem hasSum_oppositeIntegrals (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re):
    HasSum (fun p:OppositeData=>oppositeIntegral v s freq p.1.val p.2.val)
      (∫z in periodDomain,oppositeEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein oppositeMatrix v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [Equiv.trans_apply]
    rw [opposite_summand]


-- @@ L427-430 verbatim
lemma oppositeTerm_integrable (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (c x:Eis) (hc:c≠0):Integrable (fun z=>oppositeTerm z v s c x):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _


-- @@ L432-444 verbatim
lemma oppositeIntegral_sum_translate (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (h c x:Eis) (hc:c≠0):
    (∑'n:Eis,oppositeIntegral v s (cuspFrequency h) c (x+c*n))=
      ∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-cuspFrequency h*z):=by
  have hint:=trace_mul_integrable (fun z=>oppositeTerm z v s c x)
    (oppositeTerm_integrable v hv s hs c x hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [oppositeIntegral]
    rw [oppositeTerm_shift,cuspFrequency_negative_period]


-- @@ L446-456 verbatim
lemma oppositeTerm_fourier_integral (v:ℝ) (hv:0<v) (s freq:ℂ)
    (c x:Eis) (hc:c≠0):
    (∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol (3*x) c)*
          ShortDraftTrace.breveE (freq*eisEmbedding (3*x)/eisEmbedding c)):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding (3*x)/eisEmbedding c) freq]
  ring_nf


-- @@ L458-479 verbatim
lemma oppositeDenominator_integral_formula (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re)
    (h:Eis) (c:PrimaryLower):
    (∑'x:CoprimeElement c.val,oppositeIntegral v s (cuspFrequency h) c.val x.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val:=by
  have hf:Summable (fun x:CoprimeElement c.val=>oppositeIntegral v s (cuspFrequency h) c.val x.val):=
    (hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  have hsum:=(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue c.val×Eis=>
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2)) at hsum
  rw [←(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).tsum_eq]
  change (∑'q:CubicUnitResidue c.val×Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2))=_
  rw [hsum.tsum_prod]
  change (∑'r:CubicUnitResidue c.val,∑'n:Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val r.val+c.val*n))=_
  simp_rw [oppositeIntegral_sum_translate v hv s (by linarith) h c.val _ (primaryLower_ne_zero c),
    oppositeTerm_fourier_integral v hv s (cuspFrequency h) c.val _ (primaryLower_ne_zero c)]
  exact tsum_mul_left


-- @@ L481-489 verbatim
lemma unramifiedCubicGaussSeries_twentySeven (s:ℂ) (h:Eis):
    unramifiedCubicGaussSeries s (27*h)=unramifiedCubicGaussSeries s h:=by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.val-1:=(primaryGenerator_spec I.val I.2).2
  simpa only [show (3:Eis)^3=27 by norm_num,mul_comm h 27] using
    cubicUnitGaussSum_cube_shift h (primaryGenerator I.val) 3 I.2 hp
      (primary_coprime_three _ hp)


-- @@ L491-506 verbatim
theorem oppositeEisenstein_fourier (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        unramifiedCubicGaussSeries s (9*h):=by
  have hh:=hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs
  rw [←hh.tsum_eq,hh.summable.tsum_sigma]
  simp_rw [oppositeDenominator_integral_formula v hv s hs h]
  rw [←oppositeArithmeticSeries_eq s h,oppositeArithmeticSeries]
  have he (c:PrimaryLower):
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        (((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val):=by ring
  simp_rw [he]
  exact tsum_mul_left


-- @@ L508-519 verbatim
theorem oppositeEisenstein_fourier_unramified (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-(eisEmbedding h/eisLam)*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s ((eisEmbedding h/eisLam)*v))*
        unramifiedCubicGaussSeries s h:=by
  have hf:cuspFrequency (3*h)=eisEmbedding h/eisLam:=by
    unfold cuspFrequency
    rw [map_mul,map_ofNat]
    field_simp
  have hh:=oppositeEisenstein_fourier v hv s hs (3*h)
  rw [hf,show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven] at hh
  exact hh


-- @@ L521-521 verbatim
end


-- @@ L523-523 verbatim
open Filter MeasureTheory

-- @@ L524-524 verbatim
open scoped BigOperators Classical Topology ENNReal


-- @@ L526-526 verbatim
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

-- @@ L527-528 verbatim
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

-- @@ L529-530 verbatim
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)


-- @@ L532-532 verbatim
abbrev PeriodTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))


-- @@ L534-534 verbatim
def periodIocCube : Set (Fin 2→ℝ) := {x | ∀i,x i∈Set.Ioc 0 (0+1)}


-- @@ L536-536 verbatim
def periodCovolumeDensity : ℝ≥0∞ := ENNReal.ofReal (2/(9*Real.sqrt 3))


-- @@ L538-539 verbatim
lemma periodCovolumeDensity_ne_zero : periodCovolumeDensity≠0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))


-- @@ L541-542 verbatim
lemma periodIocCube_measurable : MeasurableSet periodIocCube :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)


-- @@ L544-545 verbatim
lemma periodIocCube_ae : periodCube=ᵐ[volume]periodIocCube := by
  simpa only [periodIocCube,zero_add] using periodCube_ae_Ioc


-- @@ L547-548 verbatim
def periodSection (t : UnitAddTorus (Fin 2)) : ℂ :=
  periodVector ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ)) t).val)


-- @@ L550-553 verbatim
lemma periodSection_measurableEmbedding : MeasurableEmbedding periodSection :=
  periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).measurableEmbedding)


-- @@ L555-559 verbatim
lemma periodTorus_measurable : Measurable periodTorus := by
  apply Measurable.of_eval
  intro i
  exact AddCircle.measurable_mk'.comp
    ((measurable_pi_apply i).comp periodBasis.equivFunL.continuous.measurable)


-- @@ L561-563 verbatim
lemma periodTorus_section (t : UnitAddTorus (Fin 2)) : periodTorus (periodSection t)=t := by
  rw [periodSection,periodTorus_periodVector]
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).symm_apply_apply t


-- @@ L565-572 verbatim
lemma periodVector_Ioc_measurePreserving :
    MeasurePreserving periodVector (volume.restrict periodIocCube)
      (periodCovolumeDensity • volume.restrict periodDomain) := by
  refine ⟨periodVector.continuous.measurable,?_⟩
  rw [←Measure.restrict_congr_set periodIocCube_ae,←periodVector_preimage_domain,
    ←Measure.restrict_map periodVector.continuous.measurable periodDomain_measurable,
    periodVector_map_volume,Measure.restrict_smul]
  rfl


-- @@ L574-579 verbatim
lemma periodSection_measurePreserving :
    MeasurePreserving periodSection volume
      (periodCovolumeDensity • volume.restrict periodDomain) :=
  periodVector_Ioc_measurePreserving.comp
    ((measurePreserving_subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ))))


-- @@ L581-587 verbatim
lemma periodTorus_measurePreserving :
    MeasurePreserving periodTorus (periodCovolumeDensity • volume.restrict periodDomain) volume := by
  refine ⟨periodTorus_measurable,?_⟩
  rw [←periodSection_measurePreserving.map_eq,
    Measure.map_map periodTorus_measurable periodSection_measurableEmbedding.measurable]
  have he : periodTorus ∘ periodSection=id := funext periodTorus_section
  rw [he,Measure.map_id]


-- @@ L589-594 verbatim
lemma periodSection_torus_ae :
    (fun z => periodSection (periodTorus z))=ᵐ[volume.restrict periodDomain] (fun z : ℂ => z) := by
  apply (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp
  rw [←periodSection_measurePreserving.map_eq]
  apply periodSection_measurableEmbedding.ae_map_iff.mpr
  exact Eventually.of_forall (fun t => by dsimp only; rw [periodTorus_section])


-- @@ L596-599 verbatim
lemma periodSection_memLp (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    MemLp (f ∘ periodSection) 2 volume :=
  (hf.smul_measure (by simp [periodCovolumeDensity])).comp_measurePreserving
    periodSection_measurePreserving


-- @@ L601-602 verbatim
def periodTorusL2Lift (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) : PeriodTorusL2 :=
  (periodSection_memLp f hf).toLp (f ∘ periodSection)


-- @@ L604-606 verbatim
lemma periodTorusL2Lift_ae (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    periodTorusL2Lift f hf=ᵐ[volume]f ∘ periodSection :=
  MemLp.coeFn_toLp (periodSection_memLp f hf)


-- @@ L608-615 verbatim
lemma periodTorusL2Lift_pullback (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    (fun z => periodTorusL2Lift f hf (periodTorus z))=ᵐ[volume.restrict periodDomain]f := by
  have he := periodTorus_measurePreserving.quasiMeasurePreserving.ae_eq_comp (periodTorusL2Lift_ae f hf)
  have he' := (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp he
  filter_upwards [he',periodSection_torus_ae] with z hz hsec
  change periodTorusL2Lift f hf (periodTorus z)=f (periodSection (periodTorus z)) at hz
  rw [hsec] at hz
  exact hz


-- @@ L617-624 verbatim
lemma periodTorusL2Lift_frequency_integral (f : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain)) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,periodTorusL2Lift f hf (periodTorus z)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]


-- @@ L626-634 verbatim
lemma periodTorusL2Lift_fourierCoeff (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain))
    (n : Fin 2→ℤ) :
    UnitAddTorus.mFourierCoeff (periodTorusL2Lift f hf) n=(2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [periodTorus_fourierCoeff]
  congr 1
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]


-- @@ L636-648 verbatim
theorem periodDomain_L2_ext (f g : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain))
    (hg : MemLp g 2 (volume.restrict periodDomain))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ∫z in periodDomain,g z*ShortDraftTrace.breveE (-cuspFrequency h*z)) :
    f=ᵐ[volume.restrict periodDomain]g := by
  have he : periodTorusL2Lift f hf=periodTorusL2Lift g hg := by
    apply periodTorus_L2_ext
    intro hfreq
    rw [periodTorusL2Lift_frequency_integral,periodTorusL2Lift_frequency_integral,h]
  filter_upwards [periodTorusL2Lift_pullback f hf,periodTorusL2Lift_pullback g hg] with z hz hz'
  rw [←hz,←hz',he]


-- @@ L650-650 verbatim
end CubicEisenstein


-- @@ L652-652 verbatim
end


-- @@ L654-654 verbatim
end OAI
