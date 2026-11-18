import OAI.NumberTheory.DirichletL.Eisenstein.CoverTrace


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

-- @@ L77-77 verbatim
open Filter MeasureTheory

-- @@ L78-78 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L80-80 verbatim
open ConcreteTraceCRT

-- @@ L81-81 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L83-91 verbatim
theorem sourceCusp_average_enlarged_affine (M : SL(2,ActualEisensteinCubic.O)) (b : ActualEisensteinCubic.O) (hb : b≠0)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z+c)) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  exact (period_integral_eisenstein_affine
    (fun z=>cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))
    (sourceCusp_scaled_continuous M v hv).measurable
    (sourceCusp_scaled_periodic M v hv) b hb c).trans (sourceCusp_average_all M v hv)


-- @@ L93-107 verbatim
theorem sourceCusp_average_complex_upper (M : SL(2,ActualEisensteinCubic.O)) (T : SL(2,ℂ))
    (hT : T 1 0=0) (b d : ActualEisensteinCubic.O) (hd : d≠0)
    (hscale : (T 0 0/T 1 1)*eisEmbedding b=eisEmbedding d)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • (T • upperPoint (3*(eisEmbedding b*z)) v hv)))=
      sourceCuspConstant M*((v/‖T 1 1‖^2:ℝ):ℂ)^(2/3:ℂ) := by
  have hcoord (z : ℂ) : (T 0 0*(3*(eisEmbedding b*z))+T 0 1)/T 1 1=
      3*(eisEmbedding d*z+(T 0 1/T 1 1)/3) := by
    rw [add_div]
    rw [show T 0 0*(3*(eisEmbedding b*z))/T 1 1=
      3*((T 0 0/T 1 1)*eisEmbedding b)*z by ring,hscale]
    ring
  simp_rw [complex_upper_triangular_action T hT,hcoord]
  exact sourceCusp_average_enlarged_affine M d hd _ _ _


-- @@ L109-125 verbatim
lemma sourceCuspConstant_congruent (M N : SL(2,ActualEisensteinCubic.O))
    (h : N*M⁻¹∈CubicKubota.levelThree) :
    sourceCuspConstant N=
      CubicKubota.complexCharacter ⟨N*M⁻¹,h⟩*sourceCuspConstant M := by
  let g : CubicKubota.levelThree := ⟨N*M⁻¹,h⟩
  let g₂ : CubicKubota.levelTwo :=
    ⟨(g:SL(2,ActualEisensteinCubic.O)),CubicKubota.levelThree_le_levelTwo g.property⟩
  have hg : (g₂:SL(2,ActualEisensteinCubic.O))*M=N := by
    change (N*M⁻¹)*M=N
    group
  have hh := sourceCuspConstant_left g₂ M
  rw [hg] at hh
  change sourceCuspConstant N=
    CubicKubota.levelTwoComplexCharacter
      ⟨(g:SL(2,ActualEisensteinCubic.O)),CubicKubota.levelThree_le_levelTwo g.property⟩*sourceCuspConstant M at hh
  rw [CubicKubota.levelTwoComplexCharacter_restrict] at hh
  exact hh


-- @@ L127-130 verbatim
lemma sourceCuspConstant_congruent_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h : N*M⁻¹∈CubicKubota.levelThree) (hM : sourceCuspConstant M=0) :
    sourceCuspConstant N=0 := by
  rw [sourceCuspConstant_congruent M N h,hM,mul_zero]


-- @@ L132-132 verbatim
end CubicEisenstein


-- @@ L134-134 verbatim
section


-- @@ L136-136 verbatim
open scoped Classical MatrixGroups BigOperators

-- @@ L137-137 verbatim
namespace CubicEisenstein


-- @@ L139-139 verbatim
section

-- @@ L140-140 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L141-141 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L143-144 verbatim
def cubeCuspTriangular {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) : SL(2,ℂ) :=
  (integralComplexMatrix d.matrix)⁻¹*cubeAverageMatrix p hp q*integralComplexMatrix A


-- @@ L146-150 verbatim
lemma cubeCuspTriangular_factor {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix d.matrix*cubeCuspTriangular d hp := by
  unfold cubeCuspTriangular
  group


-- @@ L152-215 verbatim
lemma cubeCuspTriangular_entries {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val ∧
    cubeCuspTriangular d hp 1 0=0 ∧
    cubeCuspTriangular d hp 1 1=(cubeDilationRoot p)⁻¹*eisEmbedding p^(3-d.exponent.val) := by
  let B:=cubeAverageMatrix p hp q*integralComplexMatrix A
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  have hx:eisEmbedding (A 0 0)+3*eisEmbedding q*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    simpa only [map_add,map_mul,map_pow,map_ofNat] using congrArg eisEmbedding d.first
  have hy:eisEmbedding p^3*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    simpa only [map_mul,map_pow] using congrArg eisEmbedding d.second
  have hB0:B 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 0 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    linear_combination (cubeDilationRoot p)⁻¹*hx
  have hB1:B 1 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 1 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.cons_val_one,
      Matrix.cons_val_zero,Matrix.cons_val_fin_one,Matrix.of_apply,zero_mul,zero_add]
    rw [mul_assoc,←hy,←he]
    field_simp
  have hinv:(integralComplexMatrix d.matrix : Matrix (Fin 2) (Fin 2) ℂ)⁻¹=
      !![eisEmbedding (d.matrix 1 1),-eisEmbedding (d.matrix 0 1);
        -eisEmbedding (d.matrix 1 0),eisEmbedding (d.matrix 0 0)] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
    rfl
  have hT:cubeCuspTriangular d hp=(integralComplexMatrix d.matrix)⁻¹*B:=by
    dsimp [cubeCuspTriangular,B]
    group
  have hdet:eisEmbedding (d.matrix 0 0)*eisEmbedding (d.matrix 1 1)-
      eisEmbedding (d.matrix 0 1)*eisEmbedding (d.matrix 1 0)=1:=by
    have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
      simpa only [Matrix.det_fin_two] using d.matrix.property
    simpa only [map_sub,map_mul,map_one] using congrArg eisEmbedding hd
  have h00:cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    linear_combination (cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*hdet
  have h10:cubeCuspTriangular d hp 1 0=0:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    ring
  refine ⟨h00,h10,?_⟩
  have hd:cubeCuspTriangular d hp 0 0*cubeCuspTriangular d hp 1 1=1:=by
    simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using (cubeCuspTriangular d hp).property
  rw [h00] at hd
  have hnon:(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val≠0:=
    mul_ne_zero (inv_ne_zero hz) (pow_ne_zero _ (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ hnon
  rw [hd]
  have hpow:eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val)=eisEmbedding p^3:=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  calc
    1=(cubeDilationRoot p)⁻¹^2*eisEmbedding p^3:=by rw [←he,inv_pow,inv_mul_cancel₀ (pow_ne_zero 2 hz)]
    _=_:=by rw [←hpow];ring


-- @@ L217-217 verbatim
end


-- @@ L219-219 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L220-220 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L222-236 verbatim
lemma cubeCuspTriangular_integral_scale {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) :
    (cubeCuspTriangular d hp 0 0/cubeCuspTriangular d hp 1 1)*eisEmbedding (p^3)=
      eisEmbedding (p^(2*d.exponent.val)) := by
  obtain ⟨h00,_,h11⟩:=cubeCuspTriangular_entries d hp
  rw [h00,h11,map_pow,map_pow]
  have he:eisEmbedding p≠0:=eisEmbedding_ne_zero hp
  have hz:=cubeDilationRoot_ne_zero p hp
  have hpow:eisEmbedding p^3=eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  have htwo:eisEmbedding p^(2*d.exponent.val)=(eisEmbedding p^d.exponent.val)^2:=by
    rw [mul_comm 2 d.exponent.val,pow_mul]
  rw [htwo]
  field_simp


-- @@ L238-241 verbatim
private lemma cube_scale_norm_real (r:ℝ) (hr:0<r) (j:Fin 4) :
    (r^3)⁻¹*(r^(3-j.val))^2=r^(3-2*(j.val:ℝ)) := by
  fin_cases j <;> norm_num [Real.rpow_neg_natCast,Real.rpow_neg_one]
  all_goals field_simp


-- @@ L243-252 verbatim
lemma cubeCuspTriangular_norm_sq {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) :
    ‖cubeCuspTriangular d hp 1 1‖^2 =
      ‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)) := by
  obtain ⟨_,_,h11⟩:=cubeCuspTriangular_entries d hp
  rw [h11,norm_mul,norm_inv,norm_pow,mul_pow,inv_pow]
  have hn:‖cubeDilationRoot p‖^2=‖eisEmbedding p‖^3:=by
    rw [←norm_pow,cubeDilationRoot_sq,norm_pow]
  rw [hn]
  exact cube_scale_norm_real _ (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) d.exponent


-- @@ L254-276 verbatim
lemma cubeCuspTriangular_height {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) (v:ℝ) (hv:0<v) :
    ((v/‖cubeCuspTriangular d hp 1 1‖^2:ℝ):ℂ)^(2/3:ℂ)=
      (v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  rw [cubeCuspTriangular_norm_sq]
  have hnon:0<‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)):=Real.rpow_pos_of_pos hr _
  have hcast:((2/3:ℝ):ℂ)=(2/3:ℂ):=by norm_num
  rw [←hcast,←Complex.ofReal_cpow (le_of_lt (div_pos hv hnon)),
    ←Complex.ofReal_cpow hv.le]
  unfold cubeCuspHeightWeight
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [Real.div_rpow hv.le hnon.le,←Real.rpow_mul hr.le]
  have hp2:(‖eisEmbedding p‖^2)^((2*(d.exponent.val:ℝ)-3)/3)=
      ‖eisEmbedding p‖^(((2*(d.exponent.val:ℝ)-3)/3)*2):=by
    rw [←Real.rpow_natCast_mul hr.le 2]
    congr 1
    ring
  rw [hp2,div_eq_mul_inv,←Real.rpow_neg hr.le]
  congr 1
  ring_nf


-- @@ L278-278 verbatim
end CubicEisenstein


-- @@ L280-280 verbatim
namespace CubicKubota

-- @@ L281-281 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified

-- @@ L282-282 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L284-305 verbatim
lemma levelTwo_primary_shift_cases (A:levelTwo) :
    ∃t:Fin 2, lambda^2∣((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0)-1 ∨
      lambda^2∣(-((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0))-1 := by
  rcases integer_congruence_primary_cases ((A:SL(2,Eis)) 0 0)
    (levelTwoRight A 0 0) (levelTwo_entry_integer A 0 0) with ha|ha|ha
  · rcases integer_congruence_primary_cases ((A:SL(2,Eis)) 1 0)
      (levelTwoRight A 1 0) (levelTwo_entry_integer A 1 0) with hc|hc|hc
    · have h1:(3:Eis)∣1:=by
        have hd:(A:SL(2,Eis)) 0 0*(A:SL(2,Eis)) 1 1-
          (A:SL(2,Eis)) 0 1*(A:SL(2,Eis)) 1 0=1:=by
            simpa only [Matrix.det_fin_two] using (A:SL(2,Eis)).property
        rw [←hd]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      have hl:lambda∣(1:Eis):=(dvd_pow_self lambda (by decide:2≠0)).trans
        (lambda_sq_dvd_three.trans h1)
      exact (residue_lambda_prime.not_isUnit (isUnit_of_dvd_one hl)).elim
    · refine ⟨1,Or.inl ?_⟩
      convert dvd_add (lambda_sq_dvd_three.trans ha) hc using 1 ; norm_num ; ring
    · refine ⟨1,Or.inr ?_⟩
      convert dvd_add (dvd_neg.mpr (lambda_sq_dvd_three.trans ha)) hc using 1 ; norm_num ; ring
  · exact ⟨0,Or.inl (by simpa using ha)⟩
  · exact ⟨0,Or.inr (by simpa using ha)⟩


-- @@ L307-307 verbatim
end CubicKubota

-- @@ L308-308 verbatim
namespace CubicEisenstein

-- @@ L309-309 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L310-310 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L312-325 verbatim
lemma rationalComplex_S_sq_action (w:HyperbolicSpace) :
    rationalComplex (ModularGroup.S^2) • w=w := by
  have he:rationalComplex (ModularGroup.S^2)=complexDiagonal (-1) (by norm_num):=by
    have hS : ((ModularGroup.S ^ 2 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![-1, 0; 0, -1] := by decide
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change eisEmbedding ((Int.castRingHom Eis) ((ModularGroup.S ^ 2 : SL(2,ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp [complexDiagonal]
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [he,complexDiagonal_action]
  apply upperPoint_congr <;> norm_num


-- @@ L327-331 verbatim
lemma rationalComplex_T_eq : rationalComplex ModularGroup.T=complexTranslation 1 := by
  rw [← rationalUnipotent_one]
  apply Subtype.ext
  rw [rationalComplex_unipotent_coe]
  norm_num [complexTranslation]


-- @@ L333-379 verbatim
theorem exists_primary_cusp_shift (A:levelTwo) :
    ∃B:levelTwo, lambda^2∣((B:SL(2,Eis)) 0 0)-1 ∧
      ∃t:Fin 2,∀w:HyperbolicSpace,
        integralComplexMatrix (B:SL(2,Eis)) • w=
          complexTranslation (t.val:ℂ) • (integralComplexMatrix (A:SL(2,Eis)) • w) := by
  obtain ⟨t,ht⟩:=levelTwo_primary_shift_cases A
  let T:levelTwo:=⟨rationalEmbedding (ModularGroup.T^t.val),rational_mem_levelTwo _⟩
  let S:levelTwo:=⟨rationalEmbedding (ModularGroup.S^2),rational_mem_levelTwo _⟩
  have hT:((T*A:levelTwo):SL(2,Eis)) 0 0=
      (A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0:=by
    have hmatrix : ((ModularGroup.T ^ t.val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![1, (t.val : ℤ); 0, 1] := by
      fin_cases t <;> decide
    change ((((ModularGroup.T ^ t.val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom Eis)) * ((A : SL(2, Eis)) : Matrix (Fin 2) (Fin 2) Eis)) 0 0 = _
    rw [hmatrix]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hST:((S*(T*A):levelTwo):SL(2,Eis)) 0 0=
      -((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0):=by
    have hneg (M:SL(2,Eis)) : (rationalEmbedding (ModularGroup.S^2)*M) 0 0= -M 0 0:=by
      have hmatrix : ((ModularGroup.S ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
          !![-1, 0; 0, -1] := by decide
      change ((((ModularGroup.S ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom Eis)) * (M : Matrix (Fin 2) (Fin 2) Eis)) 0 0 = _
      rw [hmatrix]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    exact (hneg ((T*A:levelTwo):SL(2,Eis))).trans (congrArg (fun x:Eis=> -x) hT)
  have hzero:complexTranslation 0=1:=by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  have hact (w:HyperbolicSpace):integralComplexMatrix ((T*A:levelTwo):SL(2,Eis)) • w=
      complexTranslation (t.val:ℂ) • (integralComplexMatrix (A:SL(2,Eis)) • w):=by
    change integralComplexMatrix (rationalEmbedding (ModularGroup.T^t.val)*(A:SL(2,Eis))) • w=_
    rw [map_mul,mul_smul]
    change rationalComplex (ModularGroup.T^t.val) • (integralComplexMatrix (A:SL(2,Eis)) • w)=_
    fin_cases t
    · simp only [pow_zero,map_one,one_smul,Nat.cast_zero,hzero]
    · simp only [pow_one,rationalComplex_T_eq,Nat.cast_one]
  rcases ht with ht|ht
  · exact ⟨T*A,by rwa [hT],t,hact⟩
  · refine ⟨S*(T*A),by rwa [hST],t,?_⟩
    intro w
    change integralComplexMatrix (rationalEmbedding (ModularGroup.S^2)*((T*A:levelTwo):SL(2,Eis))) • w=_
    rw [map_mul,mul_smul]
    change rationalComplex (ModularGroup.S^2) • (integralComplexMatrix ((T*A:levelTwo):SL(2,Eis)) • w)=_
    rw [rationalComplex_S_sq_action,hact]


-- @@ L381-381 verbatim
end CubicEisenstein


-- @@ L383-383 verbatim
namespace CubicKubota

-- @@ L384-384 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal

-- @@ L385-385 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L387-389 verbatim
lemma matrix_mul_upper_first_column (A T:SL(2,Eis)) (hT:T 1 0=0) (i:Fin 2) :
    (A*T) i 0=A i 0*T 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hT,mul_zero,add_zero]


-- @@ L391-391 verbatim
namespace CubeCuspData

-- @@ L392-392 verbatim
variable {A:SL(2,Eis)} {p q:Eis}


-- @@ L394-407 verbatim
def right_upper (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    CubeCuspData (A*T) p q where
  exponent:=d.exponent
  matrix:=d.matrix*T
  first:=by
    simp only [matrix_mul_upper_first_column _ T hT]
    linear_combination d.first*(T 0 0)
  second:=by
    simp only [matrix_mul_upper_first_column _ T hT]
    linear_combination d.second*(T 0 0)
  congruent:=by
    have he:(d.matrix*T)*(A*T)⁻¹=d.matrix*A⁻¹:=by group
    rw [he]
    exact d.congruent


-- @@ L409-410 verbatim
lemma right_upper_exponent (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    (d.right_upper T hT).exponent=d.exponent := rfl


-- @@ L412-418 verbatim
lemma right_upper_character (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    complexCharacter ⟨(d.right_upper T hT).matrix*(A*T)⁻¹,(d.right_upper T hT).congruent⟩=
      complexCharacter ⟨d.matrix*A⁻¹,d.congruent⟩ := by
  apply congrArg complexCharacter
  apply Subtype.ext
  change (d.matrix*T)*(A*T)⁻¹=d.matrix*A⁻¹
  group


-- @@ L420-420 verbatim
end CubeCuspData

-- @@ L421-421 verbatim
end CubicKubota

-- @@ L422-422 verbatim
end


-- @@ L424-424 verbatim
namespace CubicEisenstein


-- @@ L426-426 verbatim
section


-- @@ L428-428 verbatim
open MeasureTheory

-- @@ L429-429 verbatim
open scoped Classical MatrixGroups BigOperators

-- @@ L430-430 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L431-431 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L433-442 verbatim
lemma cubeAverage_continuous (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F) :
    Continuous (cubeAverage p hp F) := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  unfold cubeAverage
  simp only [tsum_fintype]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro r hr
  exact hF.comp (continuous_const_smul _)


-- @@ L444-469 verbatim
lemma cubeAverage_cusp_integral (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (M:SL(2,Eis)) (b:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      ∑' r:Eis⧸Ideal.span {p^3}, ∫z in periodDomain,
        F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv)) := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  let c:ℂ→UpperCoordinates:=fun z=>⟨(3*(eisEmbedding b*z),v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.mul continuous_id)).prodMk continuous_const
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (fun z=>
        F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    have hh:=(continuous_translatedUpperCoordinates
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)*integralComplexMatrix M)).comp hc
    simpa only [Function.comp_def,c,mul_smul] using hF.comp hh
  unfold cubeAverage
  simp only [tsum_fintype]
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum _ (fun r _=>hi r)


-- @@ L471-471 verbatim
end


-- @@ L473-473 verbatim
open Filter MeasureTheory

-- @@ L474-474 verbatim
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace


-- @@ L476-483 verbatim
theorem kernelSourceProjection_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelSourceProjection F)=
      kernelSourceProjection (kernelVariationalResolvent F) := by
  rw [kernelSourceProjection_apply,kernelSourceProjection_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact kernelSource_variationalResolvent _ F


-- @@ L485-489 verbatim
theorem kernelSourceProjection_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelSourceProjection F,kernelSourceProjection G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelSourceProjection_variationalResolvent,hFG]


-- @@ L491-494 verbatim
theorem kernelSourceProjection_eigenvector (F : KernelQuotientL2)
    (eigenvalue : ℂ) (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelSourceProjection F,eigenvalue • kernelSourceProjection F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelSourceProjection_operatorGraph F (eigenvalue • F) hF


-- @@ L496-499 verbatim
theorem kernelSourceProjection_cubicEisensteinResidue_eigenvector :
    (kernelSourceProjection cubicEisensteinResidue,
      (8/9:ℂ) • kernelSourceProjection cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelSourceProjection_eigenvector _ _ cubicEisensteinResidue_eigenvector


-- @@ L501-501 verbatim
end CubicEisenstein


-- @@ L503-503 verbatim
open Filter MeasureTheory

-- @@ L504-504 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L506-506 verbatim
namespace CubicEisenstein

-- @@ L507-507 verbatim
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree

-- @@ L508-508 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L510-511 verbatim
def sourceCuspLeadingCoefficient (M : SL(2,ActualEisensteinCubic.O)) : ℂ :=
  sourceCuspConstant M / ((9*Real.sqrt 3/2:ℝ):ℂ)


-- @@ L513-515 verbatim
def sourceCuspRemainder (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
    sourceCuspLeadingCoefficient M*(v:ℂ)^(2/3:ℂ)


-- @@ L517-524 verbatim
lemma sourceCuspLeadingCoefficient_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo)
    (j : Fin 3) (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0)
    (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspLeadingCoefficient M=
      levelTwoComplexCharacter G*sourceCuspLeadingCoefficient (cuspRepresentative j) := by
  unfold sourceCuspLeadingCoefficient
  rw [hM,sourceCuspConstant_upper_right _ T hT,sourceCuspConstant_left]
  ring


-- @@ L526-541 verbatim
lemma sourceCuspRemainder_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo)
    (j : Fin 3) (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0)
    (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspRemainder M z v hv=
      levelTwoComplexCharacter G*sourceCuspRemainder (cuspRepresentative j)
        (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hF : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy,
      integral_upper_triangular_action T hT]
  unfold sourceCuspRemainder
  rw [hF,sourceCuspLeadingCoefficient_decomposition M G j T hT hM]
  ring


-- @@ L543-551 verbatim
theorem sourceCuspRemainder_bound_all (K a : ℝ)
    (hK : ∀j : Fin 3,∀z : ℂ,∀v : ℝ,∀hv : 0<v,a≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hav : a≤v) :
    ‖sourceCuspRemainder M z v hv‖≤K/v^3 := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  rw [sourceCuspRemainder_decomposition M G j T hT hM z v hv,norm_mul,
    norm_levelTwoComplexCharacter,one_mul]
  exact hK j _ v hv hav


-- @@ L553-556 verbatim
lemma sourceCuspConstant_one : sourceCuspConstant (1:SL(2,ActualEisensteinCubic.O))=sourcePrincipalCuspConstant := by
  have h := sourceCuspRepresentative_average (0:Fin 3) 1 (by norm_num)
  simpa only [sourceCuspConstant,cuspRepresentative,cuspParameter,lowerCuspMatrix_zero,
    ite_true,Complex.ofReal_one,Complex.one_cpow,mul_one] using h


-- @@ L558-561 verbatim
lemma sourceCuspLeadingCoefficient_one :
    sourceCuspLeadingCoefficient (1:SL(2,ActualEisensteinCubic.O))=(3*(Real.pi:ℂ))*constantArithmeticResidue := by
  rw [sourceCuspLeadingCoefficient,sourceCuspConstant_one,sourcePrincipalCuspConstant]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (show (9*Real.sqrt 3/2:ℝ)≠0 by positivity))


-- @@ L563-570 verbatim
lemma sourceCuspRemainder_one (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspRemainder (1:SL(2,ActualEisensteinCubic.O)) z v hv=
      sourceBesselCoefficients.fullFunction 0 (upperPoint z v hv) := by
  rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_one,map_one,one_smul,
    cubicSourceResidualFunction_eq_bessel]
  simp only [sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    hyperbolicHeight_upperPoint,zero_mul,zero_add]
  ring


-- @@ L572-579 verbatim
theorem sourceCuspRemainder_principal_cubic_decay (a : ℝ) (ha : 0<a) :
    ∃K : ℝ,0≤K ∧ ∀z : ℂ,∀v : ℝ,∀hv : 0<v,a≤v→
      ‖sourceCuspRemainder (1:SL(2,ActualEisensteinCubic.O)) z v hv‖≤K/v^3 := by
  obtain ⟨K,hK,hbound⟩ := sourceBesselCoefficients.fullFunction_zero_cubic_decay a ha
  refine ⟨K,hK,?_⟩
  intro z v hv hav
  rw [sourceCuspRemainder_one]
  exact hbound v hv z hav


-- @@ L581-581 verbatim
end CubicEisenstein


-- @@ L583-583 verbatim
open Filter MeasureTheory

-- @@ L584-584 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace

-- @@ L585-585 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L587-587 verbatim
namespace CubicEisenstein

-- @@ L588-588 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L590-595 verbatim
lemma integralCoverDomain_projection_measurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralOrbitProjection H)
      (hyperbolicVolume.restrict (integralCoverDomain H K)) (integralQuotientVolume H) :=
  ⟨measurable_integralOrbitProjection H,integralQuotientVolume_independent H (hHK.trans hK) _
    (integralCoverDomain_isFundamentalDomain hHK hK)⟩


-- @@ L597-602 verbatim
lemma integralCoverSheet_measurePreserving (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) :
    MeasurePreserving (fun w : HyperbolicSpace=>integralCoverRep H K q•w)
      (hyperbolicVolume.restrict (integralCoverSheet H K q))
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) :=
  (measurePreserving_smul (integralCoverRep H K q) hyperbolicVolume).restrict_preimage
    (hyperbolicFundamentalSet_measurable K)


-- @@ L604-607 verbatim
lemma integralCoverFiberPoint_rep_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K q (integralCoverRep H K q•w)=integralOrbitProjection H w := by
  rw [integralCoverFiberPoint_rep,inv_smul_smul]


-- @@ L609-621 verbatim
lemma integralCoverFiber_integrable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    IntegrableOn (fun w=>f (integralCoverFiberPoint H K q w))
      (hyperbolicFundamentalSet K) hyperbolicVolume := by
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS : IntegrableOn (fun w=>f (integralOrbitProjection H w))
      (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  apply ((integralCoverSheet_measurePreserving H K q).integrable_comp
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable).mp
  simpa only [IntegrableOn,Function.comp_def,integralCoverFiberPoint_rep_smul] using hS


-- @@ L623-632 verbatim
theorem integralCoverTraceFunction_integrable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) :
    Integrable (integralCoverTraceFunction H K f) (integralQuotientVolume K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply ((quotient_projection_measurePreserving K).integrable_comp
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable).mp
  change Integrable (fun w=>∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)) _
  exact integrable_finsetSum Finset.univ (fun q _=>integralCoverFiber_integrable hHK hK f hmeas hf q)


-- @@ L634-641 verbatim
lemma integralCoverFiber_integral (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (f : IntegralOrbitQuotient H→ℂ) :
    (∫w in hyperbolicFundamentalSet K,f (integralCoverFiberPoint H K q w)∂hyperbolicVolume)=
      ∫w in integralCoverSheet H K q,f (integralOrbitProjection H w)∂hyperbolicVolume := by
  have hh := (measurePreserving_smul (integralCoverRep H K q) hyperbolicVolume).setIntegral_preimage_emb
    (measurableEmbedding_const_smul (integralCoverRep H K q))
    (fun w=>f (integralCoverFiberPoint H K q w)) (hyperbolicFundamentalSet K)
  simpa only [integralCoverSheet,integralCoverFiberPoint_rep_smul] using hh.symm


-- @@ L643-664 verbatim
theorem integralCoverTraceFunction_integral {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) :
    (∫q,integralCoverTraceFunction H K f q∂integralQuotientVolume K)=
      ∫q,f q∂integralQuotientVolume H := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS (q : IntegralCoverCosets H K) : IntegrableOn (fun w=>f (integralOrbitProjection H w))
      (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  rw [integralQuotientVolume_integral K _
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable]
  change (∫w in hyperbolicFundamentalSet K,
    ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)∂hyperbolicVolume)=_
  rw [integral_finsetSum Finset.univ (fun q _=>integralCoverFiber_integrable hHK hK f hmeas hf q)]
  simp_rw [integralCoverFiber_integral H K]
  rw [←integral_iUnion_fintype (integralCoverSheet_measurable H K)
    (integralCoverSheet_pairwiseDisjoint H K hK) hS]
  change (∫w in integralCoverDomain H K,f (integralOrbitProjection H w)∂hyperbolicVolume)=_
  rw [←(integralCoverDomain_projection_measurePreserving hHK hK).map_eq]
  exact (integral_map (measurable_integralOrbitProjection H).aemeasurable hmeas.aestronglyMeasurable).symm


-- @@ L666-666 verbatim
end CubicEisenstein


-- @@ L668-668 verbatim
end


-- @@ L670-670 verbatim
end OAI
