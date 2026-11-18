import OAI.NumberTheory.DirichletL.QuadraticSieve.GlobalBinLoss


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


-- @@ L73-73 verbatim
namespace CubicEisenstein


-- @@ L75-75 verbatim
section

-- @@ L76-76 verbatim
open Filter MeasureTheory

-- @@ L77-77 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix


-- @@ L79-79 verbatim
section

-- @@ L80-80 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

-- @@ L81-81 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L83-84 verbatim
def integralRowPair (M : SL(2,O)) : (Fin 2 → O)×(Fin 2 → O) :=
  (fun j => M 0 j,fun j => M 1 j)


-- @@ L86-92 verbatim
lemma integralRowPair_injective : Function.Injective integralRowPair := by
  intro M N h
  apply Subtype.ext
  funext i j
  fin_cases i
  · exact congrFun (congrArg Prod.fst h) j
  · exact congrFun (congrArg Prod.snd h) j


-- @@ L94-98 verbatim
lemma matrixFrobenius_integral (M : SL(2,O)) (g : SL(2,ℂ)) :
    matrixFrobenius (integralComplexMatrix M*g)=
      integralRowEnergy g (integralRowPair M).1+integralRowEnergy g (integralRowPair M).2 := by
  rw [matrixFrobenius,complexMatrixRow_mul,complexMatrixRow_mul]
  rfl


-- @@ L100-102 verbatim
lemma integralRowEnergy_nonneg (g : SL(2,ℂ)) (v : Fin 2 → O) : 0 ≤ integralRowEnergy g v := by
  unfold integralRowEnergy rowEnergy
  positivity


-- @@ L104-113 verbatim
theorem integral_frobenius_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {M : SL(2,O) | matrixFrobenius (integralComplexMatrix M*g)≤C} := by
  have hs := integralRowEnergy_sublevel_finite g C
  apply (Set.Finite.preimage integralRowPair_injective.injOn (hs.prod hs)).subset
  intro M hM
  change integralRowEnergy g (integralRowPair M).1≤C ∧ integralRowEnergy g (integralRowPair M).2≤C
  change matrixFrobenius (integralComplexMatrix M*g)≤C at hM
  rw [matrixFrobenius_integral] at hM
  exact ⟨by linarith [integralRowEnergy_nonneg g (integralRowPair M).2],
    by linarith [integralRowEnergy_nonneg g (integralRowPair M).1]⟩


-- @@ L115-118 verbatim
theorem integral_hyperbolic_sublevel_finite (w : HyperbolicSpace) (C : ℝ) :
    Set.Finite {M : SL(2,O) | hyperbolicFrobenius (integralComplexMatrix M • w)≤C} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact integral_frobenius_sublevel_finite g C


-- @@ L120-123 verbatim
theorem subgroup_hyperbolic_sublevel_finite (H : Subgroup (SL(2,O)))
    (w : HyperbolicSpace) (C : ℝ) :
    Set.Finite {M : H | hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤C} := by
  exact Set.Finite.preimage Subtype.val_injective.injOn (integral_hyperbolic_sublevel_finite w C)


-- @@ L125-137 verbatim
theorem subgroup_orbit_minimum (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,∀N : H,
      hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤
        hyperbolicFrobenius (integralComplexMatrix (N:SL(2,O)) • w) := by
  let S : Set H := {M | hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤hyperbolicFrobenius w}
  have hs : Set.Finite S := subgroup_hyperbolic_sublevel_finite H w _
  have hne : S.Nonempty := ⟨1,by simp [S]⟩
  obtain ⟨M,hM,hmin⟩ := Set.exists_min_image S
    (fun M : H => hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)) hs hne
  refine ⟨M,fun N => ?_⟩
  by_cases hN : N∈S
  · exact hmin N hN
  · exact hM.trans (le_of_lt (lt_of_not_ge hN))


-- @@ L139-139 verbatim
end


-- @@ L141-141 verbatim
section

-- @@ L142-142 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

-- @@ L143-143 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L145-150 verbatim
lemma integralComplexMatrix_injective : Function.Injective integralComplexMatrix := by
  intro M N h
  apply Subtype.ext
  funext i j
  apply eisEmbedding_injective
  exact congrArg (fun A : SL(2,ℂ) => A i j) h


-- @@ L152-164 verbatim
lemma levelThree_trace_divisible_nine (M : levelThree) :
    (9:O)∣((M:SL(2,O)) 0 0+(M:SL(2,O)) 1 1-2) := by
  have ha : (3:O)∣((M:SL(2,O)) 0 0-1) := by simpa using levelThree_entry M 0 0
  have hd : (3:O)∣((M:SL(2,O)) 1 1-1) := by simpa using levelThree_entry M 1 1
  have hb : (3:O)∣(M:SL(2,O)) 0 1 := by simpa using levelThree_entry M 0 1
  have hc : (3:O)∣(M:SL(2,O)) 1 0 := by simpa using levelThree_entry M 1 0
  have hdet : (M:SL(2,O)) 0 0*(M:SL(2,O)) 1 1-(M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,O)).property
  have he : (M:SL(2,O)) 0 0+(M:SL(2,O)) 1 1-2=
      (M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0-
        ((M:SL(2,O)) 0 0-1)*((M:SL(2,O)) 1 1-1) := by linear_combination hdet
  rw [he]
  exact dvd_sub (by simpa only [show (3:O)*3=9 by ring] using mul_dvd_mul hb hc) (by simpa only [show (3:O)*3=9 by ring] using mul_dvd_mul ha hd)


-- @@ L166-173 verbatim
lemma unitary_row_normSq (k : SL(2,ℂ)) (hk : k∈compactSubgroup) (i : Fin 2) :
    Complex.normSq (k i 0)+Complex.normSq (k i 1)=1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A i i).re) hu
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,Matrix.one_apply_eq,
    Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.one_re] at he
  simp only [Complex.normSq_apply]
  nlinarith


-- @@ L175-184 verbatim
lemma unitary_trace_norm_le_two (k : SL(2,ℂ)) (hk : k∈compactSubgroup) : ‖k 0 0+k 1 1‖≤2 := by
  have h0 := unitary_row_normSq k hk 0
  have h1 := unitary_row_normSq k hk 1
  have ha : ‖k 0 0‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at h0
    nlinarith [norm_nonneg (k 0 0),Complex.normSq_nonneg (k 0 1)]
  have hd : ‖k 1 1‖≤1 := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (k 1 1),sq_nonneg ‖k 1 0‖]
  exact (norm_add_le _ _).trans (by linarith)


-- @@ L186-210 verbatim
lemma unitary_trace_two_eq_one (k : SL(2,ℂ)) (hk : k∈compactSubgroup)
    (ht : k 0 0+k 1 1=2) : k=1 := by
  have h0 := unitary_row_normSq k hk 0
  have h1 := unitary_row_normSq k hk 1
  have htR := congrArg Complex.re ht
  norm_num [Complex.add_re] at htR
  have hs : Complex.normSq (k 0 0-1)+Complex.normSq (k 0 1)+
      Complex.normSq (k 1 0)+Complex.normSq (k 1 1-1)=0 := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at *
    nlinarith
  have ha : k 0 0=1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)]))
  have hb : k 0 1=0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)])
  have hc : k 1 0=0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)])
  have hd : k 1 1=1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)]))
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simpa using (by first | exact ha | exact hb | exact hc | exact hd)


-- @@ L212-220 verbatim
lemma matrix_trace_conjugate (g h : SL(2,ℂ)) :
    (g⁻¹*h*g) 0 0+(g⁻¹*h*g) 1 1=h 0 0+h 1 1 := by
  have ht := Matrix.trace_mul_cycle
    (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ))
    (h:Matrix (Fin 2) (Fin 2) ℂ) (g:Matrix (Fin 2) (Fin 2) ℂ)
  have hi : (g:Matrix (Fin 2) (Fin 2) ℂ)*(((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ))=1 :=
    congrArg (fun A : SL(2,ℂ) => (A:Matrix (Fin 2) (Fin 2) ℂ)) (mul_inv_cancel g)
  rw [hi,Matrix.one_mul] at ht
  simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two] using ht


-- @@ L222-254 verbatim
lemma levelThree_unitary_conjugate_eq_one (M : levelThree) (g : SL(2,ℂ))
    (hk : g⁻¹*complexMatrix M*g∈compactSubgroup) : M=1 := by
  let k := g⁻¹*complexMatrix M*g
  have htr := matrix_trace_conjugate g (complexMatrix M)
  have hnorm : ‖complexMatrix M 0 0+complexMatrix M 1 1-2‖≤4 := by
    have hb := unitary_trace_norm_le_two k hk
    rw [htr] at hb
    have hn := norm_sub_le (complexMatrix M 0 0+complexMatrix M 1 1) (2:ℂ)
    norm_num at hn
    linarith
  obtain ⟨a,ha⟩ := levelThree_trace_divisible_nine M
  have hmap : complexMatrix M 0 0+complexMatrix M 1 1-2=(9:ℂ)*eisEmbedding a := by
    change eisEmbedding ((M:SL(2,O)) 0 0)+eisEmbedding ((M:SL(2,O)) 1 1)-2=(9:ℂ)*eisEmbedding a
    simpa only [map_add,map_sub,map_ofNat,map_mul] using congrArg eisEmbedding ha
  have haz : a=0 := by
    by_contra hne
    have hn := one_le_normSq_embedding a hne
    rw [Complex.normSq_eq_norm_sq] at hn
    have hn1 : 1≤‖eisEmbedding a‖ := by nlinarith [norm_nonneg (eisEmbedding a)]
    rw [hmap,norm_mul] at hnorm
    norm_num at hnorm
    linarith
  have ht2 : k 0 0+k 1 1=2 := by
    rw [htr]
    apply sub_eq_zero.mp
    rw [hmap,haz,map_zero,mul_zero]
  have hk1 : k=1 := unitary_trace_two_eq_one k hk ht2
  have hM1 : complexMatrix M=1 := by
    have h := congrArg (fun A : SL(2,ℂ) => g*A*g⁻¹) hk1
    simpa [k,mul_assoc] using h
  apply Subtype.ext
  apply integralComplexMatrix_injective
  simpa only [map_one,integralComplexMatrix_levelThree] using hM1


-- @@ L256-261 verbatim
theorem levelThree_action_free (M : levelThree) (w : HyperbolicSpace)
    (hw : complexMatrix M • w=w) : M=1 := by
  induction w using Quotient.inductionOn with | _ g =>
    apply levelThree_unitary_conjugate_eq_one M g
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hw.symm)
    simpa only [mul_assoc,smul_eq_mul] using hrel


-- @@ L263-263 verbatim
end


-- @@ L265-265 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

-- @@ L266-266 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L268-272 verbatim
def hyperbolicKeyCoordinates (w : HyperbolicSpace) : Fin 9 → ℝ :=
  ![hyperbolicFrobenius w,(hyperbolicGram w 0 0).re,(hyperbolicGram w 0 0).im,
    (hyperbolicGram w 0 1).re,(hyperbolicGram w 0 1).im,
    (hyperbolicGram w 1 0).re,(hyperbolicGram w 1 0).im,
    (hyperbolicGram w 1 1).re,(hyperbolicGram w 1 1).im]


-- @@ L274-274 verbatim
def hyperbolicOrderKey (w : HyperbolicSpace) : Lex (Fin 9 → ℝ) := toLex (hyperbolicKeyCoordinates w)


-- @@ L276-289 verbatim
lemma hyperbolicOrderKey_injective : Function.Injective hyperbolicOrderKey := by
  intro w u h
  have hc : hyperbolicKeyCoordinates w=hyperbolicKeyCoordinates u := congrArg ofLex h
  apply hyperbolicGram_injective
  funext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  · exact congrFun hc 1
  · exact congrFun hc 2
  · exact congrFun hc 3
  · exact congrFun hc 4
  · exact congrFun hc 5
  · exact congrFun hc 6
  · exact congrFun hc 7
  · exact congrFun hc 8


-- @@ L291-295 verbatim
lemma hyperbolicOrderKey_lt_of_frobenius {w u : HyperbolicSpace}
    (h : hyperbolicFrobenius w<hyperbolicFrobenius u) : hyperbolicOrderKey w<hyperbolicOrderKey u := by
  refine ⟨0,?_,h⟩
  intro j hj
  exact False.elim (not_lt_of_ge (Fin.zero_le j) hj)


-- @@ L297-297 verbatim
attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous


-- @@ L299-301 verbatim
lemma hyperbolicKeyCoordinates_continuous (i : Fin 9) :
    Continuous (fun w => hyperbolicKeyCoordinates w i) := by
  fin_cases i <;> simp only [hyperbolicKeyCoordinates] <;> fun_prop


-- @@ L303-319 verbatim
lemma hyperbolicOrderKey_lt_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)<hyperbolicOrderKey (g x)} := by
  change MeasurableSet {x | ∃i : Fin 9,(∀j : Fin 9,j < i → hyperbolicKeyCoordinates (f x) j=hyperbolicKeyCoordinates (g x) j) ∧
    hyperbolicKeyCoordinates (f x) i<hyperbolicKeyCoordinates (g x) i}
  simp only [Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (isClosed_eq ((hyperbolicKeyCoordinates_continuous j).comp hf)
      ((hyperbolicKeyCoordinates_continuous j).comp hg)).measurableSet
  · exact measurableSet_lt ((hyperbolicKeyCoordinates_continuous i).comp hf).measurable
      ((hyperbolicKeyCoordinates_continuous i).comp hg).measurable


-- @@ L321-330 verbatim
lemma hyperbolicOrderKey_le_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)} := by
  have he : {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)}=
      {x | hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)}ᶜ := by
    ext x
    change hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x) ↔ ¬hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)
    exact ⟨fun h => not_lt_of_ge h,fun h => le_of_not_gt h⟩
  rw [he]
  exact (hyperbolicOrderKey_lt_measurable g f hg hf).compl


-- @@ L332-335 verbatim
instance integralSLCountable : Countable (SL(2,O)) := by
  let : Countable O := latticeCoordEquiv.injective.countable
  let : Countable (Matrix (Fin 2) (Fin 2) O) := inferInstanceAs (Countable (Fin 2 → Fin 2 → O))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) O // A.det=1})


-- @@ L337-338 verbatim
instance integralSubgroupHyperbolicAction (H : Subgroup (SL(2,O))) : MulAction H HyperbolicSpace :=
  MulAction.compHom HyperbolicSpace (integralComplexMatrix.comp H.subtype)


-- @@ L340-341 verbatim
lemma integralSubgroup_smul (H : Subgroup (SL(2,O))) (M : H) (w : HyperbolicSpace) :
    M • w=integralComplexMatrix (M:SL(2,O)) • w := rfl


-- @@ L343-344 verbatim
def hyperbolicFundamentalSet (H : Subgroup (SL(2,O))) : Set HyperbolicSpace :=
  {w | ∀M : H,hyperbolicOrderKey w≤hyperbolicOrderKey (M • w)}


-- @@ L346-353 verbatim
lemma hyperbolicFundamentalSet_measurable (H : Subgroup (SL(2,O))) :
    MeasurableSet (hyperbolicFundamentalSet H) := by
  unfold hyperbolicFundamentalSet
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro M
  exact hyperbolicOrderKey_le_measurable _ _ continuous_id
    (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O))))


-- @@ L355-366 verbatim
lemma exists_key_orbit_minimum (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,∀N : H,hyperbolicOrderKey (M • w)≤hyperbolicOrderKey (N • w) := by
  let S : Set H := {M | hyperbolicFrobenius (M • w)≤hyperbolicFrobenius w}
  have hs : Set.Finite S := subgroup_hyperbolic_sublevel_finite H w _
  have hne : S.Nonempty := ⟨1,by simp [S]⟩
  obtain ⟨M,hM,hmin⟩ := Set.exists_min_image S (fun M : H => hyperbolicOrderKey (M • w)) hs hne
  refine ⟨M,fun N => ?_⟩
  by_cases hN : N∈S
  · exact hmin N hN
  · apply le_of_lt
    apply hyperbolicOrderKey_lt_of_frobenius
    exact hM.trans_lt (lt_of_not_ge hN)


-- @@ L368-372 verbatim
lemma hyperbolicFundamentalSet_covers (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,M • w∈hyperbolicFundamentalSet H := by
  obtain ⟨M,hM⟩ := exists_key_orbit_minimum H w
  refine ⟨M,fun N => ?_⟩
  simpa only [mul_smul] using hM (N*M)


-- @@ L374-380 verbatim
lemma hyperbolicFundamentalSet_orbit_unique (H : Subgroup (SL(2,O))) (w : HyperbolicSpace)
    (hw : w∈hyperbolicFundamentalSet H) (M : H)
    (hMw : M • w∈hyperbolicFundamentalSet H) : M • w=w := by
  apply hyperbolicOrderKey_injective
  apply le_antisymm
  · simpa only [inv_smul_smul] using hMw M⁻¹
  · exact hw M


-- @@ L382-386 verbatim
lemma subgroup_action_free (H : Subgroup (SL(2,O))) (hH : H≤levelThree) (M : H)
    (w : HyperbolicSpace) (hM : M • w=w) : M=1 := by
  have he := levelThree_action_free (⟨(M:SL(2,O)),hH M.property⟩ : levelThree) w hM
  apply Subtype.ext
  exact congrArg (fun N : levelThree => (N:SL(2,O))) he


-- @@ L388-398 verbatim
theorem hyperbolicFundamentalSet_isFundamentalDomain (H : Subgroup (SL(2,O))) (hH : H≤levelThree) :
    IsFundamentalDomain H (hyperbolicFundamentalSet H) hyperbolicVolume := by
  apply IsFundamentalDomain.mk' (hyperbolicFundamentalSet_measurable H).nullMeasurableSet
  intro w
  obtain ⟨M,hM⟩ := hyperbolicFundamentalSet_covers H w
  refine ⟨M,hM,fun N hN => ?_⟩
  have he : (N*M⁻¹) • (M • w)=M • w :=
    hyperbolicFundamentalSet_orbit_unique H (M • w) hM (N*M⁻¹) (by
      simpa only [mul_smul,inv_smul_smul] using hN)
  have hNM : N*M⁻¹=1 := subgroup_action_free H hH _ _ he
  exact mul_inv_eq_one.mp hNM


-- @@ L400-402 verbatim
lemma globalKubotaKernel_le_levelThree : globalKubotaKernel≤levelThree := by
  intro M hM
  exact ((globalKubotaKernel_mem M).mp hM).choose


-- @@ L404-406 verbatim
theorem globalKubotaKernel_isFundamentalDomain :
    IsFundamentalDomain globalKubotaKernel (hyperbolicFundamentalSet globalKubotaKernel) hyperbolicVolume :=
  hyperbolicFundamentalSet_isFundamentalDomain _ globalKubotaKernel_le_levelThree


-- @@ L408-408 verbatim
end


-- @@ L410-410 verbatim
open Filter MeasureTheory

-- @@ L411-411 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L413-413 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

-- @@ L414-414 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L416-418 verbatim
instance integralSubgroupMeasurableAction (H : Subgroup (SL(2,O))) :
    MeasurableConstSMul H HyperbolicSpace :=
  ⟨fun M => (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable⟩


-- @@ L420-426 verbatim
instance integralSubgroupVolumeInvariant (H : Subgroup (SL(2,O))) :
    SMulInvariantMeasure H HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul M s hs := by
    have hm := (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s)
      (hyperbolicVolume_invariant (integralComplexMatrix (M:SL(2,O))))
    simpa only [Measure.map_apply hm hs,integralSubgroup_smul] using he


-- @@ L428-429 verbatim
lemma measurable_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Measurable (integralOrbitProjection H) := measurable_quotient_mk' (s := integralOrbitRel H)


-- @@ L431-432 verbatim
def integralQuotientVolume (H : Subgroup (SL(2,O))) : Measure (IntegralOrbitQuotient H) :=
  Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))


-- @@ L434-437 verbatim
lemma quotient_projection_measurePreserving (H : Subgroup (SL(2,O))) :
    MeasurePreserving (integralOrbitProjection H)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)) (integralQuotientVolume H) :=
  ⟨measurable_integralOrbitProjection H,rfl⟩


-- @@ L439-452 verbatim
theorem integralQuotientVolume_independent (H : Subgroup (SL(2,O))) (hH : H≤levelThree)
    (D : Set HyperbolicSpace) (hD : IsFundamentalDomain H D hyperbolicVolume) :
    Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict D)=integralQuotientVolume H := by
  apply Measure.ext
  intro S hS
  have hp := measurable_integralOrbitProjection H
  unfold integralQuotientVolume
  rw [Measure.map_apply hp hS,Measure.map_apply hp hS,Measure.restrict_apply (hp hS),
    Measure.restrict_apply (hp hS)]
  apply hD.measure_set_eq (hyperbolicFundamentalSet_isFundamentalDomain H hH) (hp hS)
  intro M
  ext w
  change integralOrbitProjection H (M • w)∈S ↔ integralOrbitProjection H w∈S
  rw [integralSubgroup_smul,integralOrbitProjection_eq]


-- @@ L454-458 verbatim
lemma integralQuotientVolume_integral (H : Subgroup (SL(2,O)))
    (f : IntegralOrbitQuotient H → ℂ) (hf : AEStronglyMeasurable f (integralQuotientVolume H)) :
    (∫q,f q∂integralQuotientVolume H)=
      ∫w in hyperbolicFundamentalSet H,f (integralOrbitProjection H w)∂hyperbolicVolume :=
  integral_map (measurable_integralOrbitProjection H).aemeasurable hf


-- @@ L460-474 verbatim
lemma hyperbolicEuclideanVolume_ne_zero : hyperbolicEuclideanVolume≠0 := by
  have hU : IsOpen euclideanUpperHalf := isOpen_lt continuous_const (by fun_prop)
  have hne : euclideanUpperHalf.Nonempty := ⟨WithLp.toLp 2 ![0,0,1],by norm_num [euclideanUpperHalf]⟩
  have hpos : 0<volume euclideanUpperHalf := hU.measure_pos volume hne
  have hAC : (volume.restrict euclideanUpperHalf) ≪ hyperbolicEuclideanVolume := by
    apply withDensity_absolutelyContinuous' hyperbolicDensity_measurable.aemeasurable
    filter_upwards [ae_restrict_mem euclideanUpperHalf_measurable] with p hp
    apply ne_of_gt
    change 0<ENNReal.ofReal ((p 2)^3)⁻¹
    apply ENNReal.ofReal_pos.mpr
    exact inv_pos.mpr (pow_pos hp 3)
  intro hz
  have hh : (volume.restrict euclideanUpperHalf) Set.univ=0 := hAC (by rw [hz]; simp)
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  exact hpos.ne' hh


-- @@ L476-477 verbatim
lemma hyperbolicVolume_ne_zero : hyperbolicVolume≠0 :=
  (Measure.map_ne_zero_iff euclideanToHyperbolic_measurable.aemeasurable).mpr hyperbolicEuclideanVolume_ne_zero


-- @@ L479-487 verbatim
lemma integralQuotientVolume_ne_zero (H : Subgroup (SL(2,O))) (hH : H≤levelThree) :
    integralQuotientVolume H≠0 := by
  apply (Measure.map_ne_zero_iff (measurable_integralOrbitProjection H).aemeasurable).mpr
  intro hz
  have hD := MeasureTheory.IsFundamentalDomain.measure_ne_zero hyperbolicVolume_ne_zero
    (hyperbolicFundamentalSet_isFundamentalDomain H hH)
  have hh := congrArg (fun ν : Measure HyperbolicSpace => ν Set.univ) hz
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  exact hD hh


-- @@ L489-489 verbatim
abbrev KernelQuotientL2 := Lp ℂ 2 (integralQuotientVolume globalKubotaKernel)

-- @@ L490-490 verbatim
example : InnerProductSpace ℂ KernelQuotientL2 := inferInstance

-- @@ L491-491 verbatim
example : CompleteSpace KernelQuotientL2 := inferInstance


-- @@ L493-499 verbatim
lemma kernel_eisenstein_invariant (M : globalKubotaKernel) (s : ℂ) (hs : 2<s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (M • w)=hyperbolicEisenstein s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := hyperbolicEisenstein_automorphy (⟨(M:SL(2,O)),hM⟩ : levelThree) s hs w
  rw [hchar,one_mul] at he
  exact he


-- @@ L501-506 verbatim
def kernelQuotientEisenstein (s : ℂ) (hs : 2<s.re) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (hyperbolicEisenstein s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_eisenstein_invariant M s hs w).symm)


-- @@ L508-510 verbatim
lemma kernelQuotientEisenstein_mk (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    kernelQuotientEisenstein s hs (integralOrbitProjection globalKubotaKernel w)=
      hyperbolicEisenstein s w := rfl


-- @@ L512-517 verbatim
lemma kernel_seed_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (M • w)=smoothCuspSeed a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeed_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he


-- @@ L519-524 verbatim
lemma kernel_defect_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (M • w)=smoothCuspSeedDefect a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeedDefect_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he


-- @@ L526-530 verbatim
def kernelQuotientSeed (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeed a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_seed_invariant a b s M w).symm)


-- @@ L532-536 verbatim
def kernelQuotientDefect (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeedDefect a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_defect_invariant a b s M w).symm)


-- @@ L538-538 verbatim
end CubicEisenstein


-- @@ L540-540 verbatim
open scoped BigOperators Classical

-- @@ L541-541 verbatim
namespace CompletedGauss

-- @@ L542-542 verbatim
open ActualEisensteinCubic

-- @@ L543-543 verbatim
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)


-- @@ L545-547 verbatim
def largeCubeCoefficient (H₀ : ℝ) (B : Ideal O) : ℂ :=
  if B=⊥ then 0 else ∑ H∈idealDivisors B,
    if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0


-- @@ L549-550 verbatim
theorem largeCubeCoefficient_zero (H₀ : ℝ) : largeCubeCoefficient H₀ ⊥=0 := by
  simp [largeCubeCoefficient]


-- @@ L552-568 verbatim
theorem largeCubeCoefficient_norm_le (H₀ : ℝ) (B : Ideal O) :
    ‖largeCubeCoefficient H₀ B‖ ≤ (idealDivisors B).card := by
  by_cases hB : B=⊥
  · simp [hB,largeCubeCoefficient]
  · rw [largeCubeCoefficient,ite_eq_right hB]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ H∈idealDivisors B,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
        · simp only [ite_eq_left h]
          by_cases hsf : Squarefree H
          · simp [hsf.moebius_eq]
          · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsf]
        · simp [h]
      _ = _ := by simp


-- @@ L570-581 verbatim
theorem largeCubeCoefficient_support (H₀ : ℝ) (B : Ideal O)
    (h : largeCubeCoefficient H₀ B ≠ 0) : B≠⊥ ∧ H₀ ≤ (Ideal.absNorm B : ℝ) := by
  have hB : B≠⊥ := fun hb => h (by simp [hb,largeCubeCoefficient])
  refine ⟨hB,?_⟩
  rw [largeCubeCoefficient,ite_eq_right hB] at h
  obtain ⟨H,hH,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hlarge : H₀ ≤ (Ideal.absNorm H : ℝ) := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  have hdiv := (mem_idealDivisors hB).mp hH
  have hpos : 0 < Ideal.absNorm B := Nat.pos_iff_ne_zero.mpr (fun hn => hB (Ideal.absNorm_eq_zero_iff.mp hn))
  exact hlarge.trans (by exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hdiv))


-- @@ L583-633 verbatim
theorem large_cube_convolution (H₀ : ℝ) (c : Ideal O →* ℂ) (hc0 : c 0=0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2))).Finite) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then
        (UniqueFactorizationMonoid.moebius H : ℂ)*c (H*J)*f (H*J) else 0) =
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*c B*f B := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.1 : ℝ) then
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2) else 0
  have hF : Summable F := summable_of_hasFiniteSupport (hfinite.subset (by
    intro p hp
    by_contra hn
    have he : (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2)=0 := not_ne_iff.mp hn
    exact hp (by dsimp [F];rw [he];simp)))
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.val)=largeCubeCoefficient H₀ B*c B*f B := by
    by_cases hB : B=0
    · subst B
      have hz : ∀ p : MulFiber 0,F p.val=0 := by
        intro p
        dsimp [F]
        rw [p.property,hc0]
        simp
      simp [hz,largeCubeCoefficient]
    · let e := mulFiberDivisorEquiv B hB
      have hsum : (∑' p : MulFiber B,
          if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0) =
          largeCubeCoefficient H₀ B := by
        calc
          _ = ∑' H : {H : Ideal O // H∈idealDivisors B},
              if H₀ ≤ (Ideal.absNorm H.val : ℝ) then (UniqueFactorizationMonoid.moebius H.val : ℂ) else 0 :=
            e.tsum_eq _
          _ = _ := by
            rw [tsum_fintype,largeCubeCoefficient,ite_eq_right (show B≠⊥ from hB)]
            exact (Finset.sum_subtype (idealDivisors B) (fun H => Iff.rfl)
              (fun H => if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0)).symm
      calc
        _ = ∑' p : MulFiber B,
            (if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0)*(c B*f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property]
          split_ifs <;> ring
        _ = _ := by rw [tsum_mul_right,hsum];ring
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.val) (∑' p,F p) at hs
  simp_rw [hfiber] at hs
  rw [← hF.tsum_prod]
  exact hs.tsum_eq.symm


-- @@ L635-658 verbatim
theorem large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=expandedTerm Ψ W X I H J := by
    simp only [f,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring


-- @@ L660-700 verbatim
theorem large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        completedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then expandedTerm Ψ W X p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((finite_support_expandedTerm Ψ W hW X hX).subset (by
      intro p hp
      by_contra hn
      have he : expandedTerm Ψ W X p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [ite_eq_left h,weighted_completedT_reopen]
      · simp only [ite_eq_right h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (large_cube_inner_reopen Ψ W hW X H₀ hX)


-- @@ L702-732 verbatim
theorem completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        completedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedT Ψ W (X/(Ideal.absNorm H : ℝ)^3)
  have hf := cube_inverse_finite_support Ψ W hW X hX
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [completed_cube_inverse Ψ W hW X hX,←large_cube_reopen Ψ W hW X H₀ hX]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]


-- @@ L734-738 verbatim
theorem large_cube_block_progress (H₀ B F : ℝ) (hB : 0 ≤ B) (hF : 1 ≤ F)
    (I : Ideal O) (hI : largeCubeCoefficient H₀ I ≠ 0) (hIB : (Ideal.absNorm I : ℝ) ≤ B) :
    H₀ ≤ B*F := by
  have hlarge := (largeCubeCoefficient_support H₀ I hI).2
  exact (hlarge.trans hIB).trans (le_mul_of_one_le_right hB hF)


-- @@ L740-740 verbatim
end CompletedGauss


-- @@ L742-742 verbatim
end


-- @@ L744-744 verbatim
end OAI
