import OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss
import OAI.NumberTheory.DirichletL.CubicSieve.PooledRows


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open MulChar AddChar

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory Real

-- @@ L14-14 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L15-15 verbatim
open Finset Complex

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open scoped Classical

-- @@ L18-18 verbatim
open Filter Real Asymptotics

-- @@ L19-19 verbatim
open ActualEisensteinCubic

-- @@ L20-20 verbatim
open Filter

-- @@ L21-21 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L22-22 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L23-23 verbatim
open Filter

-- @@ L24-24 verbatim
open scoped Topology

-- @@ L25-25 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L26-26 verbatim
open MulChar AddChar

-- @@ L27-27 verbatim
open Filter Asymptotics

-- @@ L28-28 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L29-29 verbatim
open Filter

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open MulChar AddChar

-- @@ L32-32 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L33-33 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L34-34 verbatim
open scoped Topology

-- @@ L35-35 verbatim
open Filter Asymptotics

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Filter Asymptotics

-- @@ L42-42 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L43-43 verbatim
open scoped Topology

-- @@ L44-44 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L45-45 verbatim
open Filter

-- @@ L46-46 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L47-47 verbatim
open scoped Topology

-- @@ L48-48 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L49-49 verbatim
open scoped Topology

-- @@ L50-50 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L51-51 verbatim
open scoped Topology

-- @@ L52-52 verbatim
open MeasureTheory Real

-- @@ L53-53 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L59-59 verbatim
open scoped BigOperators Classical

-- @@ L60-60 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L61-61 verbatim
open scoped BigOperators Classical

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical

-- @@ L66-66 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L67-67 verbatim
open MeasureTheory Set

-- @@ L68-68 verbatim
open scoped BigOperators

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open scoped BigOperators Classical

-- @@ L71-71 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L72-72 verbatim
open scoped BigOperators


-- @@ L74-74 verbatim
open scoped BigOperators Classical

-- @@ L75-75 verbatim
namespace InitialMeanSquare

-- @@ L76-76 verbatim
open ActualEisensteinCubic SecondPassArithmetic

-- @@ L77-77 verbatim
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

-- @@ L78-78 verbatim
open MixedCrossSeparation (columnCoefficient)


-- @@ L80-83 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


-- @@ L85-86 verbatim
def inputColumn (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*H S


-- @@ L88-92 verbatim
def transformedColumn (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S*Ψ (∏i∈S,p i)*
    rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)*
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h*H S


-- @@ L94-98 verbatim
omit [DecidableEq ι] in
lemma inputColumn_eq (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) :
    inputColumn p Ψ b d H S=secondInputCoefficient p hg Ψ (b*d) 1 1 H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [inputColumn,secondInputCoefficient,hr,one_pow,mul_one]


-- @@ L100-104 verbatim
lemma transformedColumn_eq (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    transformedColumn p hp hcop hg Ψ b d h H S=
      secondPreColumn p hp hcop hg Ψ (b*d) 1 1 d h H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [transformedColumn,secondPreColumn,hr,one_pow,mul_one]


-- @@ L106-115 verbatim
theorem transformedColumn_union (hpr : ∀i,lambda^2∣p i-1)
    (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    transformedColumn p hp hcop hg Ψ b d h H (V∪N)=
      transformedColumn p hp hcop hg Ψ b d h (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
        (fun U => H (V∪U)) N := by
  simp_rw [transformedColumn_eq p hp hcop hg]
  simpa only [mul_one,one_mul] using secondPreColumn_union p hp hcop hg hpr
    Ψ b 1 1 1 d h H V N hVN


-- @@ L117-122 verbatim
def initialPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) : ℂ :=
  ∑S∈F.powerset,∑T∈F.powerset,if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S*inputColumn p Ψ₁ b d H₁ S)*
      (supportMobius (fun i => Ideal.span {p i}) T*inputColumn p Ψ₂ b d H₂ T)*
      activeGaussRowFactor p hp hinj hg T S d h else 0


-- @@ L124-128 verbatim
lemma initialPair_eq (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      secondActualPair p hp hg hinj F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂ := by
  simp only [initialPair,secondActualPair,inputColumn_eq p hg,mul_one]


-- @@ L130-132 verbatim
def childSum (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) : ℂ :=
  ∑N∈F.powerset,secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
    (fun U => H (V∪U)) N


-- @@ L134-138 verbatim
lemma childSum_eq (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) :
    childSum p hp hcop hg F V Ψ b d h H=
      secondChildSum p hp hcop hg F V Ψ b 1 1 1 d h H := by
  rw [secondChildSum_fixed_pool]
  simp only [childSum,mul_one,one_mul]


-- @@ L140-149 verbatim
theorem initialPair_eq_children (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      ∑z : SecondRayIndex,∑V∈F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ b 1 1 1 d h (z,V)*
        star (childSum p hp hcop hg F V (secondRayMinus Ψ₁ z) b d h H₁)*
        childSum p hp hcop hg F V (secondRayPlus Ψ₂ z) b d (-h) H₂ := by
  simp_rw [initialPair_eq p hp hg,childSum_eq p hp hcop hg]
  exact secondActualPair_eq_children p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂


-- @@ L151-151 verbatim
end InitialMeanSquare


-- @@ L153-153 verbatim
namespace CubicEisenstein


-- @@ L155-155 verbatim
section

-- @@ L156-156 verbatim
open Filter MeasureTheory

-- @@ L157-157 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal


-- @@ L159-160 verbatim
instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩


-- @@ L162-177 verbatim
instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)


-- @@ L179-206 verbatim
instance kernelQuotientVolume_fullSupport :
    Measure.IsOpenPosMeasure (integralQuotientVolume globalKubotaKernel) where
  open_pos U hU hne := by
    let quotientProjection := integralOrbitProjection globalKubotaKernel
    have hp : Measurable quotientProjection := measurable_integralOrbitProjection _
    have hpre : IsOpen (quotientProjection ⁻¹' U) := hU.preimage (continuous_integralOrbitProjection _)
    have hpren : (quotientProjection ⁻¹' U).Nonempty := by
      obtain ⟨q,hq⟩ := hne
      obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
      exact ⟨w,hq⟩
    intro hzero
    have hd : hyperbolicVolume ((quotientProjection ⁻¹' U)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
      simpa only [integralQuotientVolume,quotientProjection,Measure.map_apply (measurable_integralOrbitProjection _) hU.measurableSet,
        Measure.restrict_apply ((measurable_integralOrbitProjection _) hU.measurableSet)] using hzero
    have hinv : ∀M:globalKubotaKernel,M • (quotientProjection ⁻¹' U)=quotientProjection ⁻¹' U := by
      intro M
      ext w
      constructor
      · rintro ⟨u,hu,rfl⟩
        change quotientProjection (M • u)∈U
        change quotientProjection u∈U at hu
        rwa [show quotientProjection (M • u)=quotientProjection u from integralOrbitProjection_eq _ M u]
      · intro hw
        refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
        change quotientProjection (M⁻¹ • w)∈U
        rwa [show quotientProjection (M⁻¹ • w)=quotientProjection w from integralOrbitProjection_eq _ M⁻¹ w]
    have hz := globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (quotientProjection ⁻¹' U) hinv hd
    exact hpre.measure_ne_zero _ hpren hz


-- @@ L208-211 verbatim
lemma kernel_continuous_eq_of_ae_eq (f g : IntegralOrbitQuotient globalKubotaKernel → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (he : f =ᵐ[integralQuotientVolume globalKubotaKernel] g) : f=g :=
  (MeasureTheory.Measure.eq_of_ae_eq he hf hg)


-- @@ L213-213 verbatim
end


-- @@ L215-215 verbatim
open Filter MeasureTheory

-- @@ L216-216 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal


-- @@ L218-218 verbatim
open ConcreteTraceCRT

-- @@ L219-219 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L221-232 verbatim
lemma integral_upper_triangular_height (M : SL(2,O)) (hc : M 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix M • upperPoint z v hv)=v := by
  have hdet : M 0 0*M 1 1=1 := by
    have h := M.property
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using h
  let u : Oˣ := ⟨M 1 1,M 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (M 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hyperbolicHeight_action_upperPoint]
  simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
    hn,one_pow,]
  norm_num


-- @@ L234-265 verbatim
lemma smoothCuspSeedDefect_high_zero (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hvlarge : max b a⁻¹<v) :
    smoothCuspSeedDefect a b s (integralComplexMatrix M • upperPoint z v hv)=0 := by
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  have hz : (fun r : CuspCosets => cuspCutoffTerm 1 (cuspSeedDefectProfile a b s) r
      (integralComplexMatrix M • upperPoint z v hv))=(fun _ => (0:ℂ)) := by
    funext r
    have hout : cosetHeight r (integralComplexMatrix M • upperPoint z v hv)<a ∨
        b<cosetHeight r (integralComplexMatrix M • upperPoint z v hv) := by
      induction r using Quotient.inductionOn with
      | _ N =>
        change cosetHeight (cosetOf N) _<a ∨ b<cosetHeight (cosetOf N) _
        rw [cosetHeight_cosetOf]
        change hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
          (integralComplexMatrix M • upperPoint z v hv))<a ∨
          b<hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
            (integralComplexMatrix M • upperPoint z v hv))
        simp only [←mul_smul,←map_mul]
        by_cases hc : ((N:SL(2,O))*M) 1 0=0
        · right
          rw [integral_upper_triangular_height _ hc]
          exact (le_max_left _ _).trans_lt hvlarge
        · left
          have hh := integral_hyperbolicHeight_mul_le_one ((N:SL(2,O))*M) hc (upperPoint z v hv)
          rw [hyperbolicHeight_upperPoint] at hh
          have hav : 1<a*v := by
            have hlt : a⁻¹<v := (le_max_right _ _).trans_lt hvlarge
            have hm := mul_lt_mul_of_pos_left hlt ha
            simpa only [mul_inv_cancel₀ ha.ne'] using hm
          nlinarith
    simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
  rw [hz,tsum_zero]


-- @@ L267-281 verbatim
theorem kernelQuotientDefect_hasCompactSupport (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    HasCompactSupport (kernelQuotientDefect a b s) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max b a⁻¹)
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max b a⁻¹) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max b a⁻¹) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (smoothCuspSeedDefect_high_zero a b ha hab s r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)


-- @@ L283-284 verbatim
def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]


-- @@ L286-292 verbatim
lemma hyperbolicSpatialCoordinates_continuous : Continuous hyperbolicSpatialCoordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous


-- @@ L294-295 verbatim
lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w


-- @@ L297-303 verbatim
lemma hyperbolicSpatialCoordinates_reconstruct (w : HyperbolicSpace) :
    upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+(hyperbolicSpatialCoordinates w 1:ℂ)*Complex.I)
      (hyperbolicSpatialCoordinates w 2) (hyperbolicSpatialCoordinates_positive w)=w := by
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+((hyperbolicHorizontal w).im:ℂ)*Complex.I)
    (hyperbolicHeight w) (hyperbolicHeight_pos w)=w
  rw [Complex.re_add_im]
  exact upperCoordinates_right_inverse w


-- @@ L305-316 verbatim
lemma smoothCuspSeedDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (smoothCuspSeedDefect a b s) := by
  have heq : smoothCuspSeedDefect a b s=
      fun w => heightPoincareField (cuspSeedDefectProfile a b s) (hyperbolicSpatialCoordinates w) := by
    funext w
    nth_rw 1 [←hyperbolicSpatialCoordinates_reconstruct w]
    exact smoothCuspSeedDefect_coordinate a b s ha hab _ (hyperbolicSpatialCoordinates_positive w)
  rw [heq,continuous_iff_continuousAt]
  intro w
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialCoordinates_positive w)).continuousAt.comp
      hyperbolicSpatialCoordinates_continuous.continuousAt


-- @@ L318-320 verbatim
lemma kernelQuotientDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientDefect a b s) :=
  (smoothCuspSeedDefect_continuous a b s ha hab).quotient_lift _


-- @@ L322-329 verbatim
lemma actual_smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (smoothCuspSeedDefectField a b s) p := by
  have heq : smoothCuspSeedDefectField a b s =ᶠ[𝓝 p]
      heightPoincareField (cuspSeedDefectProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedDefectField_eq a b s ha hab q hq
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq


-- @@ L331-331 verbatim
end CubicEisenstein


-- @@ L333-333 verbatim
namespace SecondPassArithmetic


-- @@ L335-335 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L336-336 verbatim
open MeasureTheory

-- @@ L337-337 verbatim
open ActualEisensteinCubic

-- @@ L338-338 verbatim
open FirstPassCubeLabels (firstLogDensity)


-- @@ L340-343 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


-- @@ L345-359 verbatim
theorem globalChildBudget_height (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
      ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*
        globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp only [globalChildBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro q hq
  simp only [globalDescentWeight,norm_zero,add_zero,one_pow,mul_one]
  ring


-- @@ L361-368 verbatim
theorem globalChildBudget_density (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
    firstLogDensity 0 t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  rw [globalChildBudget_height,← mul_assoc,FirstPassCubeLabels.firstLogDensity_pair_moment]


-- @@ L370-378 verbatim
theorem globalChildBudget_integral (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side) =
    (∫ t : ℝ,firstLogDensity 0 t)*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp_rw [globalChildBudget_density]
  exact integral_mul_const _ _


-- @@ L380-384 verbatim
def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b∈s,w b*∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2


-- @@ L386-404 verbatim
theorem globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    Integrable (fun t => firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) := by
  simp only [globalFirstFiniteEnergy,Finset.mul_sum]
  apply integrable_finsetSum
  intro b hb
  apply integrable_finsetSum
  intro z hz
  have hi := firstCoreInputRow_integrable p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (FirstPassCubeLabels.normalizedColumn p
      (fun A => g (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r z
    (FirstPassCubeLabels.firstLogDensity_integrable J)
  simpa only [globalFirstCoreRow,mul_left_comm] using hi.const_mul (w b)


-- @@ L406-406 verbatim
end SecondPassArithmetic


-- @@ L408-408 verbatim
open scoped BigOperators Classical

-- @@ L409-409 verbatim
namespace CanonicalQuadraticSieve


-- @@ L411-411 verbatim
open ActualEisensteinCubic


-- @@ L413-445 verbatim
theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring


-- @@ L447-457 verbatim
theorem ideal_reciprocal_cauchy (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (v : Ideal O → ℂ) :
    ‖∑I∈S,v I‖^2≤(∑I∈S,1/(Ideal.absNorm I:ℝ))*
      (∑I∈S,(Ideal.absNorm I:ℝ)*‖v I‖^2) := by
  have hpos (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])


-- @@ L459-459 verbatim
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel


-- @@ L461-462 verbatim
def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => squarePart I=A)


-- @@ L464-474 verbatim
theorem columnSquareFiber_injective (S : Finset (Ideal O)) (A : Ideal O) :
    Function.Injective (fun I : columnSquareFiber S A => squarefreePart I.val) := by
  intro I J he
  change squarefreePart I.val=squarefreePart J.val at he
  apply Subtype.ext
  have hi := (Finset.mem_filter.mp I.property).2
  have hj := (Finset.mem_filter.mp J.property).2
  calc
    I.val = A^2*squarefreePart I.val := by simpa only [hi] using (squarePart_sq_mul_squarefreePart I.val).symm
    _ = A^2*squarefreePart J.val := by rw [he]
    _ = J.val := by simpa only [hj] using squarePart_sq_mul_squarefreePart J.val


-- @@ L476-492 verbatim
theorem columnSquareFiber_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Admissible (squarefreePart I.val) ∧
      (Ideal.absNorm (squarefreePart I.val):ℝ)≤X/(Ideal.absNorm A:ℝ)^2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hp := (supported_square_parts I.val).mp hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A≠0 := by rw [←ha]; exact hp.1.1
  have hAn : 0<(Ideal.absNorm A:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨hp.2,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn : (Ideal.absNorm A:ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
    have hh : (Ideal.absNorm (squarePart I.val):ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
      exact_mod_cast norm_decomposition I.val
    simpa only [ha] using hh
  nlinarith


-- @@ L494-511 verbatim
theorem columnSquareFiber_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hscale : 1≤X/(Ideal.absNorm A:ℝ)^2) :
    ((columnSquareFiber S A).card:ℝ)≤128*(X/(Ideal.absNorm A:ℝ)^2) := by
  let T := (columnSquareFiber S A).image squarefreePart
  have hcard : T.card=(columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩:columnSquareFiber S A)=(⟨J,hJ⟩:columnSquareFiber S A) :=
      columnSquareFiber_injective S A he
    exact congrArg Subtype.val hh)
  rw [←hcard]
  apply DescentFiberCost.finite_ideal_count_real T _ hscale
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).1.1
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).2


-- @@ L513-564 verbatim
theorem columnSquareFiber_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  let B : Matrix T (idealRange K) ℂ := fun I k => quadraticRow k.val (primaryGenerator (squarefreePart I.val))
  have hB : ‖FiniteSieveOperator.operator B‖^2≤sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K := by
    apply family_squared_norm_le (fun I : T => squarefreePart I.val) (fun k : idealRange K => k.val)
      (columnSquareFiber_injective S A) Subtype.val_injective
    · intro I
      exact columnSquareFiber_bounds S X hS A I
    · intro k
      exact mem_idealRange.mp k.property
  have hBT : B.conjTranspose=(fun k I => quadraticRow k.val (primaryGenerator (squarefreePart I.val))) := by
    ext k I
    exact canonical_quadraticRow_star k.val (mem_idealRange.mp k.property).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun I : T => a I.val)
  rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
  have hm (k : idealRange K) :
      ‖∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val‖^2 ≤
        ‖∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val‖^2 := by
    have hrow : (∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val)=
        idealZeroMask k.val (primaryGenerator A)*
        ∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := (Finset.mem_filter.mp I.property).2
      have hq : quadraticRow k.val (primaryGenerator I.val)=
          idealZeroMask k.val (primaryGenerator A)*quadraticRow k.val (primaryGenerator (squarefreePart I.val)) := by
        have hh := canonical_quadraticRow_primary_squarefree k.val (mem_idealRange.mp k.property).1
          (squarePart I.val) (squarefreePart I.val)
        rw [squarePart_sq_mul_squarefreePart,hi] at hh
        exact hh
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖idealZeroMask k.val (primaryGenerator A)‖^2≤1 := by
      unfold idealZeroMask
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hr (k : idealRange K) :
      (∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hr]
  rw [←Finset.sum_coe_sort T (fun I => ‖a I‖^2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))


-- @@ L566-566 verbatim
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel


-- @@ L568-583 verbatim
theorem columnSquareParts_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hp := (supported_square_parts I).mp hi.1
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hp.1.1,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith


-- @@ L585-684 verbatim
theorem bounded_supported_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨128*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 128*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        gcongr
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne']
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (128*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr


-- @@ L686-686 verbatim
end CanonicalQuadraticSieve


-- @@ L688-688 verbatim
end


-- @@ L690-690 verbatim
end OAI
