import OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceAdjoint


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
open Filter MeasureTheory

-- @@ L80-80 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace

-- @@ L81-81 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L83-83 verbatim
section

-- @@ L84-84 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L86-91 verbatim
lemma kernelTestField_comp_contDiffAt (f : kernelSmoothTests) (g : SL(2,ℂ))
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f ∘ euclideanAction g) p := by
  have hd := ((((f.2.1.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff g))
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt
  simpa only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates] using hd


-- @@ L93-103 verbatim
lemma coverGradientAt_lift_continuous (F : EuclideanSpatial→ℂ)
    (hF : ∀p,0<p 2→ContDiffAt ℝ ∞ F p) :
    Continuous (fun w : HyperbolicSpace=>coverGradientAt F (hyperbolicEuclideanCoordinates w)) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3=>ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((hF _ (hyperbolicHeight_pos w)).continuousAt_fderiv (by simp)).clm_apply
    continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt


-- @@ L105-108 verbatim
def kernelCorrespondencePairLift (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (w : HyperbolicSpace) : ℂ :=
  coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)


-- @@ L110-113 verbatim
lemma kernelCorrespondencePairLift_continuous (g : SL(2,ℂ)) (f h : kernelSmoothTests) :
    Continuous (kernelCorrespondencePairLift g f h) :=
  (coverGradientAt_lift_continuous _ (kernelTestField_contDiffAt f)).inner
    (coverGradientAt_lift_continuous _ (kernelTestField_comp_contDiffAt h g))


-- @@ L115-118 verbatim
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)


-- @@ L120-144 verbatim
include hHK hJK he in
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePairLift_invariant (f h : kernelSmoothTests)
    (k : H) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (k•w)=kernelCorrespondencePairLift g f h w := by
  let A := integralComplexMatrix (k:SL(2,ActualEisensteinCubic.O))
  let B := integralComplexMatrix (e k:SL(2,ActualEisensteinCubic.O))
  have hfi : kernelTestField f ∘ euclideanAction A=kernelTestField f :=
    funext (kernelTestField_invariant f ⟨(k:SL(2,ActualEisensteinCubic.O)),hHK k.property⟩)
  have hhi : (kernelTestField h ∘ euclideanAction g) ∘ euclideanAction A=
      kernelTestField h ∘ euclideanAction g := by
    rw [Function.comp_assoc,←euclideanAction_mul,he k,euclideanAction_mul,←Function.comp_assoc]
    have hh : kernelTestField h ∘ euclideanAction B=kernelTestField h :=
      funext (kernelTestField_invariant h ⟨(e k:SL(2,ActualEisensteinCubic.O)),hJK (e k).property⟩)
    rw [hh]
  have hp := hyperbolicHeight_pos w
  have hh := coverDirichletPair_comp A (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_contDiffAt f _ (euclideanAction_positive A _)).differentiableAt (by simp))
    ((kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive A _)).differentiableAt (by simp))
  rw [hfi,hhi] at hh
  change _=coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)
  rw [integralSubgroup_smul]
  simpa only [kernelCorrespondencePairLift,A,euclideanAction,euclideanToHyperbolic_coordinates] using hh.symm


-- @@ L146-149 verbatim
def kernelCorrespondencePair (f h : kernelSmoothTests) : IntegralOrbitQuotient H→ℂ :=
  Quotient.lift (kernelCorrespondencePairLift g f h) (by
    rintro w v ⟨k,rfl⟩
    exact (kernelCorrespondencePairLift_invariant hHK hJK e g he f h k w).symm)


-- @@ L151-154 verbatim
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_projection (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelCorrespondencePair hHK hJK e g he f h (integralOrbitProjection H w)=
      kernelCorrespondencePairLift g f h w := rfl


-- @@ L156-159 verbatim
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_measurable (f h : kernelSmoothTests) :
    Measurable (kernelCorrespondencePair hHK hJK e g he f h) :=
  measurable_from_quotient.mpr (kernelCorrespondencePairLift_continuous g f h).measurable


-- @@ L161-177 verbatim
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_norm_le (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    ‖kernelCorrespondencePair hHK hJK e g he f h q‖≤
      (kernelQuotientEnergyDensity f (integralCoverMap hHK q)+
        kernelQuotientEnergyDensity h (integralCoverMap hJK (integralConjugateMap e g he q)))/2 := by
  induction q using Quotient.inductionOn with
  | _ w =>
    have hf := (kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt h g (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hb := coverDirichletPair_norm_le (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
      (hyperbolicEuclideanCoordinates w) hf hh
    rw [coverEnergyDensity_comp g _ _ (hyperbolicHeight_pos w)
      ((kernelTestField_contDiffAt h _ (euclideanAction_positive g _)).differentiableAt (by simp))] at hb
    change ‖kernelCorrespondencePairLift g f h w‖≤
      (kernelTestEnergyDensity f w+kernelTestEnergyDensity h (g•w))/2
    simpa only [kernelCorrespondencePairLift,kernelTestEnergyDensity_eq_cover,euclideanAction,
      euclideanToHyperbolic_coordinates] using hb


-- @@ L179-190 verbatim
lemma kernelCorrespondencePair_integrable (f h : kernelSmoothTests) :
    Integrable (kernelCorrespondencePair hHK hJK e g he f h) (integralQuotientVolume H) := by
  have hf := (integralCoverMap_measurePreserving hHK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable f).smul_measure
      (c:=(H.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hh := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable h).smul_measure
      (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hhh := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hh
  apply ((hf.add hhh).div_const 2).mono' (kernelCorrespondencePair_measurable hHK hJK e g he f h).aestronglyMeasurable
  exact Filter.Eventually.of_forall (kernelCorrespondencePair_norm_le hHK hJK e g he f h)


-- @@ L192-192 verbatim
end


-- @@ L194-194 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L196-211 verbatim
lemma kernelCorrespondencePairLift_kernel (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (r : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (r•w)=
      coverDirichletPair (kernelTestField f)
        (kernelTestField h ∘ euclideanAction (g*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))))
        (hyperbolicEuclideanCoordinates w) := by
  have hf := (kernelTestField_contDiffAt f _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hh := (kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hp := coverDirichletPair_comp (integralComplexMatrix r) (kernelTestField f)
    (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)
    (hyperbolicHeight_pos w) hf hh
  have hfi : kernelTestField f ∘ euclideanAction (integralComplexMatrix r)=kernelTestField f :=
    funext (kernelTestField_invariant f r)
  rw [hfi,Function.comp_assoc,←euclideanAction_mul] at hp
  simpa only [kernelCorrespondencePairLift,integralSubgroup_smul,euclideanAction,
    euclideanToHyperbolic_coordinates] using hp.symm


-- @@ L213-217 verbatim
lemma kernelTestField_comp_inverse (f : kernelSmoothTests) (g : SL(2,ℂ)) :
    (kernelTestField f ∘ euclideanAction g⁻¹) ∘ euclideanAction g=kernelTestField f := by
  funext p
  simp only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,
    inv_smul_smul]


-- @@ L219-222 verbatim
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)


-- @@ L224-252 verbatim
lemma kernelCorrespondencePair_trace (f h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h) q=
      integralCoverTraceFunction H globalKubotaKernel
        (kernelCorrespondencePair hHK hJK e g he f h) q := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h)
      (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_eq_cover]
    have hfield := funext (kernelCorrespondenceTest_field hHK hJK e g he h)
    rw [hfield]
    have hd (r : IntegralCoverCosets H globalKubotaKernel) :
        DifferentiableAt ℝ (kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
          (hyperbolicEuclideanCoordinates w) :=
      (kernelTestField_comp_contDiffAt h _ _ (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hsum := coverDirichletPair_sum_right Finset.univ (kernelTestField f)
      (fun r=>kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
      (hyperbolicEuclideanCoordinates w) (fun r _=>hd r)
    simp only [Function.comp_apply] at hsum
    rw [hsum]
    change (∑r : IntegralCoverCosets H globalKubotaKernel,_)=
      ∑r : IntegralCoverCosets H globalKubotaKernel,
        kernelCorrespondencePair hHK hJK e g he f h (integralCoverFiberPoint H globalKubotaKernel r w)
    apply Finset.sum_congr rfl
    intro r _
    rw [integralCoverFiberPoint_rep,kernelCorrespondencePair_projection,
      kernelCorrespondencePairLift_kernel]
    rfl


-- @@ L254-261 verbatim
lemma kernelCorrespondenceForm_integral (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      ∫q,kernelCorrespondencePair hHK hJK e g he f h q∂integralQuotientVolume H := by
  unfold kernelDirichletForm
  simp_rw [kernelCorrespondencePair_trace]
  exact integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
    (kernelCorrespondencePair_measurable hHK hJK e g he f h)
    (kernelCorrespondencePair_integrable hHK hJK e g he f h)


-- @@ L263-286 verbatim
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_conjugate (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    kernelCorrespondencePair hHK hJK e g he f h q=
      star (kernelCorrespondencePair hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) h f (integralConjugateMap e g he q)) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelCorrespondencePairLift g f h w=
      star (kernelCorrespondencePairLift g⁻¹ h f (g•w))
    have hf := (kernelTestField_contDiffAt h _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt f g⁻¹ _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hc := coverDirichletPair_comp g (kernelTestField h) (kernelTestField f ∘ euclideanAction g⁻¹)
      (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) hf hh
    rw [kernelTestField_comp_inverse] at hc
    have hs := congrArg star hc
    have hswap : star (inner ℂ
        (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w))
        (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w)))=
        inner ℂ (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w))
          (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)) :=
      inner_conj_symm _ _
    rw [coverDirichletPair,hswap] at hs
    simpa only [kernelCorrespondencePairLift,coverDirichletPair,euclideanAction,
      euclideanToHyperbolic_coordinates] using hs


-- @@ L288-313 verbatim
theorem kernelCorrespondenceForm_adjoint (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      kernelDirichletForm (kernelCorrespondenceTest hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) f) h := by
  let opposite := kernelCorrespondencePair hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hom := kernelCorrespondencePair_measurable hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  rw [kernelCorrespondenceForm_integral]
  calc
    _ = ∫q,star (opposite (integralConjugateMap e g he q))∂integralQuotientVolume H := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (kernelCorrespondencePair_conjugate hHK hJK e g he f h)
    _ = ∫q,star (opposite q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (continuous_star.measurable.comp hom).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = star (∫q,opposite q∂integralQuotientVolume J) := by
      simp only [Complex.star_def]
      exact integral_conj
    _ = _ := by
      rw [←kernelCorrespondenceForm_integral hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he),kernelDirichletForm_conj]


-- @@ L315-315 verbatim
end


-- @@ L317-317 verbatim
section

-- @@ L318-318 verbatim
open Filter MeasureTheory

-- @@ L319-319 verbatim
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace

-- @@ L320-320 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L322-322 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L324-327 verbatim
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)


-- @@ L329-338 verbatim
lemma kernelCorrespondenceEnergy_pairing_core (f h : kernelSmoothTests) :
    inner ℂ (kernelEnergyGraphCore f)
      (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore h))=
    inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he) (kernelEnergyGraphCore f)) (kernelEnergyGraphCore h) := by
  rw [kernelCorrespondenceEnergy_core,kernelCorrespondenceEnergy_core,
    kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  simp only [kernelEnergyMass_core,kernelEnergyGradient_core,kernelGradientToL2_inner]
  rw [kernelCorrespondenceTest_mass,kernelCorrespondenceTest_mass,
    kernelCorrespondenceL2_pairing,kernelCorrespondenceForm_adjoint]


-- @@ L340-353 verbatim
theorem kernelCorrespondenceEnergy_pairing (u v : KernelEnergyGraph) :
    inner ℂ u (kernelCorrespondenceEnergy hHK hJK e g he v)=
      inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) u) v := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_id.inner continuous_const)
    ((kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)).continuous.inner continuous_const) ?_) u
  funext f
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_const.inner (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    (continuous_const.inner continuous_id) ?_) v
  funext h
  exact kernelCorrespondenceEnergy_pairing_core hHK hJK e g he f h


-- @@ L355-360 verbatim
lemma kernelCorrespondenceEnergy_pairing_left (u v : KernelEnergyGraph) :
    inner ℂ (kernelCorrespondenceEnergy hHK hJK e g he u) v=
      inner ℂ u (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) v) := by
  have hh := congrArg star (kernelCorrespondenceEnergy_pairing hHK hJK e g he v u)
  simpa only [←starRingEnd_apply,inner_conj_symm] using hh


-- @@ L362-367 verbatim
lemma kernelCorrespondenceL2_pairing_left (F G : KernelQuotientL2) :
    inner ℂ (kernelCorrespondenceL2 hHK hJK e g he F) G=
      inner ℂ F (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) G) := by
  have hh := congrArg star (kernelCorrespondenceL2_pairing hHK hJK e g he G F)
  simpa only [←starRingEnd_apply,inner_conj_symm] using hh


-- @@ L369-377 verbatim
theorem kernelCorrespondence_variationalSolution (F : KernelQuotientL2) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F) := by
  apply kernelVariationalSolution_unique
  intro v
  rw [←kernelEnergyGraph_inner,kernelCorrespondenceEnergy_pairing_left,
    kernelEnergyGraph_inner,kernelVariationalSolution_equation,
    kernelCorrespondenceEnergy_mass]
  exact (kernelCorrespondenceL2_pairing_left hHK hJK e g he F (kernelEnergyMass v)).symm


-- @@ L379-384 verbatim
theorem kernelCorrespondence_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelCorrespondenceL2 hHK hJK e g he F)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F))=_
  rw [←kernelCorrespondence_variationalSolution,kernelCorrespondenceEnergy_mass]
  rfl


-- @@ L386-391 verbatim
theorem kernelCorrespondence_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      kernelCorrespondenceL2 hHK hJK e g he G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelCorrespondence_variationalResolvent,hFG]


-- @@ L393-397 verbatim
theorem kernelCorrespondence_eigenvector (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      eigenvalue • kernelCorrespondenceL2 hHK hJK e g he F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelCorrespondence_operatorGraph hHK hJK e g he F (eigenvalue • F) hF


-- @@ L399-399 verbatim
end


-- @@ L401-401 verbatim
section


-- @@ L403-403 verbatim
open MeasureTheory

-- @@ L404-404 verbatim
open scoped Classical MatrixGroups BigOperators


-- @@ L406-406 verbatim
section

-- @@ L407-407 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L408-408 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L410-413 verbatim
lemma cuspFrequency_mul_right (h c:Eis) : cuspFrequency (h*c)=cuspFrequency h*eisEmbedding c := by
  unfold cuspFrequency
  rw [map_mul]
  ring


-- @@ L415-419 verbatim
lemma cusp_character_continuous (h:Eis) :
    Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*
    ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
  fun_prop


-- @@ L421-432 verbatim
lemma cusp_character_fractional_period (c:Eis) (hc:c≠0) (h q:Eis) (z:ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency (h*c)*(z+3*eisEmbedding q/eisEmbedding c))=
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have he:-cuspFrequency (h*c)*(3*eisEmbedding q/eisEmbedding c)=
      -cuspFrequency h*(3*eisEmbedding q):=by
    rw [cuspFrequency_mul_right]
    field_simp [eisEmbedding_ne_zero hc]
  rw [he]
  have hz:ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding q))=1:=by
    simpa only [zero_add,mul_zero,AddChar.map_zero_eq_one] using cuspFrequency_negative_period h q 0
  rw [hz,mul_one]


-- @@ L434-449 verbatim
lemma period_fourier_fractional_translation (f:ℂ→ℂ)
    (hf:∀n:Eis,∀z:ℂ,f (z+3*eisEmbedding n)=f z)
    (c:Eis) (hc:c≠0) (h q:Eis) :
    (∫z in periodDomain,f (z+3*eisEmbedding q/eisEmbedding c)*
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z)
  have hg (n:Eis) (z:ℂ):g (z+3*eisEmbedding n)=g z:=by
    dsimp [g]
    rw [hf,cuspFrequency_negative_period]
  have hi:=period_integral_translation g hg (3*eisEmbedding q/eisEmbedding c)
  have hp (z:ℂ):g (3*eisEmbedding q/eisEmbedding c+z)=
      f (z+3*eisEmbedding q/eisEmbedding c)*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z):=by
    dsimp [g]
    rw [add_comm (3*eisEmbedding q/eisEmbedding c) z,cusp_character_fractional_period c hc]
  simpa only [hp,g] using hi


-- @@ L451-451 verbatim
end


-- @@ L453-453 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L454-454 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L456-461 verbatim
lemma cube_upperPoint_continuous (v:ℝ) (hv:0<v) : Continuous (fun z:ℂ=>upperPoint z v hv) := by
  let c:ℂ→UpperCoordinates:=fun z=>⟨(z,v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  simpa only [Function.comp_def,c] using continuous_upperCoordinates.comp hc


-- @@ L463-537 verbatim
theorem cubeAverage_fourier (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (hperiod:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ∫z in periodDomain,F (upperPoint z (v/‖eisEmbedding p‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)))*
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z) := by
  let V:=v/‖eisEmbedding p‖^3
  have hV:0<V:=div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)
  let f:ℂ→ℂ:=fun z=>F (upperPoint z V hV)
  let H:ℂ→ℂ:=fun z=>cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hf:Continuous f:=hF.comp (cube_upperPoint_continuous V hV)
  have hfperiod (n:Eis) (z:ℂ):f (z+3*eisEmbedding n)=f z:=by
    dsimp [f]
    rw [←complexTranslation_action]
    exact hperiod n _
  have hH:Continuous H:=
    ((cubeAverage_continuous p hp F hF).comp (cube_upperPoint_continuous v hv)).mul (cusp_character_continuous h)
  have hHperiod (n:Eis) (z:ℂ):H (z+3*eisEmbedding n)=H z:=by
    dsimp [H]
    rw [←complexTranslation_action,cubeAverage_period_three p hp F hperiod,cuspFrequency_negative_period]
  let term (r:Eis⧸Ideal.span {p^3}) (z:ℂ):=
    f (z+3*eisEmbedding (GaussianShiftedPartition.representative (p^3) r)/eisEmbedding (p^3))*
      ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  have hpoint (z:ℂ):H (eisEmbedding (p^3)*z)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r:Eis⧸Ideal.span {p^3},term r z):=by
    have hphase:ShortDraftTrace.breveE (-cuspFrequency h*(eisEmbedding (p^3)*z))=
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=by
      rw [cuspFrequency_mul_right]
      congr 1
      ring
    dsimp only [H,cubeAverage]
    rw [hphase]
    rw [mul_assoc,←tsum_mul_right]
    congr 1
    apply tsum_congr
    intro r
    dsimp only [term,f]
    rw [cubeAverageMatrix_action]
    congr 2
    apply upperPoint_congr
    · rw [map_pow]
      field_simp [eisEmbedding_ne_zero hp]
    · rfl
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (term r) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    exact (hf.comp (continuous_id.add continuous_const)).mul (cusp_character_continuous (h*p^3))
  have hint:(∫z in periodDomain,∑' r:Eis⧸Ideal.span {p^3},term r z)=
      ∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z:=by
    simp only [tsum_fintype]
    exact integral_finsetSum _ (fun r _=>hi r)
  have hterm (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,term r z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=
    period_fourier_fractional_translation f hfperiod (p^3) (pow_ne_zero 3 hp) h _
  have hcard:(Nat.card (Eis⧸Ideal.span {p^3}):ℂ)=(Ideal.absNorm (Ideal.span {p}):ℂ)^3:=by
    change (Ideal.absNorm (Ideal.span {p^3}):ℂ)=_
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  change (∫z in periodDomain,H z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  calc
    _=∫z in periodDomain,H (eisEmbedding (p^3)*z):=
      (period_integral_eisenstein_mul H hH.measurable hHperiod (p^3) (pow_ne_zero 3 hp)).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z):=by
      simp_rw [hpoint]
      rw [integral_const_mul,hint]
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' (_:Eis⧸Ideal.span {p^3}),∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)):=by
      congr 1
      exact tsum_congr hterm
    _=_:=by rw [tsum_const,nsmul_eq_mul,hcard];field_simp


-- @@ L539-539 verbatim
end


-- @@ L541-541 verbatim
open MeasureTheory

-- @@ L542-542 verbatim
open scoped Classical MatrixGroups BigOperators

-- @@ L543-543 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota

-- @@ L544-544 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L546-553 verbatim
theorem cubeSource_fourier (p:Eis) (hp:p≠0) (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3) := by
  rw [cubeAverage_fourier p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous
    cubicSource_period_three h v hv]
  simp_rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier _ (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) _


-- @@ L555-575 verbatim
lemma cubeSource_amplitude_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFullModeAmplitude v h := by
  have hc:((9*Real.sqrt 3/2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by positivity)
  apply mul_left_cancel₀ hc
  calc
    _=∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z):=(cubeSource_fourier p hp h v hv).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
        ShortDraftTrace.breveE (-cuspFrequency h*z)):=by
      simp_rw [hU,mul_assoc]
      exact integral_const_mul _ _
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h):=by
      simp_rw [cubicSourceResidualFunction_eq_bessel]
      rw [sourceBesselFunction_fourier]
    _=_:=by ring


-- @@ L577-582 verbatim
lemma schlafliBesselK_cubic_ne_zero (x:ℝ) (hx:0<x) : schlafliBesselK (1/3:ℂ) x≠0 := by
  have hp:0<(schlafliBesselK (1/3:ℂ) x).re:=
    lt_of_lt_of_le (mul_pos cubicBesselLowerConstant_pos (Real.exp_pos _)) (schlafliBesselK_cubic_lower x hx)
  intro he
  rw [he,Complex.zero_re] at hp
  exact (lt_irrefl 0) hp


-- @@ L584-612 verbatim
theorem sourceResidualFourierCoefficient_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=(‖eisEmbedding p‖:ℂ)*sourceResidualFourierCoefficient h := by
  have hhp:h*p^3≠0:=mul_ne_zero hh (pow_ne_zero 3 hp)
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hrC:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have hx:0<4*Real.pi*‖cuspFrequency h‖:=by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))
  have hK:=schlafliBesselK_cubic_ne_zero _ hx
  have he:=cubeSource_amplitude_of_eigenrelation p hp hU h 1 (by norm_num)
  simp only [sourceResidualFullModeAmplitude,ite_eq_right hhp,ite_eq_right hh,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_pow,mul_one,hf] at he
  have harg:4*Real.pi*(‖cuspFrequency h‖*‖eisEmbedding p‖^3)*(1/‖eisEmbedding p‖^3)=
      4*Real.pi*‖cuspFrequency h‖:=by field_simp
  rw [harg] at he
  have he':sourceResidualFourierCoefficient (h*p^3)/(‖eisEmbedding p‖:ℂ)^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFourierCoefficient h:=by
    apply mul_right_cancel₀ hK
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using he
  have hn:(Ideal.absNorm (Ideal.span {p}):ℂ)=(‖eisEmbedding p‖:ℂ)^2:=by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span p).symm
  rw [hn] at he'
  have he'' :=(div_eq_iff (pow_ne_zero 3 hrC)).mp he'
  rw [he'']
  field_simp


-- @@ L614-614 verbatim
end CubicEisenstein


-- @@ L616-616 verbatim
end


-- @@ L618-618 verbatim
end OAI
