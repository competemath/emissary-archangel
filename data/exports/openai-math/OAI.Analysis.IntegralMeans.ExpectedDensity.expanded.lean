import OAI.Analysis.IntegralMeans.AffineLaw


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set MeasureTheory Filter Function InnerProductSpace

-- @@ L7-7 verbatim
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical

-- @@ L8-8 verbatim
open MeasureTheory Function

-- @@ L9-9 verbatim
open Set Filter

-- @@ L10-10 verbatim
open Set MeasureTheory Filter Function

-- @@ L11-11 verbatim
open Set MeasureTheory Filter Function InnerProductSpace

-- @@ L12-12 verbatim
open TopologicalSpace

-- @@ L13-13 verbatim
open scoped CompactlySupported

-- @@ L14-14 verbatim
open scoped ENNReal

-- @@ L15-15 verbatim
open scoped Manifold

-- @@ L16-16 verbatim
open scoped Topology CompactlySupported ComplexConjugate

-- @@ L17-17 verbatim
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical

-- @@ L18-18 verbatim
open scoped Topology ENNReal NNReal

-- @@ L19-19 verbatim
namespace Brennan


-- @@ L21-21 verbatim
attribute [local irreducible] classWeight

-- @@ L22-22 verbatim
attribute [local irreducible] classFun

-- @@ L23-23 verbatim
attribute [local irreducible] rerootClass


-- @@ L25-25 verbatim
instance : PseudoMetrizableSpace DiskClass := inferInstanceAs (PseudoMetrizableSpace diskSchlichtSet)


-- @@ L27-36 verbatim
lemma exists_weighted_law (hρ : 2 < transferRho) :
    ∃ P : ProbabilityMeasure DiskClass, ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞,
      Measurable f →
      (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        ENNReal.ofReal ((z.val.im)^(-transferBeta))*(∫⁻ g, f g ∂(P : Measure DiskClass)) := by
  obtain ⟨P,hP⟩ := exists_weighted_continuous_law hρ
  refine ⟨P,fun z f hf => ?_⟩
  exact weighted_lintegral_of_continuous (P : Measure DiskClass) (weightAt z)
    (fun g => (classWeight_pos g z).le) (actionAt z) ((z.val.im)^(-transferBeta))
    (Real.rpow_nonneg z.2.le _) (hP z) f hf


-- @@ L38-38 verbatim
def halfRetract (z : ℂ) : halfPlane := if h : z ∈ halfPlane then ⟨z,h⟩ else halfOne


-- @@ L40-41 verbatim
lemma halfRetract_of_mem {z : ℂ} (hz : z ∈ halfPlane) : halfRetract z = ⟨z,hz⟩ := by
  simp only [halfRetract,dite_eq_left hz]


-- @@ L43-50 verbatim
lemma measurable_halfRetract : Measurable halfRetract := by
  have hm : Measurable (fun z : ℂ => (halfRetract z : ℂ)) := by
    have he : (fun z : ℂ => (halfRetract z : ℂ)) = (fun z => if z ∈ halfPlane then z else Complex.I) := by
      funext z
      by_cases hz : z ∈ halfPlane <;> simp [halfRetract,halfOne,hz]
    rw [he]
    exact measurable_id.piecewise isOpen_halfPlane.measurableSet measurable_const
  exact hm.subtype_mk


-- @@ L52-55 verbatim
def averagedDensity (β : ℝ) (Φ : DiskClass → ℝ≥0∞) (p : DiskClass × ℂ) : ℝ≥0∞ :=
  {p : DiskClass × ℂ | p.2 ∈ halfPlane}.indicator
    (fun p => ENNReal.ofReal (p.2.im^(β-1)) * ENNReal.ofReal (classWeight p.1 (halfRetract p.2)) *
      Φ (rerootClass p.1 (halfRetract p.2))) p


-- @@ L57-64 verbatim
lemma measurable_averagedDensity (β : ℝ) {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (averagedDensity β Φ) := by
  have hm : Measurable (fun p : DiskClass × ℂ => (p.1,halfRetract p.2)) :=
    measurable_fst.prodMk (measurable_halfRetract.comp measurable_snd)
  exact ((((Complex.measurable_im.comp measurable_snd).pow_const (β-1)).ennreal_ofReal.mul
    (continuous_classWeight.measurable.comp hm).ennreal_ofReal).mul
    (hΦ.comp (continuous_rerootClass.measurable.comp hm))).indicator
      (isOpen_halfPlane.measurableSet.preimage measurable_snd)


-- @@ L66-71 verbatim
lemma averagedDensity_of_mem (β : ℝ) (Φ : DiskClass → ℝ≥0∞) (g : DiskClass) (z : halfPlane) :
    averagedDensity β Φ (g,z) = transportDensity g β z * Φ (rerootClass g z) := by
  rw [averagedDensity,indicator_of_mem (show (g,(z : ℂ)) ∈ {p : DiskClass × ℂ | p.2 ∈ halfPlane} from z.property)]
  simp only [halfRetract_of_mem z.property]
  rw [transportDensity,ENNReal.ofReal_mul (Real.rpow_nonneg z.property.le _)]
  simp only [classWeight]


-- @@ L73-93 verbatim
lemma weighted_averagedDensity (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞, Measurable f →
      (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g, f g ∂(P : Measure DiskClass)))
    {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ) (z : halfPlane) :
    (∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (z.val.im⁻¹) * ∫⁻ g, Φ g ∂(P : Measure DiskClass) := by
  have hm : Measurable (fun g : DiskClass => ENNReal.ofReal (classWeight g z)*Φ (rerootClass g z)) := by
    have hp : Measurable (fun g : DiskClass => (g,z)) := measurable_id.prodMk measurable_const
    exact ((continuous_classWeight.measurable.comp hp).ennreal_ofReal).mul
      (hΦ.comp (continuous_rerootClass.measurable.comp hp))
  have he : (fun g : DiskClass => averagedDensity β Φ (g,z)) =
      fun g => ENNReal.ofReal (z.val.im^(β-1)) *
        (ENNReal.ofReal (classWeight g z)*Φ (rerootClass g z)) := by
    funext g
    rw [averagedDensity,indicator_of_mem (show (g,(z : ℂ)) ∈ {p : DiskClass × ℂ | p.2 ∈ halfPlane} from z.property)]
    simp only [halfRetract_of_mem z.property,mul_assoc]
  rw [he,lintegral_const_mul _ hm,hP z Φ hΦ,← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg z.property.le _),← Real.rpow_add z.property]
  congr 2
  rw [show β-1 + -β = (-1 : ℝ) from by ring,Real.rpow_neg_one]


-- @@ L95-111 verbatim
lemma root_test_zero_of_averaging (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞, Measurable f →
      (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g, f g ∂(P : Measure DiskClass)))
    {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ)
    (hzero : ∀ᵐ g ∂(P : Measure DiskClass), (∫⁻ z in halfPlane, averagedDensity β Φ (g,z)) = 0) :
    (∫⁻ g, Φ g ∂(P : Measure DiskClass)) = 0 := by
  have hm := measurable_averagedDensity β hΦ
  have hz : (∫⁻ z in halfPlane, ∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) = 0 :=
    (lintegral_lintegral_swap (f := fun g z => averagedDensity β Φ (g,z)) (μ := (P : Measure DiskClass)) (ν := volume.restrict halfPlane) hm.aemeasurable).symm.trans (lintegral_eq_zero_of_ae_eq_zero hzero)
  have ha := (lintegral_eq_zero_iff hm.lintegral_prod_left').mp hz
  have : (ae (volume.restrict halfPlane)).NeBot := ae_restrict_neBot.mpr
    (ne_of_gt (isOpen_halfPlane.measure_pos volume ⟨Complex.I,by simp [halfPlane]⟩))
  obtain ⟨z,hz,hz0⟩ := ((ae_restrict_mem isOpen_halfPlane.measurableSet).and ha).exists
  have he := weighted_averagedDensity P β hP hΦ ⟨z,hz⟩
  change (∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) = 0 at hz0
  exact (mul_eq_zero.mp (he.symm.trans hz0)).resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hz)))


-- @@ L113-113 verbatim
end Brennan


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
end OAI
