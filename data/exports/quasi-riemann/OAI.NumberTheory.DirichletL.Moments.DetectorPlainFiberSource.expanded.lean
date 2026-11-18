import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators SchwartzMap ComplexConjugate


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentDetectorPlainFiberSource

-- @@ L12-12 verbatim
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure

-- @@ L13-13 verbatim
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource

-- @@ L14-14 verbatim
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass

-- @@ L15-15 verbatim
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow

-- @@ L16-16 verbatim
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy

-- @@ L17-17 verbatim
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber

-- @@ L18-18 verbatim
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

-- @@ L19-19 verbatim
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm

-- @@ L20-20 verbatim
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic

-- @@ L21-21 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L22-22 verbatim
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}

-- @@ L23-23 verbatim
variable {U a ε tstar T allowance:ℝ}{i:ℕ}


-- @@ L25-28 verbatim
def plainProfile (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (j:ℕ)(σ t:ℝ):ℝ→ℂ:=
  twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
    (orientedFrequency F.reverse t)


-- @@ L30-31 verbatim
def slotWindow (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)(x:ℝ):ℂ:=
  conj (F.profile s x*(x:ℂ)^(F.external s-1))


-- @@ L33-36 verbatim
def fiberPool (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot):
    Finset (CenteredMomentAddedZeroUniform.Tuple selected):=
  completePool (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (9/4) (9/4) (U^F.m) (U^F.m)


-- @@ L38-43 verbatim
def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ):Ideal O→ℂ:=
  finiteColumnCoefficient (fiberPool F selected)
    (uncenteredProfileCoefficient 1 (fun _:selected=>idealCoeff η.inverse)
      (fun s:selected=>slotWindow F s.val) (fun s:selected=>U^(F.widths s.val))
      (plainProfile F j σ t) (plainProfile F k σ t) (U^F.m) (U^F.m) 1 1 1)


-- @@ L45-49 verbatim
def fiberSourceEnergy (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy (fun _=>True) (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))


-- @@ L51-68 verbatim
theorem detector_row_eq_source (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(u:FreeRow)(hU:0<U):
    detectorPositiveRow F η selected j k σ t u=
      (Real.sqrt ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):ℂ)⁻¹*
      ∑I∈finiteColumns (fiberPool F selected),fiberCoefficient F η selected j k σ t I*
        CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I:=by
  have he:=positiveSlotRow_eq_complete_source η fixedBadMask 1 u.val 0
    (dvd_mul_right _ _) (dvd_mul_left _ _)
    (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1)] at he
  unfold detectorPositiveRow
  rw [rowMaskElement_eq_fixed]
  exact he


-- @@ L70-109 verbatim
theorem detector_positive_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=>fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted (fun _ : O=>True) Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by simp) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le


-- @@ L111-123 verbatim
theorem fiber_plain_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  exact detector_positive_energy_le_source Φ hΦ hone F η selected j k σ t hU


-- @@ L125-126 verbatim
def radialMajorant : 𝓢(ℝ,ℂ):=
  Classical.choose DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant


-- @@ L128-129 verbatim
lemma radialMajorant_compact : HasCompactSupport (radialMajorant:ℝ→ℂ):=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).1


-- @@ L131-132 verbatim
lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x


-- @@ L134-135 verbatim
lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx


-- @@ L137-148 verbatim
theorem actual_fiber_plain_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t radialMajorant:=
  fiber_plain_energy_le_source radialMajorant radialMajorant_nonneg radialMajorant_one
    F η hdata hMm hU selected j k σ t hη


-- @@ L150-158 verbatim
theorem actual_fiber_unmarked_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (j k:ℕ)(σ t:ℝ):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t‖^2)≤fiberSourceEnergy F η ∅ j k σ t radialMajorant:=by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    actual_fiber_plain_energy_le_source F η hdata hMm hU ∅ j k σ t (by simp)


-- @@ L160-160 verbatim
end SevenEighths.CenteredMomentDetectorPlainFiberSource


-- @@ L162-162 verbatim
end


-- @@ L164-164 verbatim
end OAI
