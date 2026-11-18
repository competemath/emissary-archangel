import OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentDetectorPlainStateDictionary

-- @@ L9-9 verbatim
open HeckeFamily HeckeDetectorRawFiber HeckePrimeAnnular

-- @@ L10-10 verbatim
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource

-- @@ L11-11 verbatim
open CenteredMomentDetectorPlainSource CenteredMomentDetectorEnergyInitialState

-- @@ L12-12 verbatim
open CenteredMomentDetectorDictionary CenteredMomentEnergyState

-- @@ L13-13 verbatim
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy

-- @@ L14-14 verbatim
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge

-- @@ L15-15 verbatim
local notation "O" => HeckeFamily.O

-- @@ L16-16 verbatim
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}

-- @@ L17-17 verbatim
variable {U a ε tstar T allowance:ℝ}{i:ℕ}


-- @@ L19-23 verbatim
lemma plainProfile_eq_detectorSchwartz
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(j:ℕ)(σ t:ℝ):
    plainProfile F j σ t=(detectorSchwartz F.reverse j σ t:ℝ→ℂ):=by
  funext x
  exact (detectorSchwartz_apply F.reverse j σ t x).symm


-- @@ L25-41 verbatim
theorem retainedSourceEnergy_eq_energy
    (keep:O→Prop)(F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ))(hU:0<U):
    retainedSourceEnergy keep F η selected j k σ t Φ=
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (plainProfile F j σ t) (plainProfile F k σ t)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m) keep Φ U:=by
  exact (positive_energy_eq_complete_source η 0 keep
    (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (fun _=>Real.rpow_pos_of_pos hU _)
    (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) Φ U).symm


-- @@ L43-57 verbatim
theorem retainedSourceEnergy_empty_eq_plainEnergy
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (initialState η Q Φ bΦ U δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=by
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  simp [initialState,NaturalState.mask,detectorProfiles,positiveSlotRow]


-- @@ L59-59 verbatim
end SevenEighths.CenteredMomentDetectorPlainStateDictionary


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end OAI
