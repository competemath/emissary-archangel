import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSupport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentNaturalFixedRaySource

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily

-- @@ L10-10 verbatim
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource

-- @@ L11-11 verbatim
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge

-- @@ L12-12 verbatim
local notation "O" => HeckeFamily.O


-- @@ L14-14 verbatim
variable {Δ : ℝ} {D : Parameters.HighData Δ}


-- @@ L16-17 verbatim
def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}


-- @@ L19-21 verbatim
lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))


-- @@ L23-33 verbatim
lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))


-- @@ L35-35 verbatim
lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤F.modulus := inf_le_left

-- @@ L36-36 verbatim
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right


-- @@ L38-40 verbatim
def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val


-- @@ L42-48 verbatim
theorem source_retained_sector_nonprincipal (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu


-- @@ L50-57 verbatim
theorem source_energy_split (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm


-- @@ L59-59 verbatim
end SevenEighths.CenteredMomentNaturalFixedRaySource


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end OAI
