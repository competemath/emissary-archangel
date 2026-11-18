import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSecondExceptionalSourceFamily

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss

-- @@ L12-12 verbatim
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock

-- @@ L13-13 verbatim
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalKernel

-- @@ L14-14 verbatim
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst

-- @@ L15-15 verbatim
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L16-16 verbatim
open CenteredMomentSecondHeightFamily

-- @@ L17-17 verbatim
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion

-- @@ L18-18 verbatim
open CenteredExceptionalProfile

-- @@ L19-19 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L21-24 verbatim
lemma exceptional_part_nonzero (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):z≠0:=
  sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1


-- @@ L26-31 verbatim
lemma exceptional_part_inducing (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):
    FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z:=
  (Finset.mem_filter.mp hz).2


-- @@ L33-51 verbatim
lemma actual_family_both_rows (η:Character)(χ₀:RayCharacter)(Q:Ideal O)
    (hQ:Q≤Ideal.span {(72:O)})(m:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (τ:RayCharacter→Character)(hf:Family η C D hC hD U τ)(R:ℝ):
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)):=by
  have hz0:=exceptional_part_nonzero η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing η χ₀ Q m C D U R
  constructor
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ χ Q hQ m _ hml hm2 _ hex).1 z hz
    exact (hf.inducing_iff χ Q m z hm (hz0 z hz) hml hm2).mp hh
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ (χ⁻¹) Q hQ m _ hml hm2 _ hex).2 z hz
    simp only [inv_inv] at hh
    exact (hf.inducing_iff χ Q m (-z) hm (neg_ne_zero.mpr (hz0 z hz)) hml hm2).mp hh


-- @@ L53-59 verbatim
lemma exceptional_part_live (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    liveRows C D U R (partRows true η χ₀ Q m C D U R)=
      partRows true η χ₀ Q m C D U R:=by
  apply Finset.filter_eq_self.mpr
  intro z hz
  exact liveRows_weight C D U R _ z (Finset.mem_filter.mp hz).1


-- @@ L61-61 verbatim
end SevenEighths.CenteredMomentSecondExceptionalSourceFamily


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end OAI
