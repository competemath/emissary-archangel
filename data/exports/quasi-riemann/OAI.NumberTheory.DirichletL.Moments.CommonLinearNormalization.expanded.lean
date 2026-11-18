import OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
import OAI.NumberTheory.DirichletL.Moments.CommonRawCost


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentCommonLinearNormalization

-- @@ L10-10 verbatim
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData

-- @@ L11-11 verbatim
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentEligibleEnergy

-- @@ L12-12 verbatim
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn

-- @@ L13-13 verbatim
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair

-- @@ L14-14 verbatim
open CanonicalQuadraticSieve

-- @@ L15-15 verbatim
local notation "O" => HeckeFamily.O

-- @@ L16-16 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


-- @@ L18-19 verbatim
def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P


-- @@ L21-25 verbatim
omit [DecidableEq ι] in
theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring


-- @@ L27-47 verbatim
theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring


-- @@ L49-54 verbatim
omit [DecidableEq ι] in
theorem commonScalar_sq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P:=
  CenteredMomentDivisorRawEnergy.normalized_norm_sq _
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) _


-- @@ L56-63 verbatim
omit [DecidableEq ι] in
theorem commonScalar_sq_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2≤
      ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ):=by
  rw [commonScalar_sq]
  exact frozen_normalized_cost B.val (alloc_ne s C B) C R hC
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound s.W_bound
    s.M_ge_one s.lower s.upper s.lower_pos s.slot_support


-- @@ L65-65 verbatim
end SevenEighths.CenteredMomentCommonLinearNormalization


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
end OAI
