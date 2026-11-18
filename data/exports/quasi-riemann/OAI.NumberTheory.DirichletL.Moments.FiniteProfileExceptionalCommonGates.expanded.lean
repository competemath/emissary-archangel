import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonAsymmetric
import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates
import OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
import OAI.NumberTheory.DirichletL.Moments.FixedRowMask


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

-- @@ L12-12 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L13-13 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentSourceMass

-- @@ L14-14 verbatim
open CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair

-- @@ L15-15 verbatim
open CenteredMomentFixedRowMask CenteredExceptionalProfile CenteredMomentSecondHeightFamily

-- @@ L16-16 verbatim
local notation "O" => HeckeFamily.O

-- @@ L17-17 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


-- @@ L19-19 verbatim
open CenteredMomentCommonExceptionalGates CenteredMomentFiniteProfileExceptional

-- @@ L20-20 verbatim
variable {wlo whi:ℝ}

-- @@ L21-41 verbatim
omit [DecidableEq ι] in
theorem common_admissible (s:Input ι)(p:Profiles wlo whi)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    ProfileAdmissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂


-- @@ L43-43 verbatim
end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon


-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
