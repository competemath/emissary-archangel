import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum

-- @@ L12-12 verbatim
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

-- @@ L13-13 verbatim
open CenteredMomentSecondExceptionalPhysicalSaving

-- @@ L14-14 verbatim
open CenteredMomentFiniteProfileExceptional

-- @@ L15-15 verbatim
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock

-- @@ L16-16 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst

-- @@ L17-17 verbatim
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance

-- @@ L18-18 verbatim
open CenteredMomentRankinRadical

-- @@ L19-19 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L20-20 verbatim
universe u

-- @@ L21-21 verbatim
variable {ι:Type u}[Fintype ι][DecidableEq ι]


-- @@ L23-70 verbatim
theorem original_budget_physical_saving_full
    {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg Sprofile s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact Sprofile s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring


-- @@ L72-72 verbatim
end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end OAI
