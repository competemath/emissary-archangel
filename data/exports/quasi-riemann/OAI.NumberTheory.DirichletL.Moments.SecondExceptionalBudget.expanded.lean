import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalOriginalBlock
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open MeasureTheory


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSecondExceptionalBudget

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid

-- @@ L12-12 verbatim
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondPhysicalLedger

-- @@ L13-13 verbatim
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

-- @@ L14-14 verbatim
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost

-- @@ L15-15 verbatim
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical

-- @@ L16-16 verbatim
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit

-- @@ L17-17 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization

-- @@ L18-18 verbatim
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar

-- @@ L19-19 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L20-20 verbatim
universe u

-- @@ L21-21 verbatim
variable {ι:Type u}[Fintype ι][DecidableEq ι]


-- @@ L23-31 verbatim
lemma profileMass_self (s:Input ι)(p:Tests)(J:ℕ):
    profileMass s.toData s.toData p p J=
      p.heightWeight s.t^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring


-- @@ L33-40 verbatim
lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]


-- @@ L42-45 verbatim
def profileFactor (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.heightWeight s.t^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2


-- @@ L47-52 verbatim
omit [DecidableEq ι] in
lemma profileFactor_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor s p J Q K:=by
  unfold profileFactor
  have hp:0≤p.heightWeight s.t:=by unfold Tests.heightWeight; positivity
  positivity


-- @@ L54-73 verbatim
lemma sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring


-- @@ L75-93 verbatim
theorem central_sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp


-- @@ L95-95 verbatim
end SevenEighths.CenteredMomentSecondExceptionalBudget


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
end OAI
