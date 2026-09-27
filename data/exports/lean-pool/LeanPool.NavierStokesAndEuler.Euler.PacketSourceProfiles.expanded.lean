/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfilesRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity


-- @@ L12-18 verbatim
/-!
# Qualitative admissibility of the actual source packet recursion

The data are the prescribed coefficients, the common time interval and the
initial transverse datum. Every profile and every later forcing witness is
constructed; no prefix regularity hypothesis remains.
-/


-- @@ L20-20 verbatim
section


-- @@ L22-28 verbatim
/-!
# Actual homogeneous primary and recursively solved profiles

The initial transverse datum and coefficient data determine every profile.
Admissibility at all later grades follows from the genuine nonlinear paths,
the source mean inverse and the source transverse inverse.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace EulerPacketCylinderField


-- @@ L36-36 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion


-- @@ L38-45 verbatim
variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D I)
  (hcorrector : O.curlCorrector = D.curlCorrector P)


-- @@ L47-51 verbatim
/-- Constructed profile witness, constructed using `profileWitness`. -/
def constructedProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (profiles O (homogeneousPrimary D Iprimary O) p) :=
  profileWitness M D hT I C hmean hhigh hcorrector (homogeneousPrimary D Iprimary O)
    ((homogeneousPrimaryRegularity D Iprimary O hcorrector).changeTime hT.symm M.T_pos.le) p


-- @@ L53-58 verbatim
/-- Constructed mean forcing, constructed using `profilesMeanForcing`. -/
def constructedMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M
      (meanForce O p (profiles O (homogeneousPrimary D Iprimary O))) :=
  profilesMeanForcing M D hT I C hmean hhigh hcorrector (homogeneousPrimary D Iprimary O)
    ((homogeneousPrimaryRegularity D Iprimary O hcorrector).changeTime hT.symm M.T_pos.le) p hp


-- @@ L60-65 verbatim
/-- Constructed high forcing, constructed using `profilesHighForcing`. -/
def constructedHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D
      (highForce O p (profiles O (homogeneousPrimary D Iprimary O))) :=
  profilesHighForcing M D hT I C hmean hhigh hcorrector (homogeneousPrimary D Iprimary O)
    ((homogeneousPrimaryRegularity D Iprimary O hcorrector).changeTime hT.symm M.T_pos.le) p hp


-- @@ L67-67 verbatim
end EulerPacketCylinderField


-- @@ L69-69 verbatim
end

-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end


-- @@ L74-74 verbatim
@[expose] public section


-- @@ L76-76 verbatim
noncomputable section


-- @@ L78-78 verbatim
namespace EulerPacketCylinderField


-- @@ L80-80 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion


-- @@ L82-85 verbatim
variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)


-- @@ L87-90 verbatim
/-- Source profiles, given by `profiles (sourceOperators P M D I) (homogeneousPrimary D Iprimary
(sourceOperators P M D I))`. -/
def sourceProfiles : ℕ → Profile :=
  profiles (sourceOperators P M D I) (homogeneousPrimary D Iprimary (sourceOperators P M D I))


-- @@ L92-96 verbatim
/-- Source profile witness, given by `constructedProfileWitness M D hT I Iprimary
(sourceCoefficientData P M D I hT) rfl rfl rfl p`. -/
def sourceProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (sourceProfiles P M D I Iprimary p) :=
  constructedProfileWitness M D hT I Iprimary (sourceCoefficientData P M D I hT) rfl rfl rfl p


-- @@ L98-103 verbatim
/-- Source mean forcing, given by `constructedMeanForcing M D hT I Iprimary
(sourceCoefficientData P M D I hT) rfl rfl rfl p hp`. -/
def sourceMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary)) :=
  constructedMeanForcing M D hT I Iprimary (sourceCoefficientData P M D I hT) rfl rfl rfl p hp


-- @@ L105-110 verbatim
/-- Source high forcing, given by `constructedHighForcing M D hT I Iprimary
(sourceCoefficientData P M D I hT) rfl rfl rfl p hp`. -/
def sourceHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary)) :=
  constructedHighForcing M D hT I Iprimary (sourceCoefficientData P M D I hT) rfl rfl rfl p hp


-- @@ L112-112 verbatim
end EulerPacketCylinderField
