/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderRecursiveAdmissibility
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileStepRegularity


-- @@ L14-19 verbatim
/-!
# Genuine regularity through the full literal profile recursion

Strong induction applies the constructed mean and high solvers at each grade.
Only the primary profile is supplied; later forcing admissibility is proved.
-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerPacketCylinderField


-- @@ L28-28 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L30-38 verbatim
variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I : EulerTransversePacketProvider.InitialData P D)
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D I)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)


-- @@ L40-57 verbatim
include hT I C hmean hhigh hcorrector hprimary in
theorem profiles_regular (p : ℕ) :
    Nonempty (ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary p)) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst p
      rw [profiles_zero]
      exact ⟨ProfileRegularity.zero P M.T M.T_pos.le D.support⟩
    by_cases hp1 : p = 1
    · subst p
      rw [profiles_one]
      exact ⟨hprimary⟩
    have hp : 2 ≤ p := by omega
    let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
      fun i hi => Classical.choice (ih i hi)
    rw [profiles_step O primary p hp]
    exact ⟨ProfileRegularity.step M D hT I C hmean hhigh hcorrector hp G⟩


-- @@ L59-62 verbatim
/-- Profile witness, given by `Classical.choice (profiles_regular M D hT I C hmean hhigh
hcorrector primary hprimary p)`. -/
def profileWitness (p : ℕ) : ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary p) :=
  Classical.choice (profiles_regular M D hT I C hmean hhigh hcorrector primary hprimary p)


-- @@ L64-71 verbatim
/-- The literal mean forcing at every nonprimary grade has actual smooth spatial L² slices. -/
def profilesMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M (meanForce O p (profiles O primary)) := by
  let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
    fun i _ => profileWitness M D hT I C hmean hhigh hcorrector primary hprimary i
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  exact F.meanForcing M C (by omega) W.correctorDerivative W.corrector_time W.pressure


-- @@ L73-81 verbatim
/-- The actual supported zero-mean transverse input is built from the already generated profiles. -/
def profilesHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D (highForce O p (profiles O primary)) := by
  let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
    fun i _ => profileWitness M D hT I C hmean hhigh hcorrector primary hprimary i
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  exact F.highForcing M D hT C hp W.correctorDerivative W.corrector_time W.pressure hmean
    (ProfileRegularity.prefixLocality G) W.pressure_zero


-- @@ L83-83 verbatim
end EulerPacketCylinderField
