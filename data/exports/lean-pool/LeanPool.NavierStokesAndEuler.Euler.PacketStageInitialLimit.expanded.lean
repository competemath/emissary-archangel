/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInputs
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSmoothLimit
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldPhysicalSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVaryingHorizon
import LeanPool.NavierStokesAndEuler.Euler.PacketStageGrowth
import LeanPool.NavierStokesAndEuler.Euler.ParentOrdinaryEvolution
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Series


-- @@ L20-22 verbatim
/-! The literal initial increments of an actual stage family have one
smooth L² limit in every Sobolev order. The finite exceptional prefix
is retained in the initial velocity of stage one. -/


-- @@ L24-24 verbatim
section


-- @@ L26-28 verbatim
/-! Any actual family of packet stages with convergent H³ initial data
excludes an ordinary Euler evolution on the base horizon. Each stage is
compared only on its own genuine horizon. -/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace EulerPacketInduction.Stage


-- @@ L36-38 verbatim
open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerSmoothL2Series
  EulerPacketInductionScales EulerPacketSourceScaleActual EulerPacketBaseGuardScales

-- @@ L39-39 verbatim
open scoped Topology


-- @@ L41-43 verbatim
variable {c B : ℝ} {S : Scales c B} (P : ∀ n, Stage S n) (u₀ : Space → Space)
  (hinit : Tendsto (fun n => derivativeSum 3
    ((fun x => (P n).state.evolution.velocity (0, x)) - u₀)) atTop (𝓝 0))


-- @@ L45-45 verbatim
include P hinit


-- @@ L47-87 verbatim
theorem false_of_evolution
    (U : Evolution (baseHorizon S.J S.X) (baseHorizon_pos S.J S.j_one S.x_pos).le)
    (hU₀ : (U.velocity ⟨0, le_rfl, (baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field = u₀) :
    False := by
  let durations : ℕ → ℝ := fun n => (P n).parent.T
  let hD : ∀ n, 0 ≤ durations n := fun n => (P n).parent.T_pos.le
  let hDT : ∀ n, durations n ≤ baseHorizon S.J S.X := fun n => (P n).horizon_le
  let V : ∀ n, Evolution (durations n) (hD n) :=
    fun n => (P n).state.regularity.ordinaryEvolution
  let times : ∀ n, Icc (0 : ℝ) (durations n) :=
    fun n => ⟨(P n).time,(P n).time_nonneg,(P n).time_lt.le⟩
  have hfield (n : ℕ) :
      (((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n))
        ⟨0,le_rfl,hD n⟩).field = (fun x => (P n).state.evolution.velocity (0,x))-u₀ := by
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((P n).state.regularity.velocity ⟨0,le_rfl,(P n).parent.T_pos.le⟩).field x -
        (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field x = _
    rw [hU₀,← (P n).state.regularity.velocity_match ⟨0,le_rfl,(P n).parent.T_pos.le⟩ x]
    rfl
  have hnorm (n : ℕ) :
      tensorNorm 3 ((U.restrictTime (durations n) (hD n) (hDT n)).difference
        (V n) ⟨0,le_rfl,hD n⟩) =
      derivativeSum 3 ((fun x => (P n).state.evolution.velocity (0,x))-u₀) := by
    rw [tensorNorm_eq_derivativeSum,hfield]
  have hlim : Tendsto (fun n => tensorNorm 3
      ((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n) ⟨0,le_rfl,hD n⟩))
      atTop (𝓝 0) := by
    simpa only [hnorm] using hinit
  have hno := U.no_gradient_escape_of_initial_tendsto_varying durations hD hDT V hlim times
  apply hno
  have hactual (n : ℕ) : ((V n).velocity (times n)).field =
      fun x => (P n).state.evolution.velocity ((P n).time,x) :=
    funext (fun x => ((P n).state.regularity.velocity_match (times n) x).symm)
  have heq : (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) =
      fun n => (P n).activationGradient := by
    funext n
    rw [hactual]
    rfl
  rw [heq]
  exact gradient_atTop P


-- @@ L89-93 verbatim
theorem no_euler_evolution_of_initial_H3 :
    ¬ ∃ U : Evolution (baseHorizon S.J S.X) (baseHorizon_pos S.J S.j_one S.x_pos).le,
      (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field=u₀ := by
  rintro ⟨U,hU⟩
  exact false_of_evolution P u₀ hinit U hU


-- @@ L95-95 verbatim
end EulerPacketInduction.Stage


-- @@ L97-97 verbatim
end

-- @@ L98-98 verbatim
end


-- @@ L100-100 verbatim
end


-- @@ L102-102 verbatim
section


-- @@ L104-105 verbatim
/-! Exact reindexing of the prescribed scale sequence after finitely many
exceptional initial stages. No new choice of asymptotic scales is made. -/


-- @@ L107-107 verbatim
@[expose] public section


-- @@ L109-109 verbatim
noncomputable section


-- @@ L111-111 verbatim
namespace EulerPacketSourceScaleSequence


-- @@ L113-113 verbatim
open EulerPacketSourceScaleChoice EulerPacketUniformFrequencyScales


-- @@ L115-120 verbatim
theorem scaleSequence_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    scaleSequence (J+r) (scaleSequence J X r) n=scaleSequence J X (r+n) := by
  induction n with
  | zero => simp only [scaleSequence_zero,Nat.add_zero]
  | succ n ih =>
    rw [scaleSequence_succ,ih,show r+(n+1)=(r+n)+1 by omega,scaleSequence_succ,Nat.add_assoc]


-- @@ L122-124 verbatim
theorem frequency_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    frequency (J+r) (scaleSequence J X r) n=frequency J X (r+n) := by
  simp only [frequency,scaleSequence_shift,Nat.add_assoc]


-- @@ L126-128 verbatim
theorem supportScale_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    supportScale (J+r) (scaleSequence J X r) n=supportScale J X (r+n) := by
  simp only [supportScale,scaleSequence_shift,Nat.add_assoc]


-- @@ L130-132 verbatim
theorem spike_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    spike (J+r) (scaleSequence J X r) n=spike J X (r+n) := by
  simp only [spike,scaleSequence_shift,Nat.add_assoc]


-- @@ L134-139 verbatim
theorem parameterEnvelope_shift (J : ℕ) (hJ : 1 ≤ J) (C c : ℝ) (p q : ℕ)
    (X : ℝ) (r n : ℕ) :
    parameterEnvelope (J+r) C c p q (scaleSequence J X r) n =
      parameterEnvelope J C c p q X (r+n) := by
  have he : J+r-1+n=J-1+(r+n) := by omega
  simp only [parameterEnvelope,scaleSequence_shift,Nat.add_assoc,he]


-- @@ L141-141 verbatim
end EulerPacketSourceScaleSequence


-- @@ L143-143 verbatim
end

-- @@ L144-144 verbatim
end


-- @@ L146-146 verbatim
end


-- @@ L148-148 verbatim
@[expose] public section


-- @@ L150-150 verbatim
noncomputable section


-- @@ L152-152 verbatim
namespace EulerPacketInduction.Stage


-- @@ L154-158 verbatim
open Set Filter Finset EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketUniformFrequencyScales EulerNormalPacketParameters EulerTransverseFrameCoordinates
  EulerPacketBaseGuardScales

-- @@ L159-159 verbatim
open scoped Topology


-- @@ L161-162 verbatim
variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : ∀ n, Stage S n)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L164-168 verbatim
/-- Initial tail input as an element of `EulerPacketInitial.Input (referencePlane ((P
(1+i)).joinedNormal (by omega)))`. -/
def initialTailInput (i : ℕ) :
    EulerPacketInitial.Input (referencePlane ((P (1+i)).joinedNormal (by omega))) :=
  (P (1+i)).joinedInput (by omega) hq hB


-- @@ L170-170 verbatim
local notation "A" => initialTailInput P hq hB

-- @@ L171-171 verbatim
local notation "J" => S.J+1

-- @@ L172-172 verbatim
local notation "X" => scaleSequence S.J S.X 1


-- @@ L174-177 verbatim
theorem initialTail_parameter (i : ℕ) :
    (A i).parameterSize ≤ parameterEnvelope J (sourceConstant 4) 320 20 1000 X i := by
  rw [parameterEnvelope_shift S.J S.j_one (sourceConstant 4) 320 20 1000 S.X 1 i]
  exact (P (1+i)).joinedInput_parameterSize (by omega) hq hB


-- @@ L179-181 verbatim
theorem initialTail_scale (i : ℕ) : (A i).parent.ell=supportScale J X i := by
  rw [supportScale_shift]
  exact (P (1+i)).joinedInput_scale (by omega) hq hB


-- @@ L183-185 verbatim
theorem initialTail_sigma (i : ℕ) : (A i).frame.sigma*scaleSequence J X i ≤ 2 := by
  rw [scaleSequence_shift]
  exact (P (1+i)).joinedInput_sigma_bound (by omega) hq hB


-- @@ L187-189 verbatim
theorem initialTail_four (i : ℕ) : 4 ≤ frequency J X i := by
  rw [frequency_shift]
  exact (S.normal_frequency (1+i)).four


-- @@ L191-193 verbatim
theorem initialTail_frequency (i : ℕ) : (A i).frequencyGuard (frequency J X i) := by
  rw [frequency_shift]
  exact (P (1+i)).joinedInput_frequency (by omega) hq hB


-- @@ L195-196 verbatim
/-- Initial base, given by `(P 1).state.regularity.velocity (P 1).parent.zeroTime`. -/
def initialBase : SmoothL2Field Space := (P 1).state.regularity.velocity (P 1).parent.zeroTime


-- @@ L198-203 verbatim
/-- Initial data limit, constructed using `EulerPacketInitial.fullInitialLimit`. -/
def initialDataLimit : SmoothL2Field Space :=
  EulerPacketInitial.fullInitialLimit A J (by have h := S.stage_large; omega)
    (sourceConstant 4) 320 (sourceConstant_pos 4) (by norm_num) 20 1000 X (S.sequence_one 1)
    (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
    (initialTail_four (S := S)) (initialTail_frequency P hq hB) (initialBase P)


-- @@ L205-209 verbatim
variable (hstep : ∀ n (hn : n ≠ 0),
  (fun x => (P (n + 1)).state.evolution.velocity (0, x)) =
    (fun x => (P n).state.evolution.velocity (0, x)) +
      (((P n).joinedInput hn hq hB).high (frequency S.J S.X n) +
        ((P n).joinedInput hn hq hB).mean (frequency S.J S.X n)))


-- @@ L211-211 verbatim
include hstep


-- @@ L213-226 verbatim
theorem initial_velocity_partial (N : ℕ) :
    (fun x => (P (1+N)).state.evolution.velocity (0, x)) =
      (initialBase P).field+EulerPacketInitial.initialPartial A J X N := by
  induction N with
  | zero =>
    funext x
    simpa only [Nat.add_zero,EulerPacketInitial.initialPartial,sum_range_zero,
      Pi.add_apply,add_zero,initialBase,EulerParentPacketFrames.Parent.zeroTime] using
      (P 1).state.regularity.velocity_match (P 1).parent.zeroTime x
  | succ N ih =>
    rw [show 1+(N+1)=(1+N)+1 by omega,hstep (1+N) (by omega),ih]
    funext x
    simp only [Pi.add_apply,EulerPacketInitial.initialPartial,sum_range_succ,
      frequency_shift,initialTailInput,add_assoc]


-- @@ L228-249 verbatim
theorem initialDataLimit_Hm (s : ℕ) :
    Tendsto (fun n => derivativeSum s
      ((fun x => (P n).state.evolution.velocity (0,x))-(initialDataLimit P hq hB).field))
      atTop (𝓝 0) := by
  have hh := EulerPacketInitial.fullInitialLimit_Hm A J (by have h := S.stage_large; omega)
    (sourceConstant 4) 320 (sourceConstant_pos 4) (by norm_num) 20 1000 X (S.sequence_one 1)
    (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
    (initialTail_four (S := S)) (initialTail_frequency P hq hB) (initialBase P) s
  have ht : Tendsto (fun n => derivativeSum s
      ((fun x => (P (1+n)).state.evolution.velocity (0,x))-(initialDataLimit P hq hB).field))
      atTop (𝓝 0) := by
    simpa only [initial_velocity_partial P hq hB hstep,initialDataLimit] using hh
  apply (tendsto_add_atTop_iff_nat 1).mp
  have heq : (fun n => derivativeSum s
      ((fun x => (P (n+1)).state.evolution.velocity (0,x))-(initialDataLimit P hq hB).field)) =
      (fun n => derivativeSum s
        ((fun x => (P (1+n)).state.evolution.velocity (0,x))-(initialDataLimit P hq hB).field)) :=
            by
    funext n
    rw [Nat.add_comm n 1]
  rw [heq]
  exact ht


-- @@ L251-257 verbatim
theorem initialDataLimit_no_euler :
    ¬ ∃ U : EulerOrdinarySobolev.Evolution (baseHorizon S.J S.X)
        (baseHorizon_pos S.J S.j_one S.x_pos).le,
      (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field =
        (initialDataLimit P hq hB).field :=
  no_euler_evolution_of_initial_H3 P (initialDataLimit P hq hB).field
    (initialDataLimit_Hm P hq hB hstep 3)


-- @@ L259-259 verbatim
end EulerPacketInduction.Stage
