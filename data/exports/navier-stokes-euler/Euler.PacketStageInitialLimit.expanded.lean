import Euler.PacketStageInputs
import Euler.PacketSourceScaleShift
import Euler.PacketInitialSmoothLimit
import Euler.PacketStageContradiction


-- @@ L6-8 verbatim
/-! The literal initial increments of an actual stage family have one
smooth L² limit in every Sobolev order. The finite exceptional prefix
is retained in the initial velocity of stage one. -/


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
namespace EulerPacketInduction.Stage


-- @@ L14-18 verbatim
open Set Filter Finset EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketUniformFrequencyScales EulerNormalPacketParameters EulerTransverseFrameCoordinates
  EulerPacketBaseGuardScales

-- @@ L19-19 verbatim
open scoped Topology


-- @@ L21-22 verbatim
variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : ∀ n, Stage S n)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L24-26 verbatim
def initialTailInput (i : ℕ) :
    EulerPacketInitial.Input (referencePlane ((P (1+i)).joinedNormal (by omega))) :=
  (P (1+i)).joinedInput (by omega) hq hB


-- @@ L28-28 verbatim
local notation "A" => initialTailInput P hq hB

-- @@ L29-29 verbatim
local notation "J" => S.J+1

-- @@ L30-30 verbatim
local notation "X" => scaleSequence S.J S.X 1


-- @@ L32-35 verbatim
theorem initialTail_parameter (i : ℕ) :
    (A i).parameterSize ≤ parameterEnvelope J (sourceConstant 4) 320 20 1000 X i := by
  rw [parameterEnvelope_shift S.J S.j_one (sourceConstant 4) 320 20 1000 S.X 1 i]
  exact (P (1+i)).joinedInput_parameterSize (by omega) hq hB


-- @@ L37-39 verbatim
theorem initialTail_scale (i : ℕ) : (A i).parent.ell=supportScale J X i := by
  rw [supportScale_shift]
  exact (P (1+i)).joinedInput_scale (by omega) hq hB


-- @@ L41-43 verbatim
theorem initialTail_sigma (i : ℕ) : (A i).frame.sigma*scaleSequence J X i ≤ 2 := by
  rw [scaleSequence_shift]
  exact (P (1+i)).joinedInput_sigma_bound (by omega) hq hB


-- @@ L45-47 verbatim
theorem initialTail_four (i : ℕ) : 4 ≤ frequency J X i := by
  rw [frequency_shift]
  exact (S.normal_frequency (1+i)).four


-- @@ L49-51 verbatim
theorem initialTail_frequency (i : ℕ) : (A i).frequencyGuard (frequency J X i) := by
  rw [frequency_shift]
  exact (P (1+i)).joinedInput_frequency (by omega) hq hB


-- @@ L53-53 verbatim
def initialBase : SmoothL2Field Space := (P 1).state.regularity.velocity (P 1).parent.zeroTime


-- @@ L55-59 verbatim
def initialDataLimit : SmoothL2Field Space :=
  EulerPacketInitial.fullInitialLimit A J (by have h := S.stage_large; omega)
    (sourceConstant 4) 320 (sourceConstant_pos 4) (by norm_num) 20 1000 X (S.sequence_one 1)
    (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
    (initialTail_four (S := S)) (initialTail_frequency P hq hB) (initialBase P)


-- @@ L61-65 verbatim
variable (hstep : ∀ n (hn : n ≠ 0),
  (fun x => (P (n+1)).state.evolution.velocity (0,x)) =
    (fun x => (P n).state.evolution.velocity (0,x))+
      (((P n).joinedInput hn hq hB).high (frequency S.J S.X n)+
        ((P n).joinedInput hn hq hB).mean (frequency S.J S.X n)))


-- @@ L67-67 verbatim
include hstep


-- @@ L69-82 verbatim
theorem initial_velocity_partial (N : ℕ) :
    (fun x => (P (1+N)).state.evolution.velocity (0,x)) =
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


-- @@ L84-104 verbatim
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
        ((fun x => (P (1+n)).state.evolution.velocity (0,x))-(initialDataLimit P hq hB).field)) := by
    funext n
    rw [Nat.add_comm n 1]
  rw [heq]
  exact ht


-- @@ L106-112 verbatim
theorem initialDataLimit_no_euler :
    ¬ ∃ U : EulerOrdinarySobolev.Evolution (baseHorizon S.J S.X)
        (baseHorizon_pos S.J S.j_one S.x_pos).le,
      (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field=
        (initialDataLimit P hq hB).field :=
  no_euler_evolution_of_initial_H3 P (initialDataLimit P hq hB).field
    (initialDataLimit_Hm P hq hB hstep 3)


-- @@ L114-114 verbatim
end EulerPacketInduction.Stage
