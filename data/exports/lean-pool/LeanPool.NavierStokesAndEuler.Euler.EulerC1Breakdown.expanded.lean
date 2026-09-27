/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteLifespan
import LeanPool.NavierStokesAndEuler.Euler.PacketFirstStageSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInitialLimit


-- @@ L14-18 verbatim
/-! C¹ breakdown for the concrete compactly supported datum. The
infinite-limsup statement is expressed directly: after every time below
the maximal time, the actual gradient supremum exceeds every real bound.
The norms are bounded-continuous-function norms at individual times,
not totalized real L∞ seminorms of unverified measurable fields. -/


-- @@ L20-20 verbatim
section


-- @@ L22-23 verbatim
/-! The full smooth initial datum retains the common support of its
finite initial base and its actual summable packet increments. -/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace EulerPacketInduction.Stage


-- @@ L31-34 verbatim
open Set EulerSmoothLimit EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerNormalPacketParameters EulerPacketInitial EulerLpTranslation
  EulerLpTranslation.SmoothL2Field


-- @@ L36-37 verbatim
variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : ∀ n, Stage S n)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L39-54 verbatim
theorem initialDataLimit_support
    (hbase : tsupport (initialBase P).field ⊆ Metric.closedBall 0 2) :
    tsupport (initialDataLimit P hq hB).field ⊆ Metric.closedBall 0 2 := by
  let tail := initialLimit (initialTailInput P hq hB) (S.J+1)
    (by have h := S.stage_large; omega) (sourceConstant 4) 320 (sourceConstant_pos 4)
    (by norm_num) 20 1000 (scaleSequence S.J S.X 1) (S.sequence_one 1)
    (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
    (initialTail_four (S := S)) (initialTail_frequency P hq hB)
  have htail : tsupport tail.field ⊆ Metric.closedBall 0 2 :=
    initialLimit_support (initialTailInput P hq hB) (S.J+1)
      (by have h := S.stage_large; omega) (sourceConstant 4) 320 (sourceConstant_pos 4)
      (by norm_num) 20 1000 (scaleSequence S.J S.X 1) (S.sequence_one 1)
      (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
      (initialTail_four (S := S)) (initialTail_frequency P hq hB)
  change tsupport ((initialBase P).field+tail.field) ⊆ Metric.closedBall 0 2
  exact (tsupport_add _ _).trans (union_subset hbase htail)


-- @@ L56-60 verbatim
theorem initialDataLimit_compact
    (hbase : tsupport (initialBase P).field ⊆ Metric.closedBall 0 2) :
    HasCompactSupport (initialDataLimit P hq hB).field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _)
    (initialDataLimit_support P hq hB hbase)


-- @@ L62-68 verbatim
theorem initialDataLimit_support_of_physical
    (hbase : tsupport (fun x => (P 1).state.evolution.velocity (0, x)) ⊆ Metric.closedBall 0 2) :
    tsupport (initialDataLimit P hq hB).field ⊆ Metric.closedBall 0 2 := by
  apply initialDataLimit_support P hq hB
  have he : (initialBase P).field=(fun x => (P 1).state.evolution.velocity (0, x)) :=
    funext (fun x => ((P 1).state.regularity.velocity_match (P 1).parent.zeroTime x).symm)
  rwa [he]


-- @@ L70-70 verbatim
end EulerPacketInduction.Stage


-- @@ L72-72 verbatim
end

-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
section


-- @@ L79-81 verbatim
/-! A compactly supported, smooth, divergence-free initial velocity
whose ordinary smooth Euler solutions have a finite maximal horizon.
The separate continuation and vorticity criteria are not asserted here. -/


-- @@ L83-83 verbatim
@[expose] public section


-- @@ L85-85 verbatim
noncomputable section


-- @@ L87-87 verbatim
namespace EulerPacketInduction


-- @@ L89-90 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerPacketBaseGuardScales

-- @@ L91-91 verbatim
open scoped ContDiff


-- @@ L93-95 verbatim
theorem initialDatum_support : tsupport initialDatum.field ⊆ Metric.closedBall 0 2 :=
  Stage.initialDataLimit_support_of_physical packets le_rfl le_rfl
    (constructionScales.firstForwardStage_initial_support le_rfl le_rfl)


-- @@ L97-98 verbatim
theorem initialDatum_compact : HasCompactSupport initialDatum.field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) initialDatum_support


-- @@ L100-101 verbatim
theorem lifespan_le_one : lifespan.duration ≤ 1 :=
  lifespan_le_base.trans constructionScales.time_small


-- @@ L103-107 verbatim
/-- Has smooth euler solution, given by `∃ hT : 0 < T, ∃ U : Evolution T hT.le, (U.velocity
⟨0,le_rfl,hT.le⟩).field=u₀`. -/
def HasSmoothEulerSolution (u₀ : Space → Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ U : Evolution T hT.le,
    (U.velocity ⟨0,le_rfl,hT.le⟩).field=u₀


-- @@ L109-115 verbatim
theorem hasSmoothEulerSolution_iff (A : SmoothL2Field Space) (T : ℝ) :
    HasSmoothEulerSolution A.field T ↔ HasEulerEvolution A T := by
  constructor
  · rintro ⟨hT,U,hU⟩
    exact ⟨hT,U,field_ext hU⟩
  · rintro ⟨hT,U,hU⟩
    exact ⟨hT,U,congrArg SmoothL2Field.field hU⟩


-- @@ L117-128 verbatim
theorem exists_compact_smooth_finite_lifespan :
    ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
      (∀ x, divergence u₀ x=0) ∧
      ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧
        (∀ t : ℝ, 0 < t → t < T → HasSmoothEulerSolution u₀ t) ∧
        (∀ t : ℝ, T < t → ¬ HasSmoothEulerSolution u₀ t) := by
  refine ⟨initialDatum.field,initialDatum.smooth,initialDatum_compact,initialDatum_divergence,
    lifespan.duration,lifespan.duration_pos,lifespan_le_one,?_,?_⟩
  · intro t ht htT
    exact (hasSmoothEulerSolution_iff initialDatum t).mpr (lifespan.shorter t ht htT)
  · intro t hTt h
    exact lifespan.maximal t hTt ((hasSmoothEulerSolution_iff initialDatum t).mp h)


-- @@ L130-130 verbatim
end EulerPacketInduction


-- @@ L132-132 verbatim
end

-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end


-- @@ L137-137 verbatim
@[expose] public section


-- @@ L139-139 verbatim
noncomputable section


-- @@ L141-141 verbatim
namespace EulerOrdinarySobolev.FiniteLifespan


-- @@ L143-144 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField


-- @@ L146-146 verbatim
variable {A : SmoothL2Field Space} (L : FiniteLifespan A)


-- @@ L148-149 verbatim
/-- Maximal velocity norm, given by `‖finiteField (L.maximalField t)‖`. -/
def maximalVelocityNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t)‖


-- @@ L151-152 verbatim
/-- Maximal gradient norm, given by `‖finiteField (L.maximalField t).derivative‖`. -/
def maximalGradientNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t).derivative‖


-- @@ L154-155 verbatim
/-- Maximal C1 norm, given by `L.maximalVelocityNorm t+L.maximalGradientNorm t`. -/
def maximalC1Norm (t : L.Time) : ℝ := L.maximalVelocityNorm t+L.maximalGradientNorm t


-- @@ L157-157 verbatim
theorem maximalVelocityNorm_nonneg (t : L.Time) : 0 ≤ L.maximalVelocityNorm t := norm_nonneg _


-- @@ L159-159 verbatim
theorem maximalGradientNorm_nonneg (t : L.Time) : 0 ≤ L.maximalGradientNorm t := norm_nonneg _


-- @@ L161-164 verbatim
theorem maximalVelocityNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalVelocityNorm t ≤ K ↔ ∀ x, ‖L.maximalVelocity t x‖ ≤ K := by
  rw [maximalVelocityNorm,BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply,maximalVelocity]


-- @@ L166-170 verbatim
theorem maximalGradientNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalGradientNorm t ≤ K ↔ ∀ x, ‖fderiv ℝ (L.maximalVelocity t) x‖ ≤ K := by
  rw [maximalGradientNorm,BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply]
  rfl


-- @@ L172-173 verbatim
theorem maximalVelocityNorm_continuous : Continuous L.maximalVelocityNorm :=
  (continuous_finiteField L.maximalField L.maximalField_jet_continuous).norm


-- @@ L175-177 verbatim
theorem maximalGradientNorm_continuous : Continuous L.maximalGradientNorm :=
  (continuous_finiteField (fun t => (L.maximalField t).derivative)
    (continuous_jetLp_derivative L.maximalField L.maximalField_jet_continuous)).norm


-- @@ L179-180 verbatim
theorem maximalC1Norm_continuous : Continuous L.maximalC1Norm :=
  L.maximalVelocityNorm_continuous.add L.maximalGradientNorm_continuous


-- @@ L182-187 verbatim
theorem maximalGradientNorm_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalGradientNorm (L.shorterTime S hSL t)=(L.evolution S hS hSL).gradientNormPath t := by
  change ‖finiteField (L.maximalField (L.shorterTime S hSL t)).derivative‖=_
  rw [L.maximalField_eq_evolution S hS hSL t]
  rfl


-- @@ L189-193 verbatim
theorem maximalVelocity_gradient_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ (t : L.Time) (x : Space), τ < t ∧ K < ‖fderiv ℝ (L.maximalVelocity t) x‖ := by
  obtain ⟨S,hS,hSL,t,x,ht,hx⟩ := L.gradient_unbounded_near_endpoint τ K hτ
  refine ⟨L.shorterTime S hSL t,x,ht,?_⟩
  rwa [L.maximalVelocity_eq_evolution S hS hSL t]


-- @@ L195-198 verbatim
theorem maximalGradientNorm_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ t : L.Time, τ < t ∧ K < L.maximalGradientNorm t := by
  obtain ⟨t,x,ht,hx⟩ := L.maximalVelocity_gradient_unbounded_near_endpoint τ K hτ
  exact ⟨t,ht,hx.trans_le ((L.maximalGradientNorm_le_iff t _).mp le_rfl x)⟩


-- @@ L200-203 verbatim
theorem maximalC1Norm_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ t : L.Time, τ < t ∧ K < L.maximalC1Norm t := by
  obtain ⟨t,ht,hK⟩ := L.maximalGradientNorm_unbounded_near_endpoint τ K hτ
  exact ⟨t,ht,hK.trans_le (le_add_of_nonneg_left (L.maximalVelocityNorm_nonneg t))⟩


-- @@ L205-205 verbatim
end EulerOrdinarySobolev.FiniteLifespan


-- @@ L207-207 verbatim
namespace EulerPacketInduction


-- @@ L209-210 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev

-- @@ L211-211 verbatim
open scoped ContDiff


-- @@ L213-214 verbatim
/-- Maximal time: an abbreviation for `lifespan.Time`. -/
abbrev MaximalTime : Type := lifespan.Time


-- @@ L216-217 verbatim
/-- Maximal velocity, given by `lifespan.maximalVelocity t`. -/
def maximalVelocity (t : MaximalTime) : Space → Space := lifespan.maximalVelocity t


-- @@ L219-220 verbatim
/-- Maximal pressure, given by `lifespan.maximalPressure t`. -/
def maximalPressure (t : MaximalTime) : Space → ℝ := lifespan.maximalPressure t


-- @@ L222-223 verbatim
/-- Maximal velocity norm, given by `lifespan.maximalVelocityNorm t`. -/
def maximalVelocityNorm (t : MaximalTime) : ℝ := lifespan.maximalVelocityNorm t


-- @@ L225-226 verbatim
/-- Maximal gradient norm, given by `lifespan.maximalGradientNorm t`. -/
def maximalGradientNorm (t : MaximalTime) : ℝ := lifespan.maximalGradientNorm t


-- @@ L228-229 verbatim
/-- Maximal C1 norm, given by `lifespan.maximalC1Norm t`. -/
def maximalC1Norm (t : MaximalTime) : ℝ := lifespan.maximalC1Norm t


-- @@ L231-234 verbatim
theorem initialDatum_no_endpoint : ¬ HasSmoothEulerSolution initialDatum.field lifespan.duration :=
    by
  intro h
  exact lifespan.no_endpoint ((hasSmoothEulerSolution_iff initialDatum lifespan.duration).mp h)


-- @@ L236-237 verbatim
theorem maximalVelocity_initial : maximalVelocity lifespan.initialTime=initialDatum.field :=
  lifespan.maximalVelocity_initial


-- @@ L239-240 verbatim
theorem maximalVelocity_smooth (t : MaximalTime) : ContDiff ℝ ∞ (maximalVelocity t) :=
  lifespan.maximalVelocity_smooth t


-- @@ L242-244 verbatim
theorem maximalVelocity_joint_continuous :
    Continuous (fun z : MaximalTime × Space => maximalVelocity z.1 z.2) :=
  lifespan.maximalVelocity_joint_continuous


-- @@ L246-247 verbatim
theorem maximalVelocity_divergence (t : MaximalTime) (x : Space) :
    divergence (maximalVelocity t) x=0 := lifespan.maximalVelocity_divergence t x


-- @@ L249-252 verbatim
theorem maximalPressure_spec (t : MaximalTime) :
    ContDiff ℝ ∞ (maximalPressure t) ∧ maximalPressure t 0=0 ∧
      ∀ x, _root_.gradient (maximalPressure t) x=(lifespan.maximalPressureField t).field x :=
  lifespan.maximalPressure_spec t


-- @@ L254-256 verbatim
theorem maximalGradientNorm_spec (t : MaximalTime) (K : ℝ) :
    maximalGradientNorm t ≤ K ↔ ∀ x, ‖fderiv ℝ (maximalVelocity t) x‖ ≤ K :=
  lifespan.maximalGradientNorm_le_iff t K


-- @@ L258-260 verbatim
theorem maximalVelocityNorm_spec (t : MaximalTime) (K : ℝ) :
    maximalVelocityNorm t ≤ K ↔ ∀ x, ‖maximalVelocity t x‖ ≤ K :=
  lifespan.maximalVelocityNorm_le_iff t K


-- @@ L262-263 verbatim
theorem maximalGradientNorm_continuous : Continuous maximalGradientNorm :=
  lifespan.maximalGradientNorm_continuous


-- @@ L265-266 verbatim
theorem maximalC1Norm_continuous : Continuous maximalC1Norm :=
  lifespan.maximalC1Norm_continuous


-- @@ L268-270 verbatim
theorem pointwiseGradient_unbounded_near_maximal_time (τ K : ℝ) (hτ : τ < lifespan.duration) :
    ∃ (t : MaximalTime) (x : Space), τ < t ∧ K < ‖fderiv ℝ (maximalVelocity t) x‖ :=
  lifespan.maximalVelocity_gradient_unbounded_near_endpoint τ K hτ


-- @@ L272-275 verbatim
/-- The gradient supremum has infinite upper limit at the actual maximal time. -/
theorem gradient_unbounded_near_maximal_time (τ K : ℝ) (hτ : τ < lifespan.duration) :
    ∃ t : MaximalTime, τ < t ∧ K < maximalGradientNorm t :=
  lifespan.maximalGradientNorm_unbounded_near_endpoint τ K hτ


-- @@ L277-280 verbatim
/-- The same characterization for the sum of the actual velocity and gradient suprema. -/
theorem c1_unbounded_near_maximal_time (τ K : ℝ) (hτ : τ < lifespan.duration) :
    ∃ t : MaximalTime, τ < t ∧ K < maximalC1Norm t :=
  lifespan.maximalC1Norm_unbounded_near_endpoint τ K hτ


-- @@ L282-288 verbatim
theorem initialDatum_c1_breakdown :
    0 < lifespan.duration ∧ lifespan.duration ≤ 1 ∧
      ¬ HasSmoothEulerSolution initialDatum.field lifespan.duration ∧
      ∀ τ : ℝ, τ < lifespan.duration → ∀ K : ℝ,
        ∃ t : MaximalTime, τ < t ∧ K < maximalC1Norm t :=
  ⟨lifespan.duration_pos,lifespan_le_one,initialDatum_no_endpoint,
    fun τ hτ K => c1_unbounded_near_maximal_time τ K hτ⟩


-- @@ L290-290 verbatim
end EulerPacketInduction
