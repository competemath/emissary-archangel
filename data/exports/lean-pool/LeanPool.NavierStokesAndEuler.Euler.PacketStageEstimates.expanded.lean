/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGuards
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale


-- @@ L14-15 verbatim
/-! The actual stage guards satisfy the fixed pressure, initial-gradient
and frame-renewal budgets used by the induction. -/


-- @@ L17-17 verbatim
section


-- @@ L19-21 verbatim
/-! Actual geometric pressure increments are dominated by the literal
summable scale costs. The physical parent-strain bound is CM times the
previous shear, while the activation constants remain fixed low constants. -/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace EulerParentPacketFrames.LabelData


-- @@ L29-31 verbatim
open Set Real EulerSmoothLimit EulerPacketSourceGeometry EulerPacketGeometryLowBounds
  EulerPacketPressureScale EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice
  EulerPacketSourceScales EulerScale EulerParentBadRatio


-- @@ L33-50 verbatim
variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (A : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (Ti : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (J D : ℕ) (hJ : 3 ≤ J) (X Cθ CM CMn CHn c : ℝ)
  (hX : 1 ≤ X) (hCθ : 1 ≤ Cθ) (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) (hc : 1 ≤ c)
  (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
  (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
  (n : ℕ) (M : ℝ)
  (hK : L.K ≤ previousFrequency J D X n ^ c) (hTib : Ti ≤ previousShear J X n)
  (hCMb : A.CM ≤ CMn) (hCHb : A.CH ≤ CHn)
  (hTheta : P.horizon ≤ sourceTheta J Cθ (scaleSequence J X) n)
  (hSigma : P.sigma * scaleSequence J X n ≤ 2)
  (hchild : A.hchild ≤ shear J X n) (hMb : M ≤ CM * previousShear J X n)


-- @@ L52-52 verbatim
include hτ1 hTi hJ hX hCθ hCM hCMn hCHn hc hbaseH hbaseK hK hTib hCMb hCHb hTheta hSigma hchild hMb


-- @@ L54-72 verbatim
theorem joined_bad_pressure_cost_bound :
    2*M*A.hchild*A.badRatio ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hx := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hs : 1 ≤ P.shear := by
    have hh := mul_le_mul_of_nonneg_left hτ1 A.shear_pos.le
    linarith only [hh,A.history_layer]
  have hi : P.shear⁻¹ ≤ 1 := (inv_le_one₀ A.shear_pos).2 hs
  have hQ := parameters_le_source_exponential J D hJ X c hX hc hbaseH hbaseK n
    L.K Ti P.shear⁻¹ A.CM A.CH CMn CHn hK hTib hi hCMb hCHb hCMn hCHn
  have ht0 := (inv_pos.mpr hτ).le.trans hTi
  have hQ0 : 0 ≤ 1+L.K+Ti+P.shear⁻¹+A.CM+A.CH := by
    positivity [L.K_one,A.shear_pos,A.CM_nonneg,A.CH_nonneg]
  have hM' := hMb.trans (mul_le_mul_of_nonneg_left
    (previousShear_le_normal J (by omega) X hbaseH n) hCM)
  exact badCost_bound J hJ Cθ CM CMn CHn c hCθ hCM hCMn hCHn (scaleSequence J X) hx n
    M A.hchild A.badRatio (1+L.K+Ti+P.shear⁻¹+A.CM+A.CH) P.horizon P.sigma
    A.child_nonneg A.badRatio_nonneg hQ0 (zero_le_one.trans A.horizon_lower) A.sigma_pos
    hM' hchild hQ hTheta hSigma
    (L.badRatio_polynomial m hm R S hS H τ hτ hτT P A Ti hτ1 hTi)


-- @@ L74-85 verbatim
theorem joined_upper_pressure_cost_bound (hdelta : A.δ ≤ spike J X n) :
    2*M*A.hchild*(A.δ*goodRatio+A.badRatio) ≤
      2*CM*goodRatio*goodCost J (scaleSequence J X) n +
        badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hb := L.joined_bad_pressure_cost_bound m hm R S hS H τ hτ hτT P A Ti hτ1 hTi
    J D hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc hbaseH hbaseK n M
    hK hTib hCMb hCHb hTheta hSigma hchild hMb
  have hg := goodCost_bound J (by omega) X CM M A.δ A.hchild hCM A.delta_nonneg A.child_nonneg
    hbaseH n hMb hdelta hchild
  calc
    _ = 2*M*A.hchild*(A.δ*goodRatio)+2*M*A.hchild*A.badRatio := by ring
    _ ≤ _ := add_le_add hg hb


-- @@ L87-95 verbatim
theorem joined_initial_gradient_cost_bound (hMone : 1 ≤ M) (ev : ℝ) :
    A.hchild*A.badRatio+ev ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n+ev := by
  have hb := L.joined_bad_pressure_cost_bound m hm R S hS H τ hτ hτT P A Ti hτ1 hTi
    J D hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc hbaseH hbaseK n M
    hK hTib hCMb hCHb hTheta hSigma hchild hMb
  have hbase : A.hchild*A.badRatio ≤ 2*M*A.hchild*A.badRatio := by
    linarith only [mul_nonneg (by linarith only [hMone] : 0 ≤ 2*M-1)
      (mul_nonneg A.child_nonneg A.badRatio_nonneg)]
  exact add_le_add (hbase.trans hb) le_rfl


-- @@ L97-97 verbatim
end EulerParentPacketFrames.LabelData


-- @@ L99-99 verbatim
namespace EulerPacketSourceGeometry.ForwardGuards


-- @@ L101-103 verbatim
open Real EulerSmoothLimit EulerPacketGeometryLowBounds EulerParentBadRatio
  EulerPacketPressureScale EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice
  EulerPacketSourceScales EulerScale


-- @@ L105-106 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {P : ParentFrame D 0} (A : ForwardGuards P)


-- @@ L108-120 verbatim
omit [CompleteSpace U] in
theorem earlyRatio_bound :
    A.earlyRatio ≤ badConstant*1^degree*P.horizon^5*exp (-(1/(4*P.sigma))) := by
  have hh : cutoffBound*(8232*exp 9*P.horizon^5) ≤
      cutoffBound*(8232*exp 9*P.horizon^5+4*P.horizon*(boundConstant*1^degree)) := by
    apply mul_le_mul_of_nonneg_left _ cutoffBound_pos.le
    exact le_add_of_nonneg_right (by positivity [A.horizon_lower,constant_pos])
  rw [show A.earlyRatio=cutoffBound*(8232*exp 9*P.horizon^5)*exp (-(1/(4*P.sigma))) by
    unfold earlyRatio
    ring]
  apply (mul_le_mul_of_nonneg_right hh (exp_pos _).le).trans
  exact mul_le_mul_of_nonneg_right (prefactor_bound 1 P.horizon le_rfl A.horizon_lower) (exp_pos
      _).le


-- @@ L122-128 verbatim
variable (J : ℕ) (hJ : 3 ≤ J) (X Cθ CM CMn CHn c : ℝ)
  (hX : 1 ≤ X) (hCθ : 1 ≤ Cθ) (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) (hc : 0 ≤ c)
  (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
  (n : ℕ) (M : ℝ)
  (hTheta : P.horizon ≤ sourceTheta J Cθ (scaleSequence J X) n)
  (hSigma : P.sigma * scaleSequence J X n ≤ 2)
  (hchild : A.hchild ≤ shear J X n) (hMb : M ≤ CM * previousShear J X n)


-- @@ L130-130 verbatim
include hJ hX hCθ hCM hCMn hCHn hc hbaseH hTheta hSigma hchild hMb


-- @@ L132-145 verbatim
omit [CompleteSpace U] in
theorem bad_pressure_cost_bound :
    2*M*A.hchild*A.earlyRatio ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hx := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hz : 0 ≤ c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4) := by positivity [hx n]
  have he := one_le_exp hz
  have hQ : 1 ≤ (4+CMn+CHn)*exp (c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4)) := by
    linarith only [he,mul_nonneg hCMn (zero_le_one.trans he),mul_nonneg hCHn (zero_le_one.trans
        he)]
  have hM' := hMb.trans (mul_le_mul_of_nonneg_left
    (previousShear_le_normal J (by omega) X hbaseH n) hCM)
  exact badCost_bound J hJ Cθ CM CMn CHn c hCθ hCM hCMn hCHn (scaleSequence J X) hx n
    M A.hchild A.earlyRatio 1 P.horizon P.sigma A.child_nonneg A.earlyRatio_nonneg zero_le_one
    (zero_le_one.trans A.horizon_lower) A.sigma_pos hM' hchild hQ hTheta hSigma A.earlyRatio_bound


-- @@ L147-158 verbatim
omit [CompleteSpace U] in
theorem upper_pressure_cost_bound (hdelta : A.δ ≤ spike J X n) :
    2*M*A.hchild*(A.δ*goodRatio+A.earlyRatio) ≤
      2*CM*goodRatio*goodCost J (scaleSequence J X) n +
        badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hb := A.bad_pressure_cost_bound J hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc
    hbaseH n M hTheta hSigma hchild hMb
  have hg := goodCost_bound J (by omega) X CM M A.δ A.hchild hCM A.delta_nonneg A.child_nonneg
    hbaseH n hMb hdelta hchild
  calc
    _ = 2*M*A.hchild*(A.δ*goodRatio)+2*M*A.hchild*A.earlyRatio := by ring
    _ ≤ _ := add_le_add hg hb


-- @@ L160-168 verbatim
omit [CompleteSpace U] in
theorem initial_gradient_cost_bound (hMone : 1 ≤ M) (ev : ℝ) :
    A.hchild*A.earlyRatio+ev ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n+ev := by
  have hb := A.bad_pressure_cost_bound J hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc
    hbaseH n M hTheta hSigma hchild hMb
  have hbase : A.hchild*A.earlyRatio ≤ 2*M*A.hchild*A.earlyRatio := by
    linarith only [mul_nonneg (by linarith only [hMone] : 0 ≤ 2*M-1)
      (mul_nonneg A.child_nonneg A.earlyRatio_nonneg)]
  exact add_le_add (hbase.trans hb) le_rfl


-- @@ L170-170 verbatim
end EulerPacketSourceGeometry.ForwardGuards


-- @@ L172-172 verbatim
end

-- @@ L173-173 verbatim
end


-- @@ L175-175 verbatim
end


-- @@ L177-177 verbatim
@[expose] public section


-- @@ L179-179 verbatim
noncomputable section


-- @@ L181-181 verbatim
namespace EulerPacketInduction.Stage


-- @@ L183-187 verbatim
open Set Real EulerSmoothLimit EulerParentPacketFrames EulerPacketSourceGeometry
  EulerTransverseFrameCoordinates EulerPacketInductionScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketSourceScales
  EulerPacketLowConstants EulerPacketPressureScale EulerPacketGeometryLowBounds
  EulerParentRenewalScale EulerParentNeighborThreshold EulerPacketSupport


-- @@ L189-189 verbatim
section Joined


-- @@ L191-193 verbatim
variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L195-195 verbatim
local notation "G" => P.joinedGuards hn hq hB

-- @@ L196-196 verbatim
local notation "R" => LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))


-- @@ L198-201 verbatim
theorem joined_horizon_bound :
    (P.joinedFrame hn).horizon ≤ sourceTheta S.J 4 (scaleSequence S.J S.X) n := by
  rw [P.joinedFrame_horizon,P.restrictedFrame_horizon]
  exact P.source_stage.horizon_le_Theta


-- @@ L203-206 verbatim
include hn in
theorem history_inverse_shear : P.time⁻¹ ≤ previousShear S.J S.X n := by
  rw [← one_div]
  exact (div_le_iff₀ (P.time_pos hn)).mpr (P.history_layer hn)


-- @@ L208-226 verbatim
theorem joined_bad_cost :
    2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*(G).badRatio ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n
          :=
  P.restrictedState.labels.joined_bad_pressure_cost_bound (P.joinedNormal hn) (P.joinedNormal_unit
      hn)
    R support compact P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame
        hn)
    G P.time⁻¹ P.time_one le_rfl S.J S.D S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear S.actual.initial_frequency n (gradientConstant*previousShear S.J S.X n)
    (by
        rw [rpow_ofNat]; exact P.label_eq.le) (P.history_inverse_shear hn) (P.joinedGuards_CM hn hq
            hB).le
    (P.joinedGuards_CH hn hq hB).le (P.joined_horizon_bound hn)
    (by
        erw [P.joinedFrame_sigma]; exact P.normalized_sigma) (P.joinedGuards_shear hn hq hB).le
            le_rfl


-- @@ L228-237 verbatim
theorem joined_initial_cost :
    (G).hchild*(G).badRatio+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X n := by
  have hb := P.joined_bad_cost hn hq hB
  have hm : 1 ≤ 2*(gradientConstant*previousShear S.J S.X n) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one n) gradient_nonneg
    linarith only [gradient_properties.1,h]
  have hn0 := mul_nonneg (G).child_nonneg (G).badRatio_nonneg
  have hh := mul_le_mul_of_nonneg_right hm hn0
  unfold initialIncrement
  linarith only [hb,hh]


-- @@ L239-256 verbatim
theorem joined_pressure_cost :
    2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*((G).δ*goodRatio+(G).badRatio) +
      (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X n := by
  have h := P.restrictedState.labels.joined_upper_pressure_cost_bound
    (P.joinedNormal hn) (P.joinedNormal_unit hn) R support compact P.restrictedLow P.time
    (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn) G P.time⁻¹ P.time_one le_rfl
    S.J S.D S.stage_large S.X 4 gradientConstant gradientConstant hessianConstant 80 S.x_one
    (by norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear S.actual.initial_frequency n (gradientConstant*previousShear S.J S.X n)
    (by
        rw [rpow_ofNat]; exact P.label_eq.le) (P.history_inverse_shear hn) (P.joinedGuards_CM hn hq
            hB).le
    (P.joinedGuards_CH hn hq hB).le (P.joined_horizon_bound hn)
    (by erw [P.joinedFrame_sigma]; exact P.normalized_sigma)
    (P.joinedGuards_shear hn hq hB).le le_rfl (P.joinedGuards_delta hn hq hB).le
  unfold pressureIncrement initialIncrement
  exact (add_le_add h (le_refl ((frequency S.J S.X n)^(-(1/4 : ℝ))))).trans_eq
    (add_assoc _ _ _)


-- @@ L258-267 verbatim
theorem joined_renewal_errors :
    (P.joinedGeometry hn hq hB).couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n ∧
    (P.joinedGeometry hn hq hB).tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n := by
  exact (G).renewal_errors_on_scales (by change (1/2 : ℝ) ≤ 1; norm_num)
    S.J S.D (by have h := S.stage_large; omega) 4 (q : ℝ) frameConstant S.X P.frame.a
    (by norm_num) frame_properties.1 S.x_one P.coupling_bounds.2 n (P.joinedFrame_a hn)
    ((P.joinedFrame_shear hn).trans P.frame_shear) (P.joined_horizon_bound hn)
    ((P.joinedFrame_G hn).le.trans P.frame_bound) ((P.joinedFrame_error hn).le.trans P.frame_error)
    (P.joined_source_neighbor hn hq hB) (P.joinedGuards_y hn hq hB)
    (by erw [P.joinedFrame_sigma]; exact P.tilt_upper)


-- @@ L269-269 verbatim
end Joined


-- @@ L271-271 verbatim
section Forward


-- @@ L273-274 verbatim
variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)


-- @@ L276-276 verbatim
local notation "G" => P.forwardGuards hq hB


-- @@ L278-281 verbatim
theorem forward_horizon_bound : P.forwardFrame.horizon ≤ sourceTheta S.J 4 (scaleSequence S.J S.X)
    0 := by
  rw [P.forwardFrame_horizon,P.restrictedFrame_horizon]
  exact P.source_stage.horizon_le_Theta


-- @@ L283-293 verbatim
theorem forward_bad_cost :
    2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*(G).earlyRatio ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) 0
          := by
  apply (G).bad_pressure_cost_bound S.J S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear 0 (gradientConstant*previousShear S.J S.X 0) P.forward_horizon_bound
    _ le_rfl le_rfl
  rw [P.forwardFrame_sigma]
  exact P.normalized_sigma


-- @@ L295-304 verbatim
theorem forward_initial_cost :
    (G).hchild*(G).earlyRatio+(frequency S.J S.X 0)^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X 0 := by
  have hb := P.forward_bad_cost hq hB
  have hm : 1 ≤ 2*(gradientConstant*previousShear S.J S.X 0) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one 0) gradient_nonneg
    linarith only [gradient_properties.1,h]
  have hn0 := mul_nonneg (G).child_nonneg (G).earlyRatio_nonneg
  have hh := mul_le_mul_of_nonneg_right hm hn0
  unfold initialIncrement
  linarith only [hb,hh]


-- @@ L306-315 verbatim
theorem forward_pressure_cost :
    2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*((G).δ*goodRatio+(G).earlyRatio) +
      (frequency S.J S.X 0)^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X 0 := by
  have h := (G).upper_pressure_cost_bound S.J S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear 0 (gradientConstant*previousShear S.J S.X 0) P.forward_horizon_bound
    (by rw [P.forwardFrame_sigma]; exact P.normalized_sigma) le_rfl le_rfl le_rfl
  unfold pressureIncrement initialIncrement
  linarith only [h]


-- @@ L317-325 verbatim
theorem forward_renewal_errors :
    (P.forwardGeometry hq hB).couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 ∧
    (P.forwardGeometry hq hB).tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 := by
  exact (G).renewal_errors_on_scales (by change (1/2 : ℝ) ≤ 1; norm_num)
    S.J S.D (by have h := S.stage_large; omega) 4 (q : ℝ) frameConstant S.X P.frame.a
    (by norm_num) frame_properties.1 S.x_one P.coupling_bounds.2 0 P.forwardFrame_a
    (P.forwardFrame_shear.trans P.frame_shear) P.forward_horizon_bound
    (P.forwardFrame_G.le.trans P.frame_bound) (P.forwardFrame_error.le.trans P.frame_error)
    (P.forward_source_neighbor hq hB) rfl (by rw [P.forwardFrame_sigma]; exact P.tilt_upper)


-- @@ L327-327 verbatim
end Forward

-- @@ L328-328 verbatim
end EulerPacketInduction.Stage
