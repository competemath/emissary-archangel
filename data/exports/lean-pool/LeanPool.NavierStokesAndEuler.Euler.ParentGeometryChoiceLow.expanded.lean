/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryForwardChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryJoinedChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds


-- @@ L15-16 verbatim
/-! The same geometrically selected correction supplies the actual
child's whole-horizon physical bounds and its next localized source guard. -/


-- @@ L18-18 verbatim
section


-- @@ L20-22 verbatim
/-! The actual initialized packet changes the initial velocity gradient
by the exponentially small early/history size plus its correction error.
These are the costs needed to preserve the localized source guards. -/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerPacketPhysicalLowBounds


-- @@ L30-30 verbatim
open EulerSmoothLimit EulerPeriodicProfile


-- @@ L32-42 verbatim
theorem norm_le_of_shear_error (V : Matrix) (amp δ θ ev size : ℝ) (r w : Space)
    (hamp : 0 ≤ amp) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : amp * (‖r‖ * ‖w‖) ≤ δ * size)
    (herr : ‖V - shearTerm amp (deriv (profile δ) θ) r w‖ ≤ ev) : ‖V‖ ≤ size+ev := by
  have hshear : ‖shearTerm amp (deriv (profile δ) θ) r w‖ ≤ size :=
    (shearTerm_norm_le amp _ δ r w hamp (profile_deriv_abs δ hδ hδ1 θ)).trans
      ((div_le_iff₀ hδ).2 (by nlinarith only [hsize]))
  have h := norm_of_remainder V 0 (shearTerm amp (deriv (profile δ) θ) r w) ev
    (by simpa only [sub_zero] using herr)
  simp only [norm_zero,zero_add] at h
  exact h.trans (add_le_add hshear le_rfl)


-- @@ L44-44 verbatim
end EulerPacketPhysicalLowBounds


-- @@ L46-46 verbatim
namespace EulerParentPacketFrames.Evolution


-- @@ L48-53 verbatim
open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketGeometryLowBounds
  EulerPacketPhysicalLowBounds EulerPacketPrimaryFactorization EulerPeriodicProfile
  EulerSpatialCutoffs EulerPacketTerminalDatum

-- @@ L54-54 verbatim
open scoped ContDiff


-- @@ L56-56 verbatim
variable {A : Parent} (E : Evolution A)


-- @@ L58-66 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
      Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  (k : ℝ) (hk : k * κ = 1)


-- @@ L68-68 verbatim
section Joined


-- @@ L70-74 verbatim
variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {H : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (G : Guards hτ hτT F H) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hs : tsupport innerCutoff ⊆ support) (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)


-- @@ L76-93 verbatim
include hk hδ hδ1 in
theorem exactPacket_bad_gradient_increment
    (ev ep : ℝ) (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime τ F.a F.epsilon t ≤ 1) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x -
      fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ G.hchild*G.badRatio+ev := by
  rw [(E.exactPacket_derivative_split m hm J support hSupport B residual k hk t
      x).1,add_sub_cancel_left]
  apply norm_le_of_shear_error _ (G.primaryAmplitude hball) G.δ
    (k*⟪m,E.inverse.normalized t (A.ell⁻¹ • x)⟫_ℝ) ev (G.hchild*G.badRatio)
    ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t (A.ell⁻¹ •
        x)))
    (canonicalVelocity τ hτ hτT H G.terminal hs t (E.inverse.normalized t (A.ell⁻¹ • x)))
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.bad_primary_size hball t ht (E.inverse.normalized t (A.ell⁻¹ •
      x)) hs
  · exact (herr t (A.ell⁻¹ • x)).1


-- @@ L95-107 verbatim
include hk hδ hδ1 in
theorem exactPacket_initial_gradient_increment
    (ev ep : ℝ) (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (0,y)) x -
      fderiv ℝ (fun y => E.velocity (0,y)) x‖ ≤ G.hchild*G.badRatio+ev := by
  apply E.exactPacket_bad_gradient_increment m hm J support hSupport B residual k hk G hball hs hδ
      hδ1 ev ep herr A.zeroTime _ x
  change (F.a/F.epsilon)*(0-τ) ≤ 1
  have h : (F.a/F.epsilon)*(0-τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg G.a_pos.le G.epsilon_pos.le) (by linarith only [hτ])
  linarith only [h]


-- @@ L109-109 verbatim
end Joined


-- @@ L111-111 verbatim
section Forward


-- @@ L113-115 verbatim
variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (G : ForwardGuards F) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)


-- @@ L117-135 verbatim
include hk hδ hδ1 in
theorem exactForwardPacket_early_gradient_increment
    (ev ep : ℝ) (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime 0 F.a F.epsilon t ≤ 1) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x -
      fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ G.hchild*G.earlyRatio+ev := by
  rw [(E.exactPacket_derivative_split m hm J support hSupport B residual k hk t
      x).1,add_sub_cancel_left]
  apply norm_le_of_shear_error _ (G.primaryAmplitude hball) G.δ
    (k*⟪m,E.inverse.normalized t (A.ell⁻¹ • x)⟫_ℝ) ev (G.hchild*G.earlyRatio)
    ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t (A.ell⁻¹ •
        x)))
    (EulerPacketForwardFactorization.canonicalVelocity (A.transverseData m hm J support hSupport)
        G.initialCoordinate t (E.inverse.normalized t (A.ell⁻¹ • x)))
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.early_primary_size hball t ht (E.inverse.normalized t (A.ell⁻¹ •
      x))
  · exact (herr t (A.ell⁻¹ • x)).1


-- @@ L137-147 verbatim
include hk hδ hδ1 in
theorem exactForwardPacket_initial_gradient_increment
    (ev ep : ℝ) (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (0,y)) x -
      fderiv ℝ (fun y => E.velocity (0,y)) x‖ ≤ G.hchild*G.earlyRatio+ev := by
  apply E.exactForwardPacket_early_gradient_increment m hm J support hSupport B residual k hk G
      hball hδ hδ1 ev ep herr A.zeroTime _ x
  change (F.a/F.epsilon)*(0-0) ≤ 1
  norm_num


-- @@ L149-149 verbatim
end Forward


-- @@ L151-151 verbatim
end EulerParentPacketFrames.Evolution


-- @@ L153-153 verbatim
end

-- @@ L154-154 verbatim
end


-- @@ L156-156 verbatim
end


-- @@ L158-158 verbatim
section


-- @@ L160-162 verbatim
/-! The next packet's localized lower initial-gradient bounds and upper
pressure bound are consequences of the exact physical estimates. The
radius stays fixed, and the boundary parameter has a canonical value. -/


-- @@ L164-164 verbatim
@[expose] public section


-- @@ L166-166 verbatim
noncomputable section


-- @@ L168-168 verbatim
namespace EulerParentPacketFrames.Evolution


-- @@ L170-174 verbatim
open Set InnerProductSpace EulerSmoothLimit EulerMeanHarmonic
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerPacketTerminalDatum EulerSpatialCutoffs
  EulerPacketSourceGeometry EulerPacketGeometryLowBounds


-- @@ L176-190 verbatim
variable {A : Parent} (E : Evolution A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
      Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field period A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data period A.T) (hG : G.A = B.liftedPacketCoefficient period V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)


-- @@ L192-192 verbatim
section Joined


-- @@ L194-198 verbatim
variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {D : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (C : Guards hτ hτT F D) (hball : (1 / 2 : ℝ) ≤ C.radius)
  (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ support) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)


-- @@ L200-227 verbatim
/-- Joined child low bounds as an element of `LowBounds (A.child G k m hgraph nextEll hnext
hnext1)`. -/
def joinedChildLowBounds (H : LowBounds A) (ev ep CM CH : ℝ)
    (herr : E.SourceErrors m hm J support hSupport B residual k C hball hs ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K + 2 * CM * C.hchild * (C.δ * goodRatio + C.badRatio) + ep) * (A.T ^ 2 / 2) +
      (H.Be + (C.hchild * C.badRatio + ev)) * A.T +
      boundaryLocalizationC2 * (H.Bc + (C.hchild * C.badRatio + ev)) * H.r ^ 3 * A.T ≤ 1 / 2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  apply E.updateLowBounds
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1)
    H (C.hchild*C.badRatio+ev) (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.badRatio)+ep)
  · exact add_nonneg (mul_nonneg C.child_nonneg C.badRatio_nonneg) hev
  · positivity [H.K_nonneg,C.child_nonneg,C.delta_nonneg,goodRatio_pos,C.badRatio_nonneg]
  · intro x
    exact E.exactPacket_initial_gradient_increment m hm J support hSupport B residual k hk
      C hball hs hδ hδ1 ev ep herr x
  · intro t x z
    let EC := E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1
    rw [← EC.pressure_hessian_eq_force]
    exact (E.exactPacket_whole_horizon_low_bounds m hm J support hSupport B residual k hk
      C hball hs hδ hδ1 ev ep CM CH H.K herr hCM hCH
      (E.force_quadratic_upper_of_lowBounds H) t x).2.2 z
  · exact hsmall


-- @@ L229-229 verbatim
end Joined


-- @@ L231-231 verbatim
section Forward


-- @@ L233-235 verbatim
variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (C : ForwardGuards F) (hball : (1 / 2 : ℝ) ≤ C.radius)
  (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)


-- @@ L237-264 verbatim
/-- Forward child low bounds as an element of `LowBounds (A.child G k m hgraph nextEll hnext
hnext1)`. -/
def forwardChildLowBounds (H : LowBounds A) (ev ep CM CH : ℝ)
    (herr : E.ForwardSourceErrors m hm J support hSupport B residual k C hball ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K + 2 * CM * C.hchild * (C.δ * goodRatio + C.earlyRatio) + ep) * (A.T ^ 2 / 2) +
      (H.Be + (C.hchild * C.earlyRatio + ev)) * A.T +
      boundaryLocalizationC2 * (H.Bc + (C.hchild * C.earlyRatio + ev)) * H.r ^ 3 * A.T ≤ 1 / 2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  apply E.updateLowBounds
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1)
    H (C.hchild*C.earlyRatio+ev) (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.earlyRatio)+ep)
  · exact add_nonneg (mul_nonneg C.child_nonneg C.earlyRatio_nonneg) hev
  · positivity [H.K_nonneg,C.child_nonneg,C.delta_nonneg,goodRatio_pos,C.earlyRatio_nonneg]
  · intro x
    exact E.exactForwardPacket_initial_gradient_increment m hm J support hSupport B residual k hk
      C hball hδ hδ1 ev ep herr x
  · intro t x z
    let EC := E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1
    rw [← EC.pressure_hessian_eq_force]
    exact (E.exactForwardPacket_whole_horizon_low_bounds m hm J support hSupport B residual k hk
      C hball hδ hδ1 ev ep CM CH H.K herr hCM hCH
      (E.force_quadratic_upper_of_lowBounds H) t x).2.2 z
  · exact hsmall


-- @@ L266-266 verbatim
end Forward


-- @@ L268-268 verbatim
end EulerParentPacketFrames.Evolution


-- @@ L270-270 verbatim
end

-- @@ L271-271 verbatim
end


-- @@ L273-273 verbatim
end


-- @@ L275-275 verbatim
@[expose] public section


-- @@ L277-277 verbatim
noncomputable section


-- @@ L279-279 verbatim
namespace EulerParentPacketFrames.GeometryForwardChoice


-- @@ L281-283 verbatim
open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic


-- @@ L285-289 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)


-- @@ L291-309 verbatim
/-- Low bounds as an element of `LowBounds F.parent`. -/
def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.earlyRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.earlyRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.earlyRatio +
        k ^ (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) : LowBounds F.parent := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  let V := forwardInitializedNormalizedField I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.forwardChildLowBounds I.normal I.normal_unit I.coordinates I.support
      I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall


-- @@ L311-330 verbatim
theorem lowBounds_values (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.earlyRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.earlyRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.earlyRatio +
        k ^ (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) :
    (F.lowBounds CM CH hCM hCH
        hsmall).Be=I.low.Be+(I.geometry.hchild * I.geometry.earlyRatio + k^(-(1 / 4 : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
        hsmall).Bc=I.low.Bc+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
        hsmall).K=I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.earlyRatio) +
      k^(-(1/4 : ℝ)) ∧
    (F.lowBounds CM CH hCM hCH hsmall).r=I.low.r ∧
    (F.lowBounds CM CH hCM hCH hsmall).L =
      boundaryLocalizationC1*(F.lowBounds CM CH hCM hCH hsmall).Bc+1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩


-- @@ L332-350 verbatim
theorem physical_bounds (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (t,y)) x‖ ≤
      CM+I.geometry.hchild*(goodRatio+I.geometry.earlyRatio)+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ ((state I S k hk nextEll hnext hnext1 F hSym).evolution.force t) x‖ ≤
      CH+2*CM*I.geometry.hchild*(goodRatio+I.geometry.earlyRatio)+k^(-(1/4 : ℝ)) := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  have h := S.evolution.exactForwardPacket_whole_horizon_low_bounds I.normal I.normal_unit
      I.coordinates
    I.support I.support_compact F.Q res k (mul_inv_cancel₀ hk.pos.ne') I.geometry I.halfBall
    I.delta_pos I.delta_le_one (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH I.low.K
    F.errors hCM hCH (S.evolution.force_quadratic_upper_of_lowBounds I.low) t x
  refine ⟨h.1,?_⟩
  erw [← (state I S k hk nextEll hnext hnext1 F hSym).evolution.pressure_hessian_eq_force]
  exact h.2.1


-- @@ L352-352 verbatim
end EulerParentPacketFrames.GeometryForwardChoice


-- @@ L354-354 verbatim
namespace EulerParentPacketFrames.GeometryJoinedChoice


-- @@ L356-358 verbatim
open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic


-- @@ L360-364 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)


-- @@ L366-387 verbatim
/-- Low bounds as an element of `LowBounds F.parent`. -/
def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.badRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.badRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.badRatio + k ^
        (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) : LowBounds F.parent := by
  let res := initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos
      I.history_lt
    I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement (truncation
        k) F.hn k hk.four
  let V := initializedNormalizedField I.meanData I.data rfl I.historyTime I.history_pos
      I.history_lt I.history
    I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.joinedChildLowBounds I.normal I.normal_unit I.coordinates I.support
      I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.cutoff_support I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall


-- @@ L389-408 verbatim
theorem lowBounds_values (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.badRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.badRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.badRatio + k ^
        (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) :
    (F.lowBounds CM CH hCM hCH hsmall).Be=I.low.Be+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4
        : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH hsmall).Bc=I.low.Bc+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4
        : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
        hsmall).K=I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.badRatio) +
      k^(-(1/4 : ℝ)) ∧
    (F.lowBounds CM CH hCM hCH hsmall).r=I.low.r ∧
    (F.lowBounds CM CH hCM hCH hsmall).L =
      boundaryLocalizationC1*(F.lowBounds CM CH hCM hCH hsmall).Bc+1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩


-- @@ L410-430 verbatim
theorem physical_bounds (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (t,y)) x‖ ≤
      CM+I.geometry.hchild*(goodRatio+I.geometry.badRatio)+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ ((state I S k hk nextEll hnext hnext1 F hSym).evolution.force t) x‖ ≤
      CH+2*CM*I.geometry.hchild*(goodRatio+I.geometry.badRatio)+k^(-(1/4 : ℝ)) := by
  let res := initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos
      I.history_lt
    I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement (truncation
        k) F.hn k hk.four
  have h := S.evolution.exactPacket_whole_horizon_low_bounds I.normal I.normal_unit I.coordinates
    I.support I.support_compact F.Q res k (mul_inv_cancel₀ hk.pos.ne') I.geometry I.halfBall
        I.cutoff_support
    I.delta_pos I.delta_le_one (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH I.low.K
    F.errors hCM hCH (S.evolution.force_quadratic_upper_of_lowBounds I.low) t x
  refine ⟨h.1,?_⟩
  erw [← (state I S k hk nextEll hnext hnext1 F hSym).evolution.pressure_hessian_eq_force]
  exact h.2.1


-- @@ L432-432 verbatim
end EulerParentPacketFrames.GeometryJoinedChoice
