/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceCenter
public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalParameters
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards


-- @@ L14-15 verbatim
/-! Actual frame renewal for the very correction and flow chosen by
the geometric packet factories. Center source matching is derived. -/


-- @@ L17-17 verbatim
section


-- @@ L19-22 verbatim
/-! The geometric target of the actual forward or joined primary is the
activation time of the next parent frame. These factories are the checked
`SmoothState` renewals with the source-selected amplitude and primary;
all target matching is proved from their definitions. -/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerParentPacketFrames.SmoothState


-- @@ L30-33 verbatim
open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerSpatialCutoffs EulerPeriodicProfile
  EulerPacketMovingFrame EulerPacketNormalizedPrimary


-- @@ L35-41 verbatim
variable {A N : Parent} (S : SmoothState A) (T : SmoothState N) (hTime : N.T = A.T)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNext : Space) (hmNext : ‖mNext‖ = 1) (JNext : V ≃ₗᵢ[ℝ] referencePlane mNext)
  (supportNext : Set Space) (hSupportNext : IsCompact supportNext)


-- @@ L43-43 verbatim
local notation "D" => A.transverseData m hm J support hSupport

-- @@ L44-44 verbatim
local notation "DNext" => N.transverseData mNext hmNext JNext supportNext hSupportNext


-- @@ L46-46 verbatim
section Forward


-- @@ L48-49 verbatim
variable {P : ParentFrame (A.transverseData m hm J support hSupport) 0} (G : ForwardGuards P)
    (hball : (1 / 2 : ℝ) ≤ G.radius)


-- @@ L51-51 verbatim
local notation "Geo" => ForwardGuards.lowGeometry G hball

-- @@ L52-52 verbatim
local notation "tNext" => PhysicalGeometryData.targetTime (ForwardGuards.lowGeometry G hball)


-- @@ L54-67 verbatim
variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0 -
      (G.primaryAmplitude hball * deriv (profile G.δ)
        (k * ⟪m, S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
          (A.transverseData m hm J support hSupport) G.initialCoordinate t
              (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t
              (S.evolution.inverse.normalized t 0))‖ ≤ error)


-- @@ L69-76 verbatim
/-- The next actual frame, using exactly the forward source primary and
its target-normalized amplitude. -/
def forwardTargetRenewal : ParentFrame DNext tNext :=
  S.forwardRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext ((G.lowGeometry hball).target_time_mem).1 CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    G.initialCoordinate G.initialCoordinate_ne_zero hsource


-- @@ L78-80 verbatim
local notation "Q" => forwardTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource


-- @@ L82-94 verbatim
/-- In particular, the new ray and primary are the old source's actual
physical ray and primary at the target, not freely chosen frame vectors. -/
theorem forwardTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T := ⟨tNext,(G.lowGeometry hball).target_time_mem⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl


-- @@ L96-99 verbatim
theorem forwardTargetRenewal_shear : (Q).shear=G.hchild :=
  (forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource).shear_eq hδ


-- @@ L101-101 verbatim
theorem forwardTargetRenewal_constants : (Q).G=K ∧ (Q).error=error := ⟨rfl,rfl⟩


-- @@ L103-111 verbatim
include hTime hCM hK he hMK hHK hM hH hδ hsource in
theorem forwardTargetRenewal_remainder (hT : tNext ≤ N.T) :
    ‖(DNext).M.field ((DNext).clamp tNext) 0-(Geo).M (Geo).center tNext -
      G.hchild • rankOne ℝ (unit ((Geo).w (Geo).center tNext))
        (unit ((Geo).r (Geo).center tNext))‖ ≤ error := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.target_remainder hδ hT


-- @@ L113-123 verbatim
theorem forwardTargetRenewal_parameters (hTilt : (Geo).tiltError ≤ 1 / 2) :
    (Q).shear=G.hchild ∧ 0 < (Q).a ∧
    |(Q).a/P.a-1| ≤ (Geo).couplingError ∧
    0 < (Q).sigma ∧
    |(G.y⁻¹)^2*(Q).sigma^2-1| ≤ (Geo).tiltError ∧
    1/2 ≤ (G.y⁻¹)^2*(Q).sigma^2 ∧ (G.y⁻¹)^2*(Q).sigma^2 ≤ 3/2 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact ⟨H.shear_eq hδ,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,
    H.tilt_error hTilt,H.tilt_interval hTilt⟩


-- @@ L125-133 verbatim
theorem forwardTargetRenewal_compression
    (ht : 0 < tNext) (hT : tNext < N.T)
    (hmargin : 3 * ((Geo).G + (Geo).d) + error < (Geo).compressionScale) :
    ⟪(DNext).M.field ⟨tNext,ht.le,hT.le⟩ 0 (unit ((Q).m tNext)),
      unit ((Q).m tNext)⟫_ℝ < 0 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.activation_compression ht hT hmargin


-- @@ L135-142 verbatim
theorem forwardTargetRenewal_compression_of_error_le_one
    (hT : tNext < N.T) (herror : error ≤ 1) :
    ⟪(DNext).M.field ⟨tNext,(Geo).targetTime_pos le_rfl |>.le,hT.le⟩ 0
      (unit ((Q).m tNext)),unit ((Q).m tNext)⟫_ℝ < 0 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.activation_compression_of_error_le_one ((Geo).targetTime_pos le_rfl) hT herror


-- @@ L144-144 verbatim
end Forward


-- @@ L146-146 verbatim
section Joined


-- @@ L148-152 verbatim
variable (s : ℝ) (hs : 0 < s) (hsT : s < A.T)
  (H : HistoryData ((A.transverseData m hm J support hSupport).initial s hs hsT.le))
  {P : ParentFrame (A.transverseData m hm J support hSupport) s}
  (G : Guards hs hsT P H) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hcut : tsupport innerCutoff ⊆ support)


-- @@ L154-154 verbatim
local notation "Geo" => Guards.lowGeometry G hball

-- @@ L155-155 verbatim
local notation "tNext" => PhysicalGeometryData.targetTime (Guards.lowGeometry G hball)


-- @@ L157-169 verbatim
variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0 -
      (G.primaryAmplitude hball * deriv (profile G.δ)
        (k * ⟪m, S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity
          s hs hsT H G.terminal hcut t (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t
              (S.evolution.inverse.normalized t 0))‖ ≤ error)


-- @@ L171-178 verbatim
/-- The joined renewal retains the activation-selected endpoint and
its actual stationary-history initial trace. -/
def joinedTargetRenewal : ParentFrame DNext tNext :=
  S.joinedRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext (hs.le.trans ((G.lowGeometry hball).target_time_mem).1) CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    s hs hsT H G.terminal G.terminal_properties.1 hcut hsource


-- @@ L180-182 verbatim
local notation "Q" => joinedTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource


-- @@ L184-196 verbatim
theorem joinedTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T :=
    ⟨tNext,hs.le.trans ((G.lowGeometry hball).target_time_mem).1,
      ((G.lowGeometry hball).target_time_mem).2⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl


-- @@ L198-201 verbatim
theorem joinedTargetRenewal_shear : (Q).shear=G.hchild :=
  (joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource).shear_eq hδ


-- @@ L203-203 verbatim
theorem joinedTargetRenewal_constants : (Q).G=K ∧ (Q).error=error := ⟨rfl,rfl⟩


-- @@ L205-213 verbatim
include hTime hCM hK he hMK hHK hM hH hδ hsource in
theorem joinedTargetRenewal_remainder (hT : tNext ≤ N.T) :
    ‖(DNext).M.field ((DNext).clamp tNext) 0-(Geo).M (Geo).center tNext -
      G.hchild • rankOne ℝ (unit ((Geo).w (Geo).center tNext))
        (unit ((Geo).r (Geo).center tNext))‖ ≤ error := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.target_remainder hδ hT


-- @@ L215-225 verbatim
theorem joinedTargetRenewal_parameters (hTilt : (Geo).tiltError ≤ 1 / 2) :
    (Q).shear=G.hchild ∧ 0 < (Q).a ∧
    |(Q).a/P.a-1| ≤ (Geo).couplingError ∧
    0 < (Q).sigma ∧
    |(G.y⁻¹)^2*(Q).sigma^2-1| ≤ (Geo).tiltError ∧
    1/2 ≤ (G.y⁻¹)^2*(Q).sigma^2 ∧ (G.y⁻¹)^2*(Q).sigma^2 ≤ 3/2 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact ⟨E.shear_eq hδ,E.coupling_pos,E.coupling_error,E.sigma_pos hTilt,
    E.tilt_error hTilt,E.tilt_interval hTilt⟩


-- @@ L227-235 verbatim
theorem joinedTargetRenewal_compression
    (ht : 0 < tNext) (hT : tNext < N.T)
    (hmargin : 3 * ((Geo).G + (Geo).d) + error < (Geo).compressionScale) :
    ⟪(DNext).M.field ⟨tNext,ht.le,hT.le⟩ 0 (unit ((Q).m tNext)),
      unit ((Q).m tNext)⟫_ℝ < 0 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.activation_compression ht hT hmargin


-- @@ L237-244 verbatim
theorem joinedTargetRenewal_compression_of_error_le_one
    (hT : tNext < N.T) (herror : error ≤ 1) :
    ⟪(DNext).M.field ⟨tNext,(Geo).targetTime_pos hs.le |>.le,hT.le⟩ 0
      (unit ((Q).m tNext)),unit ((Q).m tNext)⟫_ℝ < 0 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.activation_compression_of_error_le_one ((Geo).targetTime_pos hs.le) hT herror


-- @@ L246-246 verbatim
end Joined

-- @@ L247-247 verbatim
end EulerParentPacketFrames.SmoothState


-- @@ L249-249 verbatim
end

-- @@ L250-250 verbatim
end


-- @@ L252-252 verbatim
end


-- @@ L254-254 verbatim
@[expose] public section


-- @@ L256-256 verbatim
noncomputable section


-- @@ L258-258 verbatim
namespace EulerParentPacketFrames.Evolution


-- @@ L260-260 verbatim
open Set EulerSmoothLimit EulerVolterraConvolution


-- @@ L262-262 verbatim
variable {A : Parent} (E : Evolution A)


-- @@ L264-269 verbatim
theorem centerStrain_bound (CM : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (t : ℝ) : ‖A.centerStrain t‖ ≤ CM := by
  change ‖A.strain.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CM
  rw [E.strain_eq]
  exact hCM _ _


-- @@ L271-276 verbatim
theorem centerCurvature_bound (CH : ℝ)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (t : ℝ) : ‖A.centerCurvature t‖ ≤ CH := by
  change ‖A.curvature.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CH
  rw [E.curvature_eq]
  exact hCH _ _


-- @@ L278-278 verbatim
end EulerParentPacketFrames.Evolution


-- @@ L280-280 verbatim
namespace EulerParentPacketFrames.GeometryForwardChoice


-- @@ L282-284 verbatim
open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary


-- @@ L286-297 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖ = 1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)


-- @@ L299-308 verbatim
/-- Renewal, constructed using `S.forwardTargetRenewal`. -/
def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.forwardTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.geometry I.halfBall CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)


-- @@ L310-310 verbatim
local notation "Pnew" => F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport


-- @@ L312-314 verbatim
theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall) Pnew := by
  unfold renewal
  apply SmoothState.forwardTargetRenewal_matches


-- @@ L316-316 verbatim
theorem renewal_costs : (Pnew).G=K ∧ (Pnew).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩


-- @@ L318-325 verbatim
theorem renewal_parameters (hTilt : (I.geometry.lowGeometry I.halfBall).tiltError ≤ 1 / 2) :
    (Pnew).shear=I.geometry.hchild ∧ 0 < (Pnew).a ∧
    |(Pnew).a/I.frame.a-1| ≤ (I.geometry.lowGeometry I.halfBall).couplingError ∧
    0 < (Pnew).sigma ∧
    |(I.geometry.y⁻¹)^2*(Pnew).sigma^2-1| ≤ (I.geometry.lowGeometry I.halfBall).tiltError := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  exact ⟨H.shear_eq I.delta_pos,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,H.tilt_error
      hTilt⟩


-- @@ L327-335 verbatim
theorem renewal_compression (e : ℝ) (he : e ≤ 1) :
    ⟪(Pnew).B (I.geometry.lowGeometry I.halfBall).targetTime
      (unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)),
      unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)⟫_ℝ+e < 0 := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  rw [H.background_compression_eq]
  have hm := (I.geometry.lowGeometry I.halfBall).compression_margin he
  have hc := (I.geometry.lowGeometry I.halfBall).nextCompression_le
  linarith only [hm,hc]


-- @@ L337-337 verbatim
end EulerParentPacketFrames.GeometryForwardChoice


-- @@ L339-339 verbatim
namespace EulerParentPacketFrames.GeometryJoinedChoice


-- @@ L341-343 verbatim
open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary


-- @@ L345-356 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖ = 1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)


-- @@ L358-368 verbatim
/-- Renewal, constructed using `S.joinedTargetRenewal`. -/
def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.joinedTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.historyTime I.history_pos I.history_lt I.history I.geometry I.halfBall
    I.cutoff_support CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)


-- @@ L370-370 verbatim
local notation "Pnew" => F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport


-- @@ L372-374 verbatim
theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall) Pnew := by
  unfold renewal
  apply SmoothState.joinedTargetRenewal_matches


-- @@ L376-376 verbatim
theorem renewal_costs : (Pnew).G=K ∧ (Pnew).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩


-- @@ L378-385 verbatim
theorem renewal_parameters (hTilt : (I.geometry.lowGeometry I.halfBall).tiltError ≤ 1 / 2) :
    (Pnew).shear=I.geometry.hchild ∧ 0 < (Pnew).a ∧
    |(Pnew).a/I.frame.a-1| ≤ (I.geometry.lowGeometry I.halfBall).couplingError ∧
    0 < (Pnew).sigma ∧
    |(I.geometry.y⁻¹)^2*(Pnew).sigma^2-1| ≤ (I.geometry.lowGeometry I.halfBall).tiltError := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  exact ⟨H.shear_eq I.delta_pos,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,H.tilt_error
      hTilt⟩


-- @@ L387-395 verbatim
theorem renewal_compression (e : ℝ) (he : e ≤ 1) :
    ⟪(Pnew).B (I.geometry.lowGeometry I.halfBall).targetTime
      (unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)),
      unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)⟫_ℝ+e < 0 := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  rw [H.background_compression_eq]
  have hm := (I.geometry.lowGeometry I.halfBall).compression_margin he
  have hc := (I.geometry.lowGeometry I.halfBall).nextCompression_le
  linarith only [hm,hc]


-- @@ L397-397 verbatim
end EulerParentPacketFrames.GeometryJoinedChoice
