import Mathlib
import Submission.OrbitUnknottingSmoothGlobalTube
import Submission.OrbitUnknottingSmoothCutoff
import Submission.SmallAmbientDisplacementIsotopy


-- @@ L6-19 verbatim
/-!
# Extending a periodic orbit displacement to an ambient field

A smooth period-one displacement along the zero section of a chosen orbit
tube is extended linearly in the displacement value.  A radial
`ContDiffBump` supplies an outer collar inside the globally injective tube,
while `SmoothCutoffData` makes the field vanish on neighborhoods of all other
source and target components.

The quotient phase is evaluated by `Function.Periodic.lift`.  Smoothness in
the interior is proved in a real-phase inverse-function chart supplied by
`OrbitTubeGlobalSmoothInverse.local_smooth_lift`; smoothness across the tube
boundary follows from the radial outer collar.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 500000


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open Set Function Metric Filter

-- @@ L27-27 verbatim
open scoped Topology ContDiff NNReal RealInnerProductSpace


-- @@ L29-29 verbatim
namespace Submission

-- @@ L30-30 verbatim
namespace TamedField


-- @@ L32-32 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L34-34 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L35-35 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)

-- @@ L36-36 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L38-49 verbatim
/-- Complete input contract for extending one periodic displacement.  The
strict radial inequality is the only collar condition needed by the global
smooth extension. -/
structure PeriodicDisplacementExtensionData
    (h2 : 2 ≤ n) (O : V.OrbitIndex) where
  displacement : ℝ → E
  displacement_smooth : ContDiff ℝ ∞ displacement
  displacement_periodic : Function.Periodic displacement 1
  radialBump : ContDiffBump (0 : N)
  radialBump_rOut_lt :
    radialBump.rOut < (V.globalSmoothOrbitTube O).radius
  cutoffData : OrbitUnknottingSupport.SmoothCutoffData V h2 O


-- @@ L51-51 verbatim
variable {V} {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L53-53 verbatim
namespace PeriodicDisplacementExtensionData


-- @@ L55-55 verbatim
variable (D : PeriodicDisplacementExtensionData V h2 O)


-- @@ L57-57 verbatim
/-! ## Quotient tube and the extension -/


-- @@ L59-62 verbatim
/-- The displacement descended from its period-one real lift to the phase
circle. -/
def quotientDisplacement (a : C) : E :=
  D.displacement_periodic.lift a


-- @@ L64-66 verbatim
@[simp] theorem quotientDisplacement_coe (u : ℝ) :
    D.quotientDisplacement (u : C) = D.displacement u :=
  rfl


-- @@ L68-71 verbatim
/-- The open quotient tube on which the global inverse is valid. -/
def tubeDomain (D : PeriodicDisplacementExtensionData V h2 O) : Set (C × N) :=
  (Set.univ : Set C) ×ˢ
    Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius


-- @@ L73-75 verbatim
/-- Ambient image of the chosen open quotient tube. -/
def tubeImage : Set E :=
  V.orbitTube O '' D.tubeDomain


-- @@ L77-81 verbatim
/-- Closed radial core containing the support of the extended field. -/
def supportCore : Set E :=
  V.orbitTube O ''
    ((Set.univ : Set C) ×ˢ
      Metric.closedBall (0 : N) D.radialBump.rOut)


-- @@ L83-88 verbatim
theorem isCompact_supportCore : IsCompact D.supportCore := by
  have hcompact : IsCompact
      ((Set.univ : Set C) ×ˢ
        Metric.closedBall (0 : N) D.radialBump.rOut) :=
    isCompact_univ.prod (isCompact_closedBall (0 : N) D.radialBump.rOut)
  exact hcompact.image (V.continuous_orbitTube O)


-- @@ L90-91 verbatim
theorem isClosed_supportCore : IsClosed D.supportCore :=
  D.isCompact_supportCore.isClosed


-- @@ L93-103 verbatim
/-- The compactly supported ambient displacement field.  Inside the tube it
is the periodic phase displacement multiplied by the radial bump and the
ambient obstacle cutoff; outside the tube it is zero. -/
def ambientField (x : E) : E := by
  classical
  exact if x ∈ D.tubeImage then
    D.cutoffData.cutoff x •
      (D.radialBump ((V.globalSmoothOrbitTube O).inverse x).2 •
        D.quotientDisplacement
          ((V.globalSmoothOrbitTube O).inverse x).1)
  else 0


-- @@ L105-109 verbatim
/-- On the tube image the chosen global inverse is also a right inverse. -/
theorem orbitTube_inverse_right {x : E} (hx : x ∈ D.tubeImage) :
    V.orbitTube O ((V.globalSmoothOrbitTube O).inverse x) = x := by
  rcases hx with ⟨q, hq, rfl⟩
  rw [(V.globalSmoothOrbitTube O).inverse_left q hq]


-- @@ L111-115 verbatim
theorem inverse_mem_tubeDomain {x : E} (hx : x ∈ D.tubeImage) :
    (V.globalSmoothOrbitTube O).inverse x ∈ D.tubeDomain := by
  rcases hx with ⟨q, hq, rfl⟩
  rw [(V.globalSmoothOrbitTube O).inverse_left q hq]
  exact hq


-- @@ L117-123 verbatim
/-- Coordinate formula for the ambient field on the quotient tube. -/
theorem ambientField_orbitTube (q : C × N) (hq : q ∈ D.tubeDomain) :
    D.ambientField (V.orbitTube O q) =
      D.cutoffData.cutoff (V.orbitTube O q) •
        (D.radialBump q.2 • D.quotientDisplacement q.1) := by
  rw [ambientField, if_pos ⟨q, hq, rfl⟩,
    (V.globalSmoothOrbitTube O).inverse_left q hq]


-- @@ L125-135 verbatim
/-- Real-phase version of the coordinate formula. -/
theorem ambientField_orbitTubeLift (u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    D.ambientField (V.orbitTubeLift O (u, z)) =
      D.cutoffData.cutoff (V.orbitTubeLift O (u, z)) •
        (D.radialBump z • D.displacement u) := by
  rw [← V.orbitTube_coe O u z,
    D.ambientField_orbitTube ((u : C), z)
      ⟨Set.mem_univ _, hz⟩,
    D.quotientDisplacement_coe]


-- @@ L137-142 verbatim
theorem orbitTubeLift_zero_mem_source
    (D : PeriodicDisplacementExtensionData V h2 O) (u : ℝ) :
    V.orbitTubeLift O (u, (0 : N)) ∈ (O : Set E) := by
  rw [V.orbitTubeLift_zero, intrinsicOrbitLift,
    V.orbitPoint_orbit O]
  exact V.flow_mem_orbit (V.orbitPoint O) (u * V.orbitPeriod O)


-- @@ L144-158 verbatim
/-- The extension agrees exactly with the prescribed displacement on the
source orbit zero section. -/
theorem ambientField_orbit_zero (u : ℝ) :
    D.ambientField (V.orbitTubeLift O (u, (0 : N))) =
      D.displacement u := by
  have hz : (0 : N) ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius :=
    Metric.mem_ball_self (V.globalSmoothOrbitTube O).radius_pos
  rw [D.ambientField_orbitTubeLift u 0 hz,
    OrbitUnknottingSupport.SmoothCutoffData.cutoff_eq_one_on_source
      (V := V) D.cutoffData (D.orbitTubeLift_zero_mem_source u)]
  have hb : D.radialBump (0 : N) = 1 := by
    apply D.radialBump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall] using D.radialBump.rIn_pos.le
  simp [hb]


-- @@ L160-160 verbatim
/-! ## Support and obstacle vanishing -/


-- @@ L162-164 verbatim
theorem ambientField_eq_zero_of_not_mem_tubeImage {x : E}
    (hx : x ∉ D.tubeImage) : D.ambientField x = 0 := by
  simp [ambientField, hx]


-- @@ L166-185 verbatim
/-- The field is zero outside the closed radial support core, including the
whole outer collar between `radialBump.rOut` and the tube radius. -/
theorem ambientField_eq_zero_of_not_mem_supportCore {x : E}
    (hx : x ∉ D.supportCore) : D.ambientField x = 0 := by
  by_cases ht : x ∈ D.tubeImage
  · let q : C × N := (V.globalSmoothOrbitTube O).inverse x
    have hq : q ∈ D.tubeDomain := D.inverse_mem_tubeDomain ht
    have houter : D.radialBump.rOut ≤ ‖q.2‖ := by
      by_contra hnot
      have hle : ‖q.2‖ ≤ D.radialBump.rOut :=
        (lt_of_not_ge hnot).le
      apply hx
      refine ⟨q, ⟨Set.mem_univ _, ?_⟩, D.orbitTube_inverse_right ht⟩
      simpa [Metric.mem_closedBall, dist_zero_left] using hle
    have hb : D.radialBump q.2 = 0 :=
      D.radialBump.zero_of_le_dist (by
        simpa [dist_zero_right] using houter)
    rw [ambientField, if_pos ht]
    simp [q, hb]
  · exact D.ambientField_eq_zero_of_not_mem_tubeImage ht


-- @@ L187-190 verbatim
/-- The extended field has compact support. -/
theorem hasCompactSupport_ambientField : HasCompactSupport D.ambientField := by
  exact HasCompactSupport.intro D.isCompact_supportCore
    (fun x hx => D.ambientField_eq_zero_of_not_mem_supportCore hx)


-- @@ L192-202 verbatim
/-- At every point of the complete other-component obstacle set, the field
is identically zero on a whole ambient neighborhood. -/
theorem ambientField_eventuallyEq_zero_of_mem_obstacle
    {x : E} (hx : x ∈ OrbitUnknottingSupport.obstacleSet V h2 O) :
    D.ambientField =ᶠ[nhds x] 0 := by
  have hcutoff :=
    OrbitUnknottingSupport.SmoothCutoffData.eventuallyEq_zero_of_mem_obstacle
      (V := V) D.cutoffData hx
  filter_upwards [hcutoff] with y hy
  by_cases ht : y ∈ D.tubeImage <;>
    simp [ambientField, ht, hy]


-- @@ L204-207 verbatim
theorem ambientField_eq_zero_of_mem_obstacle
    {x : E} (hx : x ∈ OrbitUnknottingSupport.obstacleSet V h2 O) :
    D.ambientField x = 0 :=
  (D.ambientField_eventuallyEq_zero_of_mem_obstacle hx).self_of_nhds


-- @@ L209-215 verbatim
theorem ambientField_eventuallyEq_zero_on_other_source
    (P : V.OrbitIndex) (hPO : P ≠ O)
    {x : E} (hx : x ∈ (P : Set E)) :
    D.ambientField =ᶠ[nhds x] 0 :=
  D.ambientField_eventuallyEq_zero_of_mem_obstacle
    (OrbitUnknottingSupport.source_subset_obstacleSet
      V h2 O P hPO hx)


-- @@ L217-223 verbatim
theorem ambientField_eventuallyEq_zero_on_other_target
    (P : V.OrbitIndex) (hPO : P ≠ O)
    {x : E} (hx : x ∈ CanonicalRoundOrbit.target V h2 P) :
    D.ambientField =ᶠ[nhds x] 0 :=
  D.ambientField_eventuallyEq_zero_of_mem_obstacle
    (OrbitUnknottingSupport.target_subset_obstacleSet
      V h2 O P hPO hx)


-- @@ L225-225 verbatim
/-! ## Smoothness -/


-- @@ L227-313 verbatim
/-- In the interior tube, the ambient field is locally its ordinary
real-phase formula in a smooth inverse-function chart. -/
theorem contDiffAt_ambientField_orbitTubeLift (u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    ContDiffAt ℝ ∞ D.ambientField (V.orbitTubeLift O (u, z)) := by
  obtain ⟨e, g₀, hf, hg₀, hg₀deriv, hg₀center, hg₀local⟩ :=
    (V.globalSmoothOrbitTube O).local_smooth_lift u z hz
  let chart : OpenPartialHomeomorph (ℝ × N) E :=
    (V.contDiff_orbitTubeLift O).contDiffAt.toOpenPartialHomeomorph
      (V.orbitTubeLift O) hf (by simp)
  let g : E → ℝ × N := chart.symm
  have hsource : (u, z) ∈ chart.source := by
    exact (V.contDiff_orbitTubeLift O).contDiffAt
      |>.mem_toOpenPartialHomeomorph_source hf (by simp)
  have htarget : V.orbitTubeLift O (u, z) ∈ chart.target :=
    chart.map_source hsource
  have hgcenter : g (V.orbitTubeLift O (u, z)) = (u, z) := by
    change chart.symm (V.orbitTubeLift O (u, z)) = (u, z)
    rw [← show (chart : (ℝ × N) → E) = V.orbitTubeLift O by rfl]
    exact chart.left_inv hsource
  have hforwardDeriv : HasFDerivAt chart
      (e : (ℝ × N) →L[ℝ] E)
      (chart.symm (V.orbitTubeLift O (u, z))) := by
    rw [show chart.symm (V.orbitTubeLift O (u, z)) = (u, z) by
      exact hgcenter]
    exact hf
  have hforwardSmooth : ContDiffAt ℝ ∞ chart
      (chart.symm (V.orbitTubeLift O (u, z))) := by
    rw [show chart.symm (V.orbitTubeLift O (u, z)) = (u, z) by
      exact hgcenter]
    exact (V.contDiff_orbitTubeLift O).contDiffAt
  have hgsmooth : ContDiffAt ℝ ∞ g
      (V.orbitTubeLift O (u, z)) :=
    chart.contDiffAt_symm htarget hforwardDeriv hforwardSmooth
  have hgball : ∀ᶠ y in nhds (V.orbitTubeLift O (u, z)),
      (g y).2 ∈ Metric.ball (0 : N)
        (V.globalSmoothOrbitTube O).radius := by
    have hg2continuous : ContinuousAt (fun y : E => (g y).2)
        (V.orbitTubeLift O (u, z)) :=
      continuous_snd.continuousAt.comp' hgsmooth.continuousAt
    have hzcenter : (g (V.orbitTubeLift O (u, z))).2 ∈
        Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius := by
      rw [hgcenter]
      exact hz
    exact hg2continuous.eventually
      (Metric.isOpen_ball.mem_nhds hzcenter)
  have hright : ∀ᶠ y in nhds (V.orbitTubeLift O (u, z)),
      V.orbitTubeLift O (g y) = y := by
    filter_upwards [chart.eventually_right_inverse htarget] with y hy
    exact hy
  have hlocal : ∀ᶠ y in nhds (V.orbitTubeLift O (u, z)),
      D.ambientField y =
        D.cutoffData.cutoff y •
          (D.radialBump (g y).2 • D.displacement (g y).1) := by
    filter_upwards [hright, hgball] with y hy hgy
    let q : C × N := (((g y).1 : C), (g y).2)
    have hq : q ∈ D.tubeDomain := ⟨Set.mem_univ _, hgy⟩
    have hyq : V.orbitTube O q = y := by
      rw [V.orbitTube_coe O (g y).1 (g y).2]
      exact hy
    have hytube : y ∈ D.tubeImage := ⟨q, hq, hyq⟩
    have hinv : (V.globalSmoothOrbitTube O).inverse y = q := by
      rw [← hyq]
      exact (V.globalSmoothOrbitTube O).inverse_left q hq
    rw [ambientField, if_pos hytube, hinv,
      D.quotientDisplacement_coe]
  have hg1 : ContDiffAt ℝ ∞ (fun y : E => (g y).1)
      (V.orbitTubeLift O (u, z)) :=
    contDiffAt_fst.comp _ hgsmooth
  have hg2 : ContDiffAt ℝ ∞ (fun y : E => (g y).2)
      (V.orbitTubeLift O (u, z)) :=
    contDiffAt_snd.comp _ hgsmooth
  have hb : ContDiffAt ℝ ∞
      (fun y : E => D.radialBump (g y).2)
      (V.orbitTubeLift O (u, z)) :=
    D.radialBump.contDiffAt.comp _ hg2
  have hd : ContDiffAt ℝ ∞
      (fun y : E => D.displacement (g y).1)
      (V.orbitTubeLift O (u, z)) :=
    D.displacement_smooth.contDiffAt.comp _ hg1
  have hsmooth : ContDiffAt ℝ ∞
      (fun y : E => D.cutoffData.cutoff y •
        (D.radialBump (g y).2 • D.displacement (g y).1))
      (V.orbitTubeLift O (u, z)) :=
    D.cutoffData.contDiff_cutoff.contDiffAt.smul (hb.smul hd)
  exact hsmooth.congr_of_eventuallyEq hlocal


-- @@ L315-337 verbatim
/-- The radial outer collar glues the interior formula to zero smoothly on
the whole ambient Euclidean space. -/
theorem contDiff_ambientField : ContDiff ℝ ∞ D.ambientField := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ D.supportCore
  · rcases hx with ⟨⟨a, z⟩, hzcore, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hzle : ‖z‖ ≤ D.radialBump.rOut := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hzcore.2
    have hz : z ∈ Metric.ball (0 : N)
        (V.globalSmoothOrbitTube O).radius := by
      simpa [Metric.mem_ball, dist_zero_left] using
        (lt_of_le_of_lt hzle D.radialBump_rOut_lt)
    simpa only [V.orbitTube_coe] using
      D.contDiffAt_ambientField_orbitTubeLift u z hz
  · have hxcompl : x ∈ D.supportCoreᶜ := hx
    have hnear : D.supportCoreᶜ ∈ nhds x :=
      D.isClosed_supportCore.isOpen_compl.mem_nhds hxcompl
    apply (show ContDiffAt ℝ ∞ (fun _ : E => (0 : E)) x from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    exact D.ambientField_eq_zero_of_not_mem_supportCore hy


-- @@ L339-339 verbatim
/-! ## Global Lipschitz control and small ambient moves -/


-- @@ L341-346 verbatim
/-- Smoothness plus compact support supplies a finite global Lipschitz
constant. -/
theorem exists_lipschitzWith_ambientField :
    ∃ K : ℝ≥0, LipschitzWith K D.ambientField := by
  exact D.contDiff_ambientField.lipschitzWith_of_hasCompactSupport
    D.hasCompactSupport_ambientField (by simp)


-- @@ L348-357 verbatim
/-- If a Lipschitz constant below one is available, the field feeds directly
into the global small-displacement isotopy primitive. -/
def toSmallAmbientDisplacement (K : ℝ≥0) (hK : K < 1)
    (hLip : LipschitzWith K D.ambientField) :
    SmallAmbientDisplacement n where
  field := D.ambientField
  smooth := D.contDiff_ambientField
  K := K
  K_lt_one := hK
  lipschitz := hLip


-- @@ L359-371 verbatim
/-- Endpoint action of the unscaled small-displacement isotopy on the source
orbit. -/
theorem toSmallAmbientDisplacement_forward_orbit_zero
    (K : ℝ≥0) (hK : K < 1)
    (hLip : LipschitzWith K D.ambientField) (u : ℝ) :
    (D.toSmallAmbientDisplacement K hK hLip).toSmoothAmbientIsotopy.forward 1
        (V.orbitTubeLift O (u, (0 : N))) =
      V.orbitTubeLift O (u, (0 : N)) + D.displacement u := by
  rw [SmallAmbientDisplacement.toSmoothAmbientIsotopy_forward_one
      (D.toSmallAmbientDisplacement K hK hLip)]
  change V.orbitTubeLift O (u, (0 : N)) +
      D.ambientField (V.orbitTubeLift O (u, (0 : N))) = _
  rw [D.ambientField_orbit_zero]


-- @@ L373-383 verbatim
/-- The unscaled small-displacement isotopy is relative to every other
source and target component. -/
theorem toSmallAmbientDisplacement_fixedOn_obstacle
    (K : ℝ≥0) (hK : K < 1)
    (hLip : LipschitzWith K D.ambientField) :
    (D.toSmallAmbientDisplacement K hK hLip).toSmoothAmbientIsotopy.FixedOn
      (OrbitUnknottingSupport.obstacleSet V h2 O) := by
  apply SmallAmbientDisplacement.fixedOn_of_field_eq_zero
  intro x hx
  change D.ambientField x = 0
  exact D.ambientField_eq_zero_of_mem_obstacle hx


-- @@ L385-396 verbatim
/-- Scaling the extension gives a small displacement whenever the scaled
Lipschitz constant is below one. -/
def toScaledSmallAmbientDisplacement (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) : SmallAmbientDisplacement n where
  field := fun x => r • D.ambientField x
  smooth := D.contDiff_ambientField.const_smul r
  K := ‖r‖₊ * K
  K_lt_one := hsmall
  lipschitz := by
    simpa [Function.comp_def] using
      (lipschitzWith_smul r).comp hLip


-- @@ L398-411 verbatim
/-- Endpoint action of the scaled construction. -/
theorem toScaledSmallAmbientDisplacement_forward_orbit_zero
    (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) (u : ℝ) :
    (SmallAmbientDisplacement.toSmoothAmbientIsotopy
      (D.toScaledSmallAmbientDisplacement r K hLip hsmall)).forward 1
          (V.orbitTubeLift O (u, (0 : N))) =
      V.orbitTubeLift O (u, (0 : N)) + r • D.displacement u := by
  rw [SmallAmbientDisplacement.toSmoothAmbientIsotopy_forward_one
      (D.toScaledSmallAmbientDisplacement r K hLip hsmall)]
  change V.orbitTubeLift O (u, (0 : N)) +
      r • D.ambientField (V.orbitTubeLift O (u, (0 : N))) = _
  rw [D.ambientField_orbit_zero]


-- @@ L413-430 verbatim
/-- Without supplying a numerical Lipschitz bound, compact support and
smoothness still produce a positive uniform scale in the small regime,
together with the expected scaled endpoint on the source orbit. -/
theorem exists_scaledSmallAmbientDisplacement :
    ∃ ε : ℝ, ε > 0 ∧ ∃ S : SmallAmbientDisplacement n,
      S.field = (fun x => ε • D.ambientField x) ∧
      ∀ u : ℝ,
        S.toSmoothAmbientIsotopy.forward 1
            (V.orbitTubeLift O (u, (0 : N))) =
          V.orbitTubeLift O (u, (0 : N)) + ε • D.displacement u := by
  obtain ⟨ε, hε, S, hS⟩ := SmallAmbientDisplacement.exists_scaled
    D.ambientField D.contDiff_ambientField D.hasCompactSupport_ambientField
  refine ⟨ε, hε, S, hS, ?_⟩
  intro u
  rw [S.toSmoothAmbientIsotopy_forward_one, hS]
  change V.orbitTubeLift O (u, (0 : N)) +
      ε • D.ambientField (V.orbitTubeLift O (u, (0 : N))) = _
  rw [D.ambientField_orbit_zero]


-- @@ L432-432 verbatim
/-! ## Canonical radial and obstacle-localization choices -/


-- @@ L434-442 verbatim
/-- A canonical radial bump strictly inside the chosen global tube. -/
def canonicalRadialBump (V : TamedField X) (O : V.OrbitIndex) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) where
  rIn := (V.globalSmoothOrbitTube O).radius / 3
  rOut := (V.globalSmoothOrbitTube O).radius / 2
  rIn_pos := by
    linarith [(V.globalSmoothOrbitTube O).radius_pos]
  rIn_lt_rOut := by
    linarith [(V.globalSmoothOrbitTube O).radius_pos]


-- @@ L444-449 verbatim
theorem canonicalRadialBump_rOut_lt_tube
    (V : TamedField X) (O : V.OrbitIndex) :
    (canonicalRadialBump V O).rOut <
      (V.globalSmoothOrbitTube O).radius := by
  dsimp [canonicalRadialBump]
  linarith [(V.globalSmoothOrbitTube O).radius_pos]


-- @@ L451-463 verbatim
/-- Consequently, every smooth period-one displacement has extension data;
no additional localizer-existence assumption is required. -/
def canonical (V : TamedField X) (h2 : 2 ≤ n) (O : V.OrbitIndex)
    (d : ℝ → EuclideanSpace ℝ (Fin (n + 1)))
    (hd : ContDiff ℝ ∞ d) (hp : Function.Periodic d 1) :
    PeriodicDisplacementExtensionData V h2 O where
  displacement := d
  displacement_smooth := hd
  displacement_periodic := hp
  radialBump := canonicalRadialBump V O
  radialBump_rOut_lt := canonicalRadialBump_rOut_lt_tube V O
  cutoffData := Classical.choice
    (OrbitUnknottingSupport.exists_smoothCutoffData V h2 O)


-- @@ L465-465 verbatim
end PeriodicDisplacementExtensionData

-- @@ L466-466 verbatim
end TamedField

-- @@ L467-467 verbatim
end Submission
