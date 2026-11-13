import Mathlib
import Submission.AmbientIsotopyCobordism
import Submission.OrbitUnknottingSmoothGlobalTube


-- @@ L5-18 verbatim
/-!
# Conjugating compactly supported tube-coordinate isotopies

This file is the ambient-extension primitive for the orbit normalization
pipeline.  A period-one coordinate isotopy is supplied both on the real lift
`ℝ × ℝⁿ` and on `AddCircle 1 × ℝⁿ`, with the expected compatibility.
If it preserves the chosen tube and is the identity on an outer radial
collar, conjugation by `globalSmoothOrbitTube` extends it by the identity to a
genuine `SmoothAmbientIsotopy` of Euclidean space.

The collar hypothesis is what makes the piecewise extension smooth across
the boundary of the tube image.  Inside the support core, smoothness follows
from a local inverse-function-theorem lift of the global tube inverse.
-/


-- @@ L20-20 verbatim
set_option autoImplicit false

-- @@ L21-21 verbatim
set_option maxHeartbeats 1200000


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function Metric

-- @@ L26-26 verbatim
open scoped Topology ContDiff


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace TamedField


-- @@ L31-31 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L33-33 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L34-34 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)

-- @@ L35-35 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L37-72 verbatim
/-- A smooth period-one isotopy in orbit-tube coordinates.  The quotient maps
are recorded explicitly; the two compatibility fields say that they are
exactly the descents of the real-phase lifts. -/
structure PeriodicTubeCoordinateIsotopy (O : V.OrbitIndex) where
  supportRadius : ℝ
  supportRadius_lt :
    supportRadius < (V.globalSmoothOrbitTube O).radius
  forwardLift : ℝ → (ℝ × N) → ℝ × N
  inverseLift : ℝ → (ℝ × N) → ℝ × N
  forwardQuot : ℝ → (C × N) → C × N
  inverseQuot : ℝ → (C × N) → C × N
  forwardLift_smooth : ContDiff ℝ ∞
    (fun p : ℝ × (ℝ × N) => forwardLift p.1 p.2)
  inverseLift_smooth : ContDiff ℝ ∞
    (fun p : ℝ × (ℝ × N) => inverseLift p.1 p.2)
  forwardQuot_coe : ∀ (s u : ℝ) (z : N),
    forwardQuot s ((u : C), z) =
      (((forwardLift s (u, z)).1 : C), (forwardLift s (u, z)).2)
  inverseQuot_coe : ∀ (s u : ℝ) (z : N),
    inverseQuot s ((u : C), z) =
      (((inverseLift s (u, z)).1 : C), (inverseLift s (u, z)).2)
  forward_zero : forwardLift 0 = id
  left_inv : ∀ (s : ℝ), LeftInverse (inverseLift s) (forwardLift s)
  right_inv : ∀ (s : ℝ), RightInverse (inverseLift s) (forwardLift s)
  forward_mem_tube : ∀ (s u : ℝ) (z : N),
    z ∈ Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius →
    (forwardLift s (u, z)).2 ∈
      Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius
  inverse_mem_tube : ∀ (s u : ℝ) (z : N),
    z ∈ Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius →
    (inverseLift s (u, z)).2 ∈
      Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius
  forward_collar : ∀ (s u : ℝ) (z : N), supportRadius ≤ ‖z‖ →
    forwardLift s (u, z) = (u, z)
  inverse_collar : ∀ (s u : ℝ) (z : N), supportRadius ≤ ‖z‖ →
    inverseLift s (u, z) = (u, z)


-- @@ L74-74 verbatim
variable {V}


-- @@ L76-76 verbatim
namespace PeriodicTubeCoordinateIsotopy


-- @@ L78-78 verbatim
variable {O : V.OrbitIndex} (A : V.PeriodicTubeCoordinateIsotopy O)


-- @@ L80-86 verbatim
/-- The descended forward coordinate map starts at the identity. -/
theorem forwardQuot_zero : A.forwardQuot 0 = id := by
  funext q
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.forwardQuot_coe, A.forward_zero]
  rfl


-- @@ L88-94 verbatim
/-- The descended coordinate maps remain mutually inverse. -/
theorem quot_left_inv (s : ℝ) :
    LeftInverse (A.inverseQuot s) (A.forwardQuot s) := by
  intro q
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.forwardQuot_coe, A.inverseQuot_coe, A.left_inv]


-- @@ L96-101 verbatim
theorem quot_right_inv (s : ℝ) :
    RightInverse (A.inverseQuot s) (A.forwardQuot s) := by
  intro q
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.inverseQuot_coe, A.forwardQuot_coe, A.right_inv]


-- @@ L103-112 verbatim
/-- Tube-radius preservation descends to the quotient. -/
theorem forwardQuot_mem_tube (s : ℝ) (q : C × N)
    (hq : q.2 ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    (A.forwardQuot s q).2 ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius := by
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.forwardQuot_coe]
  exact A.forward_mem_tube s u z hq


-- @@ L114-122 verbatim
theorem inverseQuot_mem_tube (s : ℝ) (q : C × N)
    (hq : q.2 ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    (A.inverseQuot s q).2 ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius := by
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.inverseQuot_coe]
  exact A.inverse_mem_tube s u z hq


-- @@ L124-130 verbatim
/-- The outer collar identity also descends to the quotient. -/
theorem forwardQuot_eq_self_of_support_le (s : ℝ) (q : C × N)
    (hq : A.supportRadius ≤ ‖q.2‖) :
    A.forwardQuot s q = q := by
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.forwardQuot_coe, A.forward_collar s u z hq]


-- @@ L132-137 verbatim
theorem inverseQuot_eq_self_of_support_le (s : ℝ) (q : C × N)
    (hq : A.supportRadius ≤ ‖q.2‖) :
    A.inverseQuot s q = q := by
  rcases q with ⟨a, z⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [A.inverseQuot_coe, A.inverse_collar s u z hq]


-- @@ L139-142 verbatim
/-- The open quotient tube used for conjugation. -/
def tubeDomain (A : V.PeriodicTubeCoordinateIsotopy O) : Set (C × N) :=
  (Set.univ : Set C) ×ˢ
    Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius


-- @@ L144-145 verbatim
/-- Its ambient image. -/
def tubeImage : Set E := V.orbitTube O '' A.tubeDomain


-- @@ L147-150 verbatim
/-- The closed inner core containing the support of every conjugated map. -/
def supportCore : Set E :=
  V.orbitTube O ''
    ((Set.univ : Set C) ×ˢ Metric.closedBall (0 : N) A.supportRadius)


-- @@ L152-157 verbatim
theorem isClosed_supportCore : IsClosed A.supportCore := by
  have hcompact : IsCompact
      ((Set.univ : Set C) ×ˢ
        Metric.closedBall (0 : N) A.supportRadius) :=
    isCompact_univ.prod (isCompact_closedBall (0 : N) A.supportRadius)
  exact (hcompact.image (V.continuous_orbitTube O)).isClosed


-- @@ L159-163 verbatim
/-- On the tube image, the chosen global tube inverse is also a right inverse. -/
theorem orbitTube_inverse_right {x : E} (hx : x ∈ A.tubeImage) :
    V.orbitTube O ((V.globalSmoothOrbitTube O).inverse x) = x := by
  rcases hx with ⟨q, hq, rfl⟩
  rw [(V.globalSmoothOrbitTube O).inverse_left q hq]


-- @@ L165-169 verbatim
theorem inverse_mem_tubeDomain {x : E} (hx : x ∈ A.tubeImage) :
    (V.globalSmoothOrbitTube O).inverse x ∈ A.tubeDomain := by
  rcases hx with ⟨q, hq, rfl⟩
  rw [(V.globalSmoothOrbitTube O).inverse_left q hq]
  exact hq


-- @@ L171-178 verbatim
/-- Conjugated forward map, extended by the ambient identity. -/
def ambientForward (s : ℝ) (x : E) : E :=
  by
    classical
    exact if x ∈ A.tubeImage then
      V.orbitTube O
        (A.forwardQuot s ((V.globalSmoothOrbitTube O).inverse x))
    else x


-- @@ L180-187 verbatim
/-- Conjugated inverse map, extended by the ambient identity. -/
def ambientInverse (s : ℝ) (x : E) : E :=
  by
    classical
    exact if x ∈ A.tubeImage then
      V.orbitTube O
        (A.inverseQuot s ((V.globalSmoothOrbitTube O).inverse x))
    else x


-- @@ L189-194 verbatim
theorem ambientForward_orbitTube (s : ℝ) (q : C × N)
    (hq : q ∈ A.tubeDomain) :
    A.ambientForward s (V.orbitTube O q) =
      V.orbitTube O (A.forwardQuot s q) := by
  rw [ambientForward, if_pos ⟨q, hq, rfl⟩,
    (V.globalSmoothOrbitTube O).inverse_left q hq]


-- @@ L196-201 verbatim
theorem ambientInverse_orbitTube (s : ℝ) (q : C × N)
    (hq : q ∈ A.tubeDomain) :
    A.ambientInverse s (V.orbitTube O q) =
      V.orbitTube O (A.inverseQuot s q) := by
  rw [ambientInverse, if_pos ⟨q, hq, rfl⟩,
    (V.globalSmoothOrbitTube O).inverse_left q hq]


-- @@ L203-205 verbatim
theorem ambientForward_eq_self_of_not_mem_tubeImage (s : ℝ) {x : E}
    (hx : x ∉ A.tubeImage) : A.ambientForward s x = x := by
  simp [ambientForward, hx]


-- @@ L207-209 verbatim
theorem ambientInverse_eq_self_of_not_mem_tubeImage (s : ℝ) {x : E}
    (hx : x ∉ A.tubeImage) : A.ambientInverse s x = x := by
  simp [ambientInverse, hx]


-- @@ L211-227 verbatim
/-- The conjugated map is supported in the closed inner core.  The annulus
between `supportRadius` and the chosen tube radius is literally fixed. -/
theorem ambientForward_eq_self_of_not_mem_supportCore (s : ℝ) {x : E}
    (hx : x ∉ A.supportCore) : A.ambientForward s x = x := by
  by_cases ht : x ∈ A.tubeImage
  · let q : C × N := (V.globalSmoothOrbitTube O).inverse x
    have hq : q ∈ A.tubeDomain := A.inverse_mem_tubeDomain ht
    have houter : A.supportRadius ≤ ‖q.2‖ := by
      by_contra hnot
      have hle : ‖q.2‖ ≤ A.supportRadius := le_of_not_ge hnot
      apply hx
      refine ⟨q, ⟨Set.mem_univ _, ?_⟩, A.orbitTube_inverse_right ht⟩
      simpa [Metric.mem_closedBall, dist_zero_left] using hle
    rw [ambientForward, if_pos ht,
      A.forwardQuot_eq_self_of_support_le s q houter,
      A.orbitTube_inverse_right ht]
  · exact A.ambientForward_eq_self_of_not_mem_tubeImage s ht


-- @@ L229-243 verbatim
theorem ambientInverse_eq_self_of_not_mem_supportCore (s : ℝ) {x : E}
    (hx : x ∉ A.supportCore) : A.ambientInverse s x = x := by
  by_cases ht : x ∈ A.tubeImage
  · let q : C × N := (V.globalSmoothOrbitTube O).inverse x
    have hq : q ∈ A.tubeDomain := A.inverse_mem_tubeDomain ht
    have houter : A.supportRadius ≤ ‖q.2‖ := by
      by_contra hnot
      have hle : ‖q.2‖ ≤ A.supportRadius := le_of_not_ge hnot
      apply hx
      refine ⟨q, ⟨Set.mem_univ _, ?_⟩, A.orbitTube_inverse_right ht⟩
      simpa [Metric.mem_closedBall, dist_zero_left] using hle
    rw [ambientInverse, if_pos ht,
      A.inverseQuot_eq_self_of_support_le s q houter,
      A.orbitTube_inverse_right ht]
  · exact A.ambientInverse_eq_self_of_not_mem_tubeImage s ht


-- @@ L245-259 verbatim
/-- The two ambient extensions remain mutually inverse. -/
theorem ambient_left_inv (s : ℝ) :
    LeftInverse (A.ambientInverse s) (A.ambientForward s) := by
  intro x
  by_cases hx : x ∈ A.tubeImage
  · let q : C × N := (V.globalSmoothOrbitTube O).inverse x
    have hq : q ∈ A.tubeDomain := A.inverse_mem_tubeDomain hx
    have hfq : A.forwardQuot s q ∈ A.tubeDomain :=
      ⟨Set.mem_univ _, A.forwardQuot_mem_tube s q hq.2⟩
    rw [show A.ambientForward s x = V.orbitTube O (A.forwardQuot s q) by
      rw [ambientForward, if_pos hx]]
    rw [A.ambientInverse_orbitTube s (A.forwardQuot s q) hfq,
      A.quot_left_inv s q, A.orbitTube_inverse_right hx]
  · rw [A.ambientForward_eq_self_of_not_mem_tubeImage s hx,
      A.ambientInverse_eq_self_of_not_mem_tubeImage s hx]


-- @@ L261-274 verbatim
theorem ambient_right_inv (s : ℝ) :
    RightInverse (A.ambientInverse s) (A.ambientForward s) := by
  intro x
  by_cases hx : x ∈ A.tubeImage
  · let q : C × N := (V.globalSmoothOrbitTube O).inverse x
    have hq : q ∈ A.tubeDomain := A.inverse_mem_tubeDomain hx
    have hiq : A.inverseQuot s q ∈ A.tubeDomain :=
      ⟨Set.mem_univ _, A.inverseQuot_mem_tube s q hq.2⟩
    rw [show A.ambientInverse s x = V.orbitTube O (A.inverseQuot s q) by
      rw [ambientInverse, if_pos hx]]
    rw [A.ambientForward_orbitTube s (A.inverseQuot s q) hiq,
      A.quot_right_inv s q, A.orbitTube_inverse_right hx]
  · rw [A.ambientInverse_eq_self_of_not_mem_tubeImage s hx,
      A.ambientForward_eq_self_of_not_mem_tubeImage s hx]


-- @@ L276-276 verbatim
/-! ## Smoothness on the interior tube -/


-- @@ L278-370 verbatim
/-- Near an interior lifted tube point, the ambient forward extension is the
ordinary smooth conjugate written in the real-phase IFT chart. -/
theorem contDiffAt_joint_ambientForward_orbitTubeLift
    (s u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => A.ambientForward p.1 p.2)
      (s, V.orbitTubeLift O (u, z)) := by
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
      (V.orbitTubeLift O (u, z)) := by
    exact chart.contDiffAt_symm htarget hforwardDeriv hforwardSmooth
  have hgball : ∀ᶠ y in 𝓝 (V.orbitTubeLift O (u, z)),
      (g y).2 ∈ Metric.ball (0 : N)
        (V.globalSmoothOrbitTube O).radius := by
    have hg2continuous : ContinuousAt (fun y : E => (g y).2)
        (V.orbitTubeLift O (u, z)) :=
      (show Continuous (fun p : ℝ × N => p.2) from continuous_snd)
        |>.continuousAt.comp' hgsmooth.continuousAt
    have hzcenter : (g (V.orbitTubeLift O (u, z))).2 ∈
        Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius := by
      rw [hgcenter]
      exact hz
    exact hg2continuous.eventually
      (Metric.isOpen_ball.mem_nhds hzcenter)
  have hright : ∀ᶠ y in 𝓝 (V.orbitTubeLift O (u, z)),
      V.orbitTubeLift O (g y) = y := by
    filter_upwards [chart.eventually_right_inverse htarget] with y hy
    exact hy
  have hlocal : ∀ᶠ y in 𝓝 (V.orbitTubeLift O (u, z)), ∀ t : ℝ,
      A.ambientForward t y =
        V.orbitTubeLift O (A.forwardLift t (g y)) := by
    filter_upwards [hright, hgball] with y hy hgy t
    let q : C × N := (((g y).1 : C), (g y).2)
    have hq : q ∈ A.tubeDomain := ⟨Set.mem_univ _, hgy⟩
    have hyq : V.orbitTube O q = y := by
      rw [V.orbitTube_coe O (g y).1 (g y).2]
      exact hy
    have hytube : y ∈ A.tubeImage := ⟨q, hq, hyq⟩
    have hinv : (V.globalSmoothOrbitTube O).inverse y = q := by
      rw [← hyq]
      exact (V.globalSmoothOrbitTube O).inverse_left q hq
    rw [ambientForward, if_pos hytube, hinv, A.forwardQuot_coe,
      V.orbitTube_coe]
  have hpair : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (p.1, g p.2))
      (s, V.orbitTubeLift O (u, z)) := by
    exact contDiffAt_fst.prodMk
      (hgsmooth.comp (s, V.orbitTubeLift O (u, z))
        (show ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2)
            (s, V.orbitTubeLift O (u, z)) from contDiffAt_snd))
  have hlift : ContDiffAt ℝ ∞
      (fun p : ℝ × E => A.forwardLift p.1 (g p.2))
      (s, V.orbitTubeLift O (u, z)) :=
    A.forwardLift_smooth.contDiffAt.comp _ hpair
  have hsmooth : ContDiffAt ℝ ∞
      (fun p : ℝ × E =>
        V.orbitTubeLift O (A.forwardLift p.1 (g p.2)))
      (s, V.orbitTubeLift O (u, z)) :=
    (V.contDiff_orbitTubeLift O).contDiffAt.comp _ hlift
  apply hsmooth.congr_of_eventuallyEq
  have hpull :=
    (show ContinuousAt (fun p : ℝ × E => p.2)
        (s, V.orbitTubeLift O (u, z)) from continuous_snd.continuousAt)
      |>.eventually hlocal
  filter_upwards [hpull] with p hp
  exact hp p.1


-- @@ L372-463 verbatim
/-- The same local smooth-chart statement for the explicit ambient inverse. -/
theorem contDiffAt_joint_ambientInverse_orbitTubeLift
    (s u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => A.ambientInverse p.1 p.2)
      (s, V.orbitTubeLift O (u, z)) := by
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
      (V.orbitTubeLift O (u, z)) := by
    exact chart.contDiffAt_symm htarget hforwardDeriv hforwardSmooth
  have hgball : ∀ᶠ y in 𝓝 (V.orbitTubeLift O (u, z)),
      (g y).2 ∈ Metric.ball (0 : N)
        (V.globalSmoothOrbitTube O).radius := by
    have hg2continuous : ContinuousAt (fun y : E => (g y).2)
        (V.orbitTubeLift O (u, z)) :=
      (show Continuous (fun p : ℝ × N => p.2) from continuous_snd)
        |>.continuousAt.comp' hgsmooth.continuousAt
    have hzcenter : (g (V.orbitTubeLift O (u, z))).2 ∈
        Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius := by
      rw [hgcenter]
      exact hz
    exact hg2continuous.eventually
      (Metric.isOpen_ball.mem_nhds hzcenter)
  have hright : ∀ᶠ y in 𝓝 (V.orbitTubeLift O (u, z)),
      V.orbitTubeLift O (g y) = y := by
    filter_upwards [chart.eventually_right_inverse htarget] with y hy
    exact hy
  have hlocal : ∀ᶠ y in 𝓝 (V.orbitTubeLift O (u, z)), ∀ t : ℝ,
      A.ambientInverse t y =
        V.orbitTubeLift O (A.inverseLift t (g y)) := by
    filter_upwards [hright, hgball] with y hy hgy t
    let q : C × N := (((g y).1 : C), (g y).2)
    have hq : q ∈ A.tubeDomain := ⟨Set.mem_univ _, hgy⟩
    have hyq : V.orbitTube O q = y := by
      rw [V.orbitTube_coe O (g y).1 (g y).2]
      exact hy
    have hytube : y ∈ A.tubeImage := ⟨q, hq, hyq⟩
    have hinv : (V.globalSmoothOrbitTube O).inverse y = q := by
      rw [← hyq]
      exact (V.globalSmoothOrbitTube O).inverse_left q hq
    rw [ambientInverse, if_pos hytube, hinv, A.inverseQuot_coe,
      V.orbitTube_coe]
  have hpair : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (p.1, g p.2))
      (s, V.orbitTubeLift O (u, z)) := by
    exact contDiffAt_fst.prodMk
      (hgsmooth.comp (s, V.orbitTubeLift O (u, z))
        (show ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2)
            (s, V.orbitTubeLift O (u, z)) from contDiffAt_snd))
  have hlift : ContDiffAt ℝ ∞
      (fun p : ℝ × E => A.inverseLift p.1 (g p.2))
      (s, V.orbitTubeLift O (u, z)) :=
    A.inverseLift_smooth.contDiffAt.comp _ hpair
  have hsmooth : ContDiffAt ℝ ∞
      (fun p : ℝ × E =>
        V.orbitTubeLift O (A.inverseLift p.1 (g p.2)))
      (s, V.orbitTubeLift O (u, z)) :=
    (V.contDiff_orbitTubeLift O).contDiffAt.comp _ hlift
  apply hsmooth.congr_of_eventuallyEq
  have hpull :=
    (show ContinuousAt (fun p : ℝ × E => p.2)
        (s, V.orbitTubeLift O (u, z)) from continuous_snd.continuousAt)
      |>.eventually hlocal
  filter_upwards [hpull] with p hp
  exact hp p.1


-- @@ L465-465 verbatim
/-! ## Global smoothness of the identity extension -/


-- @@ L467-493 verbatim
/-- The collar makes the forward conjugate agree with the identity on an
open neighborhood of every point outside the closed support core. -/
theorem contDiff_joint_ambientForward :
    ContDiff ℝ ∞ (fun p : ℝ × E => A.ambientForward p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s, x⟩
  by_cases hx : x ∈ A.supportCore
  · rcases hx with ⟨⟨a, z⟩, hzcore, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hzle : ‖z‖ ≤ A.supportRadius := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hzcore.2
    have hz : z ∈ Metric.ball (0 : N)
        (V.globalSmoothOrbitTube O).radius := by
      simpa [Metric.mem_ball, dist_zero_left] using
        (lt_of_le_of_lt hzle A.supportRadius_lt)
    simpa only [V.orbitTube_coe] using
      A.contDiffAt_joint_ambientForward_orbitTubeLift s u z hz
  · have hxcompl : x ∈ A.supportCoreᶜ := hx
    have hnear : A.supportCoreᶜ ∈ 𝓝 x :=
      A.isClosed_supportCore.isOpen_compl.mem_nhds hxcompl
    have hpull :=
      (show ContinuousAt (fun p : ℝ × E => p.2) (s, x) from
        continuous_snd.continuousAt) |>.eventually hnear
    apply (show ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (s, x) from
      contDiffAt_snd).congr_of_eventuallyEq
    filter_upwards [hpull] with p hp
    exact A.ambientForward_eq_self_of_not_mem_supportCore p.1 hp


-- @@ L495-519 verbatim
theorem contDiff_joint_ambientInverse :
    ContDiff ℝ ∞ (fun p : ℝ × E => A.ambientInverse p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s, x⟩
  by_cases hx : x ∈ A.supportCore
  · rcases hx with ⟨⟨a, z⟩, hzcore, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hzle : ‖z‖ ≤ A.supportRadius := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hzcore.2
    have hz : z ∈ Metric.ball (0 : N)
        (V.globalSmoothOrbitTube O).radius := by
      simpa [Metric.mem_ball, dist_zero_left] using
        (lt_of_le_of_lt hzle A.supportRadius_lt)
    simpa only [V.orbitTube_coe] using
      A.contDiffAt_joint_ambientInverse_orbitTubeLift s u z hz
  · have hxcompl : x ∈ A.supportCoreᶜ := hx
    have hnear : A.supportCoreᶜ ∈ 𝓝 x :=
      A.isClosed_supportCore.isOpen_compl.mem_nhds hxcompl
    have hpull :=
      (show ContinuousAt (fun p : ℝ × E => p.2) (s, x) from
        continuous_snd.continuousAt) |>.eventually hnear
    apply (show ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (s, x) from
      contDiffAt_snd).congr_of_eventuallyEq
    filter_upwards [hpull] with p hp
    exact A.ambientInverse_eq_self_of_not_mem_supportCore p.1 hp


-- @@ L521-521 verbatim
/-! ## The resulting smooth ambient isotopy -/


-- @@ L523-528 verbatim
theorem ambientForward_zero : A.ambientForward 0 = id := by
  funext x
  by_cases hx : x ∈ A.tubeImage
  · rw [ambientForward, if_pos hx, A.forwardQuot_zero]
    simpa only [id_eq] using A.orbitTube_inverse_right hx
  · exact A.ambientForward_eq_self_of_not_mem_tubeImage 0 hx


-- @@ L530-533 verbatim
theorem contDiff_ambientForward_slice (s : ℝ) :
    ContDiff ℝ ∞ (A.ambientForward s) := by
  exact A.contDiff_joint_ambientForward.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L535-538 verbatim
theorem contDiff_ambientInverse_slice (s : ℝ) :
    ContDiff ℝ ∞ (A.ambientInverse s) := by
  exact A.contDiff_joint_ambientInverse.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L540-567 verbatim
/-- Surjectivity of the inverse spatial derivative follows by differentiating
the two already-proved inverse identities. -/
theorem ambientInverse_fderiv_surjective (s : ℝ) (x : E) :
    Surjective (fderiv ℝ (A.ambientInverse s) x) := by
  let f : E → E := A.ambientForward s
  let g : E → E := A.ambientInverse s
  have hf : ContDiff ℝ ∞ f := A.contDiff_ambientForward_slice s
  have hg : ContDiff ℝ ∞ g := A.contDiff_ambientInverse_slice s
  let y : E := g x
  have hfy : f y = x := A.ambient_right_inv s x
  have hgf : (fun z => g (f z)) = id := by
    funext z
    exact A.ambient_left_inv s z
  have hcomp : HasFDerivAt (fun z => g (f z))
      ((fderiv ℝ g (f y)).comp (fderiv ℝ f y)) y :=
    ((hg.differentiable (by simp) (f y)).hasFDerivAt.comp y
      (hf.differentiable (by simp) y).hasFDerivAt)
  rw [hgf] at hcomp
  have hderiv0 : (fderiv ℝ g (f y)).comp (fderiv ℝ f y) =
      ContinuousLinearMap.id ℝ E :=
    hcomp.fderiv.symm.trans (hasFDerivAt_id y).fderiv
  have hderiv : (fderiv ℝ g x).comp (fderiv ℝ f y) =
      ContinuousLinearMap.id ℝ E := by
    rwa [hfy] at hderiv0
  intro z
  refine ⟨fderiv ℝ f y z, ?_⟩
  have hz := congrArg (fun L : E →L[ℝ] E => L z) hderiv
  simpa [ContinuousLinearMap.comp_apply] using hz


-- @@ L569-580 verbatim
/-- Conjugation by the chosen globally injective smooth orbit tube, followed
by identity extension, is a genuine smooth ambient isotopy. -/
def toSmoothAmbientIsotopy : SmoothAmbientIsotopy n where
  forward := A.ambientForward
  inverse := A.ambientInverse
  forward_smooth := A.contDiff_joint_ambientForward
  inverse_smooth := A.contDiff_joint_ambientInverse
  forward_zero := A.ambientForward_zero
  left_inv := fun s _ => A.ambient_left_inv s
  right_inv := fun s _ => A.ambient_right_inv s
  inverse_fderiv_surjective := fun s _ x =>
    A.ambientInverse_fderiv_surjective s x


-- @@ L582-584 verbatim
@[simp] theorem toSmoothAmbientIsotopy_forward (s : ℝ) (x : E) :
    A.toSmoothAmbientIsotopy.forward s x = A.ambientForward s x :=
  rfl


-- @@ L586-588 verbatim
@[simp] theorem toSmoothAmbientIsotopy_inverse (s : ℝ) (x : E) :
    A.toSmoothAmbientIsotopy.inverse s x = A.ambientInverse s x :=
  rfl


-- @@ L590-594 verbatim
/-- Explicit support statement for downstream relative compositions. -/
theorem toSmoothAmbientIsotopy_forward_fixed_outside_support
    (s : ℝ) {x : E} (hx : x ∉ A.supportCore) :
    A.toSmoothAmbientIsotopy.forward s x = x :=
  A.ambientForward_eq_self_of_not_mem_supportCore s hx


-- @@ L596-599 verbatim
theorem toSmoothAmbientIsotopy_inverse_fixed_outside_support
    (s : ℝ) {x : E} (hx : x ∉ A.supportCore) :
    A.toSmoothAmbientIsotopy.inverse s x = x :=
  A.ambientInverse_eq_self_of_not_mem_supportCore s hx


-- @@ L601-601 verbatim
end PeriodicTubeCoordinateIsotopy

-- @@ L602-602 verbatim
end TamedField

-- @@ L603-603 verbatim
end Submission
