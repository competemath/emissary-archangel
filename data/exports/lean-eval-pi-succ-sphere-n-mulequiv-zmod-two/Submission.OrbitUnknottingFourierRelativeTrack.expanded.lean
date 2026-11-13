import Mathlib
import Submission.OrbitUnknottingFourierEmbeddingTrack
import Submission.OrbitUnknottingFourierObstacleBadLocus
import Submission.OrbitUnknottingSupportNeighborhood


-- @@ L6-13 verbatim
/-!
# Embedded Fourier tracks relative to every other orbit

For a selected source orbit `O`, the finite obstacle family consists of both
the intrinsic source lift and canonical target lift of every `P ≠ O`.
Finite smooth range avoidance chooses one Fourier parameter which keeps the
moving circle embedded and immersed while avoiding this entire family.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false

-- @@ L16-16 verbatim
set_option maxHeartbeats 300000


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function

-- @@ L21-21 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L23-23 verbatim
namespace Submission

-- @@ L24-24 verbatim
namespace TamedField

-- @@ L25-25 verbatim
namespace FourierRelativeTrack


-- @@ L27-27 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L30-30 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L32-32 verbatim
variable {V} (h2 : 2 ≤ n) (O : V.OrbitIndex)


-- @@ L34-36 verbatim
/-- The source/target choice for every orbit different from `O`. -/
abbrev RelativeObstacleIndex :=
  {P : V.OrbitIndex // P ≠ O} × Bool


-- @@ L38-44 verbatim
/-- Time-independent lift of one fixed relative obstacle.  `false` selects
the intrinsic source circle and `true` its canonical target circle. -/
def relativeObstacleLift
    (j : RelativeObstacleIndex (V := V) O) (_s v : ℝ) : E :=
  match j.2 with
  | false => V.intrinsicOrbitLift j.1.1 v
  | true => FourierEmbeddingTrack.targetLift (V := V) h2 j.1.1 v


-- @@ L46-55 verbatim
theorem contDiff_relativeObstacleLift
    (j : RelativeObstacleIndex (V := V) O) :
    ContDiff ℝ ∞
      (fun z : ℝ × ℝ => relativeObstacleLift (V := V) h2 O j z.1 z.2) := by
  rcases j with ⟨⟨P, hPO⟩, b⟩
  cases b
  · simpa only [relativeObstacleLift, Function.comp_def] using
      (V.contDiff_intrinsicOrbitLift P).comp contDiff_snd
  · simpa only [relativeObstacleLift, Function.comp_def] using
      (FourierEmbeddingTrack.contDiff_targetLift (V := V) h2 P).comp contDiff_snd


-- @@ L57-108 verbatim
/-- A single parameter meets the self-embedding, immersion, and all relative
obstacle-avoidance conditions. -/
theorem exists_relativeGoodParameter (h3 : 3 ≤ n) :
    ∃ p : OrbitUnknottingFourier.Parameter E,
      p ∉ Set.range
        (OrbitUnknottingFourier.secantBadMap
          (FourierEmbeddingTrack.baseTrack (V := V) h2 O)) ∧
      p ∉ Set.range
        (OrbitUnknottingFourier.tangentBadMap
          (FourierEmbeddingTrack.baseTangent (V := V) h2 O)) ∧
      ∀ P : V.OrbitIndex, P ≠ O →
        p ∉ Set.range
          (OrbitUnknottingFourier.obstacleBadMap
            (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
            (fun _s v => V.intrinsicOrbitLift P v)) ∧
        p ∉ Set.range
          (OrbitUnknottingFourier.obstacleBadMap
            (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
            (fun _s v => FourierEmbeddingTrack.targetLift (V := V) h2 P v)) := by
  have hdim : 4 ≤ Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨p, _hpU, hpsec, hptan, hpobs⟩ :=
    OrbitUnknottingFourier.exists_parameter_avoiding_badRanges_and_obstacles
      (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
      (FourierEmbeddingTrack.baseTangent (V := V) h2 O)
      (relativeObstacleLift (V := V) h2 O)
      (FourierEmbeddingTrack.contDiff_baseTrack (V := V) h2 O)
      (FourierEmbeddingTrack.contDiff_baseTangent (V := V) h2 O)
      (contDiff_relativeObstacleLift (V := V) h2 O)
      hdim (U := Set.univ) isOpen_univ Set.univ_nonempty
  refine ⟨p, hpsec, hptan, ?_⟩
  intro P hPO
  have hsource := hpobs
    (⟨⟨P, hPO⟩, false⟩ : RelativeObstacleIndex (V := V) O)
  have htarget := hpobs
    (⟨⟨P, hPO⟩, true⟩ : RelativeObstacleIndex (V := V) O)
  have hsourceLift :
      relativeObstacleLift (V := V) h2 O
        (⟨⟨P, hPO⟩, false⟩ : RelativeObstacleIndex (V := V) O) =
        (fun _s v => V.intrinsicOrbitLift P v) := by
    funext s v
    rfl
  have htargetLift :
      relativeObstacleLift (V := V) h2 O
        (⟨⟨P, hPO⟩, true⟩ : RelativeObstacleIndex (V := V) O) =
        (fun _s v => FourierEmbeddingTrack.targetLift (V := V) h2 P v) := by
    funext s v
    rfl
  rw [hsourceLift] at hsource
  rw [htargetLift] at htarget
  exact ⟨hsource, htarget⟩


-- @@ L110-119 verbatim
/-- An embedded-circle track together with literal noncollision against all
other source and target lifts at every interior time. -/
structure RelativeEmbeddedCircleTrack where
  track : FourierEmbeddingTrack.EmbeddedCircleTrack (V := V) h2 O
  interior_ne_source : ∀ (s u v : ℝ) (P : V.OrbitIndex),
    P ≠ O → 0 < s → s < 1 →
      track.lift s u ≠ V.intrinsicOrbitLift P v
  interior_ne_target : ∀ (s u v : ℝ) (P : V.OrbitIndex),
    P ≠ O → 0 < s → s < 1 →
      track.lift s u ≠ FourierEmbeddingTrack.targetLift (V := V) h2 P v


-- @@ L121-158 verbatim
/-- Package one fully avoiding Fourier parameter into the relative track. -/
def relativeEmbeddedCircleTrackOfParameter
    (p : OrbitUnknottingFourier.Parameter E)
    (hpsec : p ∉ Set.range
      (OrbitUnknottingFourier.secantBadMap
        (FourierEmbeddingTrack.baseTrack (V := V) h2 O)))
    (hptan : p ∉ Set.range
      (OrbitUnknottingFourier.tangentBadMap
        (FourierEmbeddingTrack.baseTangent (V := V) h2 O)))
    (hpobs : ∀ P : V.OrbitIndex, P ≠ O →
      p ∉ Set.range
        (OrbitUnknottingFourier.obstacleBadMap
          (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
          (fun _s v => V.intrinsicOrbitLift P v)) ∧
      p ∉ Set.range
        (OrbitUnknottingFourier.obstacleBadMap
          (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
          (fun _s v => FourierEmbeddingTrack.targetLift (V := V) h2 P v))) :
    RelativeEmbeddedCircleTrack (V := V) h2 O where
  track := FourierEmbeddingTrack.embeddedCircleTrackOfParameter
    (V := V) h2 O p hpsec hptan
  interior_ne_source := by
    intro s u v P hPO hs0 hs1
    change OrbitUnknottingFourier.perturbedTrack
      (FourierEmbeddingTrack.baseTrack (V := V) h2 O) p s u ≠
        V.intrinsicOrbitLift P v
    simpa using OrbitUnknottingFourier.ne_obstacle_of_avoids_range
      (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
      (fun _s v => V.intrinsicOrbitLift P v) p (hpobs P hPO).1 hs0 hs1
  interior_ne_target := by
    intro s u v P hPO hs0 hs1
    change OrbitUnknottingFourier.perturbedTrack
      (FourierEmbeddingTrack.baseTrack (V := V) h2 O) p s u ≠
        FourierEmbeddingTrack.targetLift (V := V) h2 P v
    simpa using OrbitUnknottingFourier.ne_obstacle_of_avoids_range
      (FourierEmbeddingTrack.baseTrack (V := V) h2 O)
      (fun _s v => FourierEmbeddingTrack.targetLift (V := V) h2 P v)
      p (hpobs P hPO).2 hs0 hs1


-- @@ L160-165 verbatim
theorem exists_relativeEmbeddedCircleTrack (h3 : 3 ≤ n) :
    Nonempty (RelativeEmbeddedCircleTrack (V := V) h2 O) := by
  obtain ⟨p, hpsec, hptan, hpobs⟩ :=
    exists_relativeGoodParameter (V := V) h2 O h3
  exact ⟨relativeEmbeddedCircleTrackOfParameter
    (V := V) h2 O p hpsec hptan hpobs⟩


-- @@ L167-167 verbatim
namespace RelativeEmbeddedCircleTrack


-- @@ L169-169 verbatim
variable (R : RelativeEmbeddedCircleTrack (V := V) h2 O)


-- @@ L171-185 verbatim
/-- At an interior time the moving quotient circle is disjoint from every
other source orbit. -/
theorem interior_range_disjoint_source
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : V.OrbitIndex) (hPO : P ≠ O) :
    Disjoint (Set.range (R.track.circle s)) (P : Set E) := by
  rw [Set.disjoint_left]
  intro x hx hP
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← V.range_intrinsicOrbitEmbedding P] at hP
  obtain ⟨b, hb⟩ := hP
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [V.intrinsicOrbitEmbedding_coe, R.track.circle_coe] at hb
  exact (R.interior_ne_source s u v P hPO hs0 hs1) hb.symm


-- @@ L187-203 verbatim
/-- At an interior time the moving quotient circle is disjoint from every
other canonical target. -/
theorem interior_range_disjoint_target
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : V.OrbitIndex) (hPO : P ≠ O) :
    Disjoint (Set.range (R.track.circle s))
      (CanonicalRoundOrbit.target V h2 P) := by
  rw [Set.disjoint_left]
  intro x hx hP
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [CanonicalRoundOrbit.target] at hP
  obtain ⟨b, hb⟩ := hP
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [← FourierEmbeddingTrack.targetLift_eq_circlePoint (V := V) h2 P,
    R.track.circle_coe] at hb
  exact (R.interior_ne_target s u v P hPO hs0 hs1) hb.symm


-- @@ L205-226 verbatim
/-- Relative source disjointness also holds at the two endpoints. -/
theorem range_disjoint_source
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (P : V.OrbitIndex) (hPO : P ≠ O) :
    Disjoint (Set.range (R.track.circle s)) (P : Set E) := by
  rcases hs with ⟨hs0, hs1⟩
  by_cases hzero : s = 0
  · subst s
    rw [R.track.start_circle, V.range_intrinsicOrbitEmbedding]
    exact (OrbitUnknottingSupport.activeSet_disjoint_obstacleSet V h2 O).mono
      (fun _ hx => Or.inl hx)
      (OrbitUnknottingSupport.source_subset_obstacleSet V h2 O P hPO)
  by_cases hone : s = 1
  · subst s
    rw [R.track.finish_circle]
    change Disjoint (CanonicalRoundOrbit.target V h2 O) (P : Set E)
    exact (OrbitUnknottingSupport.activeSet_disjoint_obstacleSet V h2 O).mono
      (fun _ hx => Or.inr hx)
      (OrbitUnknottingSupport.source_subset_obstacleSet V h2 O P hPO)
  exact interior_range_disjoint_source (V := V) (h2 := h2) (O := O) R
    (lt_of_le_of_ne hs0 (Ne.symm hzero))
    (lt_of_le_of_ne hs1 hone) P hPO


-- @@ L228-251 verbatim
/-- Relative target disjointness also holds at the two endpoints. -/
theorem range_disjoint_target
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (P : V.OrbitIndex) (hPO : P ≠ O) :
    Disjoint (Set.range (R.track.circle s))
      (CanonicalRoundOrbit.target V h2 P) := by
  rcases hs with ⟨hs0, hs1⟩
  by_cases hzero : s = 0
  · subst s
    rw [R.track.start_circle, V.range_intrinsicOrbitEmbedding]
    exact (OrbitUnknottingSupport.activeSet_disjoint_obstacleSet V h2 O).mono
      (fun _ hx => Or.inl hx)
      (OrbitUnknottingSupport.target_subset_obstacleSet V h2 O P hPO)
  by_cases hone : s = 1
  · subst s
    rw [R.track.finish_circle]
    change Disjoint (CanonicalRoundOrbit.target V h2 O)
      (CanonicalRoundOrbit.target V h2 P)
    exact (OrbitUnknottingSupport.activeSet_disjoint_obstacleSet V h2 O).mono
      (fun _ hx => Or.inr hx)
      (OrbitUnknottingSupport.target_subset_obstacleSet V h2 O P hPO)
  exact interior_range_disjoint_target (V := V) (h2 := h2) (O := O) R
    (lt_of_le_of_ne hs0 (Ne.symm hzero))
    (lt_of_le_of_ne hs1 hone) P hPO


-- @@ L253-253 verbatim
end RelativeEmbeddedCircleTrack


-- @@ L255-255 verbatim
end FourierRelativeTrack

-- @@ L256-256 verbatim
end TamedField

-- @@ L257-257 verbatim
end Submission
