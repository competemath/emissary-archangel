import Submission.ProductionMorseSaddleLocalExcision


-- @@ L3-11 verbatim
/-!
# Quantitative separation of the local saddle branches

At the chronological saddle radius, the points with hyperbola parameter
`s = 0` have parameter norm exactly the chronological radius.  Hence they
lie in the inner half of the complete-cover ball.  These are the local points
used in the distance contradiction excluding collisions between exterior
flow cylinders and distinguished saddle components.
-/


-- @@ L13-13 verbatim
set_option autoImplicit false


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Metric

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}

-- @@ L23-23 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L24-24 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L25-25 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L27-27 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L29-29 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L31-55 verbatim
/-- The central point of either positive hyperbola branch is contained in
the inner half of the complete-cover ball. -/
theorem chronologicalSaddlePositiveBranch_dist_lt_half_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (b : SaddleBranch) :
    dist ((D.position.eventModel t ht).saddlePositiveBranch b
        (D.chronologicalWindowRadius t ht) 0)
        (D.position.eventCenter t ht) <
      (D.position.eventModel t ht).fiberCoverRadius / 2 := by
  apply D.chronologicalEventEmbeddedShrink_param_dist_lt_half_cover t ht
  have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b
    (D.chronologicalWindowRadius t ht) 0
  have hnorm :
      ‖pairToMorseParam
          (saddlePositiveArc b (D.chronologicalWindowRadius t ht) 0)‖ =
        D.chronologicalWindowRadius t ht := by
    have hnonneg : 0 ≤ ‖pairToMorseParam
        (saddlePositiveArc b (D.chronologicalWindowRadius t ht) 0)‖ :=
      norm_nonneg _
    have hpos := D.chronologicalWindowRadius_pos t ht
    norm_num at hsq
    nlinarith
  rw [hnorm]
  exact D.chronologicalWindowRadius_lt_embedded t ht


-- @@ L57-81 verbatim
/-- Negative-level counterpart of
`chronologicalSaddlePositiveBranch_dist_lt_half_cover`. -/
theorem chronologicalSaddleNegativeBranch_dist_lt_half_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (b : SaddleBranch) :
    dist ((D.position.eventModel t ht).saddleNegativeBranch b
        (D.chronologicalWindowRadius t ht) 0)
        (D.position.eventCenter t ht) <
      (D.position.eventModel t ht).fiberCoverRadius / 2 := by
  apply D.chronologicalEventEmbeddedShrink_param_dist_lt_half_cover t ht
  have hsq := norm_pairToMorseParam_saddleNegativeArc_sq b
    (D.chronologicalWindowRadius t ht) 0
  have hnorm :
      ‖pairToMorseParam
          (saddleNegativeArc b (D.chronologicalWindowRadius t ht) 0)‖ =
        D.chronologicalWindowRadius t ht := by
    have hnonneg : 0 ≤ ‖pairToMorseParam
        (saddleNegativeArc b (D.chronologicalWindowRadius t ht) 0)‖ :=
      norm_nonneg _
    have hpos := D.chronologicalWindowRadius_pos t ht
    norm_num at hsq
    nlinarith
  rw [hnorm]
  exact D.chronologicalWindowRadius_lt_embedded t ht


-- @@ L83-108 verbatim
/-- The inner positive branch point lies on the literal chronological
after-slice. -/
theorem chronologicalSaddlePositiveBranch_time
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    tcoord ((D.position.eventModel t ht).saddlePositiveBranch b
        (D.chronologicalWindowRadius t ht) 0) =
      D.chronologicalAfterTime t ht := by
  rw [chronologicalAfterTime]
  apply (D.position.eventModel t ht).saddlePositiveBranch_time hindex
  have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b
    (D.chronologicalWindowRadius t ht) 0
  have hnonneg : 0 ≤ ‖pairToMorseParam
      (saddlePositiveArc b (D.chronologicalWindowRadius t ht) 0)‖ :=
    norm_nonneg _
  have hpos := D.chronologicalWindowRadius_pos t ht
  have hnorm : ‖pairToMorseParam
      (saddlePositiveArc b (D.chronologicalWindowRadius t ht) 0)‖ =
        D.chronologicalWindowRadius t ht := by
    norm_num at hsq
    nlinarith
  rw [hnorm]
  exact (D.chronologicalWindowRadius_lt_embedded t ht).trans_le
    (D.chronologicalEventEmbeddedShrink t ht).radius_le


-- @@ L110-135 verbatim
/-- The inner negative branch point lies on the literal chronological
before-slice. -/
theorem chronologicalSaddleNegativeBranch_time
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    tcoord ((D.position.eventModel t ht).saddleNegativeBranch b
        (D.chronologicalWindowRadius t ht) 0) =
      D.chronologicalBeforeTime t ht := by
  rw [chronologicalBeforeTime]
  apply (D.position.eventModel t ht).saddleNegativeBranch_time hindex
  have hsq := norm_pairToMorseParam_saddleNegativeArc_sq b
    (D.chronologicalWindowRadius t ht) 0
  have hnonneg : 0 ≤ ‖pairToMorseParam
      (saddleNegativeArc b (D.chronologicalWindowRadius t ht) 0)‖ :=
    norm_nonneg _
  have hpos := D.chronologicalWindowRadius_pos t ht
  have hnorm : ‖pairToMorseParam
      (saddleNegativeArc b (D.chronologicalWindowRadius t ht) 0)‖ =
        D.chronologicalWindowRadius t ht := by
    norm_num at hsq
    nlinarith
  rw [hnorm]
  exact (D.chronologicalWindowRadius_lt_embedded t ht).trans_le
    (D.chronologicalEventEmbeddedShrink t ht).radius_le


-- @@ L137-137 verbatim
/-! ## Membership in the distinguished global components -/


-- @@ L139-186 verbatim
/-- The inner positive branch point used by the distance estimate lies on
the corresponding distinguished global orbit, not merely on one of the two
local branches. -/
theorem chronologicalSaddlePositiveBranch_mem_distinguishedOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    spacePart ((D.position.eventModel t ht).saddlePositiveBranch b
        (D.chronologicalWindowRadius t ht) 0) ∈
      ((D.chronologicalSaddlePositiveOrbit t ht hindex b :
        (D.chronologicalAfterField t ht).OrbitIndex) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let rho := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  let u : EuclideanSpace ℝ (Fin 2) :=
    pairToMorseParam (saddlePositiveArc b a 0)
  have ha : 0 < a := D.chronologicalWindowRadius_pos t ht
  have hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2 := by
    simpa [u] using morseQuadratic_saddlePositiveArc b a 0
  have hsign : 0 < signedBranch b (u 0) := by
    have hsqrt : 0 < Real.sqrt (a ^ 2) := Real.sqrt_pos.2 (sq_pos_of_pos ha)
    cases b <;> simpa [u, saddlePositiveArc, signedBranch] using hsqrt
  have hu : ‖u‖ < M.radius := by
    have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b a 0
    have hnonneg : 0 ≤ ‖u‖ := norm_nonneg _
    have hnorm : ‖u‖ = a := by
      change ‖pairToMorseParam (saddlePositiveArc b a 0)‖ = a
      norm_num at hsq
      nlinarith
    rw [hnorm]
    exact (D.chronologicalWindowRadius_lt_embedded t ht).trans_le T.radius_le
  have hmem := T.saddlePositiveParam_mem_branch_orbit_full H hindex
    b rho a u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
    hu
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalAfterField t ht)
  simpa [M, T, H, rho, a, u, chronologicalSaddlePositiveOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchOrbitIndex,
    StandardMorseEventAt.saddlePositiveBranch,
    StandardMorseEventAt.localPoint] using hmem


-- @@ L188-234 verbatim
/-- Negative-level counterpart of
`chronologicalSaddlePositiveBranch_mem_distinguishedOrbit`. -/
theorem chronologicalSaddleNegativeBranch_mem_distinguishedOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    spacePart ((D.position.eventModel t ht).saddleNegativeBranch b
        (D.chronologicalWindowRadius t ht) 0) ∈
      ((D.chronologicalSaddleNegativeOrbit t ht hindex b :
        (D.chronologicalBeforeField t ht).OrbitIndex) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let rho := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  let u : EuclideanSpace ℝ (Fin 2) :=
    pairToMorseParam (saddleNegativeArc b a 0)
  have ha : 0 < a := D.chronologicalWindowRadius_pos t ht
  have hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2) := by
    simpa [u] using morseQuadratic_saddleNegativeArc b a 0
  have hsign : 0 < signedBranch b (u 1) := by
    have hsqrt : 0 < Real.sqrt (a ^ 2) := Real.sqrt_pos.2 (sq_pos_of_pos ha)
    cases b <;> simpa [u, saddleNegativeArc, signedBranch] using hsqrt
  have hu : ‖u‖ < M.radius := by
    have hsq := norm_pairToMorseParam_saddleNegativeArc_sq b a 0
    have hnonneg : 0 ≤ ‖u‖ := norm_nonneg _
    have hnorm : ‖u‖ = a := by
      change ‖pairToMorseParam (saddleNegativeArc b a 0)‖ = a
      norm_num at hsq
      nlinarith
    rw [hnorm]
    exact (D.chronologicalWindowRadius_lt_embedded t ht).trans_le T.radius_le
  have hmem := T.saddleNegativeParam_mem_branch_orbit_full H hindex
    b rho a u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
    hu
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalBeforeField t ht)
  simpa [M, T, H, rho, a, u, chronologicalSaddleNegativeOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchOrbitIndex,
    StandardMorseEventAt.saddleNegativeBranch,
    StandardMorseEventAt.localPoint] using hmem


-- @@ L236-236 verbatim
end ValueSeparatedSignedMorsePackage

-- @@ L237-237 verbatim
end Submission
