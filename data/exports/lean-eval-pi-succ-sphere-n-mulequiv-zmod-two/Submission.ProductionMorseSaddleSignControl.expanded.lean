import Submission.ProductionMorseEventEmbeddedGeometry


-- @@ L3-16 verbatim
/-!
# Positive-sheet control for production saddle charts

The sign label of a signed framed cobordism is nonzero on its zero fiber.  An
embedded standard Morse chart therefore has a very strong local consequence:
if its critical center is positive, every point of a sufficiently small chart
ball is positive.  The proof joins the center to the point by the radial path
inside Morse coordinates.

This route-independent statement supplies the sign input for all four local
saddle branches in the actual shared-cutoff/value-separated construction.  It
replaces the earlier `ExactFiniteMorseJetInstallation`-specific branch-sign
arguments.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace Submission


-- @@ L23-23 verbatim
open Set Function Metric

-- @@ L24-24 verbatim
open scoped RealInnerProductSpace unitInterval


-- @@ L26-26 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L28-28 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L30-56 verbatim
/-- The straight radial path in Morse coordinates, transported into the
ambient zero surface. -/
def localRadialPath
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink)
    (u : E₂) (hu : ‖u‖ < T.radius) :
    Path center (M.localPoint u) where
  toContinuousMap := {
    toFun := fun q => M.param ((q : ℝ) • u)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro q
      apply (T.param_differentiableAt _ ?_).continuousAt.comp'
        ?_
      · have hqnorm : ‖(q : ℝ) • u‖ ≤ ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.2.1]
          nlinarith [q.2.2, norm_nonneg u]
        exact hqnorm.trans_lt hu
      · fun_prop
  }
  source' := by simp [StandardMorseEventAt.localPoint, M.param_zero]
  target' := by simp [StandardMorseEventAt.localPoint]


-- @@ L58-73 verbatim
/-- The radial path remains in the actual zero fiber. -/
theorem localRadialPath_fiber
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink)
    (u : E₂) (hu : ‖u‖ < T.radius) (q : I) :
    C.cobordism.G (T.localRadialPath u hu q) = 0 := by
  apply M.param_fiber
  have hqnorm : ‖(q : ℝ) • u‖ ≤ ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.2.1]
    nlinarith [q.2.2, norm_nonneg u]
  exact (hqnorm.trans_lt hu).trans_le T.radius_le


-- @@ L75-91 verbatim
/-- Positivity at the critical center propagates to every point in the
embedded event ball. -/
theorem localPoint_positive_of_center
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink)
    (hcenter : 0 < C center)
    (u : E₂) (hu : ‖u‖ < T.radius) :
    0 < C (M.localPoint u) := by
  have hsign := C.pos_iff_of_zeroFiber_path
    (T.localRadialPath u hu) (T.localRadialPath_fiber u hu)
  have hpositive := hsign.mp (by simpa [localRadialPath] using hcenter)
  simpa [localRadialPath, StandardMorseEventAt.localPoint] using hpositive


-- @@ L93-107 verbatim
/-- Positive-side saddle branches lie on the positive sheet whenever their
Morse parameters lie in the embedded ball. -/
theorem saddlePositiveBranch_positive_of_center
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddlePositiveArc b a s)‖ <
      T.radius) :
    0 < C (M.saddlePositiveBranch b a s) :=
  T.localPoint_positive_of_center hcenter _ hu


-- @@ L109-122 verbatim
/-- Negative-side saddle branches obey the same sign propagation. -/
theorem saddleNegativeBranch_positive_of_center
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddleNegativeArc b a s)‖ <
      T.radius) :
    0 < C (M.saddleNegativeBranch b a s) :=
  T.localPoint_positive_of_center hcenter _ hu


-- @@ L124-139 verbatim
/-- Every positive-side boundary end on a sufficiently small parameter circle
is positively labelled. -/
theorem saddlePositiveBoundaryEnd_positive_of_center
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius) :
    0 < C (M.saddlePositiveBoundaryEnd b e ρ a) := by
  apply T.localPoint_positive_of_center hcenter
  rw [norm_saddlePositiveBoundaryEndParam b e hρ ha]
  exact hρrad


-- @@ L141-156 verbatim
/-- Every negative-side boundary end on the same small circle is positive as
well. -/
theorem saddleNegativeBoundaryEnd_positive_of_center
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius) :
    0 < C (M.saddleNegativeBoundaryEnd b e ρ a) := by
  apply T.localPoint_positive_of_center hcenter
  rw [norm_saddleNegativeBoundaryEndParam b e hρ ha]
  exact hρrad


-- @@ L158-179 verbatim
/-- Slice form of positive-branch sign control. -/
theorem saddlePositiveBranch_sliceSign_positive
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (hindex : M.index = .saddle)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddlePositiveArc b a s)‖ <
      T.radius)
    (hreg : sliceRegular C.cobordism.G (tcoord center + a ^ 2)) :
    0 < (C.sliceSign (tcoord center + a ^ 2) hreg)
      (spacePart (M.saddlePositiveBranch b a s)) := by
  change 0 < C (cobSpaceTime
    (spacePart (M.saddlePositiveBranch b a s))
    (tcoord center + a ^ 2))
  rw [← M.saddlePositiveBranch_time hindex b a s
    (hu.trans_le T.radius_le), spaceTime_spacePart]
  exact T.saddlePositiveBranch_positive_of_center hcenter b a s hu


-- @@ L181-202 verbatim
/-- Slice form on a negative-side branch. -/
theorem saddleNegativeBranch_sliceSign_positive
    {n : ℕ}
    {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (hindex : M.index = .saddle)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddleNegativeArc b a s)‖ <
      T.radius)
    (hreg : sliceRegular C.cobordism.G (tcoord center - a ^ 2)) :
    0 < (C.sliceSign (tcoord center - a ^ 2) hreg)
      (spacePart (M.saddleNegativeBranch b a s)) := by
  change 0 < C (cobSpaceTime
    (spacePart (M.saddleNegativeBranch b a s))
    (tcoord center - a ^ 2))
  rw [← M.saddleNegativeBranch_time hindex b a s
    (hu.trans_le T.radius_le), spaceTime_spacePart]
  exact T.saddleNegativeBranch_positive_of_center hcenter b a s hu


-- @@ L204-204 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L206-206 verbatim
end Submission
