import Submission.ProductionMorseSaddleOrientedArcFlowAdapter


-- @@ L3-12 verbatim
/-!
# Short-flow adapter for production oriented saddle arcs

This file ports the endpoint calculation formerly tied to
`ExactFiniteMorseJetInstallation` to the route-independent production
interfaces.  The first layer only needs a `StandardMorseEventAt`, a compact
time-tamed field, and a local chart-cover statement at the marked critical
end.  It therefore separates the actual ODE calculation from the remaining
production-local chart issue.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
set_option maxHeartbeats 2400000


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function Metric Filter

-- @@ L20-20 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L22-22 verbatim
namespace Submission


-- @@ L24-24 verbatim
variable {n : ℕ}


-- @@ L26-26 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L27-27 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L28-28 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L30-30 verbatim
namespace StandardMorseEventAt


-- @@ L32-32 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L34-101 verbatim
/-- A short positive time flow from a critical-level chart point remains in
the supplied local chart, on the supplied signed branch, and has exactly the
positive Morse level dictated by unit-speed time flow.

Unlike the historical theorem, the local fiber cover is centered at the
actual marked end.  This removes the artificial requirement that a
center-based cover ball already contain the chosen boundary radius. -/
theorem exists_positiveFlowEndpoint_of_localCover
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    {K : Set E'}
    (R : CompactTimeTamedField C.toLevelCobordismData K)
    (hindex : M.index = .saddle)
    (b : SaddleBranch) (i : Fin 2) (u₀ : E₂)
    (hu₀Radius : ‖u₀‖ < M.radius)
    (hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0)
    (hu₀K : M.param u₀ ∈ K)
    {r εcover εbranch A : ℝ}
    (hrRadius : r ≤ M.radius)
    (hcover : ∀ v : E', dist v (M.param u₀) < εcover →
      C.G v = 0 → ∃ u : E₂, ‖u‖ < r ∧ M.param u = v)
    (hbranch : ∀ u : E₂, ‖u‖ < r →
      dist (M.param u) (M.param u₀) < εbranch →
      0 < signedBranch b (u i))
    (hAsafe : A ^ 2 ≤ R.safeTime)
    (hcoverClose : (R.base.bound : ℝ) * A ^ 2 < εcover)
    (hbranchClose : (R.base.bound : ℝ) * A ^ 2 < εbranch) :
    ∃ u : E₂, ‖u‖ < r ∧
      M.param u = R.base.flow (M.param u₀) (A ^ 2) ∧
      0 < signedBranch b (u i) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2 := by
  let v := R.base.flow (M.param u₀) (A ^ 2)
  have hu₀fiber : C.G (M.param u₀) = 0 :=
    M.param_fiber u₀ hu₀Radius
  have hvfiber : C.G v = 0 :=
    R.flow_mem_fiber hu₀fiber (A ^ 2)
  have hdist : dist v (M.param u₀) ≤
      (R.base.bound : ℝ) * A ^ 2 := by
    calc
      dist v (M.param u₀) =
          dist (R.base.flow (M.param u₀) (A ^ 2))
            (R.base.flow (M.param u₀) 0) := by simp [v]
      _ ≤ (R.base.bound : ℝ) * |A ^ 2 - 0| :=
        R.base.dist_flow_self_le (M.param u₀) (A ^ 2) 0
      _ = (R.base.bound : ℝ) * A ^ 2 := by
        rw [sub_zero, abs_of_nonneg (sq_nonneg A)]
  obtain ⟨u, hu, huParam⟩ :=
    hcover v (hdist.trans_lt hcoverClose) hvfiber
  have hparamDist : dist (M.param u) (M.param u₀) < εbranch := by
    rw [huParam]
    exact hdist.trans_lt hbranchClose
  have husign : 0 < signedBranch b (u i) :=
    hbranch u hu hparamDist
  have huRadius : ‖u‖ < M.radius := hu.trans_le hrRadius
  have htflow : tcoord v = tcoord (M.param u₀) + A ^ 2 := by
    exact R.tcoord_flow hu₀K (s := A ^ 2) (by
      rw [abs_of_nonneg (sq_nonneg A)]
      exact hAsafe)
  have htimeEq : tcoord (M.param u) =
      tcoord (M.param u₀) + A ^ 2 := by
    rw [huParam]
    exact htflow
  have htu := M.time_model u huRadius
  have htu₀ := M.time_model u₀ hu₀Radius
  rw [hindex] at htu htu₀
  have huquad : morseQuadratic .saddle (u 0, u 1) = A ^ 2 := by
    rw [htu, htu₀, hquad₀] at htimeEq
    linarith
  exact ⟨u, hu, huParam, husign, huquad⟩


-- @@ L103-167 verbatim
/-- Negative-time counterpart of
`exists_positiveFlowEndpoint_of_localCover`. -/
theorem exists_negativeFlowEndpoint_of_localCover
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    {K : Set E'}
    (R : CompactTimeTamedField C.toLevelCobordismData K)
    (hindex : M.index = .saddle)
    (b : SaddleBranch) (i : Fin 2) (u₀ : E₂)
    (hu₀Radius : ‖u₀‖ < M.radius)
    (hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0)
    (hu₀K : M.param u₀ ∈ K)
    {r εcover εbranch A : ℝ}
    (hrRadius : r ≤ M.radius)
    (hcover : ∀ v : E', dist v (M.param u₀) < εcover →
      C.G v = 0 → ∃ u : E₂, ‖u‖ < r ∧ M.param u = v)
    (hbranch : ∀ u : E₂, ‖u‖ < r →
      dist (M.param u) (M.param u₀) < εbranch →
      0 < signedBranch b (u i))
    (hAsafe : A ^ 2 ≤ R.safeTime)
    (hcoverClose : (R.base.bound : ℝ) * A ^ 2 < εcover)
    (hbranchClose : (R.base.bound : ℝ) * A ^ 2 < εbranch) :
    ∃ u : E₂, ‖u‖ < r ∧
      M.param u = R.base.flow (M.param u₀) (-(A ^ 2)) ∧
      0 < signedBranch b (u i) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2) := by
  let v := R.base.flow (M.param u₀) (-(A ^ 2))
  have hu₀fiber : C.G (M.param u₀) = 0 :=
    M.param_fiber u₀ hu₀Radius
  have hvfiber : C.G v = 0 :=
    R.flow_mem_fiber hu₀fiber (-(A ^ 2))
  have hdist : dist v (M.param u₀) ≤
      (R.base.bound : ℝ) * A ^ 2 := by
    calc
      dist v (M.param u₀) =
          dist (R.base.flow (M.param u₀) (-(A ^ 2)))
            (R.base.flow (M.param u₀) 0) := by simp [v]
      _ ≤ (R.base.bound : ℝ) * |-(A ^ 2) - 0| :=
        R.base.dist_flow_self_le (M.param u₀) (-(A ^ 2)) 0
      _ = (R.base.bound : ℝ) * A ^ 2 := by
        rw [sub_zero, abs_neg, abs_of_nonneg (sq_nonneg A)]
  obtain ⟨u, hu, huParam⟩ :=
    hcover v (hdist.trans_lt hcoverClose) hvfiber
  have hparamDist : dist (M.param u) (M.param u₀) < εbranch := by
    rw [huParam]
    exact hdist.trans_lt hbranchClose
  have husign : 0 < signedBranch b (u i) :=
    hbranch u hu hparamDist
  have huRadius : ‖u‖ < M.radius := hu.trans_le hrRadius
  have htflow : tcoord v = tcoord (M.param u₀) - A ^ 2 := by
    have h := R.tcoord_flow hu₀K
      (s := -(A ^ 2)) (by
        rw [abs_neg, abs_of_nonneg (sq_nonneg A)]
        exact hAsafe)
    linarith
  have htimeEq : tcoord (M.param u) =
      tcoord (M.param u₀) - A ^ 2 := by
    rw [huParam]
    exact htflow
  have htu := M.time_model u huRadius
  have htu₀ := M.time_model u₀ hu₀Radius
  rw [hindex] at htu htu₀
  have huquad : morseQuadratic .saddle (u 0, u 1) = -(A ^ 2) := by
    rw [htu, htu₀, hquad₀] at htimeEq
    linarith
  exact ⟨u, hu, huParam, husign, huquad⟩


-- @@ L169-169 verbatim
namespace EmbeddedShrink


-- @@ L171-235 verbatim
/-- On a compact chart shrink, an ambient neighborhood of a marked parameter
cannot meet the image of the opposite signed branch.  This is the production
counterpart of the old installed-chart branch-neighborhood lemma; the
`FullRadiusSmooth` witness supplies continuity on the whole compact bad set,
while `EmbeddedShrink.param_injOn` supplies the separation. -/
theorem exists_param_signedBranch_neighborhood
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (b : SaddleBranch) (i : Fin 2) (u₀ : E₂)
    {r rInj : ℝ} (_hr : 0 < r) (hrrInj : r < rInj)
    (hrInj : rInj ≤ T.radius)
    (hu₀ : ‖u₀‖ < rInj)
    (hu₀sign : 0 < signedBranch b (u₀ i)) :
    ∃ ε > 0, ∀ u : E₂, ‖u‖ < r →
      dist (M.param u) (M.param u₀) < ε →
      0 < signedBranch b (u i) := by
  let Φ := M.param
  let bad : Set E₂ :=
    closedBall (0 : E₂) r ∩ {u | signedBranch b (u i) ≤ 0}
  have hcoord : Continuous (fun u : E₂ => signedBranch b (u i)) := by
    cases b <;> simp only [signedBranch] <;> fun_prop
  have hbadCompact : IsCompact bad := by
    apply (isCompact_closedBall (0 : E₂) r).inter_right
    exact isClosed_le hcoord continuous_const
  have hbadSub : bad ⊆ ball (0 : E₂) M.radius := by
    intro u hu
    rw [mem_ball, dist_zero_right]
    have hur : ‖u‖ ≤ r := by
      simpa [bad, mem_closedBall, dist_zero_right] using hu.1
    exact (hur.trans_lt hrrInj).trans_le (hrInj.trans T.radius_le)
  have hΦcont : ContinuousOn Φ bad := by
    intro u hu
    exact (H.differentiableAt u
      (by simpa [Φ, mem_ball, dist_zero_right] using
        hbadSub hu)).continuousAt.continuousWithinAt
  have himageCompact : IsCompact (Φ '' bad) :=
    hbadCompact.image_of_continuousOn hΦcont
  have hu₀Ball : u₀ ∈ ball (0 : E₂) T.radius := by
    rw [mem_ball, dist_zero_right]
    exact hu₀.trans_le hrInj
  have hnotmem : Φ u₀ ∉ Φ '' bad := by
    rintro ⟨u, huBad, hu⟩
    have huBall : u ∈ ball (0 : E₂) T.radius := by
      rw [mem_ball, dist_zero_right]
      have hur : ‖u‖ ≤ r := by
        simpa [bad, mem_closedBall, dist_zero_right] using huBad.1
      exact (hur.trans_lt hrrInj).trans_le hrInj
    have heq : u = u₀ := T.param_injOn huBall hu₀Ball hu
    have hbadSign : signedBranch b (u i) ≤ 0 := huBad.2
    rw [heq] at hbadSign
    exact (not_lt_of_ge hbadSign) hu₀sign
  have hnhds : (Φ '' bad)ᶜ ∈ nhds (Φ u₀) :=
    himageCompact.isClosed.isOpen_compl.mem_nhds hnotmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ε, hε, ?_⟩
  intro u hu hdist
  by_contra hnotpos
  have huBad : u ∈ bad := by
    constructor
    · simpa [mem_closedBall, dist_zero_right] using le_of_lt hu
    · exact le_of_not_gt hnotpos
  have himage : Φ u ∈ Φ '' bad := ⟨u, huBad, rfl⟩
  have hballmem : Φ u ∈ ball (Φ u₀) ε := by
    simpa [mem_ball] using hdist
  exact (hball hballmem) himage


-- @@ L237-237 verbatim
end EmbeddedShrink


-- @@ L239-239 verbatim
end StandardMorseEventAt


-- @@ L241-241 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L242-242 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L243-243 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L245-245 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L247-247 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L248-248 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}


-- @@ L250-250 verbatim
local notation "rho" => D.chronologicalSaddleBoundaryRadius t ht

-- @@ L251-251 verbatim
local notation "a" => D.chronologicalWindowRadius t ht


-- @@ L253-253 verbatim
/-! ## A compact injective chart radius around every marked end -/


-- @@ L255-261 verbatim
/-- A single parameter radius strictly between the marked critical-end radius
and the chronological embedded radius. -/
def chronologicalSaddleEndpointParamRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : ℝ :=
  (D.chronologicalSaddleBoundaryRadius t ht +
    (D.chronologicalEventEmbeddedShrink t ht).radius) / 2


-- @@ L263-269 verbatim
theorem chronologicalSaddleBoundaryRadius_lt_endpointParamRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalSaddleBoundaryRadius t ht <
      D.chronologicalSaddleEndpointParamRadius t ht := by
  unfold chronologicalSaddleEndpointParamRadius
  linarith [D.chronologicalSaddleBoundaryRadius_lt_embedded t ht]


-- @@ L271-277 verbatim
theorem chronologicalSaddleEndpointParamRadius_lt_embedded
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalSaddleEndpointParamRadius t ht <
      (D.chronologicalEventEmbeddedShrink t ht).radius := by
  unfold chronologicalSaddleEndpointParamRadius
  linarith [D.chronologicalSaddleBoundaryRadius_lt_embedded t ht]


-- @@ L279-284 verbatim
theorem chronologicalSaddleEndpointParamRadius_pos
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    0 < D.chronologicalSaddleEndpointParamRadius t ht :=
  (D.chronologicalSaddleBoundaryRadius_pos t ht).trans
    (D.chronologicalSaddleBoundaryRadius_lt_endpointParamRadius t ht)


-- @@ L286-292 verbatim
theorem chronologicalSaddleEndpointParamRadius_le_eventRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalSaddleEndpointParamRadius t ht ≤
      (D.position.eventModel t ht).radius :=
  (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht).le.trans
    (D.chronologicalEventEmbeddedShrink t ht).radius_le


-- @@ L294-306 verbatim
theorem norm_chronologicalSaddleCriticalBoundaryEndParam
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    ‖saddleCriticalBoundaryEndParam p
        (D.chronologicalSaddleBoundaryRadius t ht)‖ =
      D.chronologicalSaddleBoundaryRadius t ht := by
  have hrho : 0 < D.chronologicalSaddleBoundaryRadius t ht :=
    D.chronologicalSaddleBoundaryRadius_pos t ht
  have hzero : (0 : ℝ) ^ 2 <
      D.chronologicalSaddleBoundaryRadius t ht ^ 2 := by
    nlinarith [sq_pos_of_pos hrho]
  exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho hzero


-- @@ L308-328 verbatim
theorem chronologicalSaddleCriticalBoundaryEndParam_first_sign
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    0 < signedBranch p.1
      ((saddleCriticalBoundaryEndParam p
        (D.chronologicalSaddleBoundaryRadius t ht)) 0) := by
  let r := D.chronologicalSaddleBoundaryRadius t ht
  have hr : 0 < r := D.chronologicalSaddleBoundaryRadius_pos t ht
  have hσ : 0 < saddleBoundaryParameter r 0 := by
    unfold saddleBoundaryParameter
    exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hr])
  have hsqrtσ : Real.sqrt (saddleBoundaryParameter r 0 ^ 2) =
      saddleBoundaryParameter r 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hσ]
  rcases p with ⟨b, e⟩
  have hσsq : 0 < saddleBoundaryParameter r 0 ^ 2 := sq_pos_of_pos hσ
  cases b <;> cases e <;>
    simpa [saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam, saddlePositiveArc,
      signedBranch, hsqrtσ, abs_of_pos hσ] using hσsq


-- @@ L330-349 verbatim
theorem chronologicalSaddleCriticalBoundaryEndParam_second_sign
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    0 < signedBranch p.2
      ((saddleCriticalBoundaryEndParam p
        (D.chronologicalSaddleBoundaryRadius t ht)) 1) := by
  let r := D.chronologicalSaddleBoundaryRadius t ht
  have hr : 0 < r := D.chronologicalSaddleBoundaryRadius_pos t ht
  have hσ : 0 < saddleBoundaryParameter r 0 := by
    unfold saddleBoundaryParameter
    exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hr])
  have hsqrtσ : Real.sqrt (saddleBoundaryParameter r 0 ^ 2) =
      saddleBoundaryParameter r 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hσ]
  rcases p with ⟨b, e⟩
  cases b <;> cases e <;>
    simpa [saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam, saddlePositiveArc,
      signedBranch, hsqrtσ, abs_of_pos hσ] using hσ


-- @@ L351-351 verbatim
/-! ## Automatic signed-branch neighborhoods at the four critical ends -/


-- @@ L353-376 verbatim
/-- Every marked critical end has an ambient neighborhood which, inside the
common endpoint chart radius, stays in its positive-slice branch label. -/
theorem exists_chronologicalSaddlePositiveBranchNeighborhood
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    ∃ ε > 0, ∀ u : E₂,
      ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht →
      dist ((D.position.eventModel t ht).param u)
          ((D.position.eventModel t ht).param
            (saddleCriticalBoundaryEndParam p
              (D.chronologicalSaddleBoundaryRadius t ht))) < ε →
      0 < signedBranch p.1 (u 0) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  apply T.exists_param_signedBranch_neighborhood H p.1 0
    (saddleCriticalBoundaryEndParam p
      (D.chronologicalSaddleBoundaryRadius t ht))
    (D.chronologicalSaddleEndpointParamRadius_pos t ht)
    (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht)
    (le_refl T.radius)
  · rw [D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p]
    exact D.chronologicalSaddleBoundaryRadius_lt_embedded t ht
  · exact D.chronologicalSaddleCriticalBoundaryEndParam_first_sign t ht p


-- @@ L378-401 verbatim
/-- The same marked critical end, read through the critical pairing switch,
has an ambient neighborhood which stays in its negative-slice branch label. -/
theorem exists_chronologicalSaddleNegativeBranchNeighborhood
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    ∃ ε > 0, ∀ u : E₂,
      ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht →
      dist ((D.position.eventModel t ht).param u)
          ((D.position.eventModel t ht).param
            (saddleCriticalBoundaryEndParam p
              (D.chronologicalSaddleBoundaryRadius t ht))) < ε →
      0 < signedBranch p.2 (u 1) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  apply T.exists_param_signedBranch_neighborhood H p.2 1
    (saddleCriticalBoundaryEndParam p
      (D.chronologicalSaddleBoundaryRadius t ht))
    (D.chronologicalSaddleEndpointParamRadius_pos t ht)
    (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht)
    (le_refl T.radius)
  · rw [D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p]
    exact D.chronologicalSaddleBoundaryRadius_lt_embedded t ht
  · exact D.chronologicalSaddleCriticalBoundaryEndParam_second_sign t ht p


-- @@ L403-408 verbatim
/-- A chosen positive-branch separation radius at a marked critical end. -/
noncomputable def chronologicalSaddlePositiveBranchRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) : ℝ :=
  (D.exists_chronologicalSaddlePositiveBranchNeighborhood t ht p).choose


-- @@ L410-415 verbatim
theorem chronologicalSaddlePositiveBranchRadius_pos
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    0 < D.chronologicalSaddlePositiveBranchRadius t ht p :=
  (D.exists_chronologicalSaddlePositiveBranchNeighborhood t ht p).choose_spec.1


-- @@ L417-430 verbatim
theorem chronologicalSaddlePositiveBranchRadius_spec
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch)
    (u : E₂)
    (hu : ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht)
    (hdist : dist ((D.position.eventModel t ht).param u)
      ((D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam p
          (D.chronologicalSaddleBoundaryRadius t ht))) <
        D.chronologicalSaddlePositiveBranchRadius t ht p) :
    0 < signedBranch p.1 (u 0) :=
  (D.exists_chronologicalSaddlePositiveBranchNeighborhood t ht p).choose_spec.2
    u hu hdist


-- @@ L432-437 verbatim
/-- A chosen negative-branch separation radius at a marked critical end. -/
noncomputable def chronologicalSaddleNegativeBranchRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) : ℝ :=
  (D.exists_chronologicalSaddleNegativeBranchNeighborhood t ht p).choose


-- @@ L439-444 verbatim
theorem chronologicalSaddleNegativeBranchRadius_pos
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    0 < D.chronologicalSaddleNegativeBranchRadius t ht p :=
  (D.exists_chronologicalSaddleNegativeBranchNeighborhood t ht p).choose_spec.1


-- @@ L446-459 verbatim
theorem chronologicalSaddleNegativeBranchRadius_spec
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch)
    (u : E₂)
    (hu : ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht)
    (hdist : dist ((D.position.eventModel t ht).param u)
      ((D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam p
          (D.chronologicalSaddleBoundaryRadius t ht))) <
        D.chronologicalSaddleNegativeBranchRadius t ht p) :
    0 < signedBranch p.2 (u 1) :=
  (D.exists_chronologicalSaddleNegativeBranchNeighborhood t ht p).choose_spec.2
    u hu hdist


-- @@ L461-461 verbatim
/-! ## The remaining production-local fiber cover -/


-- @@ L463-478 verbatim
/-- The precise endpoint-local consequence of the production IFT chart which
the generic `StandardMorseEventAt` interface does not currently expose.

This contract is deliberately centered at each marked critical end.  Its
parameter target radius has already been proved smaller than the embedded
chart radius, so injectivity and both branch neighborhoods are automatic. -/
structure ChronologicalSaddleEndpointLocalFiberCover : Type where
  radius : SaddleBranch × SaddleBranch → ℝ
  radius_pos : ∀ p, 0 < radius p
  cover : ∀ (p : SaddleBranch × SaddleBranch) (v : E'),
    dist v ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) <
        radius p →
    D.signedOutput.cobordism.G v = 0 →
    ∃ u : E₂,
      ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht ∧
      (D.position.eventModel t ht).param u = v


-- @@ L480-497 verbatim
/-- The four scalar inequalities needed to use the already fixed
chronological displacement with the arc-dependent compact time field.  All
topological and chart-separation data have been discharged before this point. -/
structure ChronologicalSaddleFixedWindowShortFlowSmallness
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData rho)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : Prop where
  safe : a ^ 2 ≤
    (D.chronologicalSaddleChosenMateArcTimeField t ht A).safeTime
  cover_close : ∀ p,
    ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.bound : ℝ) *
        a ^ 2 < L.radius p
  positive_branch_close : ∀ p,
    ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.bound : ℝ) *
        a ^ 2 < D.chronologicalSaddlePositiveBranchRadius t ht p
  negative_branch_close : ∀ p,
    ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.bound : ℝ) *
        a ^ 2 < D.chronologicalSaddleNegativeBranchRadius t ht p


-- @@ L499-499 verbatim
/-! ## Endpoint capture from the local cover and scalar smallness -/


-- @@ L501-630 verbatim
/-- The endpoint-local fiber cover plus the four explicit scalar bounds
construct all eight labelled endpoint captures for the canonical chosen-arc
field. -/
noncomputable def chronologicalSaddleChosenMateArcFlowCompatibility_of_endpointLocalCover
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData rho)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (Q : ChronologicalSaddleFixedWindowShortFlowSmallness
      (D := D) (t := t) (ht := ht) A L) :
    ChronologicalSaddleChosenMateArcFlowCompatibility
      (D := D) (t := t) (ht := ht) A := by
  let M := D.position.eventModel t ht
  let R := D.chronologicalSaddleChosenMateArcTimeField t ht A
  refine {
    safe := Q.safe
    positiveEndpoint := ?_
    negativeEndpoint := ?_ }
  · intro p
    let u₀ := saddleCriticalBoundaryEndParam p rho
    have hu₀Radius : ‖u₀‖ < M.radius := by
      calc
        ‖u₀‖ = rho := D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p
        _ < D.chronologicalSaddleEndpointParamRadius t ht :=
          D.chronologicalSaddleBoundaryRadius_lt_endpointParamRadius t ht
        _ ≤ M.radius := D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht
    have hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0 := by
      simp [u₀, saddleCriticalBoundaryEndParam,
        saddlePositiveBoundaryEndParam]
    have hu₀K : M.param u₀ ∈
        D.chronologicalSaddleChosenMateArcCore t ht A := by
      have hmem := D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore
        t ht A p 0
      rw [(A.chosenMateArc p).toPath.source] at hmem
      simpa [M, u₀, saddleCriticalBoundaryEndParam,
        StandardMorseEventAt.saddleCriticalBoundaryEnd,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint] using hmem
    have hex :=
      M.exists_positiveFlowEndpoint_of_localCover R hindex p.1 0 u₀
        hu₀Radius hquad₀ hu₀K
        (r := D.chronologicalSaddleEndpointParamRadius t ht)
        (εcover := L.radius p)
        (εbranch := D.chronologicalSaddlePositiveBranchRadius t ht p)
        (A := a)
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
        (by
          intro v hv hfiber
          apply L.cover p v
          · simpa [M, u₀, saddleCriticalBoundaryEndParam,
              StandardMorseEventAt.saddleCriticalBoundaryEnd,
              StandardMorseEventAt.saddlePositiveBoundaryEnd,
              StandardMorseEventAt.localPoint] using hv
          · exact hfiber)
        (by
          intro v hv hdist
          exact D.chronologicalSaddlePositiveBranchRadius_spec t ht p v hv hdist)
        Q.safe (Q.cover_close p) (Q.positive_branch_close p)
    let u := hex.choose
    have hu := hex.choose_spec.1
    have hend := hex.choose_spec.2.1
    have hsign := hex.choose_spec.2.2.1
    have hquad := hex.choose_spec.2.2.2
    exact {
      param := u
      param_mem := hu.trans_le
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
      endpoint_eq := by
        simpa [u, M, R, u₀, saddleCriticalBoundaryEndParam,
          StandardMorseEventAt.saddleCriticalBoundaryEnd,
          StandardMorseEventAt.saddlePositiveBoundaryEnd,
          StandardMorseEventAt.localPoint] using hend
      branch_sign := hsign
      quadratic := hquad }
  · intro p
    let u₀ := saddleCriticalBoundaryEndParam p rho
    have hu₀Radius : ‖u₀‖ < M.radius := by
      calc
        ‖u₀‖ = rho := D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p
        _ < D.chronologicalSaddleEndpointParamRadius t ht :=
          D.chronologicalSaddleBoundaryRadius_lt_endpointParamRadius t ht
        _ ≤ M.radius := D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht
    have hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0 := by
      simp [u₀, saddleCriticalBoundaryEndParam,
        saddlePositiveBoundaryEndParam]
    have hu₀K : M.param u₀ ∈
        D.chronologicalSaddleChosenMateArcCore t ht A := by
      have hmem := D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore
        t ht A p 0
      rw [(A.chosenMateArc p).toPath.source] at hmem
      simpa [M, u₀, saddleCriticalBoundaryEndParam,
        StandardMorseEventAt.saddleCriticalBoundaryEnd,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint] using hmem
    have hex :=
      M.exists_negativeFlowEndpoint_of_localCover R hindex p.2 1 u₀
        hu₀Radius hquad₀ hu₀K
        (r := D.chronologicalSaddleEndpointParamRadius t ht)
        (εcover := L.radius p)
        (εbranch := D.chronologicalSaddleNegativeBranchRadius t ht p)
        (A := a)
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
        (by
          intro v hv hfiber
          apply L.cover p v
          · simpa [M, u₀, saddleCriticalBoundaryEndParam,
              StandardMorseEventAt.saddleCriticalBoundaryEnd,
              StandardMorseEventAt.saddlePositiveBoundaryEnd,
              StandardMorseEventAt.localPoint] using hv
          · exact hfiber)
        (by
          intro v hv hdist
          exact D.chronologicalSaddleNegativeBranchRadius_spec t ht p v hv hdist)
        Q.safe (Q.cover_close p) (Q.negative_branch_close p)
    let u := hex.choose
    have hu := hex.choose_spec.1
    have hend := hex.choose_spec.2.1
    have hsign := hex.choose_spec.2.2.1
    have hquad := hex.choose_spec.2.2.2
    exact {
      param := u
      param_mem := hu.trans_le
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
      endpoint_eq := by
        simpa [u, M, R, u₀, saddleCriticalBoundaryEndParam,
          StandardMorseEventAt.saddleCriticalBoundaryEnd,
          StandardMorseEventAt.saddlePositiveBoundaryEnd,
          StandardMorseEventAt.localPoint] using hend
      branch_sign := hsign
      quadratic := hquad }


-- @@ L632-632 verbatim
/-! ## A common automatically small displacement -/


-- @@ L634-641 verbatim
/-- Minimum of a real-valued quantity over the four labelled saddle ends,
written explicitly so this layer does not need a global `Fintype` instance for
`SaddleBranch`. -/
def saddleFourEndMin
    (f : SaddleBranch × SaddleBranch → ℝ) : ℝ :=
  min (f (.positive, .positive))
    (min (f (.positive, .negative))
      (min (f (.negative, .positive)) (f (.negative, .negative))))


-- @@ L643-648 verbatim
theorem saddleFourEndMin_pos
    {f : SaddleBranch × SaddleBranch → ℝ}
    (hf : ∀ p, 0 < f p) :
    0 < saddleFourEndMin f := by
  unfold saddleFourEndMin
  exact lt_min (hf _) (lt_min (hf _) (lt_min (hf _) (hf _)))


-- @@ L650-656 verbatim
theorem saddleFourEndMin_le
    (f : SaddleBranch × SaddleBranch → ℝ)
    (p : SaddleBranch × SaddleBranch) :
    saddleFourEndMin f ≤ f p := by
  rcases p with ⟨b, e⟩
  cases b <;> cases e <;>
    simp [saddleFourEndMin]


-- @@ L658-670 verbatim
/-- One positive ambient margin which is below the endpoint-local cover and
both signed-branch separation radii at all four ends. -/
def chronologicalSaddleEndpointFlowMargin
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : ℝ :=
  min (saddleFourEndMin L.radius)
    (min
      (saddleFourEndMin
        (D.chronologicalSaddlePositiveBranchRadius t ht))
      (saddleFourEndMin
        (D.chronologicalSaddleNegativeBranchRadius t ht)))


-- @@ L672-685 verbatim
theorem chronologicalSaddleEndpointFlowMargin_pos
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    0 < D.chronologicalSaddleEndpointFlowMargin t ht L := by
  unfold chronologicalSaddleEndpointFlowMargin
  exact lt_min
    (saddleFourEndMin_pos L.radius_pos)
    (lt_min
      (saddleFourEndMin_pos
        (D.chronologicalSaddlePositiveBranchRadius_pos t ht))
      (saddleFourEndMin_pos
        (D.chronologicalSaddleNegativeBranchRadius_pos t ht)))


-- @@ L687-694 verbatim
theorem chronologicalSaddleEndpointFlowMargin_le_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleEndpointFlowMargin t ht L ≤ L.radius p :=
  (min_le_left _ _).trans (saddleFourEndMin_le L.radius p)


-- @@ L696-707 verbatim
theorem chronologicalSaddleEndpointFlowMargin_le_positiveBranch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleEndpointFlowMargin t ht L ≤
      D.chronologicalSaddlePositiveBranchRadius t ht p :=
  (min_le_right _ _).trans
    ((min_le_left _ _).trans
      (saddleFourEndMin_le
        (D.chronologicalSaddlePositiveBranchRadius t ht) p))


-- @@ L709-720 verbatim
theorem chronologicalSaddleEndpointFlowMargin_le_negativeBranch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleEndpointFlowMargin t ht L ≤
      D.chronologicalSaddleNegativeBranchRadius t ht p :=
  (min_le_right _ _).trans
    ((min_le_right _ _).trans
      (saddleFourEndMin_le
        (D.chronologicalSaddleNegativeBranchRadius t ht) p))


-- @@ L722-742 verbatim
/-- A displacement chosen after the actual mate-arc field.  It is smaller
than the fixed chronological radius and simultaneously satisfies the field's
safe time and all twelve endpoint cover/branch inequalities. -/
structure ChronologicalSaddleShortFlowScale
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData rho)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : Type where
  scale : ℝ
  scale_pos : 0 < scale
  scale_lt_window : scale < a
  safe : scale ^ 2 ≤
    (D.chronologicalSaddleChosenMateArcTimeField t ht A).safeTime
  cover_close : ∀ p,
    ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.bound : ℝ) *
        scale ^ 2 < L.radius p
  positive_branch_close : ∀ p,
    ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.bound : ℝ) *
        scale ^ 2 < D.chronologicalSaddlePositiveBranchRadius t ht p
  negative_branch_close : ∀ p,
    ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.bound : ℝ) *
        scale ^ 2 < D.chronologicalSaddleNegativeBranchRadius t ht p


-- @@ L744-800 verbatim
theorem nonempty_chronologicalSaddleShortFlowScale
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    Nonempty (ChronologicalSaddleShortFlowScale
      (D := D) (t := t) (ht := ht) A L) := by
  let R := D.chronologicalSaddleChosenMateArcTimeField t ht A
  let m := D.chronologicalSaddleEndpointFlowMargin t ht L
  let B : ℝ := (R.base.bound : ℝ)
  have hsafeN : {x : ℝ | x ^ 2 < R.safeTime} ∈ nhds 0 := by
    have hlim : Tendsto (fun x : ℝ => x ^ 2) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun x : ℝ => x ^ 2) 0 :=
        continuousAt_id.pow 2
      simpa using hcont.tendsto
    exact hlim (Iio_mem_nhds R.safeTime_pos)
  have hmarginN : {x : ℝ | B * x ^ 2 < m} ∈ nhds 0 := by
    have hlim : Tendsto (fun x : ℝ => B * x ^ 2) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun x : ℝ => B * x ^ 2) 0 :=
        continuousAt_const.mul (continuousAt_id.pow 2)
      simpa using hcont.tendsto
    exact hlim (Iio_mem_nhds
      (D.chronologicalSaddleEndpointFlowMargin_pos t ht L))
  have hgood : {x : ℝ | x ^ 2 < R.safeTime ∧ B * x ^ 2 < m} ∈ nhds 0 :=
    Filter.inter_mem hsafeN hmarginN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let c := min (D.chronologicalWindowRadius t ht) δ
  let b := c / 2
  have hc : 0 < c := lt_min
    (D.chronologicalWindowRadius_pos t ht) hδ
  have hb : 0 < b := div_pos hc (by norm_num)
  have hbc : b < c := by dsimp [b]; linarith
  have hba : b < D.chronologicalWindowRadius t ht :=
    hbc.trans_le (min_le_left _ _)
  have hbδ : dist b (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hb]
    exact hbc.trans_le (min_le_right _ _)
  have hbGood := hball hbδ
  refine ⟨{
    scale := b
    scale_pos := hb
    scale_lt_window := hba
    safe := hbGood.1.le
    cover_close := ?_
    positive_branch_close := ?_
    negative_branch_close := ?_ }⟩
  · intro p
    exact hbGood.2.trans_le
      (D.chronologicalSaddleEndpointFlowMargin_le_cover t ht L p)
  · intro p
    exact hbGood.2.trans_le
      (D.chronologicalSaddleEndpointFlowMargin_le_positiveBranch t ht L p)
  · intro p
    exact hbGood.2.trans_le
      (D.chronologicalSaddleEndpointFlowMargin_le_negativeBranch t ht L p)


-- @@ L802-812 verbatim
/-- Canonical choice of the common small displacement. -/
noncomputable def chronologicalSaddleShortFlowScale
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    ChronologicalSaddleShortFlowScale
      (D := D) (t := t) (ht := ht) A L :=
  (nonempty_chronologicalSaddleShortFlowScale D t ht A L).some


-- @@ L814-814 verbatim
/-! ## Endpoint capture at the automatically selected displacement -/


-- @@ L816-827 verbatim
structure ChronologicalSaddlePositiveEndpointCaptureAt
    {K : Set E'}
    (R : CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData K)
    (b : ℝ) (p : SaddleBranch × SaddleBranch) : Type where
  param : E₂
  param_mem : ‖param‖ < (D.position.eventModel t ht).radius
  endpoint_eq : (D.position.eventModel t ht).param param =
    R.base.flow
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) (b ^ 2)
  branch_sign : 0 < signedBranch p.1 (param 0)
  quadratic : morseQuadratic .saddle (param 0, param 1) = b ^ 2


-- @@ L829-840 verbatim
structure ChronologicalSaddleNegativeEndpointCaptureAt
    {K : Set E'}
    (R : CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData K)
    (b : ℝ) (p : SaddleBranch × SaddleBranch) : Type where
  param : E₂
  param_mem : ‖param‖ < (D.position.eventModel t ht).radius
  endpoint_eq : (D.position.eventModel t ht).param param =
    R.base.flow
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) (-(b ^ 2))
  branch_sign : 0 < signedBranch p.2 (param 1)
  quadratic : morseQuadratic .saddle (param 0, param 1) = -(b ^ 2)


-- @@ L842-858 verbatim
/-- The automatically small flow scale together with all eight endpoint
captures.  The compact core, field, and safe inequalities are the canonical
ones already constructed above. -/
structure ChronologicalSaddleShortMateArcFlowData
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData rho)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : Type where
  positiveEndpoint : ∀ p,
    ChronologicalSaddlePositiveEndpointCaptureAt
      (D := D) (t := t) (ht := ht)
      (D.chronologicalSaddleChosenMateArcTimeField t ht A)
      (D.chronologicalSaddleShortFlowScale t ht A L).scale p
  negativeEndpoint : ∀ p,
    ChronologicalSaddleNegativeEndpointCaptureAt
      (D := D) (t := t) (ht := ht)
      (D.chronologicalSaddleChosenMateArcTimeField t ht A)
      (D.chronologicalSaddleShortFlowScale t ht A L).scale p


-- @@ L860-978 verbatim
/-- The local-cover theorem constructs all short-scale endpoint captures; no
additional scalar assumption is needed. -/
noncomputable def chronologicalSaddleShortMateArcFlowData_of_endpointLocalCover
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData rho)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L := by
  let M := D.position.eventModel t ht
  let R := D.chronologicalSaddleChosenMateArcTimeField t ht A
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  refine {
    positiveEndpoint := ?_
    negativeEndpoint := ?_ }
  · intro p
    let u₀ := saddleCriticalBoundaryEndParam p rho
    have hu₀Radius : ‖u₀‖ < M.radius := by
      calc
        ‖u₀‖ = rho := D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p
        _ < D.chronologicalSaddleEndpointParamRadius t ht :=
          D.chronologicalSaddleBoundaryRadius_lt_endpointParamRadius t ht
        _ ≤ M.radius := D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht
    have hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0 := by
      simp [u₀, saddleCriticalBoundaryEndParam,
        saddlePositiveBoundaryEndParam]
    have hu₀K : M.param u₀ ∈
        D.chronologicalSaddleChosenMateArcCore t ht A := by
      have hmem := D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore
        t ht A p 0
      rw [(A.chosenMateArc p).toPath.source] at hmem
      simpa [M, u₀, saddleCriticalBoundaryEndParam,
        StandardMorseEventAt.saddleCriticalBoundaryEnd,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint] using hmem
    have hex :=
      M.exists_positiveFlowEndpoint_of_localCover R hindex p.1 0 u₀
        hu₀Radius hquad₀ hu₀K
        (r := D.chronologicalSaddleEndpointParamRadius t ht)
        (εcover := L.radius p)
        (εbranch := D.chronologicalSaddlePositiveBranchRadius t ht p)
        (A := Q.scale)
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
        (by
          intro v hv hfiber
          apply L.cover p v
          · simpa [M, u₀, saddleCriticalBoundaryEndParam,
              StandardMorseEventAt.saddleCriticalBoundaryEnd,
              StandardMorseEventAt.saddlePositiveBoundaryEnd,
              StandardMorseEventAt.localPoint] using hv
          · exact hfiber)
        (by
          intro v hv hdist
          exact D.chronologicalSaddlePositiveBranchRadius_spec t ht p v hv hdist)
        Q.safe (Q.cover_close p) (Q.positive_branch_close p)
    let u := hex.choose
    exact {
      param := u
      param_mem := hex.choose_spec.1.trans_le
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
      endpoint_eq := by
        simpa [u, M, R, Q, u₀, saddleCriticalBoundaryEndParam,
          StandardMorseEventAt.saddleCriticalBoundaryEnd,
          StandardMorseEventAt.saddlePositiveBoundaryEnd,
          StandardMorseEventAt.localPoint] using hex.choose_spec.2.1
      branch_sign := hex.choose_spec.2.2.1
      quadratic := hex.choose_spec.2.2.2 }
  · intro p
    let u₀ := saddleCriticalBoundaryEndParam p rho
    have hu₀Radius : ‖u₀‖ < M.radius := by
      calc
        ‖u₀‖ = rho := D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p
        _ < D.chronologicalSaddleEndpointParamRadius t ht :=
          D.chronologicalSaddleBoundaryRadius_lt_endpointParamRadius t ht
        _ ≤ M.radius := D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht
    have hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0 := by
      simp [u₀, saddleCriticalBoundaryEndParam,
        saddlePositiveBoundaryEndParam]
    have hu₀K : M.param u₀ ∈
        D.chronologicalSaddleChosenMateArcCore t ht A := by
      have hmem := D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore
        t ht A p 0
      rw [(A.chosenMateArc p).toPath.source] at hmem
      simpa [M, u₀, saddleCriticalBoundaryEndParam,
        StandardMorseEventAt.saddleCriticalBoundaryEnd,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint] using hmem
    have hex :=
      M.exists_negativeFlowEndpoint_of_localCover R hindex p.2 1 u₀
        hu₀Radius hquad₀ hu₀K
        (r := D.chronologicalSaddleEndpointParamRadius t ht)
        (εcover := L.radius p)
        (εbranch := D.chronologicalSaddleNegativeBranchRadius t ht p)
        (A := Q.scale)
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
        (by
          intro v hv hfiber
          apply L.cover p v
          · simpa [M, u₀, saddleCriticalBoundaryEndParam,
              StandardMorseEventAt.saddleCriticalBoundaryEnd,
              StandardMorseEventAt.saddlePositiveBoundaryEnd,
              StandardMorseEventAt.localPoint] using hv
          · exact hfiber)
        (by
          intro v hv hdist
          exact D.chronologicalSaddleNegativeBranchRadius_spec t ht p v hv hdist)
        Q.safe (Q.cover_close p) (Q.negative_branch_close p)
    let u := hex.choose
    exact {
      param := u
      param_mem := hex.choose_spec.1.trans_le
        (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
      endpoint_eq := by
        simpa [u, M, R, Q, u₀, saddleCriticalBoundaryEndParam,
          StandardMorseEventAt.saddleCriticalBoundaryEnd,
          StandardMorseEventAt.saddlePositiveBoundaryEnd,
          StandardMorseEventAt.localPoint] using hex.choose_spec.2.1
      branch_sign := hex.choose_spec.2.2.1
      quadratic := hex.choose_spec.2.2.2 }


-- @@ L980-980 verbatim
/-! ## The two automatically selected regular slices -/


-- @@ L982-990 verbatim
def chronologicalSaddleShortBeforeTime
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : ℝ :=
  tcoord (D.position.eventCenter t ht) -
    (D.chronologicalSaddleShortFlowScale t ht A L).scale ^ 2


-- @@ L992-1000 verbatim
def chronologicalSaddleShortAfterTime
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : ℝ :=
  tcoord (D.position.eventCenter t ht) +
    (D.chronologicalSaddleShortFlowScale t ht A L).scale ^ 2


-- @@ L1002-1024 verbatim
private theorem eventTime_eq_of_mem_chronologicalBracket
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    {s : ℝ} (hsEvent : s ∈ D.position.eventTimes)
    (hs : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after) :
    s = t := by
  let v := D.position.eventCenter s hsEvent
  have hvCritical : v ∈ timeCritical D.signedOutput.cobordism.G :=
    (D.position.eventCenter_mem_coreCriticalPoints s hsEvent).1
  have hvInterval : tcoord v ∈
      Icc (D.position.eventBracket t ht).before
        (D.position.eventBracket t ht).after := by
    change tcoord (D.position.eventCenter s hsEvent) ∈ _
    rw [D.position.eventCenter_time s hsEvent]
    exact hs
  have hvEq : v = D.position.eventCenter t ht :=
    (D.position.eventBracket t ht).isolates v hvCritical hvInterval
  calc
    s = tcoord (D.position.eventCenter s hsEvent) :=
      (D.position.eventCenter_time s hsEvent).symm
    _ = tcoord (D.position.eventCenter t ht) := congrArg tcoord hvEq
    _ = t := D.position.eventCenter_time t ht


-- @@ L1026-1037 verbatim
theorem chronologicalSaddleShortScale_sq_lt_window_sq
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleShortFlowScale t ht A L).scale ^ 2 <
      D.chronologicalWindowRadius t ht ^ 2 := by
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  exact (sq_lt_sq₀ Q.scale_pos.le
    (D.chronologicalWindowRadius_pos t ht).le).2 Q.scale_lt_window


-- @@ L1039-1068 verbatim
theorem regularSlab_chronologicalSaddleShortAfter_to_window
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    regularSlab D.signedOutput.cobordism.G
      (D.chronologicalSaddleShortAfterTime t ht A L)
      (D.chronologicalAfterTime t ht) := by
  rw [D.position.regularSlab_iff_avoid_eventTimes]
  intro s hsEvent hs
  have hcenterShort : tcoord (D.position.eventCenter t ht) <
      D.chronologicalSaddleShortAfterTime t ht A L := by
    rw [chronologicalSaddleShortAfterTime]
    exact lt_add_of_pos_right _
      (sq_pos_of_pos
        (D.chronologicalSaddleShortFlowScale t ht A L).scale_pos)
  have hsBracket : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after := by
    constructor
    · exact (D.position.eventBracket t ht).before_lt.le.trans
        (hcenterShort.le.trans hs.1)
    · exact hs.2.trans
        (D.chronologicalAfterTime_mem_bracket t ht).2.le
  have hst : s = t :=
    D.eventTime_eq_of_mem_chronologicalBracket t ht hsEvent hsBracket
  have htShort : t < D.chronologicalSaddleShortAfterTime t ht A L :=
    (D.position.eventCenter_time t ht).symm.trans_lt hcenterShort
  exact (not_le_of_gt htShort) (hst ▸ hs.1)


-- @@ L1070-1098 verbatim
theorem regularSlab_window_to_chronologicalSaddleShortBefore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    regularSlab D.signedOutput.cobordism.G
      (D.chronologicalBeforeTime t ht)
      (D.chronologicalSaddleShortBeforeTime t ht A L) := by
  rw [D.position.regularSlab_iff_avoid_eventTimes]
  intro s hsEvent hs
  have hshortCenter : D.chronologicalSaddleShortBeforeTime t ht A L <
      tcoord (D.position.eventCenter t ht) := by
    rw [chronologicalSaddleShortBeforeTime]
    exact sub_lt_self _
      (sq_pos_of_pos
        (D.chronologicalSaddleShortFlowScale t ht A L).scale_pos)
  have hsBracket : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after := by
    constructor
    · exact (D.chronologicalBeforeTime_mem_bracket t ht).1.le.trans hs.1
    · exact hs.2.trans
        (hshortCenter.le.trans (D.position.eventBracket t ht).lt_after.le)
  have hst : s = t :=
    D.eventTime_eq_of_mem_chronologicalBracket t ht hsEvent hsBracket
  have hshortT : D.chronologicalSaddleShortBeforeTime t ht A L < t :=
    hshortCenter.trans_eq (D.position.eventCenter_time t ht)
  exact (not_le_of_gt hshortT) (hst ▸ hs.2)


-- @@ L1100-1114 verbatim
theorem chronologicalSaddleShortAfterTime_regular
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    sliceRegular D.signedOutput.cobordism.G
      (D.chronologicalSaddleShortAfterTime t ht A L) :=
  (D.regularSlab_chronologicalSaddleShortAfter_to_window t ht A L).sliceRegular
    ⟨le_rfl, by
      rw [chronologicalSaddleShortAfterTime, chronologicalAfterTime]
      simpa [add_comm] using add_le_add_left
        (D.chronologicalSaddleShortScale_sq_lt_window_sq t ht A L).le
        (tcoord (D.position.eventCenter t ht))⟩


-- @@ L1116-1129 verbatim
theorem chronologicalSaddleShortBeforeTime_regular
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    sliceRegular D.signedOutput.cobordism.G
      (D.chronologicalSaddleShortBeforeTime t ht A L) :=
  (D.regularSlab_window_to_chronologicalSaddleShortBefore t ht A L).sliceRegular
    ⟨by
      rw [chronologicalBeforeTime, chronologicalSaddleShortBeforeTime]
      exact sub_le_sub_left
        (D.chronologicalSaddleShortScale_sq_lt_window_sq t ht A L).le _, le_rfl⟩


-- @@ L1131-1140 verbatim
def chronologicalSaddleShortAfterSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt D.signedOutput.cobordism.toLevelCobordismData
    (D.chronologicalSaddleShortAfterTime t ht A L)
    (D.chronologicalSaddleShortAfterTime_regular t ht A L)


-- @@ L1142-1151 verbatim
def chronologicalSaddleShortBeforeSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt D.signedOutput.cobordism.toLevelCobordismData
    (D.chronologicalSaddleShortBeforeTime t ht A L)
    (D.chronologicalSaddleShortBeforeTime_regular t ht A L)


-- @@ L1153-1161 verbatim
noncomputable def chronologicalSaddleShortAfterField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    TamedField (D.chronologicalSaddleShortAfterSlice t ht A L) :=
  (D.chronologicalSaddleShortAfterSlice t ht A L).exists_tamedField.some


-- @@ L1163-1171 verbatim
noncomputable def chronologicalSaddleShortBeforeField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    TamedField (D.chronologicalSaddleShortBeforeSlice t ht A L) :=
  (D.chronologicalSaddleShortBeforeSlice t ht A L).exists_tamedField.some


-- @@ L1173-1192 verbatim
noncomputable def chronologicalSaddleShortPositiveOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (branch : SaddleBranch) :
    (D.chronologicalSaddleShortAfterField t ht A L).OrbitIndex := by
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  let T := D.chronologicalEventEmbeddedShrink t ht
  apply T.saddlePositiveBranchOrbitIndex hindex branch
    (D.chronologicalSaddleBoundaryRadius t ht) Q.scale
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
  · exact (sq_lt_sq₀ Q.scale_pos.le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
      (Q.scale_lt_window.trans
        (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht))
  · exact D.chronologicalSaddleBoundaryRadius_lt_embedded t ht


-- @@ L1194-1213 verbatim
noncomputable def chronologicalSaddleShortNegativeOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (branch : SaddleBranch) :
    (D.chronologicalSaddleShortBeforeField t ht A L).OrbitIndex := by
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  let T := D.chronologicalEventEmbeddedShrink t ht
  apply T.saddleNegativeBranchOrbitIndex hindex branch
    (D.chronologicalSaddleBoundaryRadius t ht) Q.scale
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
  · exact (sq_lt_sq₀ Q.scale_pos.le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
      (Q.scale_lt_window.trans
        (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht))
  · exact D.chronologicalSaddleBoundaryRadius_lt_embedded t ht


-- @@ L1215-1215 verbatim
namespace ChronologicalSaddleShortMateArcFlowData


-- @@ L1217-1219 verbatim
variable {A :
  (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
    (D.chronologicalSaddleBoundaryRadius t ht)}

-- @@ L1220-1221 verbatim
variable {L : ChronologicalSaddleEndpointLocalFiberCover
  (D := D) (t := t) (ht := ht)}

-- @@ L1222-1222 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L1224-1254 verbatim
theorem positiveEndpoint_mem_shortBranchOrbit
    (F : ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L)
    (p : SaddleBranch × SaddleBranch) :
    spacePart
        ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.flow
          ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho)
          ((D.chronologicalSaddleShortFlowScale t ht A L).scale ^ 2)) ∈
      ((D.chronologicalSaddleShortPositiveOrbit t ht hindex A L p.1 :
        (D.chronologicalSaddleShortAfterField t ht A L).OrbitIndex) : Set E₁) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  obtain ⟨u, hu, hend, hsign, hquad⟩ := F.positiveEndpoint p
  have hmem := T.saddlePositiveParam_mem_branch_orbit_full H hindex p.1
    rho Q.scale u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    ((sq_lt_sq₀ Q.scale_pos.le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
      (Q.scale_lt_window.trans
        (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)))
    hu
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalSaddleShortAfterTime_regular t ht A L)
    (D.chronologicalSaddleShortAfterField t ht A L)
  rw [hend] at hmem
  simpa [M, T, Q, chronologicalSaddleShortPositiveOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchOrbitIndex]
    using hmem


-- @@ L1256-1286 verbatim
theorem negativeEndpoint_mem_shortBranchOrbit
    (F : ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L)
    (p : SaddleBranch × SaddleBranch) :
    spacePart
        ((D.chronologicalSaddleChosenMateArcTimeField t ht A).base.flow
          ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho)
          (-((D.chronologicalSaddleShortFlowScale t ht A L).scale ^ 2))) ∈
      ((D.chronologicalSaddleShortNegativeOrbit t ht hindex A L p.2 :
        (D.chronologicalSaddleShortBeforeField t ht A L).OrbitIndex) : Set E₁) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  obtain ⟨u, hu, hend, hsign, hquad⟩ := F.negativeEndpoint p
  have hmem := T.saddleNegativeParam_mem_branch_orbit_full H hindex p.2
    rho Q.scale u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    ((sq_lt_sq₀ Q.scale_pos.le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
      (Q.scale_lt_window.trans
        (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)))
    hu
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalSaddleShortBeforeTime_regular t ht A L)
    (D.chronologicalSaddleShortBeforeField t ht A L)
  rw [hend] at hmem
  simpa [M, T, Q, chronologicalSaddleShortNegativeOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchOrbitIndex]
    using hmem


-- @@ L1288-1315 verbatim
theorem positiveMateShortOrbit_eq
    (F : ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L)
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleShortPositiveOrbit t ht hindex A L p.1 =
      D.chronologicalSaddleShortPositiveOrbit t ht hindex A L (A.mate p).1 := by
  let gamma := A.chosenMateArc p
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  let R := D.chronologicalSaddleChosenMateArcTimeField t ht A
  let V := D.chronologicalSaddleShortAfterField t ht A L
  have hsafe : |Q.scale ^ 2| ≤ R.safeTime := by
    rw [abs_of_nonneg (sq_nonneg Q.scale)]
    exact Q.safe
  have hflow := R.flowSlicePath_endpoints_mem_same_orbit
    gamma.toPath
    (D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore t ht A p)
    (fun u => (gamma.mem_exterior u).2.1)
    (fun u => (gamma.mem_exterior u).1)
    hsafe (D.chronologicalSaddleShortAfterTime_regular t ht A L) V
  have hmem₁ := F.positiveEndpoint_mem_shortBranchOrbit
    (hindex := hindex) p
  have hmem₂ := F.positiveEndpoint_mem_shortBranchOrbit
    (hindex := hindex) (A.mate p)
  have heq₁ := V.orbit_eq_of_mem hmem₁
  have heq₂ := V.orbit_eq_of_mem hmem₂
  have heqflow := V.orbit_eq_of_mem hflow
  apply Subtype.ext
  exact heq₁.symm.trans (heqflow.symm.trans heq₂)


-- @@ L1317-1347 verbatim
theorem negativeMateShortOrbit_eq
    (F : ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L)
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleShortNegativeOrbit t ht hindex A L p.2 =
      D.chronologicalSaddleShortNegativeOrbit t ht hindex A L (A.mate p).2 := by
  let gamma := A.chosenMateArc p
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  let R := D.chronologicalSaddleChosenMateArcTimeField t ht A
  let V := D.chronologicalSaddleShortBeforeField t ht A L
  have hsafe : |-(Q.scale ^ 2)| ≤ R.safeTime := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg Q.scale)]
    exact Q.safe
  have hflow := R.flowSlicePath_endpoints_mem_same_orbit
    gamma.toPath
    (D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore t ht A p)
    (fun u => (gamma.mem_exterior u).2.1)
    (fun u => (gamma.mem_exterior u).1)
    hsafe (by
      simpa only [chronologicalSaddleShortBeforeTime, sub_eq_add_neg,
        FramedLevelCobordism.toLevelCobordismData] using
        D.chronologicalSaddleShortBeforeTime_regular t ht A L) V
  have hmem₁ := F.negativeEndpoint_mem_shortBranchOrbit
    (hindex := hindex) p
  have hmem₂ := F.negativeEndpoint_mem_shortBranchOrbit
    (hindex := hindex) (A.mate p)
  have heq₁ := V.orbit_eq_of_mem hmem₁
  have heq₂ := V.orbit_eq_of_mem hmem₂
  have heqflow := V.orbit_eq_of_mem hflow
  apply Subtype.ext
  exact heq₁.symm.trans (heqflow.symm.trans heq₂)


-- @@ L1349-1349 verbatim
end ChronologicalSaddleShortMateArcFlowData


-- @@ L1351-1351 verbatim
/-! ## Regular component transport from the short slices to the fixed window -/


-- @@ L1353-1364 verbatim
noncomputable def chronologicalSaddleShortAfterToWindowSlabField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    SlabTamedField D.signedOutput.cobordism.toLevelCobordismData
      (D.chronologicalSaddleShortAfterTime t ht A L)
      (D.chronologicalAfterTime t ht) :=
  (exists_slabTamedField D.signedOutput.cobordism.toLevelCobordismData
    (D.regularSlab_chronologicalSaddleShortAfter_to_window t ht A L)).some


-- @@ L1366-1377 verbatim
noncomputable def chronologicalSaddleWindowToShortBeforeSlabField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    SlabTamedField D.signedOutput.cobordism.toLevelCobordismData
      (D.chronologicalBeforeTime t ht)
      (D.chronologicalSaddleShortBeforeTime t ht A L) :=
  (exists_slabTamedField D.signedOutput.cobordism.toLevelCobordismData
    (D.regularSlab_window_to_chronologicalSaddleShortBefore t ht A L)).some


-- @@ L1379-1403 verbatim
noncomputable def chronologicalSaddleShortAfterToWindowOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleShortAfterField t ht A L).OrbitIndex ≃
      (D.chronologicalAfterField t ht).OrbitIndex := by
  let hreg := D.regularSlab_chronologicalSaddleShortAfter_to_window t ht A L
  let W := D.chronologicalSaddleShortAfterToWindowSlabField t ht A L
  have hs : D.chronologicalSaddleShortAfterTime t ht A L ∈
      Icc (D.chronologicalSaddleShortAfterTime t ht A L)
        (D.chronologicalAfterTime t ht) :=
    ⟨le_rfl, by
      rw [chronologicalSaddleShortAfterTime, chronologicalAfterTime]
      simpa [add_comm] using add_le_add_left
        (D.chronologicalSaddleShortScale_sq_lt_window_sq t ht A L).le
        (tcoord (D.position.eventCenter t ht))⟩
  have ha : D.chronologicalAfterTime t ht ∈
      Icc (D.chronologicalSaddleShortAfterTime t ht A L)
        (D.chronologicalAfterTime t ht) := ⟨hs.2, le_rfl⟩
  exact W.sliceOrbitEquiv hreg hs ha
    (D.chronologicalSaddleShortAfterField t ht A L)
    (D.chronologicalAfterField t ht)


-- @@ L1405-1428 verbatim
noncomputable def chronologicalSaddleShortBeforeToWindowOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleShortBeforeField t ht A L).OrbitIndex ≃
      (D.chronologicalBeforeField t ht).OrbitIndex := by
  let hreg := D.regularSlab_window_to_chronologicalSaddleShortBefore t ht A L
  let W := D.chronologicalSaddleWindowToShortBeforeSlabField t ht A L
  have ha : D.chronologicalBeforeTime t ht ∈
      Icc (D.chronologicalBeforeTime t ht)
        (D.chronologicalSaddleShortBeforeTime t ht A L) :=
    ⟨le_rfl, by
      rw [chronologicalBeforeTime, chronologicalSaddleShortBeforeTime]
      exact sub_le_sub_left
        (D.chronologicalSaddleShortScale_sq_lt_window_sq t ht A L).le _⟩
  have hs : D.chronologicalSaddleShortBeforeTime t ht A L ∈
      Icc (D.chronologicalBeforeTime t ht)
        (D.chronologicalSaddleShortBeforeTime t ht A L) := ⟨ha.2, le_rfl⟩
  exact W.sliceOrbitEquiv hreg hs ha
    (D.chronologicalSaddleShortBeforeField t ht A L)
    (D.chronologicalBeforeField t ht)


-- @@ L1430-1433 verbatim
/-! The local hyperbola branch varies continuously with the radius.  Flowing
that varying point to the fixed target slice gives a path in one target
component, which identifies the transported short branch with the original
chronological branch. -/

-- @@ L1434-1606 verbatim
theorem chronologicalSaddleShortAfterToWindowOrbitEquiv_branch
    {A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)}
    {L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)}
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (branch : SaddleBranch) :
    D.chronologicalSaddleShortAfterToWindowOrbitEquiv t ht A L
        (D.chronologicalSaddleShortPositiveOrbit t ht hindex A L branch) =
      D.chronologicalSaddlePositiveOrbit t ht hindex branch := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  let b := Q.scale
  let afix := D.chronologicalWindowRadius t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let sourceTime := D.chronologicalSaddleShortAfterTime t ht A L
  let targetTime := D.chronologicalAfterTime t ht
  let hreg := D.regularSlab_chronologicalSaddleShortAfter_to_window t ht A L
  let W := D.chronologicalSaddleShortAfterToWindowSlabField t ht A L
  let Vshort := D.chronologicalSaddleShortAfterField t ht A L
  let Vtarget := D.chronologicalAfterField t ht
  let Oshort := D.chronologicalSaddleShortPositiveOrbit
    t ht hindex A L branch
  let c : C(I, ℝ) := {
    toFun := fun q => b + (q : ℝ) * (afix - b)
    continuous_toFun :=
      continuous_const.add (continuous_subtype_val.mul continuous_const) }
  have hbc (q : I) : b ≤ c q := by
    dsimp [c]
    have hq₀ : 0 ≤ (q : ℝ) := q.property.1
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hca (q : I) : c q ≤ afix := by
    dsimp [c]
    have hq₁ : (q : ℝ) ≤ 1 := q.property.2
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hcpos (q : I) : 0 < c q := Q.scale_pos.trans_le (hbc q)
  have hcr (q : I) : c q < r :=
    (hca q).trans_lt (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)
  have hcsq (q : I) : (c q) ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (hcpos q).le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2 (hcr q)
  let u : I → E₂ := fun q =>
    saddlePositiveBoundaryEndParam branch .negative r (c q)
  have hucont : Continuous u := by
    dsimp [u, c]
    cases branch <;>
      simp [saddlePositiveBoundaryEndParam, saddlePositiveArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have huRadius (q : I) : ‖u q‖ < M.radius := by
    rw [show ‖u q‖ = r from
      norm_saddlePositiveBoundaryEndParam branch .negative
        (D.chronologicalSaddleBoundaryRadius_pos t ht) (hcsq q)]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  let z : C(I, E') := {
    toFun := fun q => M.param (u q)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro q
      exact (H.differentiableAt (u q) (huRadius q)).continuousAt.comp'
        hucont.continuousAt }
  let tau : C(I, ℝ) := {
    toFun := fun q => afix ^ 2 - (c q) ^ 2
    continuous_toFun := continuous_const.sub (c.continuous.pow 2) }
  let gamma : C(I, E₁) := {
    toFun := fun q => spacePart (W.flow (z q) (tau q))
    continuous_toFun := continuous_spacePart.comp
      (W.continuous_flow_uncurry.comp
        (z.continuous.prodMk tau.continuous)) }
  have hsourceMem (q : I) :
      tcoord (D.position.eventCenter t ht) + (c q) ^ 2 ∈
        Icc sourceTime targetTime := by
    have hbSq : b ^ 2 ≤ (c q) ^ 2 :=
      (sq_le_sq₀ Q.scale_pos.le (hcpos q).le).2 (hbc q)
    have hcSq : (c q) ^ 2 ≤ afix ^ 2 :=
      (sq_le_sq₀ (hcpos q).le
        (D.chronologicalWindowRadius_pos t ht).le).2 (hca q)
    constructor
    · simpa [sourceTime, chronologicalSaddleShortAfterTime, b, Q] using
        add_le_add_left hbSq (tcoord (D.position.eventCenter t ht))
    · simpa [targetTime, chronologicalAfterTime, afix] using
        add_le_add_left hcSq (tcoord (D.position.eventCenter t ht))
  have htargetMem : targetTime ∈ Icc sourceTime targetTime := by
    refine ⟨?_, le_rfl⟩
    simpa [sourceTime, targetTime, chronologicalSaddleShortAfterTime,
      chronologicalAfterTime, b, afix, Q, add_comm] using add_le_add_left
        (D.chronologicalSaddleShortScale_sq_lt_window_sq t ht A L).le
        (tcoord (D.position.eventCenter t ht))
  have hzFiber (q : I) : D.signedOutput.cobordism.G (z q) = 0 := by
    exact M.param_fiber (u q) (huRadius q)
  have hzTime (q : I) : tcoord (z q) =
      tcoord (D.position.eventCenter t ht) + (c q) ^ 2 := by
    have htime := M.time_model (u q) (huRadius q)
    rw [hindex] at htime
    simpa [z, u, saddlePositiveBoundaryEndParam] using htime
  have hgammaFiber : ∀ q,
      gamma q ∈ (D.chronologicalAfterSlice t ht).fiber := by
    intro q
    have hx : spacePart (z q) ∈ SlabTamedField.sliceFiber
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) + (c q) ^ 2) := by
      change D.signedOutput.cobordism.G
        (cobSpaceTime (spacePart (z q))
          (tcoord (D.position.eventCenter t ht) + (c q) ^ 2)) = 0
      rw [← hzTime q, spaceTime_spacePart]
      exact hzFiber q
    have hmap := W.sliceTransport_mapsTo hreg (hsourceMem q) htargetMem hx
    have hzst : cobSpaceTime (spacePart (z q))
        (tcoord (D.position.eventCenter t ht) + (c q) ^ 2) = z q := by
      rw [← hzTime q, spaceTime_spacePart]
    rw [SlabTamedField.sliceTransport, hzst] at hmap
    change D.signedOutput.cobordism.toLevelCobordismData.G
      (cobSpaceTime (gamma q) targetTime) = 0
    simpa [SlabTamedField.sliceFiber, gamma, tau, targetTime,
      chronologicalAfterTime, afix] using hmap
  have hgamma₀ : gamma 0 =
      W.sliceTransport sourceTime targetTime
        (spacePart (T.saddlePositiveBranchBase branch r b)) := by
    have hz₀Time : tcoord (z 0) = sourceTime := by
      simpa [sourceTime, chronologicalSaddleShortAfterTime, c, b, Q] using
        hzTime 0
    have hz₀st : cobSpaceTime (spacePart (z 0)) sourceTime = z 0 := by
      rw [← hz₀Time, spaceTime_spacePart]
    have hz₀Base : z 0 = T.saddlePositiveBranchBase branch r b := by
      simp [z, u, c,
        StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint, M, T, b, r, Q]
    rw [SlabTamedField.sliceTransport, ← hz₀Base, hz₀st]
    simp [gamma, tau, z, u, c, sourceTime, targetTime,
      chronologicalSaddleShortAfterTime, chronologicalAfterTime,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hgamma₁ : gamma 1 =
      spacePart (T.saddlePositiveBranchBase branch r afix) := by
    simp [gamma, tau, z, u, c,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hpath := Vtarget.continuousMap_mem_orbit gamma hgammaFiber 1
  rw [hgamma₀, hgamma₁] at hpath
  have hbaseFiber : spacePart (T.saddlePositiveBranchBase branch r b) ∈
      (D.chronologicalSaddleShortAfterSlice t ht A L).fiber := by
    apply T.saddlePositiveBranchBase_mem_fiber hindex branch
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      ((sq_lt_sq₀ Q.scale_pos.le
        (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
        (Q.scale_lt_window.trans
          (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)))
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
  have hbaseOrbit : spacePart (T.saddlePositiveBranchBase branch r b) ∈
      Vshort.orbit (Vshort.orbitPoint Oshort) := by
    rw [← Vshort.orbitPoint_orbit Oshort]
    exact Vshort.mem_orbit_self _
  have hshortMem : sourceTime ∈ Icc sourceTime targetTime :=
    ⟨le_rfl, htargetMem.1⟩
  have hmapOrbit := W.sliceTransport_mapsTo_orbit hreg
    hshortMem htargetMem Vshort Vtarget
      (Vshort.orbitPoint_mem_fiber Oshort) hbaseOrbit
  have hsame := Vtarget.orbit_eq_of_mem hmapOrbit
  rw [hsame] at hpath
  apply Subtype.ext
  change Vtarget.orbit
      (W.sliceTransport sourceTime targetTime (Vshort.orbitPoint Oshort)) =
    Vtarget.orbit
      (spacePart (T.saddlePositiveBranchBase branch r afix))
  exact (Vtarget.orbit_eq_of_mem hpath).symm


-- @@ L1608-1773 verbatim
/-- Time-reversed counterpart of
`chronologicalSaddleShortAfterToWindowOrbitEquiv_branch`. -/
theorem chronologicalSaddleShortBeforeToWindowOrbitEquiv_branch
    {A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)}
    {L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)}
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (branch : SaddleBranch) :
    D.chronologicalSaddleShortBeforeToWindowOrbitEquiv t ht A L
        (D.chronologicalSaddleShortNegativeOrbit t ht hindex A L branch) =
      D.chronologicalSaddleNegativeOrbit t ht hindex branch := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleShortFlowScale t ht A L
  let b := Q.scale
  let afix := D.chronologicalWindowRadius t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let sourceTime := D.chronologicalSaddleShortBeforeTime t ht A L
  let targetTime := D.chronologicalBeforeTime t ht
  let hreg := D.regularSlab_window_to_chronologicalSaddleShortBefore t ht A L
  let W := D.chronologicalSaddleWindowToShortBeforeSlabField t ht A L
  let Vshort := D.chronologicalSaddleShortBeforeField t ht A L
  let Vtarget := D.chronologicalBeforeField t ht
  let Oshort := D.chronologicalSaddleShortNegativeOrbit
    t ht hindex A L branch
  let c : C(I, ℝ) := {
    toFun := fun q => b + (q : ℝ) * (afix - b)
    continuous_toFun :=
      continuous_const.add (continuous_subtype_val.mul continuous_const) }
  have hbc (q : I) : b ≤ c q := by
    dsimp [c]
    have hq₀ : 0 ≤ (q : ℝ) := q.property.1
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hca (q : I) : c q ≤ afix := by
    dsimp [c]
    have hq₁ : (q : ℝ) ≤ 1 := q.property.2
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hcpos (q : I) : 0 < c q := Q.scale_pos.trans_le (hbc q)
  have hcr (q : I) : c q < r :=
    (hca q).trans_lt (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)
  have hcsq (q : I) : (c q) ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (hcpos q).le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2 (hcr q)
  let u : I → E₂ := fun q =>
    saddleNegativeBoundaryEndParam branch .negative r (c q)
  have hucont : Continuous u := by
    dsimp [u, c]
    cases branch <;>
      simp [saddleNegativeBoundaryEndParam, saddleNegativeArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have huRadius (q : I) : ‖u q‖ < M.radius := by
    rw [show ‖u q‖ = r from
      norm_saddleNegativeBoundaryEndParam branch .negative
        (D.chronologicalSaddleBoundaryRadius_pos t ht) (hcsq q)]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  let z : C(I, E') := {
    toFun := fun q => M.param (u q)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro q
      exact (H.differentiableAt (u q) (huRadius q)).continuousAt.comp'
        hucont.continuousAt }
  let tau : C(I, ℝ) := {
    toFun := fun q => (c q) ^ 2 - afix ^ 2
    continuous_toFun := (c.continuous.pow 2).sub continuous_const }
  let gamma : C(I, E₁) := {
    toFun := fun q => spacePart (W.flow (z q) (tau q))
    continuous_toFun := continuous_spacePart.comp
      (W.continuous_flow_uncurry.comp
        (z.continuous.prodMk tau.continuous)) }
  have hsourceMem (q : I) :
      tcoord (D.position.eventCenter t ht) - (c q) ^ 2 ∈
        Icc targetTime sourceTime := by
    have hbSq : b ^ 2 ≤ (c q) ^ 2 :=
      (sq_le_sq₀ Q.scale_pos.le (hcpos q).le).2 (hbc q)
    have hcSq : (c q) ^ 2 ≤ afix ^ 2 :=
      (sq_le_sq₀ (hcpos q).le
        (D.chronologicalWindowRadius_pos t ht).le).2 (hca q)
    constructor
    · simpa [targetTime, chronologicalBeforeTime, afix] using
        sub_le_sub_left hcSq (tcoord (D.position.eventCenter t ht))
    · simpa [sourceTime, chronologicalSaddleShortBeforeTime, b, Q] using
        sub_le_sub_left hbSq (tcoord (D.position.eventCenter t ht))
  have htargetMem : targetTime ∈ Icc targetTime sourceTime := by
    refine ⟨le_rfl, ?_⟩
    simpa [sourceTime, targetTime, chronologicalSaddleShortBeforeTime,
      chronologicalBeforeTime, b, afix, Q] using sub_le_sub_left
        (D.chronologicalSaddleShortScale_sq_lt_window_sq t ht A L).le
        (tcoord (D.position.eventCenter t ht))
  have hzFiber (q : I) : D.signedOutput.cobordism.G (z q) = 0 := by
    exact M.param_fiber (u q) (huRadius q)
  have hzTime (q : I) : tcoord (z q) =
      tcoord (D.position.eventCenter t ht) - (c q) ^ 2 := by
    have htime := M.time_model (u q) (huRadius q)
    rw [hindex] at htime
    simpa [z, u, saddleNegativeBoundaryEndParam, sub_eq_add_neg] using htime
  have hgammaFiber : ∀ q,
      gamma q ∈ (D.chronologicalBeforeSlice t ht).fiber := by
    intro q
    have hx : spacePart (z q) ∈ SlabTamedField.sliceFiber
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) - (c q) ^ 2) := by
      change D.signedOutput.cobordism.G
        (cobSpaceTime (spacePart (z q))
          (tcoord (D.position.eventCenter t ht) - (c q) ^ 2)) = 0
      rw [← hzTime q, spaceTime_spacePart]
      exact hzFiber q
    have hmap := W.sliceTransport_mapsTo hreg (hsourceMem q) htargetMem hx
    have hzst : cobSpaceTime (spacePart (z q))
        (tcoord (D.position.eventCenter t ht) - (c q) ^ 2) = z q := by
      rw [← hzTime q, spaceTime_spacePart]
    rw [SlabTamedField.sliceTransport, hzst] at hmap
    change D.signedOutput.cobordism.toLevelCobordismData.G
      (cobSpaceTime (gamma q) targetTime) = 0
    simpa [SlabTamedField.sliceFiber, gamma, tau, targetTime,
      chronologicalBeforeTime, afix] using hmap
  have hgamma₀ : gamma 0 =
      W.sliceTransport sourceTime targetTime
        (spacePart (T.saddleNegativeBranchBase branch r b)) := by
    have hz₀Time : tcoord (z 0) = sourceTime := by
      simpa [sourceTime, chronologicalSaddleShortBeforeTime, c, b, Q] using
        hzTime 0
    have hz₀st : cobSpaceTime (spacePart (z 0)) sourceTime = z 0 := by
      rw [← hz₀Time, spaceTime_spacePart]
    have hz₀Base : z 0 = T.saddleNegativeBranchBase branch r b := by
      simp [z, u, c,
        StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
        StandardMorseEventAt.saddleNegativeBoundaryEnd,
        StandardMorseEventAt.localPoint, M, T, b, r, Q]
    rw [SlabTamedField.sliceTransport, ← hz₀Base, hz₀st]
    simp [gamma, tau, z, u, c, sourceTime, targetTime,
      chronologicalSaddleShortBeforeTime, chronologicalBeforeTime,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
      StandardMorseEventAt.saddleNegativeBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hgamma₁ : gamma 1 =
      spacePart (T.saddleNegativeBranchBase branch r afix) := by
    simp [gamma, tau, z, u, c,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
      StandardMorseEventAt.saddleNegativeBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hpath := Vtarget.continuousMap_mem_orbit gamma hgammaFiber 1
  rw [hgamma₀, hgamma₁] at hpath
  have hbaseOrbit : spacePart (T.saddleNegativeBranchBase branch r b) ∈
      Vshort.orbit (Vshort.orbitPoint Oshort) := by
    rw [← Vshort.orbitPoint_orbit Oshort]
    exact Vshort.mem_orbit_self _
  have hshortMem : sourceTime ∈ Icc targetTime sourceTime :=
    ⟨htargetMem.2, le_rfl⟩
  have hmapOrbit := W.sliceTransport_mapsTo_orbit hreg
    hshortMem htargetMem Vshort Vtarget
      (Vshort.orbitPoint_mem_fiber Oshort) hbaseOrbit
  have hsame := Vtarget.orbit_eq_of_mem hmapOrbit
  rw [hsame] at hpath
  apply Subtype.ext
  change Vtarget.orbit
      (W.sliceTransport sourceTime targetTime (Vshort.orbitPoint Oshort)) =
    Vtarget.orbit
      (spacePart (T.saddleNegativeBranchBase branch r afix))
  exact (Vtarget.orbit_eq_of_mem hpath).symm


-- @@ L1775-1775 verbatim
/-! ## Fixed-window mate equalities and the final topology adapter -/


-- @@ L1777-1777 verbatim
namespace ChronologicalSaddleShortMateArcFlowData


-- @@ L1779-1805 verbatim
/-- The positive mate equality proved on the automatically small slice,
transported to the fixed chronological slice. -/
theorem positiveMateOrbit_eq
    {A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)}
    {L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)}
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (F : ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L)
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddlePositiveOrbit t ht hindex p.1 =
      D.chronologicalSaddlePositiveOrbit t ht hindex (A.mate p).1 := by
  let E := D.chronologicalSaddleShortAfterToWindowOrbitEquiv t ht A L
  calc
    D.chronologicalSaddlePositiveOrbit t ht hindex p.1 =
        E (D.chronologicalSaddleShortPositiveOrbit
          t ht hindex A L p.1) :=
      (D.chronologicalSaddleShortAfterToWindowOrbitEquiv_branch
        (t := t) (ht := ht) (A := A) (L := L) hindex p.1).symm
    _ = E (D.chronologicalSaddleShortPositiveOrbit
          t ht hindex A L (A.mate p).1) :=
      congrArg E (F.positiveMateShortOrbit_eq (hindex := hindex) p)
    _ = D.chronologicalSaddlePositiveOrbit
          t ht hindex (A.mate p).1 :=
      D.chronologicalSaddleShortAfterToWindowOrbitEquiv_branch
        (t := t) (ht := ht) (A := A) (L := L) hindex (A.mate p).1


-- @@ L1807-1833 verbatim
/-- The negative mate equality proved on the automatically small slice,
transported to the fixed chronological slice. -/
theorem negativeMateOrbit_eq
    {A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)}
    {L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)}
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (F : ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A L)
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleNegativeOrbit t ht hindex p.2 =
      D.chronologicalSaddleNegativeOrbit t ht hindex (A.mate p).2 := by
  let E := D.chronologicalSaddleShortBeforeToWindowOrbitEquiv t ht A L
  calc
    D.chronologicalSaddleNegativeOrbit t ht hindex p.2 =
        E (D.chronologicalSaddleShortNegativeOrbit
          t ht hindex A L p.2) :=
      (D.chronologicalSaddleShortBeforeToWindowOrbitEquiv_branch
        (t := t) (ht := ht) (A := A) (L := L) hindex p.2).symm
    _ = E (D.chronologicalSaddleShortNegativeOrbit
          t ht hindex A L (A.mate p).2) :=
      congrArg E (F.negativeMateShortOrbit_eq (hindex := hindex) p)
    _ = D.chronologicalSaddleNegativeOrbit
          t ht hindex (A.mate p).2 :=
      D.chronologicalSaddleShortBeforeToWindowOrbitEquiv_branch
        (t := t) (ht := ht) (A := A) (L := L) hindex (A.mate p).2


-- @@ L1835-1835 verbatim
end ChronologicalSaddleShortMateArcFlowData


-- @@ L1837-1879 verbatim
/-- The production saddle topology follows from the actual punctured
critical-arc pairing, the endpoint-local fiber cover, and regular-orbit arc
recovery.  All flow scales and endpoint captures are chosen automatically. -/
theorem chronologicalSaddleTopologyDichotomy_of_endpointLocalFiberCover
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (H : ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex)) :
    D.ChronologicalSaddleMergeTopology t ht hindex ∨
      D.ChronologicalSaddleSplitTopology t ht hindex := by
  let F := D.chronologicalSaddleShortMateArcFlowData_of_endpointLocalCover
    (t := t) (ht := ht) hindex A L
  have hdich :=
    StandardMorseEventAt.saddleExteriorArcPairing_eq_flipSecond_or_eq_flipFirst
      (D.position.eventModel t ht)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalSaddleBoundaryRadius_pos t ht) A
  rcases hdich with hsecond | hfirst
  · right
    refine {
      positive_ne :=
        ChronologicalSaddleRegularOrbitArcRecovery.positive_ne_of_mate_eq_flipSecond
          (D := D) (t := t) (ht := ht) (hindex := hindex) H hsecond
      negative_eq := ?_ }
    let p : SaddleBranch × SaddleBranch := (.negative, .negative)
    have h := F.negativeMateOrbit_eq (hindex := hindex) p
    rw [hsecond p] at h
    simpa [p, saddleBranchEndFlipSecond] using h
  · left
    refine {
      negative_ne :=
        ChronologicalSaddleRegularOrbitArcRecovery.negative_ne_of_mate_eq_flipFirst
          (D := D) (t := t) (ht := ht) (hindex := hindex) H hfirst
      positive_eq := ?_ }
    let p : SaddleBranch × SaddleBranch := (.negative, .negative)
    have h := F.positiveMateOrbit_eq (hindex := hindex) p
    rw [hfirst p] at h
    simpa [p, saddleBranchEndFlipFirst] using h


-- @@ L1881-1881 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L1883-1883 verbatim
end Submission
