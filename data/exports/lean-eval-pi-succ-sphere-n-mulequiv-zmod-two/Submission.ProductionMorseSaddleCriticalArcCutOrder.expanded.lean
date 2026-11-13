import Submission.ProductionMorseSaddleOrientedShortFlowAdapter
import Submission.ProductionMorseSaddleCriticalArcRecovery


-- @@ L4-33 verbatim
/-!
# Cut-order checker separation for punctured critical saddle arcs

This file reduces the oriented endpoint theorem for arbitrary punctured
critical saddle arcs — the statement `arc_checker_ne` consumed by
`saddlePuncturedCriticalArcPairingData_of_candidate` — to a single
quantifier-free regular-slice parity statement.

The reduction is by safe flow of one arbitrary arc.  Every punctured
critical arc carries its own canonical compact time-tamed field
(`recoveryTimeField`).  An automatically small displacement flows the arc
onto a single orbit of a nearby regular slice on either side of the event;
endpoint-local chart covers capture the two flowed critical ends inside
their labelled local hyperbola branches.  Transporting the resulting branch
orbits to the fixed chronological window slices proves: a critical arc from
end `p` to end `q` forces

* `chronologicalSaddlePositiveOrbit p.1 = chronologicalSaddlePositiveOrbit q.1`,
* `chronologicalSaddleNegativeOrbit p.2 = chronologicalSaddleNegativeOrbit q.2`.

If the two ends had equal checkerboard parity (and distinct labels) they
would be the diagonal pair: both first labels and both second labels would
differ, so the two positive branch orbits and the two negative branch
orbits would each coincide — the saddle would merge and split at the same
time.  The residual hypothesis `ChronologicalSaddleOrientedCutParity`
excludes exactly this two-sided common-orbit configuration; it is the
orientation content of Pontryagin's Theorem 20 saddle analysis (an oriented
saddle surgery changes the component count by exactly one, so it cannot
simultaneously identify the two branches before and after the event).
-/


-- @@ L35-35 verbatim
set_option autoImplicit false

-- @@ L36-36 verbatim
set_option maxHeartbeats 2400000


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open Set Function Metric Filter

-- @@ L41-41 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L43-43 verbatim
namespace Submission


-- @@ L45-45 verbatim
variable {n : ℕ}


-- @@ L47-47 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L48-48 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L49-49 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L51-51 verbatim
/-! ## A small-radius endpoint cover with an arbitrary target radius -/


-- @@ L53-53 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L55-55 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L56-56 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L57-57 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L59-118 verbatim
/-- `exists_smallSaddleBoundaryRadius_endpointCover` with an arbitrary
parameter target radius.  The proof never uses the target radius, so a
center-based cover into any prescribed radius yields one smaller boundary
radius whose four critical ends carry endpoint-local covers into the same
prescribed radius. -/
theorem exists_smallSaddleBoundaryRadius_endpointCoverTarget
    (T : M.EmbeddedShrink) {r : ℝ}
    (hcover : ∃ ε > 0,
      ∀ v : EuclideanSpace ℝ (Fin (n + 2)),
        dist v center < ε → C.G v = 0 →
        ∃ u : E₂, ‖u‖ < r ∧ M.param u = v) :
    ∃ rho > 0, rho < T.radius ∧ ∃ δ > 0,
      ∀ (p : SaddleBranch × SaddleBranch)
        (v : EuclideanSpace ℝ (Fin (n + 2))),
        dist v (M.saddleCriticalBoundaryEnd p rho) < δ →
        C.G v = 0 →
        ∃ u : E₂, ‖u‖ < r ∧ M.param u = v := by
  obtain ⟨ε, hε, hcover⟩ := hcover
  have hzero : ‖(0 : E₂)‖ < T.radius := by
    simpa using T.radius_pos
  have hcont : ContinuousAt M.param 0 :=
    (T.param_differentiableAt 0 hzero).continuousAt
  obtain ⟨eta, heta, hclose⟩ := (Metric.continuousAt_iff.mp hcont)
    (ε / 2) (by positivity)
  let rho := min T.radius eta / 2
  have hmin : 0 < min T.radius eta := lt_min T.radius_pos heta
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hrhoT : rho < T.radius := by
    dsimp [rho]
    have hle := min_le_left T.radius eta
    nlinarith
  have hrhoEta : rho < eta := by
    dsimp [rho]
    have hle := min_le_right T.radius eta
    nlinarith
  refine ⟨rho, hrho, hrhoT, ε / 2, by positivity, ?_⟩
  intro p v hv hendFiber
  have hendClose : dist (M.saddleCriticalBoundaryEnd p rho) center <
      ε / 2 := by
    let u := saddleCriticalBoundaryEndParam p rho
    have huEta : dist u 0 < eta := by
      rw [dist_zero_right, show ‖u‖ = rho by
        exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho
          (by nlinarith [sq_pos_of_pos hrho])]
      exact hrhoEta
    have h := hclose huEta
    simpa [u, M.param_zero,
      StandardMorseEventAt.saddleCriticalBoundaryEnd,
      saddleCriticalBoundaryEndParam,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint] using h
  have hvCenter : dist v center < ε := by
    calc
      dist v center ≤ dist v (M.saddleCriticalBoundaryEnd p rho) +
          dist (M.saddleCriticalBoundaryEnd p rho) center :=
        dist_triangle _ _ _
      _ < ε := by linarith
  exact hcover v hvCenter hendFiber


-- @@ L120-120 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L122-122 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L123-123 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L124-124 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L126-126 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L128-128 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L129-129 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}


-- @@ L131-131 verbatim
/-! ## The chronological small-radius endpoint cover -/


-- @@ L133-151 verbatim
/-- A small saddle boundary radius, below the chronological embedded chart,
whose four critical ends carry ambient fiber covers into the fixed endpoint
parameter chart radius. -/
structure ChronologicalSaddleSmallEndCover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Type where
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt_embedded :
    sigma < (D.chronologicalEventEmbeddedShrink t ht).radius
  delta : ℝ
  delta_pos : 0 < delta
  cover : ∀ (p : SaddleBranch × SaddleBranch) (v : E'),
    dist v ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p sigma) <
        delta →
    D.signedOutput.cobordism.G v = 0 →
    ∃ u : E₂,
      ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht ∧
      (D.position.eventModel t ht).param u = v


-- @@ L153-169 verbatim
/-- The arbitrarily small production center cover supplies the small-radius
endpoint cover canonically. -/
theorem nonempty_chronologicalSaddleSmallEndCover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    Nonempty (ChronologicalSaddleSmallEndCover D t ht) := by
  obtain ⟨sigma, hsigma, hsigmaT, delta, hdelta, hcov⟩ :=
    (D.chronologicalEventEmbeddedShrink t ht).exists_smallSaddleBoundaryRadius_endpointCoverTarget
      (D.eventModel_covers_fiber_within_morseRadius t ht
        (D.chronologicalSaddleEndpointParamRadius_pos t ht))
  exact ⟨{
    sigma := sigma
    sigma_pos := hsigma
    sigma_lt_embedded := hsigmaT
    delta := delta
    delta_pos := hdelta
    cover := hcov }⟩


-- @@ L171-177 verbatim
/-- Norm of a labelled critical end parameter at the small cover radius. -/
theorem saddleArcCutEndParam_norm
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    ‖saddleCriticalBoundaryEndParam p Cov.sigma‖ = Cov.sigma := by
  exact norm_saddlePositiveBoundaryEndParam p.1 p.2 Cov.sigma_pos
    (by nlinarith [sq_pos_of_pos Cov.sigma_pos])


-- @@ L179-179 verbatim
/-! ## Signed-branch neighborhoods at the small-radius ends -/


-- @@ L181-200 verbatim
/-- Positive-slice signed-branch neighborhood at a small-radius end. -/
theorem exists_saddleArcCutPositiveBranchNeighborhood
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    ∃ ε > 0, ∀ u : E₂,
      ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht →
      dist ((D.position.eventModel t ht).param u)
          ((D.position.eventModel t ht).param
            (saddleCriticalBoundaryEndParam p Cov.sigma)) < ε →
      0 < signedBranch p.1 (u 0) := by
  apply (D.chronologicalEventEmbeddedShrink t ht).exists_param_signedBranch_neighborhood
    (D.chronologicalEventFullRadiusSmooth t ht) p.1 0
    (saddleCriticalBoundaryEndParam p Cov.sigma)
    (D.chronologicalSaddleEndpointParamRadius_pos t ht)
    (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht)
    (le_refl (D.chronologicalEventEmbeddedShrink t ht).radius)
  · rw [saddleArcCutEndParam_norm Cov p]
    exact Cov.sigma_lt_embedded
  · exact StandardMorseEventAt.EmbeddedShrink.saddleCriticalBoundaryEndParam_first_sign
      p Cov.sigma_pos


-- @@ L202-221 verbatim
/-- Negative-slice signed-branch neighborhood at a small-radius end. -/
theorem exists_saddleArcCutNegativeBranchNeighborhood
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    ∃ ε > 0, ∀ u : E₂,
      ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht →
      dist ((D.position.eventModel t ht).param u)
          ((D.position.eventModel t ht).param
            (saddleCriticalBoundaryEndParam p Cov.sigma)) < ε →
      0 < signedBranch p.2 (u 1) := by
  apply (D.chronologicalEventEmbeddedShrink t ht).exists_param_signedBranch_neighborhood
    (D.chronologicalEventFullRadiusSmooth t ht) p.2 1
    (saddleCriticalBoundaryEndParam p Cov.sigma)
    (D.chronologicalSaddleEndpointParamRadius_pos t ht)
    (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht)
    (le_refl (D.chronologicalEventEmbeddedShrink t ht).radius)
  · rw [saddleArcCutEndParam_norm Cov p]
    exact Cov.sigma_lt_embedded
  · exact StandardMorseEventAt.EmbeddedShrink.saddleCriticalBoundaryEndParam_second_sign
      p Cov.sigma_pos


-- @@ L223-227 verbatim
/-- A chosen positive-branch separation radius at a small-radius end. -/
noncomputable def saddleArcCutPositiveBranchRadius
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) : ℝ :=
  (exists_saddleArcCutPositiveBranchNeighborhood Cov p).choose


-- @@ L229-233 verbatim
theorem saddleArcCutPositiveBranchRadius_pos
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    0 < saddleArcCutPositiveBranchRadius Cov p :=
  (exists_saddleArcCutPositiveBranchNeighborhood Cov p).choose_spec.1


-- @@ L235-245 verbatim
theorem saddleArcCutPositiveBranchRadius_spec
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) (u : E₂)
    (hu : ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht)
    (hdist : dist ((D.position.eventModel t ht).param u)
      ((D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam p Cov.sigma)) <
      saddleArcCutPositiveBranchRadius Cov p) :
    0 < signedBranch p.1 (u 0) :=
  (exists_saddleArcCutPositiveBranchNeighborhood Cov p).choose_spec.2
    u hu hdist


-- @@ L247-251 verbatim
/-- A chosen negative-branch separation radius at a small-radius end. -/
noncomputable def saddleArcCutNegativeBranchRadius
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) : ℝ :=
  (exists_saddleArcCutNegativeBranchNeighborhood Cov p).choose


-- @@ L253-257 verbatim
theorem saddleArcCutNegativeBranchRadius_pos
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    0 < saddleArcCutNegativeBranchRadius Cov p :=
  (exists_saddleArcCutNegativeBranchNeighborhood Cov p).choose_spec.1


-- @@ L259-269 verbatim
theorem saddleArcCutNegativeBranchRadius_spec
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) (u : E₂)
    (hu : ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht)
    (hdist : dist ((D.position.eventModel t ht).param u)
      ((D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam p Cov.sigma)) <
      saddleArcCutNegativeBranchRadius Cov p) :
    0 < signedBranch p.2 (u 1) :=
  (exists_saddleArcCutNegativeBranchNeighborhood Cov p).choose_spec.2
    u hu hdist


-- @@ L271-277 verbatim
/-- One positive margin below the endpoint cover radius and all eight
signed-branch separation radii. -/
noncomputable def saddleArcCutMargin
    (Cov : ChronologicalSaddleSmallEndCover D t ht) : ℝ :=
  min Cov.delta
    (min (saddleFourEndMin (saddleArcCutPositiveBranchRadius Cov))
      (saddleFourEndMin (saddleArcCutNegativeBranchRadius Cov)))


-- @@ L279-286 verbatim
theorem saddleArcCutMargin_pos
    (Cov : ChronologicalSaddleSmallEndCover D t ht) :
    0 < saddleArcCutMargin Cov := by
  unfold saddleArcCutMargin
  exact lt_min Cov.delta_pos
    (lt_min
      (saddleFourEndMin_pos (saddleArcCutPositiveBranchRadius_pos Cov))
      (saddleFourEndMin_pos (saddleArcCutNegativeBranchRadius_pos Cov)))


-- @@ L288-291 verbatim
theorem saddleArcCutMargin_le_delta
    (Cov : ChronologicalSaddleSmallEndCover D t ht) :
    saddleArcCutMargin Cov ≤ Cov.delta :=
  min_le_left _ _


-- @@ L293-299 verbatim
theorem saddleArcCutMargin_le_positiveBranch
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    saddleArcCutMargin Cov ≤ saddleArcCutPositiveBranchRadius Cov p :=
  (min_le_right _ _).trans
    ((min_le_left _ _).trans
      (saddleFourEndMin_le (saddleArcCutPositiveBranchRadius Cov) p))


-- @@ L301-307 verbatim
theorem saddleArcCutMargin_le_negativeBranch
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p : SaddleBranch × SaddleBranch) :
    saddleArcCutMargin Cov ≤ saddleArcCutNegativeBranchRadius Cov p :=
  (min_le_right _ _).trans
    ((min_le_right _ _).trans
      (saddleFourEndMin_le (saddleArcCutNegativeBranchRadius Cov) p))


-- @@ L309-309 verbatim
/-! ## One arbitrary critical arc at the small cover radius -/


-- @@ L311-320 verbatim
/-- A punctured critical saddle arc between two labelled ends at the small
cover radius. -/
abbrev SaddleArcCutArc
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    (p q : SaddleBranch × SaddleBranch) : Type _ :=
  SaddleCriticalExteriorArc
    (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r
      Cov.sigma)
    (StandardMorseEventAt.puncturedCriticalSlice
      D.signedOutput.cobordism (D.position.eventCenter t ht)) p q


-- @@ L322-331 verbatim
/-- The canonical per-arc compact time-tamed field. -/
@[reducible] noncomputable def saddleArcCutTimeField
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    {p q : SaddleBranch × SaddleBranch} (B : SaddleArcCutArc Cov p q) :
    CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData
      (SaddleCriticalExteriorArc.recoveryCore (n := n) B) :=
  SaddleCriticalExteriorArc.recoveryTimeField
    (n := n) (C := D.signedOutput.cobordism) (P := D.position)
    (t := t) (ht := ht) B


-- @@ L333-345 verbatim
/-- The arc's source end lies in its own compact recovery core. -/
theorem saddleArcCut_source_mem_core
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    {p q : SaddleBranch × SaddleBranch} (B : SaddleArcCutArc Cov p q) :
    (D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam p Cov.sigma) ∈
      SaddleCriticalExteriorArc.recoveryCore (n := n) B := by
  refine ⟨0, ?_⟩
  rw [B.toPath.source]
  simp [saddleCriticalBoundaryEndParam,
    StandardMorseEventAt.saddleCriticalBoundaryEnd,
    StandardMorseEventAt.saddlePositiveBoundaryEnd,
    StandardMorseEventAt.localPoint]


-- @@ L347-359 verbatim
/-- The arc's target end lies in its own compact recovery core. -/
theorem saddleArcCut_target_mem_core
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    {p q : SaddleBranch × SaddleBranch} (B : SaddleArcCutArc Cov p q) :
    (D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam q Cov.sigma) ∈
      SaddleCriticalExteriorArc.recoveryCore (n := n) B := by
  refine ⟨1, ?_⟩
  rw [B.toPath.target]
  simp [saddleCriticalBoundaryEndParam,
    StandardMorseEventAt.saddleCriticalBoundaryEnd,
    StandardMorseEventAt.saddlePositiveBoundaryEnd,
    StandardMorseEventAt.localPoint]


-- @@ L361-379 verbatim
/-- An automatically small displacement for one arc: below the fixed window
radius, safe for the arc's own compact field, and small enough for all
endpoint cover and branch-separation margins. -/
structure SaddleArcCutScale
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    {p q : SaddleBranch × SaddleBranch}
    (B : SaddleArcCutArc Cov p q) : Type where
  scale : ℝ
  scale_pos : 0 < scale
  scale_lt_window : scale < D.chronologicalWindowRadius t ht
  safe : scale ^ 2 ≤ (saddleArcCutTimeField Cov B).safeTime
  cover_close :
    ((saddleArcCutTimeField Cov B).base.bound : ℝ) * scale ^ 2 < Cov.delta
  positive_branch_close : ∀ r : SaddleBranch × SaddleBranch,
    ((saddleArcCutTimeField Cov B).base.bound : ℝ) * scale ^ 2 <
      saddleArcCutPositiveBranchRadius Cov r
  negative_branch_close : ∀ r : SaddleBranch × SaddleBranch,
    ((saddleArcCutTimeField Cov B).base.bound : ℝ) * scale ^ 2 <
      saddleArcCutNegativeBranchRadius Cov r


-- @@ L381-426 verbatim
theorem nonempty_saddleArcCutScale
    (Cov : ChronologicalSaddleSmallEndCover D t ht)
    {p q : SaddleBranch × SaddleBranch} (B : SaddleArcCutArc Cov p q) :
    Nonempty (SaddleArcCutScale Cov B) := by
  let R := saddleArcCutTimeField Cov B
  let m := saddleArcCutMargin Cov
  let Bd : ℝ := (R.base.bound : ℝ)
  have hsafeN : {x : ℝ | x ^ 2 < R.safeTime} ∈ nhds 0 := by
    have hlim : Tendsto (fun x : ℝ => x ^ 2) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun x : ℝ => x ^ 2) 0 :=
        continuousAt_id.pow 2
      simpa using hcont.tendsto
    exact hlim (Iio_mem_nhds R.safeTime_pos)
  have hmarginN : {x : ℝ | Bd * x ^ 2 < m} ∈ nhds 0 := by
    have hlim : Tendsto (fun x : ℝ => Bd * x ^ 2) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun x : ℝ => Bd * x ^ 2) 0 :=
        continuousAt_const.mul (continuousAt_id.pow 2)
      simpa using hcont.tendsto
    exact hlim (Iio_mem_nhds (saddleArcCutMargin_pos Cov))
  have hgood : {x : ℝ | x ^ 2 < R.safeTime ∧ Bd * x ^ 2 < m} ∈ nhds 0 :=
    Filter.inter_mem hsafeN hmarginN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let c := min (D.chronologicalWindowRadius t ht) δ
  let b := c / 2
  have hc : 0 < c := lt_min (D.chronologicalWindowRadius_pos t ht) hδ
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
  · exact hbGood.2.trans_le (saddleArcCutMargin_le_delta Cov)
  · intro r
    exact hbGood.2.trans_le (saddleArcCutMargin_le_positiveBranch Cov r)
  · intro r
    exact hbGood.2.trans_le (saddleArcCutMargin_le_negativeBranch Cov r)


-- @@ L428-434 verbatim
theorem saddleArcCutScale_sq_lt_window_sq
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    S.scale ^ 2 < D.chronologicalWindowRadius t ht ^ 2 :=
  (sq_lt_sq₀ S.scale_pos.le
    (D.chronologicalWindowRadius_pos t ht).le).2 S.scale_lt_window


-- @@ L436-444 verbatim
theorem saddleArcCutScale_sq_lt_saddleBoundaryRadius_sq
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    S.scale ^ 2 < D.chronologicalSaddleBoundaryRadius t ht ^ 2 :=
  (sq_lt_sq₀ S.scale_pos.le
    (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
    (S.scale_lt_window.trans
      (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht))


-- @@ L446-446 verbatim
/-! ## The two per-arc regular slices -/


-- @@ L448-453 verbatim
/-- The per-arc regular time below the event. -/
def saddleArcCutBeforeTime
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) : ℝ :=
  tcoord (D.position.eventCenter t ht) - S.scale ^ 2


-- @@ L455-460 verbatim
/-- The per-arc regular time above the event. -/
def saddleArcCutAfterTime
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) : ℝ :=
  tcoord (D.position.eventCenter t ht) + S.scale ^ 2


-- @@ L462-484 verbatim
private theorem saddleArcCut_eventTime_eq_of_mem_bracket
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


-- @@ L486-509 verbatim
theorem regularSlab_saddleArcCutAfter_to_window
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    regularSlab D.signedOutput.cobordism.G
      (saddleArcCutAfterTime S) (D.chronologicalAfterTime t ht) := by
  rw [D.position.regularSlab_iff_avoid_eventTimes]
  intro s hsEvent hs
  have hcenterShort : tcoord (D.position.eventCenter t ht) <
      saddleArcCutAfterTime S := by
    rw [saddleArcCutAfterTime]
    exact lt_add_of_pos_right _ (sq_pos_of_pos S.scale_pos)
  have hsBracket : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after := by
    constructor
    · exact (D.position.eventBracket t ht).before_lt.le.trans
        (hcenterShort.le.trans hs.1)
    · exact hs.2.trans
        (D.chronologicalAfterTime_mem_bracket t ht).2.le
  have hst : s = t :=
    saddleArcCut_eventTime_eq_of_mem_bracket D t ht hsEvent hsBracket
  have htShort : t < saddleArcCutAfterTime S :=
    (D.position.eventCenter_time t ht).symm.trans_lt hcenterShort
  exact (not_le_of_gt htShort) (hst ▸ hs.1)


-- @@ L511-533 verbatim
theorem regularSlab_window_to_saddleArcCutBefore
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    regularSlab D.signedOutput.cobordism.G
      (D.chronologicalBeforeTime t ht) (saddleArcCutBeforeTime S) := by
  rw [D.position.regularSlab_iff_avoid_eventTimes]
  intro s hsEvent hs
  have hshortCenter : saddleArcCutBeforeTime S <
      tcoord (D.position.eventCenter t ht) := by
    rw [saddleArcCutBeforeTime]
    exact sub_lt_self _ (sq_pos_of_pos S.scale_pos)
  have hsBracket : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after := by
    constructor
    · exact (D.chronologicalBeforeTime_mem_bracket t ht).1.le.trans hs.1
    · exact hs.2.trans
        (hshortCenter.le.trans (D.position.eventBracket t ht).lt_after.le)
  have hst : s = t :=
    saddleArcCut_eventTime_eq_of_mem_bracket D t ht hsEvent hsBracket
  have hshortT : saddleArcCutBeforeTime S < t :=
    hshortCenter.trans_eq (D.position.eventCenter_time t ht)
  exact (not_le_of_gt hshortT) (hst ▸ hs.2)


-- @@ L535-542 verbatim
theorem saddleArcCutAfterTime_le_window
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    saddleArcCutAfterTime S ≤ D.chronologicalAfterTime t ht := by
  rw [saddleArcCutAfterTime, chronologicalAfterTime]
  have h := saddleArcCutScale_sq_lt_window_sq S
  linarith


-- @@ L544-550 verbatim
theorem window_le_saddleArcCutBeforeTime
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    D.chronologicalBeforeTime t ht ≤ saddleArcCutBeforeTime S := by
  rw [saddleArcCutBeforeTime, chronologicalBeforeTime]
  exact sub_le_sub_left (saddleArcCutScale_sq_lt_window_sq S).le _


-- @@ L552-558 verbatim
theorem saddleArcCutAfterTime_regular
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    sliceRegular D.signedOutput.cobordism.G (saddleArcCutAfterTime S) :=
  (regularSlab_saddleArcCutAfter_to_window S).sliceRegular
    ⟨le_rfl, saddleArcCutAfterTime_le_window S⟩


-- @@ L560-566 verbatim
theorem saddleArcCutBeforeTime_regular
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    sliceRegular D.signedOutput.cobordism.G (saddleArcCutBeforeTime S) :=
  (regularSlab_window_to_saddleArcCutBefore S).sliceRegular
    ⟨window_le_saddleArcCutBeforeTime S, le_rfl⟩


-- @@ L568-574 verbatim
/-- The per-arc regular slice above the event. -/
def saddleArcCutAfterSlice
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt D.signedOutput.cobordism.toLevelCobordismData
    (saddleArcCutAfterTime S) (saddleArcCutAfterTime_regular S)


-- @@ L576-582 verbatim
/-- The per-arc regular slice below the event. -/
def saddleArcCutBeforeSlice
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt D.signedOutput.cobordism.toLevelCobordismData
    (saddleArcCutBeforeTime S) (saddleArcCutBeforeTime_regular S)


-- @@ L584-589 verbatim
noncomputable def saddleArcCutAfterField
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    TamedField (saddleArcCutAfterSlice S) :=
  (saddleArcCutAfterSlice S).exists_tamedField.some


-- @@ L591-596 verbatim
noncomputable def saddleArcCutBeforeField
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    TamedField (saddleArcCutBeforeSlice S) :=
  (saddleArcCutBeforeSlice S).exists_tamedField.some


-- @@ L598-605 verbatim
noncomputable def saddleArcCutAfterSlabField
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    SlabTamedField D.signedOutput.cobordism.toLevelCobordismData
      (saddleArcCutAfterTime S) (D.chronologicalAfterTime t ht) :=
  (exists_slabTamedField D.signedOutput.cobordism.toLevelCobordismData
    (regularSlab_saddleArcCutAfter_to_window S)).some


-- @@ L607-614 verbatim
noncomputable def saddleArcCutBeforeSlabField
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    SlabTamedField D.signedOutput.cobordism.toLevelCobordismData
      (D.chronologicalBeforeTime t ht) (saddleArcCutBeforeTime S) :=
  (exists_slabTamedField D.signedOutput.cobordism.toLevelCobordismData
    (regularSlab_window_to_saddleArcCutBefore S)).some


-- @@ L616-616 verbatim
/-! ## Endpoint captures for the arc's own field -/


-- @@ L618-673 verbatim
/-- Positive-time capture at any small-radius end contained in the arc's
compact core. -/
theorem exists_saddleArcCutPositiveCapture
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B)
    (r : SaddleBranch × SaddleBranch)
    (hmem : (D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam r Cov.sigma) ∈
      SaddleCriticalExteriorArc.recoveryCore (n := n) B) :
    ∃ u : E₂, ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht ∧
      (D.position.eventModel t ht).param u =
        (saddleArcCutTimeField Cov B).base.flow
          ((D.position.eventModel t ht).saddleCriticalBoundaryEnd r
            Cov.sigma) (S.scale ^ 2) ∧
      0 < signedBranch r.1 (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = S.scale ^ 2 := by
  let M := D.position.eventModel t ht
  let R := saddleArcCutTimeField Cov B
  let u₀ := saddleCriticalBoundaryEndParam r Cov.sigma
  have hu₀Radius : ‖u₀‖ < M.radius := by
    calc
      ‖u₀‖ = Cov.sigma := saddleArcCutEndParam_norm Cov r
      _ < (D.chronologicalEventEmbeddedShrink t ht).radius :=
        Cov.sigma_lt_embedded
      _ ≤ M.radius := (D.chronologicalEventEmbeddedShrink t ht).radius_le
  have hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0 := by
    simp [u₀, saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam]
  have hex :=
    M.exists_positiveFlowEndpoint_of_localCover R hindex r.1 0 u₀
      hu₀Radius hquad₀ hmem
      (r := D.chronologicalSaddleEndpointParamRadius t ht)
      (εcover := Cov.delta)
      (εbranch := saddleArcCutPositiveBranchRadius Cov r)
      (A := S.scale)
      (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
      (by
        intro v hv hfiber
        apply Cov.cover r v
        · simpa [M, u₀, saddleCriticalBoundaryEndParam,
            StandardMorseEventAt.saddleCriticalBoundaryEnd,
            StandardMorseEventAt.saddlePositiveBoundaryEnd,
            StandardMorseEventAt.localPoint] using hv
        · exact hfiber)
      (by
        intro v hv hdist
        exact saddleArcCutPositiveBranchRadius_spec Cov r v hv hdist)
      S.safe S.cover_close (S.positive_branch_close r)
  obtain ⟨u, hu, hend, hsign, hquad⟩ := hex
  refine ⟨u, hu, ?_, hsign, hquad⟩
  simpa [M, R, u₀, saddleCriticalBoundaryEndParam,
    StandardMorseEventAt.saddleCriticalBoundaryEnd,
    StandardMorseEventAt.saddlePositiveBoundaryEnd,
    StandardMorseEventAt.localPoint] using hend


-- @@ L675-730 verbatim
/-- Negative-time capture at any small-radius end contained in the arc's
compact core. -/
theorem exists_saddleArcCutNegativeCapture
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B)
    (r : SaddleBranch × SaddleBranch)
    (hmem : (D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam r Cov.sigma) ∈
      SaddleCriticalExteriorArc.recoveryCore (n := n) B) :
    ∃ u : E₂, ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht ∧
      (D.position.eventModel t ht).param u =
        (saddleArcCutTimeField Cov B).base.flow
          ((D.position.eventModel t ht).saddleCriticalBoundaryEnd r
            Cov.sigma) (-(S.scale ^ 2)) ∧
      0 < signedBranch r.2 (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(S.scale ^ 2) := by
  let M := D.position.eventModel t ht
  let R := saddleArcCutTimeField Cov B
  let u₀ := saddleCriticalBoundaryEndParam r Cov.sigma
  have hu₀Radius : ‖u₀‖ < M.radius := by
    calc
      ‖u₀‖ = Cov.sigma := saddleArcCutEndParam_norm Cov r
      _ < (D.chronologicalEventEmbeddedShrink t ht).radius :=
        Cov.sigma_lt_embedded
      _ ≤ M.radius := (D.chronologicalEventEmbeddedShrink t ht).radius_le
  have hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0 := by
    simp [u₀, saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam]
  have hex :=
    M.exists_negativeFlowEndpoint_of_localCover R hindex r.2 1 u₀
      hu₀Radius hquad₀ hmem
      (r := D.chronologicalSaddleEndpointParamRadius t ht)
      (εcover := Cov.delta)
      (εbranch := saddleArcCutNegativeBranchRadius Cov r)
      (A := S.scale)
      (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
      (by
        intro v hv hfiber
        apply Cov.cover r v
        · simpa [M, u₀, saddleCriticalBoundaryEndParam,
            StandardMorseEventAt.saddleCriticalBoundaryEnd,
            StandardMorseEventAt.saddlePositiveBoundaryEnd,
            StandardMorseEventAt.localPoint] using hv
        · exact hfiber)
      (by
        intro v hv hdist
        exact saddleArcCutNegativeBranchRadius_spec Cov r v hv hdist)
      S.safe S.cover_close (S.negative_branch_close r)
  obtain ⟨u, hu, hend, hsign, hquad⟩ := hex
  refine ⟨u, hu, ?_, hsign, hquad⟩
  simpa [M, R, u₀, saddleCriticalBoundaryEndParam,
    StandardMorseEventAt.saddleCriticalBoundaryEnd,
    StandardMorseEventAt.saddlePositiveBoundaryEnd,
    StandardMorseEventAt.localPoint] using hend


-- @@ L732-732 verbatim
/-! ## Flowed ends on the per-arc branch orbits -/


-- @@ L734-766 verbatim
/-- A captured flowed end lies on the labelled positive local branch orbit
at the chronological boundary radius and the per-arc scale. -/
theorem saddleArcCut_positiveFlow_mem_branchOrbit
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B)
    (r : SaddleBranch × SaddleBranch)
    (hmem : (D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam r Cov.sigma) ∈
      SaddleCriticalExteriorArc.recoveryCore (n := n) B) :
    spacePart ((saddleArcCutTimeField Cov B).base.flow
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd r
          Cov.sigma) (S.scale ^ 2)) ∈
      (saddleArcCutAfterField S).orbit
        (spacePart
          ((D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchBase
            r.1 (D.chronologicalSaddleBoundaryRadius t ht) S.scale)) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  obtain ⟨u, hu, hend, hsign, hquad⟩ :=
    exists_saddleArcCutPositiveCapture hindex S r hmem
  have hmem2 := T.saddlePositiveParam_mem_branch_orbit_full H hindex r.1
    (D.chronologicalSaddleBoundaryRadius t ht) S.scale u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (saddleArcCutScale_sq_lt_saddleBoundaryRadius_sq S)
    (hu.trans_le (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht))
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (saddleArcCutAfterTime_regular S)
    (saddleArcCutAfterField S)
  rw [hend] at hmem2
  exact hmem2


-- @@ L768-800 verbatim
/-- Negative counterpart: a captured backward-flowed end lies on the
labelled negative local branch orbit. -/
theorem saddleArcCut_negativeFlow_mem_branchOrbit
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B)
    (r : SaddleBranch × SaddleBranch)
    (hmem : (D.position.eventModel t ht).param
        (saddleCriticalBoundaryEndParam r Cov.sigma) ∈
      SaddleCriticalExteriorArc.recoveryCore (n := n) B) :
    spacePart ((saddleArcCutTimeField Cov B).base.flow
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd r
          Cov.sigma) (-(S.scale ^ 2))) ∈
      (saddleArcCutBeforeField S).orbit
        (spacePart
          ((D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchBase
            r.2 (D.chronologicalSaddleBoundaryRadius t ht) S.scale)) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  obtain ⟨u, hu, hend, hsign, hquad⟩ :=
    exists_saddleArcCutNegativeCapture hindex S r hmem
  have hmem2 := T.saddleNegativeParam_mem_branch_orbit_full H hindex r.2
    (D.chronologicalSaddleBoundaryRadius t ht) S.scale u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (saddleArcCutScale_sq_lt_saddleBoundaryRadius_sq S)
    (hu.trans_le (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht))
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (saddleArcCutBeforeTime_regular S)
    (saddleArcCutBeforeField S)
  rw [hend] at hmem2
  exact hmem2


-- @@ L802-802 verbatim
/-! ## One arc puts the two labelled branch bases on one orbit -/


-- @@ L804-840 verbatim
/-- Flowing the arc for the safe positive time puts the two labelled
positive branch bases on one orbit of the per-arc after slice. -/
theorem saddleArcCut_positiveBase_mem
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    spacePart
        ((D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchBase
          q.1 (D.chronologicalSaddleBoundaryRadius t ht) S.scale) ∈
      (saddleArcCutAfterField S).orbit
        (spacePart
          ((D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchBase
            p.1 (D.chronologicalSaddleBoundaryRadius t ht) S.scale)) := by
  let V := saddleArcCutAfterField S
  have hsafe : |S.scale ^ 2| ≤ (saddleArcCutTimeField Cov B).safeTime := by
    rw [abs_of_nonneg (sq_nonneg S.scale)]
    exact S.safe
  have hflow : spacePart ((saddleArcCutTimeField Cov B).base.flow
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd q
        Cov.sigma) (S.scale ^ 2)) ∈
      V.orbit (spacePart ((saddleArcCutTimeField Cov B).base.flow
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p
          Cov.sigma) (S.scale ^ 2))) := by
    exact SaddleCriticalExteriorArc.flowed_target_mem_source_orbit
      (n := n) (C := D.signedOutput.cobordism) (P := D.position)
      (t := t) (ht := ht) B hsafe
      (saddleArcCutAfterTime_regular S) V
  have hmemP := saddleArcCut_positiveFlow_mem_branchOrbit hindex S p
    (saddleArcCut_source_mem_core Cov B)
  have hmemQ := saddleArcCut_positiveFlow_mem_branchOrbit hindex S q
    (saddleArcCut_target_mem_core Cov B)
  have heqP := V.orbit_eq_of_mem hmemP
  have heqQ := V.orbit_eq_of_mem hmemQ
  have heqFlow := V.orbit_eq_of_mem hflow
  rw [← heqP, ← heqFlow, heqQ]
  exact V.mem_orbit_self _


-- @@ L842-881 verbatim
/-- Flowing the arc for the safe negative time puts the two labelled
negative branch bases on one orbit of the per-arc before slice. -/
theorem saddleArcCut_negativeBase_mem
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    spacePart
        ((D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchBase
          q.2 (D.chronologicalSaddleBoundaryRadius t ht) S.scale) ∈
      (saddleArcCutBeforeField S).orbit
        (spacePart
          ((D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchBase
            p.2 (D.chronologicalSaddleBoundaryRadius t ht) S.scale)) := by
  let V := saddleArcCutBeforeField S
  have hsafe : |-(S.scale ^ 2)| ≤ (saddleArcCutTimeField Cov B).safeTime := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg S.scale)]
    exact S.safe
  have hreg : sliceRegular D.signedOutput.cobordism.G
      (tcoord (D.position.eventCenter t ht) + -(S.scale ^ 2)) := by
    simpa only [saddleArcCutBeforeTime, sub_eq_add_neg] using
      saddleArcCutBeforeTime_regular S
  have hflow : spacePart ((saddleArcCutTimeField Cov B).base.flow
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd q
        Cov.sigma) (-(S.scale ^ 2))) ∈
      V.orbit (spacePart ((saddleArcCutTimeField Cov B).base.flow
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p
          Cov.sigma) (-(S.scale ^ 2)))) := by
    exact SaddleCriticalExteriorArc.flowed_target_mem_source_orbit
      (n := n) (C := D.signedOutput.cobordism) (P := D.position)
      (t := t) (ht := ht) B hsafe hreg V
  have hmemP := saddleArcCut_negativeFlow_mem_branchOrbit hindex S p
    (saddleArcCut_source_mem_core Cov B)
  have hmemQ := saddleArcCut_negativeFlow_mem_branchOrbit hindex S q
    (saddleArcCut_target_mem_core Cov B)
  have heqP := V.orbit_eq_of_mem hmemP
  have heqQ := V.orbit_eq_of_mem hmemQ
  have heqFlow := V.orbit_eq_of_mem hflow
  rw [← heqP, ← heqFlow, heqQ]
  exact V.mem_orbit_self _


-- @@ L883-883 verbatim
/-! ## Transport of the per-arc branch bases to the fixed window slices -/


-- @@ L885-1033 verbatim
/-- Transporting a positive branch base from the per-arc slice to the fixed
chronological after slice lands on the chronological branch orbit.  The path
witness interpolates the boundary level from the per-arc scale to the fixed
window radius along the local hyperbola branch. -/
theorem saddleArcCut_positiveBase_window_orbit
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) (branch : SaddleBranch) :
    spacePart
        ((D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchBase
          branch (D.chronologicalSaddleBoundaryRadius t ht)
          (D.chronologicalWindowRadius t ht)) ∈
      (D.chronologicalAfterField t ht).orbit
        ((saddleArcCutAfterSlabField S).sliceTransport
          (saddleArcCutAfterTime S) (D.chronologicalAfterTime t ht)
          (spacePart
            ((D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchBase
              branch (D.chronologicalSaddleBoundaryRadius t ht)
              S.scale))) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let b := S.scale
  let afix := D.chronologicalWindowRadius t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let sourceTime := saddleArcCutAfterTime S
  let targetTime := D.chronologicalAfterTime t ht
  let hreg := regularSlab_saddleArcCutAfter_to_window S
  let W := saddleArcCutAfterSlabField S
  let Vtarget := D.chronologicalAfterField t ht
  let c : C(I, ℝ) := {
    toFun := fun w => b + (w : ℝ) * (afix - b)
    continuous_toFun :=
      continuous_const.add (continuous_subtype_val.mul continuous_const) }
  have hbc (w : I) : b ≤ c w := by
    dsimp [c]
    have hw₀ : 0 ≤ (w : ℝ) := w.property.1
    have hab : 0 < afix - b := sub_pos.mpr S.scale_lt_window
    nlinarith
  have hca (w : I) : c w ≤ afix := by
    dsimp [c]
    have hw₁ : (w : ℝ) ≤ 1 := w.property.2
    have hab : 0 < afix - b := sub_pos.mpr S.scale_lt_window
    nlinarith
  have hcpos (w : I) : 0 < c w := S.scale_pos.trans_le (hbc w)
  have hcr (w : I) : c w < r :=
    (hca w).trans_lt (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)
  have hcsq (w : I) : (c w) ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (hcpos w).le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2 (hcr w)
  let u : I → E₂ := fun w =>
    saddlePositiveBoundaryEndParam branch .negative r (c w)
  have hucont : Continuous u := by
    dsimp [u, c]
    cases branch <;>
      simp [saddlePositiveBoundaryEndParam, saddlePositiveArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have huRadius (w : I) : ‖u w‖ < M.radius := by
    rw [show ‖u w‖ = r from
      norm_saddlePositiveBoundaryEndParam branch .negative
        (D.chronologicalSaddleBoundaryRadius_pos t ht) (hcsq w)]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  let z : C(I, E') := {
    toFun := fun w => M.param (u w)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro w
      exact (H.differentiableAt (u w) (huRadius w)).continuousAt.comp'
        hucont.continuousAt }
  let tau : C(I, ℝ) := {
    toFun := fun w => afix ^ 2 - (c w) ^ 2
    continuous_toFun := continuous_const.sub (c.continuous.pow 2) }
  let gamma : C(I, E₁) := {
    toFun := fun w => spacePart (W.flow (z w) (tau w))
    continuous_toFun := continuous_spacePart.comp
      (W.continuous_flow_uncurry.comp
        (z.continuous.prodMk tau.continuous)) }
  have hsourceMem (w : I) :
      tcoord (D.position.eventCenter t ht) + (c w) ^ 2 ∈
        Icc sourceTime targetTime := by
    have hbSq : b ^ 2 ≤ (c w) ^ 2 :=
      (sq_le_sq₀ S.scale_pos.le (hcpos w).le).2 (hbc w)
    have hcSq : (c w) ^ 2 ≤ afix ^ 2 :=
      (sq_le_sq₀ (hcpos w).le
        (D.chronologicalWindowRadius_pos t ht).le).2 (hca w)
    constructor
    · simpa [sourceTime, saddleArcCutAfterTime, b] using
        add_le_add_left hbSq (tcoord (D.position.eventCenter t ht))
    · simpa [targetTime, chronologicalAfterTime, afix] using
        add_le_add_left hcSq (tcoord (D.position.eventCenter t ht))
  have htargetMem : targetTime ∈ Icc sourceTime targetTime :=
    ⟨saddleArcCutAfterTime_le_window S, le_rfl⟩
  have hzFiber (w : I) : D.signedOutput.cobordism.G (z w) = 0 := by
    exact M.param_fiber (u w) (huRadius w)
  have hzTime (w : I) : tcoord (z w) =
      tcoord (D.position.eventCenter t ht) + (c w) ^ 2 := by
    have htime := M.time_model (u w) (huRadius w)
    rw [hindex] at htime
    simpa [z, u, saddlePositiveBoundaryEndParam] using htime
  have hgammaFiber : ∀ w,
      gamma w ∈ (D.chronologicalAfterSlice t ht).fiber := by
    intro w
    have hx : spacePart (z w) ∈ SlabTamedField.sliceFiber
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) + (c w) ^ 2) := by
      change D.signedOutput.cobordism.G
        (cobSpaceTime (spacePart (z w))
          (tcoord (D.position.eventCenter t ht) + (c w) ^ 2)) = 0
      rw [← hzTime w, spaceTime_spacePart]
      exact hzFiber w
    have hmap := W.sliceTransport_mapsTo hreg (hsourceMem w) htargetMem hx
    have hzst : cobSpaceTime (spacePart (z w))
        (tcoord (D.position.eventCenter t ht) + (c w) ^ 2) = z w := by
      rw [← hzTime w, spaceTime_spacePart]
    rw [SlabTamedField.sliceTransport, hzst] at hmap
    change D.signedOutput.cobordism.toLevelCobordismData.G
      (cobSpaceTime (gamma w) targetTime) = 0
    simpa [SlabTamedField.sliceFiber, gamma, tau, targetTime,
      chronologicalAfterTime, afix] using hmap
  have hgamma₀ : gamma 0 =
      W.sliceTransport sourceTime targetTime
        (spacePart (T.saddlePositiveBranchBase branch r b)) := by
    have hz₀Time : tcoord (z 0) = sourceTime := by
      simpa [sourceTime, saddleArcCutAfterTime, c, b] using hzTime 0
    have hz₀st : cobSpaceTime (spacePart (z 0)) sourceTime = z 0 := by
      rw [← hz₀Time, spaceTime_spacePart]
    have hz₀Base : z 0 = T.saddlePositiveBranchBase branch r b := by
      simp [z, u, c,
        StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint, M, T, b, r]
    rw [SlabTamedField.sliceTransport, ← hz₀Base, hz₀st]
    simp [gamma, tau, z, u, c, sourceTime, targetTime,
      saddleArcCutAfterTime, chronologicalAfterTime,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r]
  have hgamma₁ : gamma 1 =
      spacePart (T.saddlePositiveBranchBase branch r afix) := by
    simp [gamma, tau, z, u, c,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r]
  have hpath := Vtarget.continuousMap_mem_orbit gamma hgammaFiber 1
  rw [hgamma₀, hgamma₁] at hpath
  exact hpath


-- @@ L1035-1180 verbatim
/-- Negative counterpart of `saddleArcCut_positiveBase_window_orbit`. -/
theorem saddleArcCut_negativeBase_window_orbit
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) (branch : SaddleBranch) :
    spacePart
        ((D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchBase
          branch (D.chronologicalSaddleBoundaryRadius t ht)
          (D.chronologicalWindowRadius t ht)) ∈
      (D.chronologicalBeforeField t ht).orbit
        ((saddleArcCutBeforeSlabField S).sliceTransport
          (saddleArcCutBeforeTime S) (D.chronologicalBeforeTime t ht)
          (spacePart
            ((D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchBase
              branch (D.chronologicalSaddleBoundaryRadius t ht)
              S.scale))) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let b := S.scale
  let afix := D.chronologicalWindowRadius t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let sourceTime := saddleArcCutBeforeTime S
  let targetTime := D.chronologicalBeforeTime t ht
  let hreg := regularSlab_window_to_saddleArcCutBefore S
  let W := saddleArcCutBeforeSlabField S
  let Vtarget := D.chronologicalBeforeField t ht
  let c : C(I, ℝ) := {
    toFun := fun w => b + (w : ℝ) * (afix - b)
    continuous_toFun :=
      continuous_const.add (continuous_subtype_val.mul continuous_const) }
  have hbc (w : I) : b ≤ c w := by
    dsimp [c]
    have hw₀ : 0 ≤ (w : ℝ) := w.property.1
    have hab : 0 < afix - b := sub_pos.mpr S.scale_lt_window
    nlinarith
  have hca (w : I) : c w ≤ afix := by
    dsimp [c]
    have hw₁ : (w : ℝ) ≤ 1 := w.property.2
    have hab : 0 < afix - b := sub_pos.mpr S.scale_lt_window
    nlinarith
  have hcpos (w : I) : 0 < c w := S.scale_pos.trans_le (hbc w)
  have hcr (w : I) : c w < r :=
    (hca w).trans_lt (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)
  have hcsq (w : I) : (c w) ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (hcpos w).le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2 (hcr w)
  let u : I → E₂ := fun w =>
    saddleNegativeBoundaryEndParam branch .negative r (c w)
  have hucont : Continuous u := by
    dsimp [u, c]
    cases branch <;>
      simp [saddleNegativeBoundaryEndParam, saddleNegativeArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have huRadius (w : I) : ‖u w‖ < M.radius := by
    rw [show ‖u w‖ = r from
      norm_saddleNegativeBoundaryEndParam branch .negative
        (D.chronologicalSaddleBoundaryRadius_pos t ht) (hcsq w)]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  let z : C(I, E') := {
    toFun := fun w => M.param (u w)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro w
      exact (H.differentiableAt (u w) (huRadius w)).continuousAt.comp'
        hucont.continuousAt }
  let tau : C(I, ℝ) := {
    toFun := fun w => (c w) ^ 2 - afix ^ 2
    continuous_toFun := (c.continuous.pow 2).sub continuous_const }
  let gamma : C(I, E₁) := {
    toFun := fun w => spacePart (W.flow (z w) (tau w))
    continuous_toFun := continuous_spacePart.comp
      (W.continuous_flow_uncurry.comp
        (z.continuous.prodMk tau.continuous)) }
  have hsourceMem (w : I) :
      tcoord (D.position.eventCenter t ht) - (c w) ^ 2 ∈
        Icc targetTime sourceTime := by
    have hbSq : b ^ 2 ≤ (c w) ^ 2 :=
      (sq_le_sq₀ S.scale_pos.le (hcpos w).le).2 (hbc w)
    have hcSq : (c w) ^ 2 ≤ afix ^ 2 :=
      (sq_le_sq₀ (hcpos w).le
        (D.chronologicalWindowRadius_pos t ht).le).2 (hca w)
    constructor
    · simpa [targetTime, chronologicalBeforeTime, afix] using
        sub_le_sub_left hcSq (tcoord (D.position.eventCenter t ht))
    · simpa [sourceTime, saddleArcCutBeforeTime, b] using
        sub_le_sub_left hbSq (tcoord (D.position.eventCenter t ht))
  have htargetMem : targetTime ∈ Icc targetTime sourceTime :=
    ⟨le_rfl, window_le_saddleArcCutBeforeTime S⟩
  have hzFiber (w : I) : D.signedOutput.cobordism.G (z w) = 0 := by
    exact M.param_fiber (u w) (huRadius w)
  have hzTime (w : I) : tcoord (z w) =
      tcoord (D.position.eventCenter t ht) - (c w) ^ 2 := by
    have htime := M.time_model (u w) (huRadius w)
    rw [hindex] at htime
    simpa [z, u, saddleNegativeBoundaryEndParam, sub_eq_add_neg] using htime
  have hgammaFiber : ∀ w,
      gamma w ∈ (D.chronologicalBeforeSlice t ht).fiber := by
    intro w
    have hx : spacePart (z w) ∈ SlabTamedField.sliceFiber
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) - (c w) ^ 2) := by
      change D.signedOutput.cobordism.G
        (cobSpaceTime (spacePart (z w))
          (tcoord (D.position.eventCenter t ht) - (c w) ^ 2)) = 0
      rw [← hzTime w, spaceTime_spacePart]
      exact hzFiber w
    have hmap := W.sliceTransport_mapsTo hreg (hsourceMem w) htargetMem hx
    have hzst : cobSpaceTime (spacePart (z w))
        (tcoord (D.position.eventCenter t ht) - (c w) ^ 2) = z w := by
      rw [← hzTime w, spaceTime_spacePart]
    rw [SlabTamedField.sliceTransport, hzst] at hmap
    change D.signedOutput.cobordism.toLevelCobordismData.G
      (cobSpaceTime (gamma w) targetTime) = 0
    simpa [SlabTamedField.sliceFiber, gamma, tau, targetTime,
      chronologicalBeforeTime, afix] using hmap
  have hgamma₀ : gamma 0 =
      W.sliceTransport sourceTime targetTime
        (spacePart (T.saddleNegativeBranchBase branch r b)) := by
    have hz₀Time : tcoord (z 0) = sourceTime := by
      simpa [sourceTime, saddleArcCutBeforeTime, c, b] using hzTime 0
    have hz₀st : cobSpaceTime (spacePart (z 0)) sourceTime = z 0 := by
      rw [← hz₀Time, spaceTime_spacePart]
    have hz₀Base : z 0 = T.saddleNegativeBranchBase branch r b := by
      simp [z, u, c,
        StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
        StandardMorseEventAt.saddleNegativeBoundaryEnd,
        StandardMorseEventAt.localPoint, M, T, b, r]
    rw [SlabTamedField.sliceTransport, ← hz₀Base, hz₀st]
    simp [gamma, tau, z, u, c, sourceTime, targetTime,
      saddleArcCutBeforeTime, chronologicalBeforeTime,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
      StandardMorseEventAt.saddleNegativeBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r]
  have hgamma₁ : gamma 1 =
      spacePart (T.saddleNegativeBranchBase branch r afix) := by
    simp [gamma, tau, z, u, c,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
      StandardMorseEventAt.saddleNegativeBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r]
  have hpath := Vtarget.continuousMap_mem_orbit gamma hgammaFiber 1
  rw [hgamma₀, hgamma₁] at hpath
  exact hpath


-- @@ L1182-1182 verbatim
/-! ## Window-level orbit equalities forced by one critical arc -/


-- @@ L1184-1233 verbatim
/-- One punctured critical arc between two labelled ends forces equality of
the two labelled positive branch orbits at the fixed chronological window. -/
theorem saddleArcCut_positiveWindowOrbit_eq
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    D.chronologicalSaddlePositiveOrbit t ht hindex p.1 =
      D.chronologicalSaddlePositiveOrbit t ht hindex q.1 := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let afix := D.chronologicalWindowRadius t ht
  let V := saddleArcCutAfterField S
  let Vwin := D.chronologicalAfterField t ht
  let W := saddleArcCutAfterSlabField S
  let hregslab := regularSlab_saddleArcCutAfter_to_window S
  have hsrc : saddleArcCutAfterTime S ∈
      Icc (saddleArcCutAfterTime S) (D.chronologicalAfterTime t ht) :=
    ⟨le_rfl, saddleArcCutAfterTime_le_window S⟩
  have htgt : D.chronologicalAfterTime t ht ∈
      Icc (saddleArcCutAfterTime S) (D.chronologicalAfterTime t ht) :=
    ⟨saddleArcCutAfterTime_le_window S, le_rfl⟩
  have hbase := saddleArcCut_positiveBase_mem hindex S
  have hfib : spacePart (T.saddlePositiveBranchBase p.1 r S.scale) ∈
      (T.saddlePositiveSlice S.scale
        (saddleArcCutAfterTime_regular S)).fiber :=
    T.saddlePositiveBranchBase_mem_fiber hindex p.1
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (saddleArcCutScale_sq_lt_saddleBoundaryRadius_sq S)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (saddleArcCutAfterTime_regular S)
  have htrans := W.sliceTransport_mapsTo_orbit hregslab hsrc htgt
    V Vwin hfib hbase
  have hpWin := saddleArcCut_positiveBase_window_orbit hindex S p.1
  have hqWin := saddleArcCut_positiveBase_window_orbit hindex S q.1
  apply Subtype.ext
  change Vwin.orbit (spacePart (T.saddlePositiveBranchBase p.1 r afix)) =
    Vwin.orbit (spacePart (T.saddlePositiveBranchBase q.1 r afix))
  calc
    Vwin.orbit (spacePart (T.saddlePositiveBranchBase p.1 r afix)) =
        Vwin.orbit (W.sliceTransport (saddleArcCutAfterTime S)
          (D.chronologicalAfterTime t ht)
          (spacePart (T.saddlePositiveBranchBase p.1 r S.scale))) :=
      Vwin.orbit_eq_of_mem hpWin
    _ = Vwin.orbit (W.sliceTransport (saddleArcCutAfterTime S)
          (D.chronologicalAfterTime t ht)
          (spacePart (T.saddlePositiveBranchBase q.1 r S.scale))) :=
      (Vwin.orbit_eq_of_mem htrans).symm
    _ = Vwin.orbit (spacePart (T.saddlePositiveBranchBase q.1 r afix)) :=
      (Vwin.orbit_eq_of_mem hqWin).symm


-- @@ L1235-1284 verbatim
/-- One punctured critical arc between two labelled ends forces equality of
the two labelled negative branch orbits at the fixed chronological window. -/
theorem saddleArcCut_negativeWindowOrbit_eq
    (hindex : (D.position.eventModel t ht).index = .saddle)
    {Cov : ChronologicalSaddleSmallEndCover D t ht}
    {p q : SaddleBranch × SaddleBranch} {B : SaddleArcCutArc Cov p q}
    (S : SaddleArcCutScale Cov B) :
    D.chronologicalSaddleNegativeOrbit t ht hindex p.2 =
      D.chronologicalSaddleNegativeOrbit t ht hindex q.2 := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let afix := D.chronologicalWindowRadius t ht
  let V := saddleArcCutBeforeField S
  let Vwin := D.chronologicalBeforeField t ht
  let W := saddleArcCutBeforeSlabField S
  let hregslab := regularSlab_window_to_saddleArcCutBefore S
  have hsrc : saddleArcCutBeforeTime S ∈
      Icc (D.chronologicalBeforeTime t ht) (saddleArcCutBeforeTime S) :=
    ⟨window_le_saddleArcCutBeforeTime S, le_rfl⟩
  have htgt : D.chronologicalBeforeTime t ht ∈
      Icc (D.chronologicalBeforeTime t ht) (saddleArcCutBeforeTime S) :=
    ⟨le_rfl, window_le_saddleArcCutBeforeTime S⟩
  have hbase := saddleArcCut_negativeBase_mem hindex S
  have hfib : spacePart (T.saddleNegativeBranchBase p.2 r S.scale) ∈
      (T.saddleNegativeSlice S.scale
        (saddleArcCutBeforeTime_regular S)).fiber :=
    T.saddleNegativeBranchBase_mem_fiber hindex p.2
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (saddleArcCutScale_sq_lt_saddleBoundaryRadius_sq S)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (saddleArcCutBeforeTime_regular S)
  have htrans := W.sliceTransport_mapsTo_orbit hregslab hsrc htgt
    V Vwin hfib hbase
  have hpWin := saddleArcCut_negativeBase_window_orbit hindex S p.2
  have hqWin := saddleArcCut_negativeBase_window_orbit hindex S q.2
  apply Subtype.ext
  change Vwin.orbit (spacePart (T.saddleNegativeBranchBase p.2 r afix)) =
    Vwin.orbit (spacePart (T.saddleNegativeBranchBase q.2 r afix))
  calc
    Vwin.orbit (spacePart (T.saddleNegativeBranchBase p.2 r afix)) =
        Vwin.orbit (W.sliceTransport (saddleArcCutBeforeTime S)
          (D.chronologicalBeforeTime t ht)
          (spacePart (T.saddleNegativeBranchBase p.2 r S.scale))) :=
      Vwin.orbit_eq_of_mem hpWin
    _ = Vwin.orbit (W.sliceTransport (saddleArcCutBeforeTime S)
          (D.chronologicalBeforeTime t ht)
          (spacePart (T.saddleNegativeBranchBase q.2 r S.scale))) :=
      (Vwin.orbit_eq_of_mem htrans).symm
    _ = Vwin.orbit (spacePart (T.saddleNegativeBranchBase q.2 r afix)) :=
      (Vwin.orbit_eq_of_mem hqWin).symm


-- @@ L1286-1286 verbatim
/-! ## The residual oriented parity statement -/


-- @@ L1288-1303 verbatim
/-- The residual regular-slice orientation input: a production saddle cannot
merge its two incoming branches and split into two outgoing branches at the
same time.  Equivalently, if the two positive local branches lie on one
after-slice orbit then the two negative local branches lie on two distinct
before-slice orbits.  This is the orientation content of the oriented
one-manifold surgery at a saddle (Pontryagin's Theorem 20): an oriented
saddle changes the number of fiber components by exactly one. -/
structure ChronologicalSaddleOrientedCutParity
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop where
  positive_common_excludes_negative :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
        D.chronologicalSaddlePositiveOrbit t ht hindex .positive →
      D.chronologicalSaddleNegativeOrbit t ht hindex .negative ≠
        D.chronologicalSaddleNegativeOrbit t ht hindex .positive


-- @@ L1305-1321 verbatim
/-- The merge/split topology dichotomy implies the cut-order parity: a merge
keeps its two negative branch orbits distinct, while a split keeps its two
positive branch orbits distinct.  In particular the parity follows from the
project's single residual global law via
`ChronologicalSaddleGlobalLaw.topologyDichotomy`. -/
theorem chronologicalSaddleOrientedCutParity_of_topologyDichotomy
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (h : D.ChronologicalSaddleMergeTopology t ht hindex ∨
      D.ChronologicalSaddleSplitTopology t ht hindex) :
    ChronologicalSaddleOrientedCutParity D t ht hindex where
  positive_common_excludes_negative := by
    intro hposEq
    rcases h with hm | hs
    · exact hm.negative_ne
    · exact absurd hposEq hs.positive_ne


-- @@ L1323-1323 verbatim
/-! ## The checker separation theorem -/


-- @@ L1325-1376 verbatim
/-- Oriented endpoint theorem for arbitrary punctured critical saddle arcs,
conditional on the cut-order parity: two distinct labelled ends joined by an
arc inside the punctured critical slice carry opposite checkerboard
labels.  This is precisely the hypothesis `arc_checker_ne` of
`saddlePuncturedCriticalArcPairingData_of_candidate`. -/
theorem saddleArcCut_checker_ne_of_parity
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Par : ChronologicalSaddleOrientedCutParity D t ht hindex)
    {rho : ℝ} (hrho : 0 < rho)
    (hrho_radius : rho < (D.chronologicalEventEmbeddedShrink t ht).radius)
    {p q : SaddleBranch × SaddleBranch} (hne : q ≠ p)
    (harc : Nonempty (SaddleCriticalExteriorArc
      (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r rho)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht)) p q)) :
    saddleBranchEndChecker p ≠ saddleBranchEndChecker q := by
  intro hchecker
  obtain ⟨Cov⟩ := nonempty_chronologicalSaddleSmallEndCover D t ht
  have hBne : Nonempty (SaddleArcCutArc Cov p q) :=
    harc.map fun B0 =>
      B0.changeSaddleBoundaryRadius
        (D.chronologicalEventEmbeddedShrink t ht)
        (D.chronologicalEventFullRadiusSmooth t ht) hindex
        hrho Cov.sigma_pos hrho_radius Cov.sigma_lt_embedded
  obtain ⟨B⟩ := hBne
  obtain ⟨S⟩ := nonempty_saddleArcCutScale Cov B
  have hpos := saddleArcCut_positiveWindowOrbit_eq hindex S
  have hneg := saddleArcCut_negativeWindowOrbit_eq hindex S
  have hlabels : p.1 ≠ q.1 ∧ p.2 ≠ q.2 := by
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
      simp_all [saddleBranchEndChecker]
  have hposNP : D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive := by
    have h := hpos
    cases hp1 : p.1 <;> cases hq1 : q.1 <;> rw [hp1, hq1] at h
    · exact absurd (hp1.trans hq1.symm) hlabels.1
    · exact h.symm
    · exact h
    · exact absurd (hp1.trans hq1.symm) hlabels.1
  have hnegNP : D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive := by
    have h := hneg
    cases hp2 : p.2 <;> cases hq2 : q.2 <;> rw [hp2, hq2] at h
    · exact absurd (hp2.trans hq2.symm) hlabels.2
    · exact h.symm
    · exact h
    · exact absurd (hp2.trans hq2.symm) hlabels.2
  exact Par.positive_common_excludes_negative hposNP hnegNP


-- @@ L1378-1395 verbatim
/-- The exact `arc_checker_ne` closure form at the chronological boundary
radius, ready for `saddlePuncturedCriticalArcPairingData_of_candidate`. -/
theorem chronologicalSaddle_arc_checker_ne_of_parity
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Par : ChronologicalSaddleOrientedCutParity D t ht hindex) :
    ∀ {p q : SaddleBranch × SaddleBranch}, q ≠ p →
      Nonempty (SaddleCriticalExteriorArc
        (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r
          (D.chronologicalSaddleBoundaryRadius t ht))
        (StandardMorseEventAt.puncturedCriticalSlice
          D.signedOutput.cobordism (D.position.eventCenter t ht)) p q) →
      saddleBranchEndChecker p ≠ saddleBranchEndChecker q := by
  intro p q hne harc
  exact saddleArcCut_checker_ne_of_parity D t ht hindex Par
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hne harc


-- @@ L1397-1397 verbatim
/-! ## Full pairing data from parity plus candidate mate arcs -/


-- @@ L1399-1420 verbatim
/-- Complete punctured critical-arc pairing data from the parity residual
plus one positive-side (`flipSecond`) candidate arc for every end.  All
uniqueness and orientation obligations are discharged by the checker
separation theorem. -/
theorem chronologicalSaddlePairingData_of_parity_of_flipSecond_arcs
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Par : ChronologicalSaddleOrientedCutParity D t ht hindex)
    (mate_arc : ∀ p, Nonempty (SaddleCriticalExteriorArc
      (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      p (saddleBranchEndFlipSecond p))) :
    (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht) :=
  StandardMorseEventAt.saddlePuncturedCriticalArcPairingData_of_flipSecond
    (D.chronologicalSaddleBoundaryRadius_pos t ht) mate_arc
    (fun {p q} hne harc =>
      chronologicalSaddle_arc_checker_ne_of_parity D t ht hindex Par
        (p := p) (q := q) hne harc)


-- @@ L1422-1440 verbatim
/-- Negative-side (`flipFirst`) counterpart. -/
theorem chronologicalSaddlePairingData_of_parity_of_flipFirst_arcs
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Par : ChronologicalSaddleOrientedCutParity D t ht hindex)
    (mate_arc : ∀ p, Nonempty (SaddleCriticalExteriorArc
      (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      p (saddleBranchEndFlipFirst p))) :
    (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht) :=
  StandardMorseEventAt.saddlePuncturedCriticalArcPairingData_of_flipFirst
    (D.chronologicalSaddleBoundaryRadius_pos t ht) mate_arc
    (fun {p q} hne harc =>
      chronologicalSaddle_arc_checker_ne_of_parity D t ht hindex Par
        (p := p) (q := q) hne harc)


-- @@ L1442-1442 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L1444-1444 verbatim
end Submission
