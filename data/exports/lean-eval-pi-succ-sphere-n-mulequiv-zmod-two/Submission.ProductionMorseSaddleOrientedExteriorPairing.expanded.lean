import Submission.SaddleOrientedFourEndPairing
import Submission.ProductionMorseEventEmbeddedGeometry
import Submission.FramedMorseDefiniteNormalLimit


-- @@ L5-22 verbatim
/-!
# Local boundary orientation at a production Morse saddle

The global exterior mate is not part of `StandardMorseEventAt`: that structure
contains the exact Morse chart and its critical-locus description, but no
choice of an arc in the complement of the chart.  What *is* already forced by
the chart is the orientation sign of each of its four ends.

For the saddle quadratic `q(x,y)=x²-y²`, let `J(x,y)=(-y,x)` be the
counterclockwise tangent to the parameter circle.  The boundary sign is

`Dq_(x,y)(J(x,y)) = -4xy`.

Consequently it is positive precisely in the two off-diagonal quadrants,
which is exactly `saddleBranchEndChecker`.  The statements below make this
calculation at the literal boundary parameters used by every
`StandardMorseEventAt`; there is no global pairing assumption in this file.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false

-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace unitInterval


-- @@ L30-30 verbatim
namespace Submission


-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L34-37 verbatim
/-- Counterclockwise tangent to the centered parameter circle at `u`. -/
def saddleBoundaryCounterclockwiseTangent (u : E₂) : E₂ :=
  (-u 1) • EuclideanSpace.single 0 1 +
    (u 0) • EuclideanSpace.single 1 1


-- @@ L39-41 verbatim
@[simp] theorem saddleBoundaryCounterclockwiseTangent_apply_zero (u : E₂) :
    saddleBoundaryCounterclockwiseTangent u 0 = -u 1 := by
  simp [saddleBoundaryCounterclockwiseTangent]


-- @@ L43-45 verbatim
@[simp] theorem saddleBoundaryCounterclockwiseTangent_apply_one (u : E₂) :
    saddleBoundaryCounterclockwiseTangent u 1 = u 0 := by
  simp [saddleBoundaryCounterclockwiseTangent]


-- @@ L47-51 verbatim
/-- The unnormalised oriented-boundary sign in the local Morse chart. -/
def saddleBoundaryOrientationRaw (u : E₂) : ℝ :=
  fderiv ℝ
    (fun z : E₂ => (0 : ℝ) + morseQuadratic .saddle (z 0, z 1)) u
    (saddleBoundaryCounterclockwiseTangent u)


-- @@ L53-59 verbatim
/-- The boundary sign has the expected elementary determinant formula. -/
theorem saddleBoundaryOrientationRaw_eq (u : E₂) :
    saddleBoundaryOrientationRaw u = -4 * u 0 * u 1 := by
  rw [saddleBoundaryOrientationRaw,
    fderiv_const_add_morseQuadratic_apply]
  simp [morseHessianPairing]
  ring


-- @@ L61-68 verbatim
/-- A positive chart-boundary radius gives a nonzero end parameter. -/
theorem saddleBoundaryParameter_pos_at_zero {rho : ℝ} (hrho : 0 < rho) :
    0 < saddleBoundaryParameter rho 0 := by
  unfold saddleBoundaryParameter
  apply Real.sqrt_pos.2
  have hrho_sq : 0 < rho ^ 2 := sq_pos_of_pos hrho
  norm_num
  positivity


-- @@ L70-84 verbatim
/-- On the positive slice, the local boundary orientation is the
checkerboard parity of the component/end labels. -/
theorem saddlePositiveBoundaryOrientation_pos_iff_checker
    (b e : SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    0 < saddleBoundaryOrientationRaw
        (saddlePositiveBoundaryEndParam b e rho 0) ↔
      saddleBranchEndChecker (b, e) = true := by
  have hs : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  rw [saddleBoundaryOrientationRaw_eq]
  cases b <;> cases e <;>
    simp [saddlePositiveBoundaryEndParam, saddlePositiveArc,
      pairToMorseParam, signedBranch, saddleBranchEndChecker,
      Real.sqrt_sq_eq_abs, abs_of_pos hs] <;>
    nlinarith


-- @@ L86-99 verbatim
/-- On the negative slice the labels have the same checkerboard rule. -/
theorem saddleNegativeBoundaryOrientation_pos_iff_checker
    (b e : SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    0 < saddleBoundaryOrientationRaw
        (saddleNegativeBoundaryEndParam b e rho 0) ↔
      saddleBranchEndChecker (b, e) = true := by
  have hs : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  rw [saddleBoundaryOrientationRaw_eq]
  cases b <;> cases e <;>
    simp [saddleNegativeBoundaryEndParam, saddleNegativeArc,
      pairToMorseParam, signedBranch, saddleBranchEndChecker,
      Real.sqrt_sq_eq_abs, abs_of_pos hs] <;>
    nlinarith


-- @@ L101-101 verbatim
/-! ## A concrete bridge from boundary orientation to `checker_reversing` -/


-- @@ L103-108 verbatim
/-- Use the positive-chart labels as a single name for a critical-level end.
The pairing-switch theorem identifies this point with the negative-chart end
whose two labels are exchanged. -/
def saddleCriticalBoundaryEndParam
    (p : SaddleBranch × SaddleBranch) (rho : ℝ) : E₂ :=
  saddlePositiveBoundaryEndParam p.1 p.2 rho 0


-- @@ L110-114 verbatim
theorem saddleCriticalBoundaryEndParam_eq_negative
    (p : SaddleBranch × SaddleBranch) (rho : ℝ) :
    saddleCriticalBoundaryEndParam p rho =
      saddleNegativeBoundaryEndParam p.2 p.1 rho 0 := by
  exact saddle_boundary_pairing_switch p.1 p.2 rho


-- @@ L116-124 verbatim
/-- The local orientation at a critical end is positive exactly when its
checkerboard label is `true`. -/
theorem saddleCriticalBoundaryOrientation_pos_iff_checker
    (p : SaddleBranch × SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    0 < saddleBoundaryOrientationRaw
        (saddleCriticalBoundaryEndParam p rho) ↔
      saddleBranchEndChecker p = true := by
  rcases p with ⟨b, e⟩
  exact saddlePositiveBoundaryOrientation_pos_iff_checker b e hrho


-- @@ L126-140 verbatim
/-- All four local critical-level boundary orientations are nonzero. -/
theorem saddleCriticalBoundaryOrientation_ne_zero
    (p : SaddleBranch × SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    saddleBoundaryOrientationRaw
        (saddleCriticalBoundaryEndParam p rho) ≠ 0 := by
  rcases p with ⟨b, e⟩
  have hs : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  rw [saddleBoundaryOrientationRaw_eq]
  cases b <;> cases e <;>
    simp [saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam, saddlePositiveArc,
      pairToMorseParam, signedBranch,
      Real.sqrt_sq_eq_abs, abs_of_pos hs] <;>
    nlinarith


-- @@ L142-160 verbatim
/-- Two critical ends have opposite local boundary orientations exactly when
their checkerboard labels differ.  This is the geometric content needed from
the local chart by an exterior mate construction. -/
theorem saddleCriticalBoundaryOrientation_mul_neg_iff_checker_ne
    (p q : SaddleBranch × SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    saddleBoundaryOrientationRaw (saddleCriticalBoundaryEndParam p rho) *
        saddleBoundaryOrientationRaw (saddleCriticalBoundaryEndParam q rho) < 0
      ↔ saddleBranchEndChecker p ≠ saddleBranchEndChecker q := by
  rcases p with ⟨bp, ep⟩
  rcases q with ⟨bq, eq⟩
  have hs : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  simp only [saddleCriticalBoundaryEndParam,
    saddleBoundaryOrientationRaw_eq]
  cases bp <;> cases ep <;> cases bq <;> cases eq <;>
    simp [saddlePositiveBoundaryEndParam, saddlePositiveArc,
      pairToMorseParam, signedBranch, saddleBranchEndChecker,
      Real.sqrt_sq_eq_abs, abs_of_pos hs] <;>
    nlinarith


-- @@ L162-187 verbatim
/-- An exterior mate which pairs opposite local boundary orientations
automatically satisfies the finite `checker_reversing` condition.  The only
remaining geometric input is the usual endpoint-orientation theorem for the
actual exterior arcs. -/
def orientedSaddleBranchEndPairingOfBoundaryOrientation
    (rho : ℝ) (hrho : 0 < rho)
    (mate : SaddleBranch × SaddleBranch →
      SaddleBranch × SaddleBranch)
    (mate_involutive : Function.Involutive mate)
    (orientation_opposite : ∀ p,
      saddleBoundaryOrientationRaw
          (saddleCriticalBoundaryEndParam p rho) *
        saddleBoundaryOrientationRaw
          (saddleCriticalBoundaryEndParam (mate p) rho) < 0) :
    OrientedSaddleBranchEndPairing where
  mate := mate
  mate_involutive := mate_involutive
  checker_reversing := by
    intro p
    have hne : saddleBranchEndChecker p ≠
        saddleBranchEndChecker (mate p) :=
      (saddleCriticalBoundaryOrientation_mul_neg_iff_checker_ne
        p (mate p) hrho).mp (orientation_opposite p)
    cases hp : saddleBranchEndChecker p <;>
      cases hmate : saddleBranchEndChecker (mate p) <;>
      simp_all


-- @@ L189-189 verbatim
/-! ## The exact exterior-arc input still missing from the production API -/


-- @@ L191-198 verbatim
/-- A path in the critical exterior between two labelled saddle ends.  The
endpoints are allowed on the boundary of `K`; every point of the path is
required to remain in `K`. -/
structure SaddleCriticalExteriorArc
    {P X : Type*} [TopologicalSpace X]
    (endpoint : P → X) (K : Set X) (p q : P) where
  toPath : Path (endpoint p) (endpoint q)
  mem_exterior : ∀ u : I, toPath u ∈ K


-- @@ L200-200 verbatim
namespace SaddleCriticalExteriorArc


-- @@ L202-202 verbatim
variable {P X : Type*} [TopologicalSpace X]

-- @@ L203-203 verbatim
variable {endpoint : P → X} {K : Set X} {p q : P}


-- @@ L205-212 verbatim
/-- Exterior connectivity is symmetric. -/
def symm
    (A : SaddleCriticalExteriorArc endpoint K p q) :
    SaddleCriticalExteriorArc endpoint K q p where
  toPath := A.toPath.symm
  mem_exterior := by
    intro u
    exact A.mem_exterior (σ u)


-- @@ L214-229 verbatim
/-- Exterior connectivity is transitive. -/
def trans {r : P}
    (A : SaddleCriticalExteriorArc endpoint K p q)
    (B : SaddleCriticalExteriorArc endpoint K q r) :
    SaddleCriticalExteriorArc endpoint K p r where
  toPath := A.toPath.trans B.toPath
  mem_exterior := by
    intro u
    have hu : A.toPath.trans B.toPath u ∈
        Set.range (A.toPath.trans B.toPath) := ⟨u, rfl⟩
    rw [Path.trans_range] at hu
    rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [← hv]
      exact A.mem_exterior v
    · rw [← hv]
      exact B.mem_exterior v


-- @@ L231-231 verbatim
end SaddleCriticalExteriorArc


-- @@ L233-247 verbatim
/-- Minimal honest global input for the four-end argument.

`paired` says that each boundary end lies in one exterior interval component
with a unique *other* labelled endpoint.  `orientation_opposite` is the
boundary-orientation theorem for an oriented one-manifold interval.  Neither
field follows from `StandardMorseEventAt`; proving them for the actual
critical exterior is the remaining global topology step. -/
structure SaddleCriticalExteriorArcPairingData
    {P X : Type*} [TopologicalSpace X]
    (endpoint : P → X) (K : Set X) (boundaryRaw : P → ℝ) where
  paired : ∀ p, ∃! q,
    q ≠ p ∧ Nonempty (SaddleCriticalExteriorArc endpoint K p q)
  orientation_opposite : ∀ {p q},
    q ≠ p → Nonempty (SaddleCriticalExteriorArc endpoint K p q) →
      boundaryRaw p * boundaryRaw q < 0


-- @@ L249-249 verbatim
namespace SaddleCriticalExteriorArcPairingData


-- @@ L251-251 verbatim
variable {P X : Type*} [TopologicalSpace X]

-- @@ L252-252 verbatim
variable {endpoint : P → X} {K : Set X} {boundaryRaw : P → ℝ}


-- @@ L254-274 verbatim
/-- Construct the pairing package from an explicit mate, one arc to that
mate, and uniqueness of the other endpoint of every nontrivial exterior arc.
This is the convenient interface for transporting an arbitrary compact arc
to a sufficiently small regular slice. -/
theorem ofMate
    (mate : P → P)
    (mate_ne : ∀ p, mate p ≠ p)
    (mate_arc : ∀ p,
      Nonempty (SaddleCriticalExteriorArc endpoint K p (mate p)))
    (unique : ∀ {p q}, q ≠ p →
      Nonempty (SaddleCriticalExteriorArc endpoint K p q) → q = mate p)
    (mate_orientation : ∀ p,
      boundaryRaw p * boundaryRaw (mate p) < 0) :
    SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw where
  paired p := ⟨mate p, ⟨mate_ne p, mate_arc p⟩, by
    intro q hq
    exact unique hq.1 hq.2⟩
  orientation_opposite := by
    intro p q hne harc
    rw [unique hne harc]
    exact mate_orientation p


-- @@ L276-280 verbatim
/-- The other endpoint in the unique exterior interval component. -/
noncomputable def mate
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw)
    (p : P) : P :=
  (A.paired p).choose


-- @@ L282-285 verbatim
theorem mate_ne
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw)
    (p : P) : A.mate p ≠ p :=
  (A.paired p).choose_spec.1.1


-- @@ L287-291 verbatim
theorem mate_arc
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw)
    (p : P) :
    Nonempty (SaddleCriticalExteriorArc endpoint K p (A.mate p)) :=
  (A.paired p).choose_spec.1.2


-- @@ L293-298 verbatim
theorem eq_mate_of_ne_arc
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw)
    {p q : P} (hne : q ≠ p)
    (harc : Nonempty (SaddleCriticalExteriorArc endpoint K p q)) :
    q = A.mate p :=
  (A.paired p).choose_spec.2 q ⟨hne, harc⟩


-- @@ L300-309 verbatim
/-- Symmetry of paths plus uniqueness of the other endpoint makes `mate` an
involution; no involutivity assumption is stored. -/
theorem mate_involutive
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw) :
    Function.Involutive A.mate := by
  intro p
  have harc : Nonempty
      (SaddleCriticalExteriorArc endpoint K (A.mate p) p) :=
    A.mate_arc p |>.map SaddleCriticalExteriorArc.symm
  exact (A.eq_mate_of_ne_arc (A.mate_ne p).symm harc).symm


-- @@ L311-317 verbatim
/-- The oriented interval endpoint theorem gives the concrete raw-sign
condition consumed by the local checker calculation. -/
theorem mate_orientation_opposite
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw)
    (p : P) :
    boundaryRaw p * boundaryRaw (A.mate p) < 0 :=
  A.orientation_opposite (A.mate_ne p) (A.mate_arc p)


-- @@ L319-319 verbatim
end SaddleCriticalExteriorArcPairingData


-- @@ L321-321 verbatim
namespace StandardMorseEventAt


-- @@ L323-323 verbatim
variable {n : ℕ}

-- @@ L324-324 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L325-325 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L327-332 verbatim
/-- Ambient realization of a labelled end on the critical chart boundary. -/
def saddleCriticalBoundaryEnd
    (M : StandardMorseEventAt (n := n) C center)
    (p : SaddleBranch × SaddleBranch) (rho : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  M.saddlePositiveBoundaryEnd p.1 p.2 rho 0


-- @@ L334-341 verbatim
/-- The critical zero slice with the saddle center removed.  This, rather
than the regular-time exterior orbit collection, is the space whose interval
components pair the four saddle ends. -/
def puncturedCriticalSlice
    (C : FramedLevelCobordism n)
    (center : EuclideanSpace ℝ (Fin (n + 2))) :
    Set (EuclideanSpace ℝ (Fin (n + 2))) :=
  {x | C.G x = 0 ∧ tcoord x = tcoord center ∧ x ≠ center}


-- @@ L343-343 verbatim
namespace EmbeddedShrink


-- @@ L345-345 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L347-377 verbatim
/-- Every labelled end at a positive radius inside the embedded shrink lies
in the actual punctured critical slice. -/
theorem saddleCriticalBoundaryEnd_mem_puncturedCriticalSlice
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (p : SaddleBranch × SaddleBranch) {rho : ℝ}
    (hrho : 0 < rho) (hrho_radius : rho < T.radius) :
    M.saddleCriticalBoundaryEnd p rho ∈ puncturedCriticalSlice C center := by
  rcases p with ⟨b, e⟩
  have hrho_sq : (0 : ℝ) ^ 2 < rho ^ 2 := by
    nlinarith [sq_pos_of_pos hrho]
  refine ⟨?_, ?_, ?_⟩
  · exact M.saddlePositiveBoundaryEnd_fiber b e hrho hrho_sq
      (hrho_radius.trans_le T.radius_le)
  · simpa [saddleCriticalBoundaryEnd] using
      M.saddlePositiveBoundaryEnd_time hindex b e hrho
      hrho_sq (hrho_radius.trans_le T.radius_le)
  · intro hend
    have hu_mem : saddlePositiveBoundaryEndParam b e rho 0 ∈
        Metric.ball (0 : E₂) T.radius := by
      rw [Metric.mem_ball, dist_zero_right,
        norm_saddlePositiveBoundaryEndParam b e hrho hrho_sq]
      exact hrho_radius
    have hzero_mem : (0 : E₂) ∈ Metric.ball (0 : E₂) T.radius := by
      simpa [Metric.mem_ball] using T.radius_pos
    have hparam : saddlePositiveBoundaryEndParam b e rho 0 = 0 :=
      T.param_injOn hu_mem hzero_mem (by
        simpa [saddleCriticalBoundaryEnd, saddlePositiveBoundaryEnd,
          localPoint, M.param_zero] using hend)
    have hnorm := norm_saddlePositiveBoundaryEndParam b e hrho hrho_sq
    rw [hparam, norm_zero] at hnorm
    linarith


-- @@ L379-379 verbatim
end EmbeddedShrink


-- @@ L381-390 verbatim
/-- The precise unproved global object for a standard saddle chart: exterior
interval components of the actual punctured critical slice, with their
oriented endpoint theorem. -/
abbrev SaddlePuncturedCriticalArcPairingData
    (M : StandardMorseEventAt (n := n) C center) (rho : ℝ) :=
  SaddleCriticalExteriorArcPairingData
    (fun p => M.saddleCriticalBoundaryEnd p rho)
    (puncturedCriticalSlice C center)
    (fun p => saddleBoundaryOrientationRaw
      (saddleCriticalBoundaryEndParam p rho))


-- @@ L392-406 verbatim
/-- Once the actual critical exterior has been proved to be a union of
oriented intervals pairing the four chart ends, the production saddle has an
`OrientedSaddleBranchEndPairing`.  This theorem does not assert that the
required exterior data already exists. -/
noncomputable def orientedSaddleBranchEndPairingOfExteriorArcs
    (M : StandardMorseEventAt (n := n) C center)
    (K : Set (EuclideanSpace ℝ (Fin (n + 2))))
    (rho : ℝ) (hrho : 0 < rho)
    (A : SaddleCriticalExteriorArcPairingData
      (fun p => M.saddleCriticalBoundaryEnd p rho) K
      (fun p => saddleBoundaryOrientationRaw
        (saddleCriticalBoundaryEndParam p rho))) :
    OrientedSaddleBranchEndPairing :=
  orientedSaddleBranchEndPairingOfBoundaryOrientation rho hrho A.mate
    A.mate_involutive A.mate_orientation_opposite


-- @@ L408-415 verbatim
/-- Specialization to the actual punctured critical slice. -/
noncomputable def orientedSaddleBranchEndPairingOfPuncturedCriticalArcs
    (M : StandardMorseEventAt (n := n) C center)
    (rho : ℝ) (hrho : 0 < rho)
    (A : M.SaddlePuncturedCriticalArcPairingData rho) :
    OrientedSaddleBranchEndPairing :=
  M.orientedSaddleBranchEndPairingOfExteriorArcs
    (puncturedCriticalSlice C center) rho hrho A


-- @@ L417-429 verbatim
/-- The same exterior-arc input immediately gives the merge/split matching
dichotomy in geometric branch labels. -/
theorem saddleExteriorArcPairing_eq_flipSecond_or_eq_flipFirst
    (M : StandardMorseEventAt (n := n) C center)
    (K : Set (EuclideanSpace ℝ (Fin (n + 2))))
    (rho : ℝ) (hrho : 0 < rho)
    (A : SaddleCriticalExteriorArcPairingData
      (fun p => M.saddleCriticalBoundaryEnd p rho) K
      (fun p => saddleBoundaryOrientationRaw
        (saddleCriticalBoundaryEndParam p rho))) :
    (∀ p, A.mate p = saddleBranchEndFlipSecond p) ∨
      (∀ p, A.mate p = saddleBranchEndFlipFirst p) :=
  (M.orientedSaddleBranchEndPairingOfExteriorArcs K rho hrho A).eq_flipSecond_or_eq_flipFirst


-- @@ L431-431 verbatim
end StandardMorseEventAt


-- @@ L433-433 verbatim
end Submission
