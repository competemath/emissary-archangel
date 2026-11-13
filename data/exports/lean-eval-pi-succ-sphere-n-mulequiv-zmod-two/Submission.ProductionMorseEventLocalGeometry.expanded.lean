import Submission.FramedMorseDefiniteEvent
import Submission.IndexedMorsePositionAssembly


-- @@ L4-20 verbatim
/-!
# Route-independent local geometry for production Morse events

The first installed-event development was phrased for
`ExactFiniteMorseJetInstallation`.  The assumption-free production route uses
`SharedCutoffMorseData` followed by `StableCriticalValueShiftData` instead.
Both routes, however, end in exactly the same local interface:
`StandardMorseEventAt`.

This file records the part of the definite and saddle geometry which depends
only on that interface.  It then specializes the generic statements to the
actual value-separated event `transportedStandardMorseEvent`.  Consequently
the production chronological schedule has concrete zero-fiber circles,
hyperbola branches, four boundary ends, exact event times, spatial regularity,
and the saddle pairing switch without constructing an
`ExactFiniteMorseJetInstallation`.
-/


-- @@ L22-22 verbatim
set_option autoImplicit false

-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function Metric

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L33-33 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L35-35 verbatim
/-! ## Geometry carried by every exact standard event -/


-- @@ L37-37 verbatim
namespace StandardMorseEventAt


-- @@ L39-39 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L40-40 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L42-46 verbatim
/-- A fixed ambient radius on which the event parameter covers the complete
zero fiber.  This choice belongs to the common event interface, so it is
available before the definite/saddle specializations. -/
def fiberCoverRadius (M : StandardMorseEventAt (n := n) C center) : ℝ :=
  M.covers_fiber.choose


-- @@ L48-51 verbatim
theorem fiberCoverRadius_pos
    (M : StandardMorseEventAt (n := n) C center) :
    0 < M.fiberCoverRadius :=
  M.covers_fiber.choose_spec.1


-- @@ L53-56 verbatim
/-- A route-independent name for a point in the installed event chart. -/
def localPoint (M : StandardMorseEventAt (n := n) C center) (u : E₂) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  M.param u


-- @@ L58-61 verbatim
@[simp] theorem localPoint_zero
    (M : StandardMorseEventAt (n := n) C center) :
    M.localPoint 0 = center :=
  M.param_zero


-- @@ L63-66 verbatim
theorem localPoint_fiber (M : StandardMorseEventAt (n := n) C center)
    (u : E₂) (hu : ‖u‖ < M.radius) :
    C.G (M.localPoint u) = 0 :=
  M.param_fiber u hu


-- @@ L68-72 verbatim
theorem localPoint_time (M : StandardMorseEventAt (n := n) C center)
    (u : E₂) (hu : ‖u‖ < M.radius) :
    tcoord (M.localPoint u) =
      tcoord center + morseQuadratic M.index (u 0, u 1) :=
  M.time_model u hu


-- @@ L74-86 verbatim
/-- Every noncentral point in a standard event chart is spatially regular.
This uses only the zero-fiber and critical-locus fields of the common event
interface. -/
theorem localPoint_spatialDeriv_surjective_of_ne_zero
    (M : StandardMorseEventAt (n := n) C center)
    (u : E₂) (hu : ‖u‖ < M.radius) (hu0 : u ≠ 0) :
    Surjective (spatialDeriv C.G (M.localPoint u)) := by
  have hnot : M.localPoint u ∉ timeCritical C.G := by
    intro hcrit
    exact hu0 ((M.critical_model u hu).mp (by
      simpa [localPoint] using hcrit))
  by_contra hns
  exact hnot ⟨M.localPoint_fiber u hu, hns⟩


-- @@ L88-88 verbatim
/-! ### Definite circles -/


-- @@ L90-94 verbatim
/-- The literal radius-`a` circle transported through an arbitrary standard
Morse event chart. -/
def definiteCircle (M : StandardMorseEventAt (n := n) C center)
    (a theta : ℝ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  M.localPoint (definiteCircleParam a theta)


-- @@ L96-102 verbatim
theorem definiteCircle_fiber
    (M : StandardMorseEventAt (n := n) C center)
    {a theta : ℝ} (ha : 0 ≤ a) (hrad : a < M.radius) :
    C.G (M.definiteCircle a theta) = 0 := by
  apply M.localPoint_fiber
  rw [norm_definiteCircleParam ha]
  exact hrad


-- @@ L104-111 verbatim
theorem definiteCircle_spatialDeriv_surjective
    (M : StandardMorseEventAt (n := n) C center)
    {a theta : ℝ} (ha : 0 < a) (hrad : a < M.radius) :
    Surjective (spatialDeriv C.G (M.definiteCircle a theta)) := by
  apply M.localPoint_spatialDeriv_surjective_of_ne_zero
  · rw [norm_definiteCircleParam ha.le]
    exact hrad
  · exact definiteCircleParam_ne_zero ha.ne'


-- @@ L113-122 verbatim
/-- The nonempty circle of a minimum lies at time `center + a²`. -/
theorem minimumCircle_time
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .minimum)
    {a theta : ℝ} (ha : 0 ≤ a) (hrad : a < M.radius) :
    tcoord (M.definiteCircle a theta) = tcoord center + a ^ 2 := by
  rw [definiteCircle, localPoint_time M _ (by
    rw [norm_definiteCircleParam ha]
    exact hrad), hindex,
    morseQuadratic_minimum_definiteCircleParam]


-- @@ L124-134 verbatim
/-- The nonempty circle of a maximum lies at time `center - a²`. -/
theorem maximumCircle_time
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .maximum)
    {a theta : ℝ} (ha : 0 ≤ a) (hrad : a < M.radius) :
    tcoord (M.definiteCircle a theta) = tcoord center - a ^ 2 := by
  rw [definiteCircle, localPoint_time M _ (by
    rw [norm_definiteCircleParam ha]
    exact hrad), hindex,
    morseQuadratic_maximum_definiteCircleParam]
  ring


-- @@ L136-136 verbatim
/-! ### Saddle branches and boundary ends -/


-- @@ L138-142 verbatim
/-- A positive-side saddle branch transported through an arbitrary standard
event chart. -/
def saddlePositiveBranch (M : StandardMorseEventAt (n := n) C center)
    (b : SaddleBranch) (a s : ℝ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  M.localPoint (pairToMorseParam (Submission.saddlePositiveArc b a s))


-- @@ L144-148 verbatim
/-- A negative-side saddle branch transported through an arbitrary standard
event chart. -/
def saddleNegativeBranch (M : StandardMorseEventAt (n := n) C center)
    (b : SaddleBranch) (a s : ℝ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  M.localPoint (pairToMorseParam (Submission.saddleNegativeArc b a s))


-- @@ L150-155 verbatim
theorem saddlePositiveBranch_fiber
    (M : StandardMorseEventAt (n := n) C center)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddlePositiveArc b a s)‖ < M.radius) :
    C.G (M.saddlePositiveBranch b a s) = 0 :=
  M.localPoint_fiber _ hu


-- @@ L157-162 verbatim
theorem saddleNegativeBranch_fiber
    (M : StandardMorseEventAt (n := n) C center)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddleNegativeArc b a s)‖ < M.radius) :
    C.G (M.saddleNegativeBranch b a s) = 0 :=
  M.localPoint_fiber _ hu


-- @@ L164-170 verbatim
theorem saddlePositiveBranch_time
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .saddle) (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddlePositiveArc b a s)‖ < M.radius) :
    tcoord (M.saddlePositiveBranch b a s) = tcoord center + a ^ 2 := by
  rw [saddlePositiveBranch, M.localPoint_time _ hu, hindex]
  simp


-- @@ L172-179 verbatim
theorem saddleNegativeBranch_time
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .saddle) (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (Submission.saddleNegativeArc b a s)‖ < M.radius) :
    tcoord (M.saddleNegativeBranch b a s) = tcoord center - a ^ 2 := by
  rw [saddleNegativeBranch, M.localPoint_time _ hu, hindex]
  simp
  ring


-- @@ L181-186 verbatim
/-- One of the four positive-side endpoints on a radius-`ρ` chart boundary. -/
def saddlePositiveBoundaryEnd
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) (ρ a : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  M.localPoint (Submission.saddlePositiveBoundaryEndParam b e ρ a)


-- @@ L188-193 verbatim
/-- One of the four negative-side endpoints on the same chart boundary. -/
def saddleNegativeBoundaryEnd
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) (ρ a : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  M.localPoint (Submission.saddleNegativeBoundaryEndParam b e ρ a)


-- @@ L195-202 verbatim
theorem saddlePositiveBoundaryEnd_fiber
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < M.radius) :
    C.G (M.saddlePositiveBoundaryEnd b e ρ a) = 0 := by
  apply M.localPoint_fiber
  rw [norm_saddlePositiveBoundaryEndParam b e hρ ha]
  exact hρrad


-- @@ L204-211 verbatim
theorem saddleNegativeBoundaryEnd_fiber
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < M.radius) :
    C.G (M.saddleNegativeBoundaryEnd b e ρ a) = 0 := by
  apply M.localPoint_fiber
  rw [norm_saddleNegativeBoundaryEndParam b e hρ ha]
  exact hρrad


-- @@ L213-224 verbatim
theorem saddlePositiveBoundaryEnd_time
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < M.radius) :
    tcoord (M.saddlePositiveBoundaryEnd b e ρ a) =
      tcoord center + a ^ 2 := by
  have hu : ‖Submission.saddlePositiveBoundaryEndParam b e ρ a‖ < M.radius := by
    rw [norm_saddlePositiveBoundaryEndParam b e hρ ha]
    exact hρrad
  rw [saddlePositiveBoundaryEnd, M.localPoint_time _ hu, hindex]
  simp [Submission.saddlePositiveBoundaryEndParam]


-- @@ L226-238 verbatim
theorem saddleNegativeBoundaryEnd_time
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < M.radius) :
    tcoord (M.saddleNegativeBoundaryEnd b e ρ a) =
      tcoord center - a ^ 2 := by
  have hu : ‖Submission.saddleNegativeBoundaryEndParam b e ρ a‖ < M.radius := by
    rw [norm_saddleNegativeBoundaryEndParam b e hρ ha]
    exact hρrad
  rw [saddleNegativeBoundaryEnd, M.localPoint_time _ hu, hindex]
  simp [Submission.saddleNegativeBoundaryEndParam]
  ring


-- @@ L240-251 verbatim
theorem saddlePositiveBoundaryEnd_spatialDeriv_surjective
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < M.radius) :
    Surjective (spatialDeriv C.G (M.saddlePositiveBoundaryEnd b e ρ a)) := by
  have hnorm := norm_saddlePositiveBoundaryEndParam b e hρ ha
  apply M.localPoint_spatialDeriv_surjective_of_ne_zero
  · rw [hnorm]
    exact hρrad
  · intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith


-- @@ L253-264 verbatim
theorem saddleNegativeBoundaryEnd_spatialDeriv_surjective
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < M.radius) :
    Surjective (spatialDeriv C.G (M.saddleNegativeBoundaryEnd b e ρ a)) := by
  have hnorm := norm_saddleNegativeBoundaryEndParam b e hρ ha
  apply M.localPoint_spatialDeriv_surjective_of_ne_zero
  · rw [hnorm]
    exact hρrad
  · intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith


-- @@ L266-274 verbatim
/-- At the critical time the four saddle ends undergo the standard pairing
switch, independently of the global construction route. -/
theorem saddle_boundary_pairing_switch
    (M : StandardMorseEventAt (n := n) C center)
    (b e : SaddleBranch) (ρ : ℝ) :
    M.saddlePositiveBoundaryEnd b e ρ 0 =
      M.saddleNegativeBoundaryEnd e b ρ 0 := by
  exact congrArg M.localPoint
    (Submission.saddle_boundary_pairing_switch b e ρ)


-- @@ L276-276 verbatim
end StandardMorseEventAt


-- @@ L278-278 verbatim
/-! ## The assumption-free production route -/


-- @@ L280-280 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData

-- @@ L281-281 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [instι : Fintype ι]

-- @@ L282-282 verbatim
variable {B : FiniteIFTSurfaceCover C ι}


-- @@ L284-284 verbatim
namespace CriticalValueShiftData


-- @@ L286-298 verbatim
/-- Concrete local geometry of a value-separated production event.  This is
definitionally the generic geometry of `transportedStandardMorseEvent`. -/
def productionEvent
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : (@CriticalValueShiftData n C ι instι B K U χ R))
    (e : (@GlobalCriticalEvent n C ι instι B K U χ R)) :
    StandardMorseEventAt (n := n)
      (@CriticalValueShiftData.output n C ι instι B K U χ R S)
      (@CriticalValueShiftData.shiftedCenter n C ι instι B K U χ R S e) :=
  @CriticalValueShiftData.transportedStandardMorseEvent
    n C ι instι B K U χ R S e


-- @@ L300-307 verbatim
@[simp] theorem productionEvent_index
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : (@CriticalValueShiftData n C ι instι B K U χ R))
    (e : (@GlobalCriticalEvent n C ι instι B K U χ R)) :
    (S.productionEvent e).index = (S.ownerModel e).index :=
  rfl


-- @@ L309-316 verbatim
@[simp] theorem productionEvent_radius
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : (@CriticalValueShiftData n C ι instι B K U χ R))
    (e : (@GlobalCriticalEvent n C ι instι B K U χ R)) :
    (S.productionEvent e).radius = (S.eventTransportShrink e).radius :=
  rfl


-- @@ L318-318 verbatim
end CriticalValueShiftData


-- @@ L320-320 verbatim
/-! ## Chronological access to the same production geometry -/


-- @@ L322-322 verbatim
namespace StableCriticalValueShiftData


-- @@ L324-336 verbatim
/-- The concrete route-independent local event underneath a chronological
event time in the production Morse position. -/
def chronologicalProductionEvent
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : @StableCriticalValueShiftData n C ι instι B K U χ R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    StandardMorseEventAt (n := n) S.output
      (S.shiftedCenter (S.chronologicalGlobalEvent t ht)) :=
  @CriticalValueShiftData.productionEvent
    n C ι instι B K U χ R S.toCriticalValueShiftData
      (S.chronologicalGlobalEvent t ht)


-- @@ L338-347 verbatim
@[simp] theorem chronologicalProductionEvent_index
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : @StableCriticalValueShiftData n C ι instι B K U χ R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    (S.chronologicalProductionEvent t ht).index =
      (S.toCriticalValueShiftData.ownerModel
        (S.chronologicalGlobalEvent t ht)).index :=
  rfl


-- @@ L349-359 verbatim
/-- The center time appearing in every local production formula is literally
the chronological schedule time. -/
theorem chronologicalProductionEvent_center_time
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : @StableCriticalValueShiftData n C ι instι B K U χ R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    tcoord (S.toCriticalValueShiftData.shiftedCenter
      (S.chronologicalGlobalEvent t ht)) = t :=
  S.chronologicalGlobalEvent_time t ht


-- @@ L361-361 verbatim
end StableCriticalValueShiftData

-- @@ L362-362 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L364-364 verbatim
end Submission
