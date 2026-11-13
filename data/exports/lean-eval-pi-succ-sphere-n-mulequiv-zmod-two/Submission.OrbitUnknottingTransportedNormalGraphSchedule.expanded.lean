import Mathlib
import Submission.OrbitUnknottingNormalGraphTranslation
import Submission.AmbientEndpointConjugation
import Submission.AmbientNormalizationPrimitive
import Submission.AmbientFiniteComponentSchedule


-- @@ L7-27 verbatim
/-!
# Transported schedules of original-tube normal-graph moves

Each `SmallPeriodicNormalGraph` produces an ambient isotopy in the original
orbit tube.  A finite sequence of such original-coordinate moves cannot be
composed naively after the first stage: every later move has to be conjugated
by the endpoint accumulated so far.

This file specializes `SmoothAmbientIsotopy.endpointFoldFrom` to those
normal-graph moves.  It records:

* the empty/cons recursion which performs endpoint conjugation at every stage;
* the final endpoint of every original orbit point as the corresponding
  original-coordinate endpoint fold; and
* stationary behaviour on the common exterior of all original support cores,
  throughout the full transported isotopy.

Thus the only local geometric input left to a downstream application is a
finite list of pairs consisting of an orbit and a
`SmallPeriodicNormalGraph` in its chosen global tube.
-/


-- @@ L29-29 verbatim
set_option autoImplicit false


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
open Set Function Metric

-- @@ L34-34 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L36-36 verbatim
namespace Submission


-- @@ L38-38 verbatim
/-! ## Fixed sets and endpoint-conjugated folds -/


-- @@ L40-40 verbatim
namespace SmoothAmbientIsotopy


-- @@ L42-42 verbatim
variable {n : ℕ}


-- @@ L44-44 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L46-57 verbatim
/-- If both the accumulated isotopy and an original-coordinate move fix the
same set, then transporting that move by the accumulated endpoint still fixes
the original set. -/
theorem FixedOn.conjugateByEndpoint_of_fixedOn
    {A B : SmoothAmbientIsotopy n} {K : Set E}
    (hB : B.FixedOn K) (hA : A.FixedOn K) :
    (B.conjugateByEndpoint A).FixedOn K := by
  intro s hs x hx
  rw [conjugateByEndpoint_forward,
    hA.inverse_eq (s := (1 : ℝ)) ⟨zero_le_one, le_rfl⟩ hx,
    hB s hs x hx,
    hA 1 ⟨zero_le_one, le_rfl⟩ x hx]


-- @@ L59-73 verbatim
/-- Endpoint-conjugated accumulation preserves every fixed set shared by the
initial accumulator and all original-coordinate moves. -/
theorem endpointFoldFrom_fixedOn {K : Set E}
    (A : SmoothAmbientIsotopy n) (moves : List (SmoothAmbientIsotopy n))
    (hA : A.FixedOn K) (hMoves : ∀ B ∈ moves, B.FixedOn K) :
    (endpointFoldFrom A moves).FixedOn K := by
  induction moves generalizing A with
  | nil => simpa using hA
  | cons B tail ih =>
      rw [endpointFoldFrom_cons]
      apply ih
      · exact hA.followedBy
          ((hMoves B (by simp)).conjugateByEndpoint_of_fixedOn hA)
      · intro C hC
        exact hMoves C (List.mem_cons_of_mem B hC)


-- @@ L75-81 verbatim
/-- Accumulation from the identity preserves every fixed set shared by all
original-coordinate moves. -/
theorem endpointFold_fixedOn {K : Set E}
    (moves : List (SmoothAmbientIsotopy n))
    (hMoves : ∀ B ∈ moves, B.FixedOn K) :
    (endpointFold moves).FixedOn K := by
  exact endpointFoldFrom_fixedOn (refl n) moves (fixedOn_refl K) hMoves


-- @@ L83-83 verbatim
end SmoothAmbientIsotopy


-- @@ L85-85 verbatim
/-! ## Original-tube normal-graph movers -/


-- @@ L87-87 verbatim
namespace TamedField


-- @@ L89-89 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L91-91 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L92-92 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)


-- @@ L94-98 verbatim
/-- The minimal datum consumed by the algebraic schedule: one chosen original
orbit and one small periodic normal graph in that orbit's fixed global tube. -/
structure OriginalTubeNormalGraphMover where
  orbit : V.OrbitIndex
  graph : V.SmallPeriodicNormalGraph orbit


-- @@ L100-100 verbatim
variable {V}


-- @@ L102-102 verbatim
namespace OriginalTubeNormalGraphMover


-- @@ L104-104 verbatim
variable (M : V.OriginalTubeNormalGraphMover)


-- @@ L106-109 verbatim
/-- The original-coordinate ambient isotopy supplied by the graph
translation construction. -/
def ambientMove : SmoothAmbientIsotopy n :=
  M.graph.toSmoothAmbientIsotopy


-- @@ L111-113 verbatim
/-- The closed original-tube core containing the support of `ambientMove`. -/
def supportCore : Set E :=
  M.graph.toPeriodicTubeCoordinateIsotopy.supportCore


-- @@ L115-118 verbatim
/-- A point of an original orbit, represented by the zero section of its
chosen tube. -/
def originalOrbitPoint (O : V.OrbitIndex) (u : ℝ) : E :=
  V.orbitTubeLift O (u, (0 : N))


-- @@ L120-122 verbatim
/-- The normal-graph target point prescribed by this mover. -/
def targetGraphPoint (u : ℝ) : E :=
  V.orbitTubeLift M.orbit (u, M.graph.h u)


-- @@ L124-130 verbatim
/-- One graph mover has the advertised endpoint on its original zero
section. -/
theorem ambientMove_forward_originalOrbitPoint (u : ℝ) :
    M.ambientMove.forward 1 (originalOrbitPoint M.orbit u) =
      M.targetGraphPoint u := by
  simpa [ambientMove, originalOrbitPoint, targetGraphPoint] using
    M.graph.toSmoothAmbientIsotopy_forward_orbit_zero u


-- @@ L132-141 verbatim
/-- A graph mover is stationary throughout geometric time outside its closed
original support core. -/
theorem ambientMove_fixedOn_supportCore_compl :
    M.ambientMove.FixedOn M.supportCoreᶜ := by
  intro s _ x hx
  change
    M.graph.toPeriodicTubeCoordinateIsotopy.toSmoothAmbientIsotopy.forward
        s x = x
  exact M.graph.toPeriodicTubeCoordinateIsotopy
    |>.toSmoothAmbientIsotopy_forward_fixed_outside_support s hx


-- @@ L143-143 verbatim
/-! ## The finite transported schedule -/


-- @@ L145-148 verbatim
/-- The list of ambient movers, still expressed in the original tubes. -/
def ambientMoves (moves : List V.OriginalTubeNormalGraphMover) :
    List (SmoothAmbientIsotopy n) :=
  moves.map ambientMove


-- @@ L150-151 verbatim
@[simp] theorem ambientMoves_nil :
    ambientMoves ([] : List V.OriginalTubeNormalGraphMover) = [] := rfl


-- @@ L153-155 verbatim
@[simp] theorem ambientMoves_cons
    (tail : List V.OriginalTubeNormalGraphMover) :
    ambientMoves (M :: tail) = M.ambientMove :: ambientMoves tail := rfl


-- @@ L157-161 verbatim
/-- The original-coordinate endpoint fold.  Its head is the outermost
endpoint map, exactly as in `SmoothAmbientIsotopy.endpointAction`. -/
def originalEndpointFold
    (moves : List V.OriginalTubeNormalGraphMover) : E → E :=
  SmoothAmbientIsotopy.endpointAction (ambientMoves moves)


-- @@ L163-165 verbatim
@[simp] theorem originalEndpointFold_nil (x : E) :
    originalEndpointFold ([] : List V.OriginalTubeNormalGraphMover) x = x :=
  rfl


-- @@ L167-171 verbatim
@[simp] theorem originalEndpointFold_cons
    (tail : List V.OriginalTubeNormalGraphMover) (x : E) :
    originalEndpointFold (M :: tail) x =
      M.ambientMove.forward 1 (originalEndpointFold tail x) :=
  rfl


-- @@ L173-176 verbatim
/-- Accumulation from an arbitrary previous ambient isotopy. -/
def transportedScheduleFrom (A : SmoothAmbientIsotopy n)
    (moves : List V.OriginalTubeNormalGraphMover) : SmoothAmbientIsotopy n :=
  SmoothAmbientIsotopy.endpointFoldFrom A (ambientMoves moves)


-- @@ L178-181 verbatim
/-- The transported schedule starting from the identity. -/
def transportedSchedule
    (moves : List V.OriginalTubeNormalGraphMover) : SmoothAmbientIsotopy n :=
  transportedScheduleFrom (SmoothAmbientIsotopy.refl n) moves


-- @@ L183-186 verbatim
@[simp] theorem transportedScheduleFrom_nil (A : SmoothAmbientIsotopy n) :
    transportedScheduleFrom A
        ([] : List V.OriginalTubeNormalGraphMover) = A :=
  rfl


-- @@ L188-196 verbatim
/-- Cons recurrence: install the head in original coordinates, conjugated by
the endpoint accumulated in `A`, and recurse from that new accumulator. -/
@[simp] theorem transportedScheduleFrom_cons
    (A : SmoothAmbientIsotopy n)
    (tail : List V.OriginalTubeNormalGraphMover) :
    transportedScheduleFrom A (M :: tail) =
      transportedScheduleFrom
        (A.followedBy (M.ambientMove.conjugateByEndpoint A)) tail :=
  rfl


-- @@ L198-201 verbatim
@[simp] theorem transportedSchedule_nil :
    transportedSchedule ([] : List V.OriginalTubeNormalGraphMover) =
      SmoothAmbientIsotopy.refl n :=
  rfl


-- @@ L203-210 verbatim
@[simp] theorem transportedSchedule_cons
    (tail : List V.OriginalTubeNormalGraphMover) :
    transportedSchedule (M :: tail) =
      transportedScheduleFrom
        ((SmoothAmbientIsotopy.refl n).followedBy
          (M.ambientMove.conjugateByEndpoint
            (SmoothAmbientIsotopy.refl n))) tail :=
  rfl


-- @@ L212-219 verbatim
/-- Endpoint tracking from an arbitrary prior accumulator. -/
theorem transportedScheduleFrom_forward_one
    (A : SmoothAmbientIsotopy n)
    (moves : List V.OriginalTubeNormalGraphMover) (x : E) :
    (transportedScheduleFrom A moves).forward 1 x =
      A.forward 1 (originalEndpointFold moves x) := by
  exact SmoothAmbientIsotopy.endpointFoldFrom_forward_one
    A (ambientMoves moves) x


-- @@ L221-229 verbatim
/-- The endpoint of the transported schedule is exactly the nested fold of
the original-tube endpoint maps. -/
@[simp] theorem transportedSchedule_forward_one
    (moves : List V.OriginalTubeNormalGraphMover) (x : E) :
    (transportedSchedule moves).forward 1 x =
      originalEndpointFold moves x := by
  simpa [transportedSchedule] using
    transportedScheduleFrom_forward_one
      (V := V) (SmoothAmbientIsotopy.refl n) moves x


-- @@ L231-238 verbatim
/-- In particular, the final endpoint of every original orbit point is
tracked by the same explicit original-coordinate fold. -/
theorem transportedSchedule_forward_originalOrbitPoint
    (moves : List V.OriginalTubeNormalGraphMover)
    (O : V.OrbitIndex) (u : ℝ) :
    (transportedSchedule moves).forward 1 (originalOrbitPoint O u) =
      originalEndpointFold moves (originalOrbitPoint O u) := by
  exact transportedSchedule_forward_one moves (originalOrbitPoint O u)


-- @@ L240-240 verbatim
/-! ## Common exterior fixedness -/


-- @@ L242-245 verbatim
/-- Points outside every original support core in the finite list. -/
def commonExterior
    (moves : List V.OriginalTubeNormalGraphMover) : Set E :=
  {x | ∀ Q ∈ moves, x ∉ Q.supportCore}


-- @@ L247-251 verbatim
@[simp] theorem mem_commonExterior
    {moves : List V.OriginalTubeNormalGraphMover} {x : E} :
    x ∈ commonExterior moves ↔
      ∀ Q ∈ moves, x ∉ Q.supportCore :=
  Iff.rfl


-- @@ L253-256 verbatim
@[simp] theorem commonExterior_nil :
    commonExterior ([] : List V.OriginalTubeNormalGraphMover) = Set.univ := by
  ext x
  simp [commonExterior]


-- @@ L258-262 verbatim
@[simp] theorem commonExterior_cons
    (tail : List V.OriginalTubeNormalGraphMover) :
    commonExterior (M :: tail) = M.supportCoreᶜ ∩ commonExterior tail := by
  ext x
  simp [commonExterior]


-- @@ L264-272 verbatim
/-- Every listed original mover fixes the common exterior. -/
theorem ambientMove_fixedOn_commonExterior
    {moves : List V.OriginalTubeNormalGraphMover}
    {Q : V.OriginalTubeNormalGraphMover} (hQ : Q ∈ moves) :
    Q.ambientMove.FixedOn (commonExterior moves) := by
  apply Q.ambientMove_fixedOn_supportCore_compl.mono
  intro x hx
  change x ∉ Q.supportCore
  exact (mem_commonExterior.mp hx) Q hQ


-- @@ L274-281 verbatim
/-- List form of common-exterior fixedness, ready for `endpointFold`. -/
theorem ambientMoves_fixedOn_commonExterior
    (moves : List V.OriginalTubeNormalGraphMover) :
    ∀ A ∈ ambientMoves moves, A.FixedOn (commonExterior moves) := by
  intro A hA
  rw [ambientMoves, List.mem_map] at hA
  obtain ⟨Q, hQ, rfl⟩ := hA
  exact ambientMove_fixedOn_commonExterior hQ


-- @@ L283-290 verbatim
/-- Despite all later endpoint conjugations, the full schedule remains
stationary throughout time on the common exterior of the original support
cores. -/
theorem transportedSchedule_fixedOn_commonExterior
    (moves : List V.OriginalTubeNormalGraphMover) :
    (transportedSchedule moves).FixedOn (commonExterior moves) := by
  exact SmoothAmbientIsotopy.endpointFold_fixedOn
    (ambientMoves moves) (ambientMoves_fixedOn_commonExterior moves)


-- @@ L292-298 verbatim
/-- Pointwise form of common-exterior fixedness. -/
theorem transportedSchedule_forward_eq_self_of_mem_commonExterior
    (moves : List V.OriginalTubeNormalGraphMover)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {x : E} (hx : x ∈ commonExterior moves) :
    (transportedSchedule moves).forward s x = x :=
  transportedSchedule_fixedOn_commonExterior moves s hs x hx


-- @@ L300-300 verbatim
end OriginalTubeNormalGraphMover

-- @@ L301-301 verbatim
end TamedField

-- @@ L302-302 verbatim
end Submission
