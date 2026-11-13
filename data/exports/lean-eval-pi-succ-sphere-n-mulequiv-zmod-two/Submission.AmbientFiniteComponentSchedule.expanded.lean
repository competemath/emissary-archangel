import Mathlib
import Submission.AmbientEndpointConjugation
import Submission.Delta


-- @@ L5-22 verbatim
/-!
# Finite schedules of relative ambient component moves

An orbitwise normalizer is naturally written in the original coordinates:
one local ambient isotopy for each component.  To execute these moves in
sequence, every next move is conjugated by the endpoint accumulated so far.

This file formalizes the finite induction.  A component move records its
source and target sets.  Pairwise relative moves fix each other's source and
target sets throughout the isotopy.  The transported finite schedule then:

* has the expected nested original-coordinate endpoint action;
* carries every recorded source set to its recorded target set; and
* transports every relative fixed set to its current endpoint image.

The remaining geometric input is therefore local: construct one supported
ambient move per orbit component.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open Set Function

-- @@ L29-29 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L31-31 verbatim
namespace Submission

-- @@ L32-32 verbatim
namespace SmoothAmbientIsotopy


-- @@ L34-34 verbatim
variable {n : ℕ}


-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L38-42 verbatim
/-- Original-coordinate endpoint action of a list of moves.  The head is the
outermost map, matching the endpoint of the accumulated conjugated fold. -/
def endpointAction : List (SmoothAmbientIsotopy n) → E → E
  | [], x => x
  | B :: tail, x => B.forward 1 (endpointAction tail x)


-- @@ L44-45 verbatim
@[simp] theorem endpointAction_nil (x : E) :
    endpointAction ([] : List (SmoothAmbientIsotopy n)) x = x := rfl


-- @@ L47-49 verbatim
@[simp] theorem endpointAction_cons (B : SmoothAmbientIsotopy n)
    (tail : List (SmoothAmbientIsotopy n)) (x : E) :
    endpointAction (B :: tail) x = B.forward 1 (endpointAction tail x) := rfl


-- @@ L51-58 verbatim
/-- Accumulate a list of original-coordinate moves, transporting each next
move by the endpoint constructed so far. -/
def endpointFoldFrom (A : SmoothAmbientIsotopy n) :
    List (SmoothAmbientIsotopy n) → SmoothAmbientIsotopy n
  | [] => A
  | B :: tail =>
      let A' := A.followedBy (B.conjugateByEndpoint A)
      endpointFoldFrom A' tail


-- @@ L60-63 verbatim
/-- Accumulation starting from the identity ambient isotopy. -/
def endpointFold (moves : List (SmoothAmbientIsotopy n)) :
    SmoothAmbientIsotopy n :=
  endpointFoldFrom (refl n) moves


-- @@ L65-66 verbatim
@[simp] theorem endpointFoldFrom_nil (A : SmoothAmbientIsotopy n) :
    endpointFoldFrom A [] = A := rfl


-- @@ L68-71 verbatim
@[simp] theorem endpointFoldFrom_cons (A B : SmoothAmbientIsotopy n)
    (tail : List (SmoothAmbientIsotopy n)) :
    endpointFoldFrom A (B :: tail) =
      endpointFoldFrom (A.followedBy (B.conjugateByEndpoint A)) tail := rfl


-- @@ L73-84 verbatim
/-- The transported fold has the nested original-coordinate endpoint action. -/
theorem endpointFoldFrom_forward_one (A : SmoothAmbientIsotopy n) :
    ∀ (moves : List (SmoothAmbientIsotopy n)) (x : E),
      (endpointFoldFrom A moves).forward 1 x =
        A.forward 1 (endpointAction moves x)
  | [], x => rfl
  | B :: tail, x => by
      rw [endpointFoldFrom_cons,
        endpointFoldFrom_forward_one
          (A.followedBy (B.conjugateByEndpoint A)) tail x,
        followedBy_conjugateByEndpoint_forward_one]
      rfl


-- @@ L86-89 verbatim
@[simp] theorem endpointFold_forward_one
    (moves : List (SmoothAmbientIsotopy n)) (x : E) :
    (endpointFold moves).forward 1 x = endpointAction moves x := by
  rw [endpointFold, endpointFoldFrom_forward_one, refl_forward]


-- @@ L91-101 verbatim
/-- A list of moves fixing `K` has identity endpoint action on `K`. -/
theorem endpointAction_eq_of_fixedOn {K : Set E} :
    ∀ (moves : List (SmoothAmbientIsotopy n)),
      (∀ B ∈ moves, B.FixedOn K) →
      ∀ x ∈ K, endpointAction moves x = x
  | [], _, x, _ => rfl
  | B :: tail, h, x, hx => by
      rw [endpointAction_cons,
        endpointAction_eq_of_fixedOn tail
          (fun C hC => h C (by simp [hC])) x hx]
      exact h B (by simp) 1 ⟨zero_le_one, le_rfl⟩ x hx


-- @@ L103-113 verbatim
/-- Set-image form of `endpointAction_eq_of_fixedOn`. -/
theorem endpointAction_image_eq_of_fixedOn {K : Set E}
    (moves : List (SmoothAmbientIsotopy n))
    (h : ∀ B ∈ moves, B.FixedOn K) :
    endpointAction moves '' K = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [endpointAction_eq_of_fixedOn moves h y hy]
  · intro hx
    exact ⟨x, hx, endpointAction_eq_of_fixedOn moves h x hx⟩


-- @@ L115-122 verbatim
private theorem image_comp_eq (f g : E → E) (K : Set E) :
    (fun x => f (g x)) '' K = f '' (g '' K) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩


-- @@ L124-129 verbatim
/-- A local component move in the original coordinates. -/
structure ComponentMove (n : ℕ) where
  source : Set (EuclideanSpace ℝ (Fin (n + 1)))
  target : Set (EuclideanSpace ℝ (Fin (n + 1)))
  move : SmoothAmbientIsotopy n
  endpoint_image : move.forward 1 '' source = target


-- @@ L131-131 verbatim
namespace ComponentMove


-- @@ L133-137 verbatim
/-- Two component moves are mutually relative when each is stationary on
both the source and target of the other. -/
def MutuallyRelative (P Q : ComponentMove n) : Prop :=
  P.move.FixedOn (Q.source ∪ Q.target) ∧
    Q.move.FixedOn (P.source ∪ P.target)


-- @@ L139-141 verbatim
theorem mutuallyRelative_comm {P Q : ComponentMove n} :
    MutuallyRelative P Q ↔ MutuallyRelative Q P := by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩


-- @@ L143-146 verbatim
private theorem head_fixedOn_target
    {P Q : ComponentMove n} (h : MutuallyRelative P Q) :
    P.move.FixedOn Q.target :=
  h.1.mono subset_union_right


-- @@ L148-155 verbatim
private theorem tail_fixedOn_source
    (P : ComponentMove n) {tail : List (ComponentMove n)}
    (h : ∀ Q ∈ tail, MutuallyRelative P Q) :
    ∀ B ∈ tail.map ComponentMove.move, B.FixedOn P.source := by
  intro B hB
  rw [List.mem_map] at hB
  obtain ⟨Q, hQt, rfl⟩ := hB
  exact (h Q hQt).2.mono subset_union_left


-- @@ L157-202 verbatim
/-- Pairwise relative component moves simultaneously realize every recorded
source-to-target image at the original-coordinate endpoint action. -/
theorem endpointAction_image_source :
    ∀ {schedule : List (ComponentMove n)},
      schedule.Pairwise MutuallyRelative →
      ∀ P ∈ schedule,
        endpointAction (schedule.map ComponentMove.move) '' P.source = P.target
  | [], _, P, hP => by simp at hP
  | head :: tail, hpair, P, hP => by
      rw [List.pairwise_cons] at hpair
      rcases hpair with ⟨hhead, htail⟩
      rw [List.mem_cons] at hP
      rcases hP with rfl | hP
      · rw [List.map_cons]
        calc
          endpointAction (P.move :: tail.map ComponentMove.move) '' P.source =
              P.move.forward 1 ''
                (endpointAction (tail.map ComponentMove.move) '' P.source) := by
            change (fun x => P.move.forward 1
              (endpointAction (tail.map ComponentMove.move) x)) '' P.source = _
            exact image_comp_eq _ _ _
          _ = P.move.forward 1 '' P.source := by
            rw [endpointAction_image_eq_of_fixedOn
              (tail.map ComponentMove.move)
              (tail_fixedOn_source P hhead)]
          _ = P.target := P.endpoint_image
      · have ih := endpointAction_image_source htail P hP
        have hfix : head.move.FixedOn P.target :=
          head_fixedOn_target (hhead P hP)
        rw [List.map_cons]
        calc
          endpointAction (head.move :: tail.map ComponentMove.move) '' P.source =
              head.move.forward 1 ''
                (endpointAction (tail.map ComponentMove.move) '' P.source) := by
            change (fun x => head.move.forward 1
              (endpointAction (tail.map ComponentMove.move) x)) '' P.source = _
            exact image_comp_eq _ _ _
          _ = head.move.forward 1 '' P.target := by rw [ih]
          _ = P.target := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              rwa [hfix 1 ⟨zero_le_one, le_rfl⟩ y hy]
            · intro hx
              exact ⟨x, hx,
                hfix 1 ⟨zero_le_one, le_rfl⟩ x hx⟩


-- @@ L204-215 verbatim
/-- Endpoint-fold form of the finite component theorem. -/
theorem endpointFold_forward_image_source
    {schedule : List (ComponentMove n)}
    (hpair : schedule.Pairwise MutuallyRelative)
    (P : ComponentMove n) (hP : P ∈ schedule) :
    (endpointFold (schedule.map ComponentMove.move)).forward 1 '' P.source =
      P.target := by
  rw [show (endpointFold (schedule.map ComponentMove.move)).forward 1 =
      endpointAction (schedule.map ComponentMove.move) by
    funext x
    exact endpointFold_forward_one _ x]
  exact endpointAction_image_source hpair P hP


-- @@ L217-223 verbatim
/-- The next original-coordinate relative set is fixed after transport to its
current image under any accumulated endpoint. -/
theorem transportedMove_fixedOn_currentImage
    (P : ComponentMove n) (A : SmoothAmbientIsotopy n) {K : Set E}
    (hP : P.move.FixedOn K) :
    (P.move.conjugateByEndpoint A).FixedOn (A.forward 1 '' K) :=
  hP.conjugateByEndpoint


-- @@ L225-225 verbatim
end ComponentMove


-- @@ L227-227 verbatim
/-! ## The canonical finite schedule of orbit moves -/


-- @@ L229-243 verbatim
/-- Local ambient moves, one for each component of a tamed framed level set.

The relative condition is deliberately symmetric and includes both the source
and target of every other orbit.  It is exactly the support-separation input
needed by the finite schedule theorem above: later transported moves preserve
already installed targets, while earlier moves preserve the sources still to
be processed. -/
structure OrbitMoveFamily (X : FramedLevelSet n) (V : TamedField X) where
  target : V.OrbitIndex → Set E
  move : V.OrbitIndex → SmoothAmbientIsotopy n
  endpoint_image : ∀ O : V.OrbitIndex,
    (move O).forward 1 '' (O : Set E) = target O
  mutuallyRelative : ∀ O P : V.OrbitIndex, O ≠ P →
    (move O).FixedOn ((P : Set E) ∪ target P) ∧
      (move P).FixedOn ((O : Set E) ∪ target O)


-- @@ L245-245 verbatim
namespace OrbitMoveFamily


-- @@ L247-247 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}


-- @@ L249-255 verbatim
/-- Package one orbitwise ambient normalizer as a generic component move. -/
def componentMove (F : OrbitMoveFamily X V) (O : V.OrbitIndex) :
    ComponentMove n where
  source := (O : Set E)
  target := F.target O
  move := F.move O
  endpoint_image := F.endpoint_image O


-- @@ L257-259 verbatim
/-- The canonical schedule contains every orbit exactly once. -/
def componentSchedule (F : OrbitMoveFamily X V) : List (ComponentMove n) :=
  (Finset.univ : Finset V.OrbitIndex).toList.map F.componentMove


-- @@ L261-263 verbatim
/-- The corresponding list of original-coordinate ambient moves. -/
def moveSchedule (F : OrbitMoveFamily X V) : List (SmoothAmbientIsotopy n) :=
  F.componentSchedule.map ComponentMove.move


-- @@ L265-268 verbatim
/-- The accumulated ambient isotopy obtained by endpoint-conjugating each
successive original-coordinate orbit move. -/
def ambientSchedule (F : OrbitMoveFamily X V) : SmoothAmbientIsotopy n :=
  endpointFold F.moveSchedule


-- @@ L270-277 verbatim
theorem componentSchedule_pairwise (F : OrbitMoveFamily X V) :
    F.componentSchedule.Pairwise ComponentMove.MutuallyRelative := by
  classical
  rw [componentSchedule, List.pairwise_map]
  apply (List.nodup_iff_pairwise_ne.mp
    (Finset.nodup_toList (Finset.univ : Finset V.OrbitIndex))).imp
  intro O P hOP
  exact F.mutuallyRelative O P hOP


-- @@ L279-284 verbatim
theorem componentMove_mem_componentSchedule
    (F : OrbitMoveFamily X V) (O : V.OrbitIndex) :
    F.componentMove O ∈ F.componentSchedule := by
  classical
  rw [componentSchedule, List.mem_map]
  exact ⟨O, by simp, rfl⟩


-- @@ L286-295 verbatim
/-- The finite transported schedule sends every original orbit component to
its prescribed target.  Thus after local supported orbit moves have been
constructed, no additional global compatibility or enumeration input is
needed. -/
theorem ambientSchedule_endpoint_image
    (F : OrbitMoveFamily X V) (O : V.OrbitIndex) :
    F.ambientSchedule.forward 1 '' (O : Set E) = F.target O := by
  exact ComponentMove.endpointFold_forward_image_source
    F.componentSchedule_pairwise (F.componentMove O)
      (F.componentMove_mem_componentSchedule O)


-- @@ L297-297 verbatim
end OrbitMoveFamily


-- @@ L299-299 verbatim
end SmoothAmbientIsotopy

-- @@ L300-300 verbatim
end Submission
