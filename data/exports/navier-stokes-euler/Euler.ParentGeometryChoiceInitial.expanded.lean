import Euler.ParentGeometryChoiceCenter
import Euler.ParentForwardInitialSupport


-- @@ L4-6 verbatim
/-! The initial traces of the actual chosen Euler states are the same
compact high and mean increments used in the initial-data convergence
proof. Restriction to a shorter horizon preserves these equalities. -/


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace EulerParentPacketFrames


-- @@ L12-13 verbatim
open Set EulerSmoothLimit EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerAllOrderDriftCorrection EulerPacketPhysicalLowBounds EulerPhysicalL2Scaling


-- @@ L15-15 verbatim
namespace SmoothState


-- @@ L17-20 verbatim
theorem velocityIncrement_restrictTime {A B : Parent} (S : SmoothState A) (T : SmoothState B)
    (s : ℝ) (hs : 0 < s) (hA : s ≤ A.T) (hB : s ≤ B.T) :
    (S.restrictTime s hs hA).velocityIncrement (T.restrictTime s hs hB) =
      S.velocityIncrement T := rfl


-- @@ L22-22 verbatim
end SmoothState


-- @@ L24-24 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]


-- @@ L26-26 verbatim
namespace GeometryJoinedChoice


-- @@ L28-31 verbatim
variable (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)


-- @@ L33-33 verbatim
local notation "res" => residual I S k hk nextEll hnext hnext1 F


-- @@ L35-46 verbatim
theorem normalized_initial :
    I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates I.support I.support_compact
      F.Q res k S.evolution.inverse I.parent.zeroTime =
    initializedExactPhysicalVelocity I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime id := by
  change initializedExactPhysicalVelocity I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime
      (S.evolution.inverse.normalized I.parent.zeroTime) = _
  rw [show S.evolution.inverse.normalized I.parent.zeroTime=id from
    funext S.evolution.inverse.normalized_initial]


-- @@ L48-48 verbatim
variable (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

-- @@ L49-49 verbatim
local notation "T" => state I S k hk nextEll hnext hnext1 F hSym


-- @@ L51-63 verbatim
theorem initial_increment : S.velocityIncrement T 0 = I.exactInitial k hk.four F.hn F.Q := by
  funext x
  have he : (T).evolution.velocity (0,x) =
      addVelocity I.parent.ell (fun y => S.evolution.velocity (0,y))
        (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
          I.support I.support_compact F.Q res k S.evolution.inverse I.parent.zeroTime) x :=
    I.parent.exactPacketVelocity_eq_addVelocity I.normal I.normal_unit I.coordinates
      I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity I.parent.zeroTime x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=_
  rw [he]
  simp only [addVelocity,add_sub_cancel_left,
    normalized_initial I S k hk nextEll hnext hnext1 F,EulerPacketInitial.Input.exactInitial,scale]
  rfl


-- @@ L65-67 verbatim
theorem initial_increment_eq : S.velocityIncrement T 0 = I.high k+I.mean k :=
  (initial_increment I S k hk nextEll hnext hnext1 F hSym).trans
    (I.exactInitial_eq k hk.four F.hn F.Q)


-- @@ L69-75 verbatim
theorem state_velocity_initial :
    (fun x => (T).evolution.velocity (0,x)) =
      (fun x => S.evolution.velocity (0,x))+(I.high k+I.mean k) := by
  funext x
  have he := congrFun (initial_increment_eq I S k hk nextEll hnext hnext1 F hSym) x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=(I.high k+I.mean k) x at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)


-- @@ L77-79 verbatim
theorem restricted_initial_increment (s : ℝ) (hs : 0 < s) (hT : s ≤ I.parent.T) :
    (S.restrictTime s hs hT).velocityIncrement ((T).restrictTime s hs hT) 0 =
      I.high k+I.mean k := initial_increment_eq I S k hk nextEll hnext hnext1 F hSym


-- @@ L81-81 verbatim
end GeometryJoinedChoice


-- @@ L83-83 verbatim
namespace GeometryForwardInput


-- @@ L85-85 verbatim
variable (I : GeometryForwardInput U)


-- @@ L87-88 verbatim
def high (k : ℝ) : Space → Space := forwardInitializedInitialHigh I.meanData I.data
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k


-- @@ L90-91 verbatim
def mean (k : ℝ) : Space → Space := forwardInitializedInitialMean I.meanData I.data
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k


-- @@ L93-97 verbatim
def exactInitial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : I.correctionBudget k hk hn) :
    Space → Space := scale I.parent.ell
  (forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
    (truncation k) hn k hk Q I.parent.zeroTime id)


-- @@ L99-102 verbatim
theorem exactInitial_eq (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : I.correctionBudget k hk hn) :
    I.exactInitial k hk hn Q=I.high k+I.mean k :=
  forwardInitializedExactPhysicalVelocity_initial_split I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) hn k hk Q


-- @@ L104-104 verbatim
end GeometryForwardInput


-- @@ L106-106 verbatim
namespace GeometryForwardChoice


-- @@ L108-111 verbatim
variable (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)


-- @@ L113-113 verbatim
local notation "res" => residual I S k hk nextEll hnext hnext1 F


-- @@ L115-126 verbatim
theorem normalized_initial :
    I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates I.support I.support_compact
      F.Q res k S.evolution.inverse I.parent.zeroTime =
    forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime id := by
  change forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime
      (S.evolution.inverse.normalized I.parent.zeroTime) = _
  rw [show S.evolution.inverse.normalized I.parent.zeroTime=id from
    funext S.evolution.inverse.normalized_initial]


-- @@ L128-128 verbatim
variable (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

-- @@ L129-129 verbatim
local notation "T" => state I S k hk nextEll hnext hnext1 F hSym


-- @@ L131-142 verbatim
theorem initial_increment : S.velocityIncrement T 0 = I.exactInitial k hk.four F.hn F.Q := by
  funext x
  have he : (T).evolution.velocity (0,x) =
      addVelocity I.parent.ell (fun y => S.evolution.velocity (0,y))
        (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
          I.support I.support_compact F.Q res k S.evolution.inverse I.parent.zeroTime) x :=
    I.parent.exactPacketVelocity_eq_addVelocity I.normal I.normal_unit I.coordinates
      I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity I.parent.zeroTime x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=_
  rw [he]
  simp only [addVelocity,add_sub_cancel_left,
    normalized_initial I S k hk nextEll hnext hnext1 F,GeometryForwardInput.exactInitial,scale]


-- @@ L144-146 verbatim
theorem initial_increment_eq : S.velocityIncrement T 0 = I.high k+I.mean k :=
  (initial_increment I S k hk nextEll hnext hnext1 F hSym).trans
    (I.exactInitial_eq k hk.four F.hn F.Q)


-- @@ L148-154 verbatim
theorem state_velocity_initial :
    (fun x => (T).evolution.velocity (0,x)) =
      (fun x => S.evolution.velocity (0,x))+(I.high k+I.mean k) := by
  funext x
  have he := congrFun (initial_increment_eq I S k hk nextEll hnext hnext1 F hSym) x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=(I.high k+I.mean k) x at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)


-- @@ L156-158 verbatim
theorem restricted_initial_increment (s : ℝ) (hs : 0 < s) (hT : s ≤ I.parent.T) :
    (S.restrictTime s hs hT).velocityIncrement ((T).restrictTime s hs hT) 0 =
      I.high k+I.mean k := initial_increment_eq I S k hk nextEll hnext hnext1 F hSym


-- @@ L160-160 verbatim
end GeometryForwardChoice

-- @@ L161-161 verbatim
end EulerParentPacketFrames
