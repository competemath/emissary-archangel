/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketForwardInput
import LeanPool.NavierStokesAndEuler.Euler.BaseEulerSign
public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerState
public import LeanPool.NavierStokesAndEuler.Euler.ParentState


-- @@ L13-14 verbatim
/-! Concrete support, transverse coordinate and short-time source
budgets for the first packet over the compact base Euler solution. -/


-- @@ L16-16 verbatim
section


-- @@ L18-20 verbatim
/-! The concrete compactly supported datum supplies the full recursive
state: the physical Euler solution, all Sobolev orders, particle labels,
and odd symmetry all refer to the same solution. -/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerBaseDatum


-- @@ L28-28 verbatim
open EulerParentPacketFrames


-- @@ L30-37 verbatim
/-- Initial state, bundling `evolution`, `regularity`, `labels`, `odd`. -/
def initialState (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) :
    SmoothState (initialParent β hβ ell hell hell1) where
  evolution := initialEvolution β hβ ell hell hell1
  regularity := initialSobolevData β hβ ell hell hell1
  labels := initialLabelData β hβ ell hell hell1
  odd := initialOddData β hβ ell hell hell1


-- @@ L39-39 verbatim
end EulerBaseDatum


-- @@ L41-41 verbatim
end

-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end


-- @@ L46-46 verbatim
@[expose] public section


-- @@ L48-48 verbatim
noncomputable section


-- @@ L50-50 verbatim
namespace EulerPacketSupport


-- @@ L52-52 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs


-- @@ L54-55 verbatim
/-- Support, given by `tsupport innerCutoff`. -/
def support : Set Space := tsupport innerCutoff


-- @@ L57-57 verbatim
theorem compact : IsCompact support := innerCutoff_compactSupport


-- @@ L59-59 verbatim
theorem subset_halfBall : support ⊆ Metric.ball 0 (1/2 : ℝ) := innerCutoff_support


-- @@ L61-69 verbatim
theorem symmetric (x : Space) : -x ∈ support ↔ x ∈ support := by
  have hf : innerCutoff ∘ Homeomorph.neg Space=innerCutoff := by
    funext y
    exact innerCutoff_even y
  calc
    -x ∈ support ↔ x ∈ tsupport (innerCutoff ∘ Homeomorph.neg Space) := by
      rw [tsupport_comp_eq_preimage]
      rfl
    _ ↔ x ∈ support := by rw [hf]; rfl


-- @@ L71-72 verbatim
theorem norm_lt (x : Space) (hx : x ∈ support) : ‖x‖ < (1/2 : ℝ) := by
  simpa only [Metric.mem_ball,dist_zero_right] using subset_halfBall hx


-- @@ L74-74 verbatim
end EulerPacketSupport


-- @@ L76-76 verbatim
namespace EulerBaseDatum


-- @@ L78-79 verbatim
open Set InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerTransverseFrameCoordinates EulerBaseEulerGuards EulerPacketSupport


-- @@ L81-82 verbatim
/-- First normal, given by `EuclideanSpace.single 0 1`. -/
def firstNormal : Space := EuclideanSpace.single 0 1


-- @@ L84-84 verbatim
theorem firstNormal_unit : ‖firstNormal‖=1 := by simp [firstNormal]


-- @@ L86-87 verbatim
/-- First plane: an abbreviation for `referencePlane firstNormal`. -/
abbrev FirstPlane := referencePlane firstNormal


-- @@ L89-90 verbatim
/-- First frame, given by `LinearIsometryEquiv.refl ℝ _`. -/
def firstFrame : FirstPlane ≃ₗᵢ[ℝ] referencePlane firstNormal := LinearIsometryEquiv.refl ℝ _


-- @@ L92-95 verbatim
/-- First coordinate as an element of `FirstPlane`. -/
def firstCoordinate : FirstPlane := ⟨EuclideanSpace.single 1 1,by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [firstNormal,EuclideanSpace.inner_single_left]⟩


-- @@ L97-97 verbatim
theorem firstCoordinate_map : (firstFrame firstCoordinate : Space)=EuclideanSpace.single 1 1 := rfl


-- @@ L99-101 verbatim
theorem firstCoordinate_norm : ‖firstCoordinate‖=1 := by
  change ‖(EuclideanSpace.single 1 1 : Space)‖=1
  simp


-- @@ L103-104 verbatim
variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)


-- @@ L106-108 verbatim
/-- Packet base parent, given by `(initialParent β hβ ell hell hell1).restrictTime T hT hTB`. -/
def packetBaseParent : Parent :=
  (initialParent β hβ ell hell hell1).restrictTime T hT hTB


-- @@ L110-112 verbatim
/-- Packet base state, given by `(initialState β hβ ell hell hell1).restrictTime T hT hTB`. -/
def packetBaseState : SmoothState (packetBaseParent β hβ ell hell hell1 T hT hTB) :=
  (initialState β hβ ell hell hell1).restrictTime T hT hTB


-- @@ L114-117 verbatim
/-- Packet base low bounds, given by `(initialLowBounds β hβ ell hell hell1).restrictTime T hT
hTB`. -/
def packetBaseLowBounds : LowBounds (packetBaseParent β hβ ell hell hell1 T hT hTB) :=
  (initialLowBounds β hβ ell hell hell1).restrictTime T hT hTB


-- @@ L119-120 verbatim
theorem packetBase_label_constant :
    (packetBaseState β hβ ell hell hell1 T hT hTB).labels.K=solutionLabelConstant := rfl


-- @@ L122-123 verbatim
theorem packetBase_boundary_zero :
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB).L=0 := rfl


-- @@ L125-128 verbatim
include hTB in
theorem packetBase_short : initialCoefficientCost*T ≤ 1/2 :=
  ((mul_le_mul_of_nonneg_left hTB initialCoefficientCost_nonneg).trans initialTime_small.1).trans
    (by norm_num)


-- @@ L130-138 verbatim
include hTB in
theorem packetBase_sign_short :
    EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost initialCoefficientCost*T ≤
        1/2 := by
  have hnonneg : 0 ≤ EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost
      initialCoefficientCost := by
    unfold EulerPacketFirstPressureSign.firstSignRate
    positivity [initialCoefficientCost_nonneg]
  exact ((mul_le_mul_of_nonneg_left hTB hnonneg).trans initialTime_small.2).trans (by norm_num)


-- @@ L140-145 verbatim
theorem packetBase_strain_bound (t : Icc (0 : ℝ) T) (x : Space) :
    ‖(packetBaseParent β hβ ell hell hell1 T hT hTB).strain.field t x‖ ≤ initialCoefficientCost :=
        by
  change ‖((initialParent β hβ ell hell hell1).restrictTime T hT hTB).strain.field t x‖ ≤ _
  erw [Parent.restrictTime_strain]
  exact initial_strain_bound β hβ ell hell hell1 _ x


-- @@ L147-152 verbatim
theorem packetBase_curvature_bound (t : Icc (0 : ℝ) T) (x : Space) :
    ‖(packetBaseParent β hβ ell hell hell1 T hT hTB).curvature.field t x‖ ≤ initialCoefficientCost
        := by
  change ‖((initialParent β hβ ell hell hell1).restrictTime T hT hTB).curvature.field t x‖ ≤ _
  erw [Parent.restrictTime_curvature]
  exact initial_curvature_bound β hβ ell hell hell1 _ x


-- @@ L154-161 verbatim
theorem packetBase_initialStrain (x : Space) (hx : x ∈ support) :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).initialStrain.field x=linear β := by
  erw [packetBaseParent,Parent.restrictTime_initialStrain]
  apply initialStrain_plateau β hβ ell hell hell1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hell]
  have hb := mul_le_mul_of_nonneg_right hell1 (norm_nonneg x)
  have hx' := norm_lt x hx
  nlinarith only [hb,hx']


-- @@ L163-177 verbatim
/-- First packet inputs used in base packet setup. -/
def firstPacketInputs :
    ForwardInputs
      ((packetBaseParent β hβ ell hell hell1 T hT hTB).meanData
        (packetBaseLowBounds β hβ ell hell hell1 T hT hTB))
      ((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
        firstNormal firstNormal_unit firstFrame support compact) :=
  (packetBaseState β hβ ell hell hell1 T hT hTB).labels.forwardInputs
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact
    initialCoefficientCost initialCoefficientCost_nonneg
    (fun t x _ => packetBase_strain_bound β hβ ell hell hell1 T hT hTB t x)
    (Metric.ball 0 (1/2 : ℝ)) Metric.isOpen_ball.measurableSet Metric.isOpen_ball subset_halfBall
    (fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hx))
    (packetBase_short T hTB) T⁻¹ (hTB.trans initialTime_le_one) le_rfl


-- @@ L179-180 verbatim
theorem firstPacketInputs_growth :
    (firstPacketInputs β hβ ell hell hell1 T hT hTB).linear.g=1 := rfl


-- @@ L182-195 verbatim
theorem firstPacket_pressure_numerator (t : Icc (0 : ℝ) T)
    (x : Space) (hx : x ∈ support) :
    1/2 ≤ ⟪((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact).normal.field t x,
      (packetBaseParent β hβ ell hell hell1 T hT hTB).strain.field t x
        (EulerPacketForwardFactorization.uncutVelocity
          ((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
            firstNormal firstNormal_unit firstFrame support compact) firstCoordinate t x)⟫_ℝ := by
  apply source_numerator_pos (packetBaseState β hβ ell hell hell1 T hT hTB).labels
    firstNormal firstNormal_unit firstFrame support compact firstCoordinate firstCoordinate_norm x
  · rw [packetBase_initialStrain β hβ ell hell hell1 T hT hTB x hx,firstCoordinate_map,linear_q]
    simp [firstNormal,EuclideanSpace.inner_single_left,PiLp.add_apply,PiLp.smul_apply]
  · exact packetBase_short T hTB
  · exact packetBase_sign_short T hTB


-- @@ L197-197 verbatim
end EulerBaseDatum
