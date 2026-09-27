/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedJointDifferentiability
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalEulerTransform
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildParent


-- @@ L18-20 verbatim
/-! The actual normalized parent coordinates used by the packet. Joint
regularity, the frame, and inverse regularity are derived from the parent
time laws and the literal inverse map. -/


-- @@ L22-22 verbatim
section


-- @@ L24-25 verbatim
/-! The child particle velocity matches the physical reconstruction of
the actual common correction, including the source spatial scaling. -/


-- @@ L27-27 verbatim
section


-- @@ L29-31 verbatim
/-! The constructed child particle velocity is the Eulerian pushforward
of the actual graph velocity. The normalized packet formula follows
from the literal lifted coefficient, with the physical scale explicit. -/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
namespace EulerPhysicalGraphFlowBounds.Data


-- @@ L39-40 verbatim
open Set EulerLiftedGradientSpace EulerGraphInvariantFlow EulerSmoothBanachFlow
    EulerSmoothFlowGevrey


-- @@ L42-44 verbatim
variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
  (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)


-- @@ L46-52 verbatim
include hgraph hell in
theorem physicalDisplacementCoefficient_position (t : Icc (0 : ℝ) T) (x : Vector3) :
    x+(G.physicalDisplacementCoefficient k m ell).field t x =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t x := by
  rw [G.physicalDisplacementCoefficient_eq k m ell hell,
    G.displacementField_eq k m hgraph ell hell,displacement_eq]
  abel


-- @@ L54-60 verbatim
include hgraph hell in
theorem physicalVelocityCoefficient_material (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalVelocityCoefficient k m ell).field t x =
      (physicalCoefficient k m T G.A ell).field t
        ((flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t x) := by
  rw [G.physicalVelocityCoefficient_eq k m ell hell,G.velocityField_eq k m hgraph ell hell]
  rfl


-- @@ L62-62 verbatim
end EulerPhysicalGraphFlowBounds.Data


-- @@ L64-64 verbatim
namespace EulerParentPacketFrames.Parent


-- @@ L66-67 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow EulerSmoothBanachFlow
  EulerMetricTransport


-- @@ L69-72 verbatim
variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)


-- @@ L74-79 verbatim
/-- Graph pushforward velocity, constructed using `u`. -/
def graphPushforwardVelocity (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  u t x + (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) (Y t
      x))
    ((physicalCoefficient k m A.T G.A A.ell).field t (Y t x))


-- @@ L81-85 verbatim
theorem child_position (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).position t x =
      A.position t ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
          x) :=
  A.child_particleMap G k m hgraph nextEll hnext hnext1 t x


-- @@ L87-100 verbatim
theorem child_velocity_formula (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      let y := (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x
      A.velocity.field t y +
        (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) y)
          ((physicalCoefficient k m A.T G.A A.ell).field t y) := by
  change (EulerChildParticleTime.velocity A.displacement A.velocity
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)).field
        t x=_
  rw [EulerChildParticleTime.velocity_apply,
    G.physicalDisplacementCoefficient_position k m A.ell A.ell_pos hgraph,
    G.physicalVelocityCoefficient_material k m A.ell A.ell_pos hgraph]
  simp only [_root_.add_apply,ContinuousLinearMap.id_apply]
  abel


-- @@ L102-112 verbatim
theorem child_velocity_pushforward (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x)
    (hvelocity : ∀ t x, A.velocity.field t x = u t (A.position t x))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      A.graphPushforwardVelocity G k m Y u t
        ((A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  rw [A.child_velocity_formula G k m hgraph nextEll hnext hnext1,graphPushforwardVelocity,
    A.child_position G k m hgraph nextEll hnext hnext1,hYX]
  dsimp only
  rw [hvelocity]


-- @@ L114-129 verbatim
theorem graphPushforwardVelocity_packet
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (κ : ℝ)
    (z : Icc (0 : ℝ) A.T → LiftTangent → Space)
    (hlift : ∀ t q, G.A.field t q = transportDirection κ m (z t q))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.graphPushforwardVelocity G k m Y u t x =
      u t x + A.ell • (κ • A.frame.field t (A.ell⁻¹ • Y t x)
        (z t (graphLinear k m (A.ell⁻¹ • Y t x)))) := by
  rw [graphPushforwardVelocity,physicalCoefficient_apply,hlift]
  change u t x +
    (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) (Y t x))
      (A.ell • (κ • z t (graphLinear k m (A.ell⁻¹ • Y t x))))=_
  rw [map_smul,map_smul,A.frame_apply]
  have hx : A.ell • (A.ell⁻¹ • Y t x)=Y t x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rw [hx]


-- @@ L131-131 verbatim
end EulerParentPacketFrames.Parent


-- @@ L133-133 verbatim
end

-- @@ L134-134 verbatim
end


-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
@[expose] public section


-- @@ L140-140 verbatim
noncomputable section


-- @@ L142-142 verbatim
namespace EulerParentPacketFrames.Parent


-- @@ L144-146 verbatim
open Set InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerGraphPressurePotential
  EulerMetricTransport EulerPacketPhysicalTransform


-- @@ L148-150 verbatim
variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] {C : EulerAllOrderCorrectionData.Data P A.T}
  (B : EulerAllOrderDriftCorrection.Budget P A.T_pos C)


-- @@ L152-156 verbatim
/-- Corrected packet velocity, constructed using `u`. -/
def correctedPacketVelocity (k : ℝ) (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  u t x + A.ell • (C.κ • A.frame.field t (A.ell⁻¹ • Y t x)
    ((B.correctedFieldTower P).pointField t (cylinderGraph P k C.direction (A.ell⁻¹ • Y t x))))


-- @@ L158-160 verbatim
/-- Packet inverse, given by `A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)`. -/
def packetInverse (Y : Icc (0 : ℝ) A.T → Space → Space) (q : ℝ × Space) : Space :=
  A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)


-- @@ L162-174 verbatim
theorem correctedPacketVelocity_eq_physical (k : ℝ)
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.correctedPacketVelocity B k Y u t x =
      u t x + A.ell • physicalVelocity C.κ k C.direction
        (fun q => A.frame.realField A.T A.T_pos.le q.1 q.2)
        ((B.correctedFieldTower P).rawField A.T_pos.le) (A.packetInverse Y) (t,A.ell⁻¹ • x) := by
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  simp only [correctedPacketVelocity,EulerPacketPhysicalTransform.physicalVelocity,
    EulerPacketPhysicalTransform.inverseCoordinates,EulerPacketPhysicalTransform.graphVelocity,
    EulerPacketPhysicalTransform.spaceTimeGraph_apply, packetInverse, FieldTower.rawField,
        SmoothTimeField.realField_apply,
    projIcc_of_mem A.T_pos.le t.property,hx,cylinderGraph,coveringMap]


-- @@ L176-180 verbatim
variable {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw)
  (hV : C.approximation = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (hG : G.A = B.liftedPacketCoefficient P V)


-- @@ L182-188 verbatim
include hV hG in
theorem lifted_graph_constraint (k : ℝ) (hk : k * C.κ = 1)
    (t : Icc (0 : ℝ) A.T) (q : LiftTangent) :
    graphConstraint k C.direction (G.A.field t q)=0 := by
  rw [hG,B.liftedPacketCoefficient_eq_corrected P V hV]
  simp only [graphConstraint_apply,transportDirection,real_inner_smul_right]
  rw [← mul_assoc,hk,one_mul,sub_self]


-- @@ L190-200 verbatim
include hV hG in
theorem graphPushforwardVelocity_corrected (k : ℝ)
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.graphPushforwardVelocity G k C.direction Y u t x = A.correctedPacketVelocity B k Y u t x := by
  have h := A.graphPushforwardVelocity_packet G k C.direction Y u C.κ
    (fun s q => (B.correctedFieldTower P).pointField s (coveringMap P q))
    (by
      intro s q
      rw [hG]
      exact B.liftedPacketCoefficient_eq_corrected P V hV s q) t x
  simpa only [correctedPacketVelocity,graphLinear_apply,cylinderGraph,coveringMap] using h


-- @@ L202-215 verbatim
include hV hG in
theorem child_velocity_corrected (k : ℝ)
    (hgraph : ∀ t q, graphConstraint k C.direction (G.A.field t q) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x)
    (hvelocity : ∀ t x, A.velocity.field t x = u t (A.position t x))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k C.direction hgraph nextEll hnext hnext1).velocity.field t x =
      A.correctedPacketVelocity B k Y u t
        ((A.child G k C.direction hgraph nextEll hnext hnext1).position t x) :=
  (A.child_velocity_pushforward G k C.direction hgraph nextEll hnext hnext1 Y u hYX hvelocity t
      x).trans
    (A.graphPushforwardVelocity_corrected B V hV G hG k Y u t _)


-- @@ L217-217 verbatim
end EulerParentPacketFrames.Parent


-- @@ L219-219 verbatim
end

-- @@ L220-220 verbatim
end


-- @@ L222-222 verbatim
end


-- @@ L224-224 verbatim
section


-- @@ L226-228 verbatim
/-! A true particle velocity law and the actual Euler equation determine
the particle acceleration. Continuity extends the identity to both
endpoints; no acceleration or pressure-force match is assumed. -/


-- @@ L230-230 verbatim
@[expose] public section


-- @@ L232-232 verbatim
noncomputable section


-- @@ L234-234 verbatim
namespace EulerParentPacketFrames.Parent


-- @@ L236-236 verbatim
open Set Filter EulerSmoothLimit

-- @@ L237-237 verbatim
open scoped Topology


-- @@ L239-239 verbatim
variable (A : EulerParentPacketFrames.Parent)


-- @@ L241-243 verbatim
/-- Real position, given by `x+A.displacement.realField A.T A.T_pos.le t x`. -/
def realPosition (t : ℝ) (x : Space) : Space :=
  x+A.displacement.realField A.T A.T_pos.le t x


-- @@ L245-247 verbatim
@[simp] theorem realPosition_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.realPosition t x=A.position t x := by
  simp only [realPosition,SmoothTimeField.realField_apply,position]


-- @@ L249-250 verbatim
theorem realPosition_joint_continuous : Continuous (Function.uncurry A.realPosition) :=
  continuous_snd.add (A.displacement.realField_joint_continuous A.T A.T_pos.le)


-- @@ L252-254 verbatim
theorem position_time (t : Icc (0 : ℝ) A.T) (x : Space) :
    HasDerivWithinAt (fun s => A.realPosition s x) (A.velocity.field t x) (Icc (0 : ℝ) A.T) t :=
  (A.displacement_time t x).const_add x


-- @@ L256-283 verbatim
theorem acceleration_eq_neg_gradient
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
    (hdiff : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
    (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, EulerLagrangian.momentumResidual u p (t, x) = 0)
    (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    A.acceleration.field t x= -gradient (fun y => p (t,y)) (A.position t x) := by
  have hp := (A.position_time t x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hi := (hasDerivAt_id (t : ℝ)).prodMk hp
  have ho : HasFDerivAt u (fderiv ℝ u (t,A.position t x)) (id (t : ℝ),A.realPosition t x) := by
    simpa only [id_eq,A.realPosition_apply] using (hdiff t ht (A.position t x)).hasFDerivAt
  have hc := ho.comp_hasDerivAt (t : ℝ) hi
  have hc' : HasDerivAt (fun s => u (s,A.realPosition s x))
      (fderiv ℝ u (t,A.position t x) (1,A.velocity.field t x)) t := by
    simpa only [Function.comp_def,id_eq,A.realPosition_apply] using hc
  have he : (fun s => u (s,A.realPosition s x)) =ᶠ[𝓝 (t : ℝ)]
      (fun s => A.velocity.realField A.T A.T_pos.le s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hm := hvelocity ⟨s,hs.1.le,hs.2.le⟩ x
    simpa only [realPosition,SmoothTimeField.realField,EulerVolterraConvolution.extendPath,
      projIcc_of_mem A.T_pos.le ⟨hs.1.le,hs.2.le⟩,position] using hm.symm
  have hv := ((A.velocity_time t x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).congr_of_eventuallyEq he
  have ha := hv.unique hc'
  have hh := heuler t ht (A.position t x)
  change fderiv ℝ u (t,A.position t x) (1,u (t,A.position t x)) +
    gradient (fun y => p (t,y)) (A.position t x)=0 at hh
  rw [← hvelocity t x,← ha] at hh
  exact eq_neg_of_add_eq_zero_left hh


-- @@ L285-314 verbatim
theorem acceleration_physical_of_euler
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (force : Icc (0 : ℝ) A.T → Space → Space)
    (hforce : Continuous (Function.uncurry force))
    (hgradient : ∀ (t : Icc (0 : ℝ) A.T) x, gradient (fun y => p (t, y)) x = force t x)
    (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
    (hdiff : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
    (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, EulerLagrangian.momentumResidual u p (t, x) = 0)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.acceleration.field t x= -force t (A.position t x) := by
  let f : ℝ → Space := fun s => A.acceleration.realField A.T A.T_pos.le s x
  let g : ℝ → Space := fun s => -force (projIcc 0 A.T A.T_pos.le s) (A.realPosition s x)
  have hf : Continuous f :=
    (A.acceleration.realField_joint_continuous A.T A.T_pos.le).comp
      (continuous_id.prodMk continuous_const)
  have hg : Continuous g :=
    (hforce.comp ((show Continuous (projIcc 0 A.T A.T_pos.le) from continuous_projIcc).prodMk
      (A.realPosition_joint_continuous.comp (continuous_id.prodMk continuous_const)))).neg
  have he : EqOn f g (Ioo 0 A.T) := by
    intro s hs
    have hh := A.acceleration_eq_neg_gradient u p hvelocity hdiff heuler ⟨s,hs.1.le,hs.2.le⟩ hs x
    rw [hgradient] at hh
    simpa only [f,g,realPosition,SmoothTimeField.realField,EulerVolterraConvolution.extendPath,
      projIcc_of_mem A.T_pos.le ⟨hs.1.le,hs.2.le⟩,position] using hh
  have htc : (t : ℝ) ∈ closure (Ioo (0 : ℝ) A.T) := by
    rw [closure_Ioo A.T_pos.ne]
    exact t.property
  have hh := he.closure hf hg htc
  simpa only [f,g,SmoothTimeField.realField_apply,A.realPosition_apply,
    projIcc_of_mem A.T_pos.le t.property] using hh


-- @@ L316-316 verbatim
end EulerParentPacketFrames.Parent


-- @@ L318-318 verbatim
end

-- @@ L319-319 verbatim
end


-- @@ L321-321 verbatim
end


-- @@ L323-323 verbatim
section


-- @@ L325-326 verbatim
/-! Two actual time-derivative pairs give genuine joint C² regularity
for a smooth spatial coefficient path on interior times. -/


-- @@ L328-328 verbatim
@[expose] public section


-- @@ L330-330 verbatim
noncomputable section


-- @@ L332-332 verbatim
open scoped ContDiff Topology


-- @@ L334-334 verbatim
namespace SmoothTimeField


-- @@ L336-336 verbatim
open Set Filter


-- @@ L338-340 verbatim
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ A₂ : SmoothTimeField (Icc (0 : ℝ) T) E V)


-- @@ L342-356 verbatim
theorem jointDerivative_contDiffAt_one
    (hA : TimeDerivative T hT A A₁) (hA₁ : TimeDerivative T hT A₁ A₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (jointDerivative T hT A A₁)) (t,x) := by
  have hq := realField_contDiffAt_one T hT A₁ A₂ hA₁ t ht x
  have hJ := realField_contDiffAt_one T hT A.derivative A₁.derivative
    (TimeDerivative.derivative T hT A A₁ hA) t ht x
  have hs := (ContinuousLinearMap.toSpanSingletonLIE ℝ
      V).toContinuousLinearEquiv.contDiff.contDiffAt.comp
    (t,x) hq
  let L : ((ℝ →L[ℝ] V) × (E →L[ℝ] V)) →L[ℝ] ((ℝ × E) →L[ℝ] V) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := E) (G := V) ℝ).toContinuousLinearMap
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
    (E := (ℝ →L[ℝ] V) × (E →L[ℝ] V)) (F := (ℝ × E) →L[ℝ] V) L).contDiffAt.comp
    (t,x) (hs.prodMk hJ)


-- @@ L358-368 verbatim
theorem realField_contDiffAt_two
    (hA : TimeDerivative T hT A A₁) (hA₁ : TimeDerivative T hT A₁ A₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (A.realField T hT)) (t,x) := by
  rw [show (2 : ℕ∞ω) = ((1 : ℕ)+1) from rfl,contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨Function.uncurry (jointDerivative T hT A A₁),
    ⟨{p : ℝ × E | p.1 ∈ Ioo 0 T},?_,?_⟩,
    jointDerivative_contDiffAt_one T hT A A₁ A₂ hA hA₁ t ht x⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact realField_hasFDerivAt T hT A A₁ hA p.1 hp p.2


-- @@ L370-370 verbatim
end SmoothTimeField


-- @@ L372-372 verbatim
end

-- @@ L373-373 verbatim
end


-- @@ L375-375 verbatim
end


-- @@ L377-377 verbatim
@[expose] public section


-- @@ L379-379 verbatim
noncomputable section


-- @@ L381-381 verbatim
namespace EulerParentPacketFrames.Parent


-- @@ L383-383 verbatim
open Set Filter ContinuousLinearMap EulerSmoothLimit EulerSmoothBanachFlow

-- @@ L384-384 verbatim
open scoped ContDiff Topology


-- @@ L386-386 verbatim
variable (A : EulerParentPacketFrames.Parent)


-- @@ L388-389 verbatim
/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry1 : NormedAddCommGroup Space := inferInstance

-- @@ L390-391 verbatim
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry2 : NormedSpace ℝ Space := inferInstance

-- @@ L392-393 verbatim
/-- Cache the standard `NormedAddCommGroup (ℝ × Space)` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry3 : NormedAddCommGroup (ℝ × Space) := inferInstance

-- @@ L394-395 verbatim
/-- Cache the standard `NormedSpace ℝ (ℝ × Space)` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry4 : NormedSpace ℝ (ℝ × Space) := inferInstance


-- @@ L397-399 verbatim
/-- Packet position, given by `A.ell⁻¹ • A.realPosition q.1 (A.ell • q.2)`. -/
def packetPosition (q : ℝ × Space) : Space :=
  A.ell⁻¹ • A.realPosition q.1 (A.ell • q.2)


-- @@ L401-403 verbatim
@[simp] theorem packetPosition_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.packetPosition (t,x)=A.ell⁻¹ • A.position t (A.ell • x) := by
  rw [packetPosition,A.realPosition_apply]


-- @@ L405-409 verbatim
theorem realPosition_contDiffAt_two (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    ContDiffAt ℝ 2 (Function.uncurry A.realPosition) (t,x) :=
  contDiffAt_snd.add
    (SmoothTimeField.realField_contDiffAt_two A.T A.T_pos.le
      A.displacement A.velocity A.acceleration A.displacement_time A.velocity_time t ht x)


-- @@ L411-414 verbatim
theorem packetPosition_contDiffAt_two (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    ContDiffAt ℝ 2 A.packetPosition (t,x) :=
  ((A.realPosition_contDiffAt_two t ht (A.ell • x)).comp (t,x)
    (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul A.ell))).const_smul A.ell⁻¹


-- @@ L416-418 verbatim
theorem packetPosition_joint_continuous : Continuous A.packetPosition :=
  (A.realPosition_joint_continuous.comp
    (continuous_fst.prodMk (continuous_snd.const_smul A.ell))).const_smul A.ell⁻¹


-- @@ L420-442 verbatim
theorem realPosition_hasFDerivAt (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    HasFDerivAt (Function.uncurry A.realPosition)
      ((toSpanSingleton ℝ (A.velocity.field t x)).coprod
        (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x)) (t,x)
            := by
  have h := hasFDerivAt_snd.add
    (SmoothTimeField.realField_hasFDerivAt A.T A.T_pos.le
      A.displacement A.velocity A.displacement_time t ht x)
  have he : snd ℝ ℝ Space + SmoothTimeField.jointDerivative A.T A.T_pos.le
        A.displacement A.velocity t x =
      (toSpanSingleton ℝ (A.velocity.field t x)).coprod
        (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x) := by
    apply ContinuousLinearMap.ext
    intro v
    change v.2+(v.1 • A.velocity.realField A.T A.T_pos.le t x +
      A.displacement.derivative.realField A.T A.T_pos.le t x v.2) =
      v.1 • A.velocity.field t x+(v.2+fderiv ℝ (A.displacement.field t : Space → Space) x v.2)
    rw [SmoothTimeField.realField_apply,SmoothTimeField.realField_apply]
    change v.2+(v.1 • A.velocity.field t x+A.displacement.derivativeField t x v.2) = _
    rw [A.displacement.derivativeField_eq]
    abel
  rw [he] at h
  exact h


-- @@ L444-447 verbatim
/-- Packet position derivative, given by `(toSpanSingleton ℝ (A.ell⁻¹ • A.velocity.field t
(A.ell • x))).coprod (A.frame.field t x)`. -/
def packetPositionDerivative (t : Icc (0 : ℝ) A.T) (x : Space) : (ℝ × Space) →L[ℝ] Space :=
  (toSpanSingleton ℝ (A.ell⁻¹ • A.velocity.field t (A.ell • x))).coprod (A.frame.field t x)


-- @@ L449-470 verbatim
theorem packetPosition_hasFDerivAt (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    HasFDerivAt A.packetPosition (A.packetPositionDerivative t x) (t,x) := by
  let L : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
    (fst ℝ ℝ Space).prod ((A.ell • ContinuousLinearMap.id ℝ Space).comp (snd ℝ ℝ Space))
  let J : (ℝ × Space) →L[ℝ] Space :=
    (toSpanSingleton ℝ (A.velocity.field t (A.ell • x))).coprod
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell • x))
  have hp : HasFDerivAt (Function.uncurry A.realPosition) J (L (t,x)) :=
    A.realPosition_hasFDerivAt t ht (A.ell • x)
  have h := (hp.comp ((t : ℝ),x) L.hasFDerivAt).const_smul A.ell⁻¹
  have he : A.ell⁻¹ • J.comp L = A.packetPositionDerivative t x := by
    apply ContinuousLinearMap.ext
    intro v
    change A.ell⁻¹ • (v.1 • A.velocity.field t (A.ell • x) +
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell • x))
        (A.ell • v.2)) = v.1 • (A.ell⁻¹ • A.velocity.field t (A.ell • x))+A.frame.field t x v.2
    rw [smul_add]
    apply congrArg₂ (fun a b : Space => a+b)
    · exact smul_comm A.ell⁻¹ v.1 _
    · rw [map_smul,smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul,A.frame_apply]
  rw [he] at h
  exact h


-- @@ L472-490 verbatim
theorem packetPosition_spatial (t : Icc (0 : ℝ) A.T) (x : Space) :
    HasFDerivAt (fun y => A.packetPosition (t,y)) (A.frame.field t x) x := by
  have h := ((A.position_hasFDerivAt t (A.ell • x)).comp x
    (A.ell • ContinuousLinearMap.id ℝ Space).hasFDerivAt).const_smul A.ell⁻¹
  have he : A.ell⁻¹ •
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell •
          x)).comp
        (A.ell • ContinuousLinearMap.id ℝ Space) = A.frame.field t x := by
    apply ContinuousLinearMap.ext
    intro v
    change A.ell⁻¹ •
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell • x))
        (A.ell • v)=A.frame.field t x v
    rw [map_smul,smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul,A.frame_apply]
  rw [he] at h
  have hf : (fun y => A.packetPosition (t,y)) = (fun y => A.ell⁻¹ • A.position t (A.ell • y)) :=
    funext (A.packetPosition_apply t)
  rw [hf]
  exact h


-- @@ L492-501 verbatim
theorem packetPosition_frame (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    A.frame.realField A.T A.T_pos.le t x =
      (fderiv ℝ A.packetPosition (t,x)).comp (inr ℝ ℝ Space) := by
  rw [(A.packetPosition_hasFDerivAt ⟨t,ht.1.le,ht.2.le⟩ ht x).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [packetPositionDerivative, comp_apply, inr_apply, coprod_apply, toSpanSingleton_apply,
      zero_smul, zero_add]
  simp only [SmoothTimeField.realField,EulerVolterraConvolution.extendPath,
    projIcc_of_mem A.T_pos.le ⟨ht.1.le,ht.2.le⟩]


-- @@ L503-507 verbatim
theorem packetPosition_frame_eventually (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    (fun q : ℝ × Space => A.frame.realField A.T A.T_pos.le q.1 q.2) =ᶠ[𝓝 (t,x)]
      fun q => (fderiv ℝ A.packetPosition q).comp (inr ℝ ℝ Space) := by
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with q hq
  exact A.packetPosition_frame q.1 hq q.2


-- @@ L509-513 verbatim
theorem packetPosition_time (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    fderiv ℝ A.packetPosition (t,x) (1,0) =
      A.ell⁻¹ • A.velocity.field ⟨t,ht.1.le,ht.2.le⟩ (A.ell • x) := by
  rw [(A.packetPosition_hasFDerivAt ⟨t,ht.1.le,ht.2.le⟩ ht x).fderiv]
  simp only [packetPositionDerivative,coprod_apply,toSpanSingleton_apply,one_smul,map_zero,add_zero]


-- @@ L515-521 verbatim
theorem packetInverse_left (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x) (q : ℝ × Space) :
    A.packetInverse Y (q.1,A.packetPosition q)=q.2 := by
  change A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1)
    (A.ell • (A.ell⁻¹ • A.position (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)))=q.2
  rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,hYX,
    smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul]


-- @@ L523-529 verbatim
theorem packetInverse_right (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, A.position t (Y t x) = x) (q : ℝ × Space) :
    A.packetPosition (q.1,A.packetInverse Y q)=q.2 := by
  change A.ell⁻¹ • A.position (projIcc 0 A.T A.T_pos.le q.1)
    (A.ell • (A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)))=q.2
  rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,hXY,
    smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul]


-- @@ L531-535 verbatim
theorem packetInverse_joint_continuous (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) : Continuous (A.packetInverse Y) :=
  (hY.comp (((show Continuous (projIcc 0 A.T A.T_pos.le) from continuous_projIcc).comp
      continuous_fst).prodMk
    (continuous_snd.const_smul A.ell))).const_smul A.ell⁻¹


-- @@ L537-541 verbatim
/-- Frame equiv, given by `ContinuousLinearEquiv.equivOfInverse (A.frame.field t x)
(A.inverse.field t x) (A.inverse_left t x) (A.inverse_right t x)`. -/
def frameEquiv (t : Icc (0 : ℝ) A.T) (x : Space) : Space ≃L[ℝ] Space :=
  ContinuousLinearEquiv.equivOfInverse (A.frame.field t x) (A.inverse.field t x)
    (A.inverse_left t x) (A.inverse_right t x)


-- @@ L543-544 verbatim
/-- Packet lift, given by `(q.1,A.packetPosition q)`. -/
def packetLift (q : ℝ × Space) : ℝ × Space := (q.1,A.packetPosition q)

-- @@ L545-547 verbatim
/-- Packet inverse lift, given by `(q.1,A.packetInverse Y q)`. -/
def packetInverseLift (Y : Icc (0 : ℝ) A.T → Space → Space) (q : ℝ × Space) : ℝ × Space :=
  (q.1,A.packetInverse Y q)


-- @@ L549-563 verbatim
theorem packetLift_hasFDerivAt (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    HasFDerivAt A.packetLift
      (timeLiftEquiv (A.frameEquiv t x) (A.ell⁻¹ • A.velocity.field t (A.ell •
          x))).toContinuousLinearMap
      (t,x) := by
  have h := hasFDerivAt_fst.prodMk (A.packetPosition_hasFDerivAt t ht x)
  have he : (fst ℝ ℝ Space).prod (A.packetPositionDerivative t x) =
      (timeLiftEquiv (A.frameEquiv t x) (A.ell⁻¹ • A.velocity.field t (A.ell •
          x))).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext rfl
    rfl
  rw [he] at h
  exact h


-- @@ L565-583 verbatim
theorem packetInverseLift_contDiffAt_two (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, A.position t (Y t x) = x)
    (hY : Continuous (Function.uncurry Y))
    (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    ContDiffAt ℝ 2 (A.packetInverseLift Y) (t,x) := by
  let y := A.packetInverse Y (t,x)
  apply EulerSmoothImplicitLift.contDiffAt_of_identity
    (A.packetInverseLift Y) A.packetLift id (t,x) 2 (by norm_num)
    ((continuous_fst.prodMk (A.packetInverse_joint_continuous Y hY)).continuousAt)
    (contDiffAt_fst.prodMk (A.packetPosition_contDiffAt_two t ht y))
    contDiff_id.contDiffAt
    (timeLiftEquiv (A.frameEquiv ⟨t,ht.1.le,ht.2.le⟩ y)
      (A.ell⁻¹ • A.velocity.field ⟨t,ht.1.le,ht.2.le⟩ (A.ell • y)))
  · exact A.packetLift_hasFDerivAt ⟨t,ht.1.le,ht.2.le⟩ ht y
  · intro q
    change (q.1,A.packetPosition (q.1,A.packetInverse Y q))=q
    apply Prod.ext
    · rfl
    · exact A.packetInverse_right Y hXY q


-- @@ L585-585 verbatim
end EulerParentPacketFrames.Parent
