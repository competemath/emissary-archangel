/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedJointDifferentiability
import LeanPool.NavierStokesAndEuler.Euler.CommonPressureRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.GraphPressurePotential
import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GraphPullback


-- @@ L14-15 verbatim
/-! The actual total pressure of an exact lifted packet has a canonically
normalized scalar pressure on the oscillating graph. -/


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
/-! Genuine lifted divergence-free fields remain divergence-free on the oscillating graph. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerGraphDivergence


-- @@ L27-29 verbatim
open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerClassicalDivergence EulerGraphPullback EulerGraphPressurePotential
  EulerTransportDerivatives

-- @@ L30-30 verbatim
open scoped ContDiff Topology


-- @@ L32-32 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L34-69 verbatim
/-- The physical graph of an actual smooth representative of a lifted solenoidal L² field is
classically divergence-free. -/
theorem divergenceFree_graph (κ k : ℝ) (hκ : k * κ = 1) (m : Vector3)
    (u : LiftL2 period) (hu : u ∈ divergenceFreeSpace period κ m)
    (g : LiftDomain period → Vector3)
    (hrep : (u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, (∑ i : Fin 3,
      (fderiv ℝ (fun y => g (cylinderGraph period k m y)) x (EuclideanSpace.single i 1)) i) = 0 :=
          by
  let P : LiftTangent → Vector3 := localFieldLift period g 0
  have heq : (fun y => P (graphMap k m y)) = fun y => g (cylinderGraph period k m y) := by
    funext y
    simp only [P,localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add,graphMap_apply,cylinderGraph]
  have hdir (i : Fin 3) : liftedDirection κ m (EuclideanSpace.single i 1) = coordinateDirection κ m
      i := by
    simp [liftedDirection_apply,coordinateDirection,EuclideanSpace.inner_single_right]
  intro x
  have hzero := divergenceFree_classical_divergence_zero period κ m u hu g hrep hg
    (cylinderGraph period k m x)
  have hd : fderiv ℝ P (graphMap k m x) =
      fderiv ℝ (localFieldLift period g (cylinderGraph period k m x)) 0 := by
    have h := (fderiv_localFieldLift_cover period g (graphMap k m x)).symm
    simpa only [P,coveringMap,graphMap_apply,cylinderGraph] using h
  calc
    _ = ∑ i : Fin 3, k*(fieldDerivative period (coordinateDirection κ m i) g (cylinderGraph period
        k m x)) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← heq,graph_fderiv P k κ hκ m x (EuclideanSpace.single i 1) ((hg 0).differentiable (by
          simp) _),hdir,hd]
      rfl
    _ = k*(∑ i : Fin 3, (fieldDerivative period (coordinateDirection κ m i) g (cylinderGraph period
        k m x)) i) :=
      (Finset.mul_sum ..).symm
    _ = 0 := by rw [hzero,mul_zero]


-- @@ L71-71 verbatim
end EulerGraphDivergence


-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end


-- @@ L78-78 verbatim
@[expose] public section


-- @@ L80-80 verbatim
noncomputable section


-- @@ L82-82 verbatim
namespace EulerAllOrderDriftCorrection.ExactLiftedPacket


-- @@ L84-85 verbatim
open Set InnerProductSpace EulerLiftedGradientSpace EulerAllOrderCorrectionData
  EulerGraphPressurePotential EulerCanonicalGraphPotential

-- @@ L86-86 verbatim
open scoped ContDiff


-- @@ L88-89 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T} {A : Data P T} {B : Budget P hT A}
  (S : ExactLiftedPacket P hT A B)


-- @@ L91-93 verbatim
/-- Graph pressure, given by `A.κ • S.pressure.pointField t (cylinderGraph P k A.direction x)`. -/
def graphPressure (k : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) : Vector3 :=
  A.κ • S.pressure.pointField t (cylinderGraph P k A.direction x)


-- @@ L95-99 verbatim
theorem graphPressure_joint_continuous (k : ℝ) :
    Continuous (S.graphPressure k).uncurry :=
  (S.pressure.pointField_joint_continuous.comp
    (continuous_fst.prodMk ((EulerCommonPressureRepresentative.cylinderGraph_continuous
      P k A.direction).comp continuous_snd))).const_smul A.κ


-- @@ L101-106 verbatim
theorem graphPressure_has_potential (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, _root_.gradient q x = S.graphPressure k t x :=
  gradientSpace_has_graph_potential P A.κ k hk A.direction
    (S.pressure.field t) (S.gradient t) (S.pressure.pointField t)
    (S.pressure.pointField_ae t) (S.pressure.pointField_smooth t)


-- @@ L108-110 verbatim
/-- Graph potential, given by `radialPotential (S.graphPressure k t)`. -/
def graphPotential (k : ℝ) (t : Icc (0 : ℝ) T) : Vector3 → ℝ :=
  radialPotential (S.graphPressure k t)


-- @@ L112-113 verbatim
theorem graphPotential_zero (k : ℝ) (t : Icc (0 : ℝ) T) :
    S.graphPotential k t 0 = 0 := radialPotential_zero _


-- @@ L115-117 verbatim
theorem graphPotential_joint_continuous (k : ℝ) :
    Continuous (S.graphPotential k).uncurry :=
  radialPotential_joint_continuous _ (S.graphPressure_joint_continuous k)


-- @@ L119-123 verbatim
theorem graphPotential_smooth (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (S.graphPotential k t) := by
  obtain ⟨q,hq,hgrad⟩ := S.graphPressure_has_potential k hk t
  exact radialPotential_smooth _
    (Continuous.uncurry_left t (S.graphPressure_joint_continuous k)) q hq hgrad


-- @@ L125-131 verbatim
theorem graphPotential_gradient (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    _root_.gradient (S.graphPotential k t) x =
      A.κ • S.pressure.pointField t (cylinderGraph P k A.direction x) := by
  obtain ⟨q,hq,hgrad⟩ := S.graphPressure_has_potential k hk t
  exact radialPotential_gradient _
    (Continuous.uncurry_left t (S.graphPressure_joint_continuous k)) q hq hgrad x


-- @@ L133-135 verbatim
/-- Raw graph potential, given by `S.graphPotential k (projIcc 0 T hT.le q.1) q.2`. -/
def rawGraphPotential (k : ℝ) (q : ℝ × Vector3) : ℝ :=
  S.graphPotential k (projIcc 0 T hT.le q.1) q.2


-- @@ L137-140 verbatim
theorem rawGraphPotential_smooth (k : ℝ) (hk : k * A.κ = 1) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => S.rawGraphPotential k (t,x)) := by
  change ContDiff ℝ ∞ (S.graphPotential k (projIcc 0 T hT.le t))
  exact S.graphPotential_smooth k hk (projIcc 0 T hT.le t)


-- @@ L142-147 verbatim
theorem rawGraphPotential_gradient (k : ℝ) (hk : k * A.κ = 1) (t : ℝ) (x : Vector3) :
    _root_.gradient (fun y => S.rawGraphPotential k (t,y)) x =
      A.κ • S.rawPressure (t,(x,k*⟪A.direction,x⟫_ℝ)) := by
  change _root_.gradient (S.graphPotential k (projIcc 0 T hT.le t)) x =
    A.κ • S.pressure.pointField (projIcc 0 T hT.le t) (cylinderGraph P k A.direction x)
  exact S.graphPotential_gradient k hk (projIcc 0 T hT.le t) x


-- @@ L149-156 verbatim
theorem graphVelocity_divergence (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (∑ i : Fin 3, (fderiv ℝ (fun y =>
      S.velocity.pointField t (cylinderGraph P k A.direction y)) x
        (EuclideanSpace.single i 1)) i) = 0 :=
  EulerGraphDivergence.divergenceFree_graph P A.κ k hk A.direction
    (S.velocity.field t) (S.divergence t) (S.velocity.pointField t)
    (S.velocity.pointField_ae t) (S.velocity.pointField_smooth t) x


-- @@ L158-158 verbatim
end EulerAllOrderDriftCorrection.ExactLiftedPacket
