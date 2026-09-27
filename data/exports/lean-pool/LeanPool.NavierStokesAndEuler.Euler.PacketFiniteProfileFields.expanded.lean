/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation
public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeAlgebra


-- @@ L14-14 verbatim
/-! The literal finite packet and its genuine time derivative are actual cylinder fields. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField


-- @@ L23-23 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades


-- @@ L25-28 verbatim
/-- Raw time derivative, defined pointwise by `derivWithin (fun t => raw (t,z.2)) (Icc (0 : ℝ)
T) z.1`. -/
def rawTimeDerivative (T : ℝ) (raw : VectorField) : VectorField := fun z =>
  derivWithin (fun t => raw (t,z.2)) (Icc (0 : ℝ) T) z.1


-- @@ L30-30 verbatim
variable {P T : ℝ} [Fact (0 < P)]


-- @@ L32-38 verbatim
/-- Time derivative field, given by `H.congr (fun t x θ => (G.raw_hasDerivWithinAt hT.le H ht t
x θ).derivWithin ((uniqueDiffOn_Icc hT) _ t.property))`. -/
def Field.timeDerivativeField {raw raw_t : VectorField} (G : Field P T raw) (hT : 0 < T)
    (H : Field P T raw_t) (ht : TimeDerivative hT.le G H) :
    Field P T (rawTimeDerivative T raw) :=
  H.congr (fun t x θ => (G.raw_hasDerivWithinAt hT.le H ht t x θ).derivWithin
    ((uniqueDiffOn_Icc hT) _ t.property))


-- @@ L40-42 verbatim
theorem Field.timeDerivativeField_time {raw raw_t : VectorField} (G : Field P T raw) (hT : 0 < T)
    (H : Field P T raw_t) (ht : TimeDerivative hT.le G H) :
    TimeDerivative hT.le G (G.timeDerivativeField hT H ht) := ht


-- @@ L44-44 verbatim
namespace ProfileRegularity


-- @@ L46-47 verbatim
variable {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))


-- @@ L49-52 verbatim
/-- Velocity grade field, constructed using `Field.assembleFamily`. -/
def velocityGradeField (i : ℕ) : Field P T (assembledVelocity N a i) :=
  Field.assembleFamily N (fun j => (a j).high+(a j).mean) (fun j => (a j).corrector)
    (fun j hj => (G j hj).high.add (G j hj).mean) (fun j hj => (G j hj).corrector) i


-- @@ L54-58 verbatim
/-- Velocity time coefficients, given by `assemble N (fun i => rawTimeDerivative T ((a
i).high+(a i).mean)) (fun i => rawTimeDerivative T (a i).corrector)`. -/
def velocityTimeCoefficients : ℕ → VectorField :=
  assemble N (fun i => rawTimeDerivative T ((a i).high+(a i).mean))
    (fun i => rawTimeDerivative T (a i).corrector)


-- @@ L60-69 verbatim
/-- Velocity grade derivative field, constructed using `Field.assembleFamily`. -/
def velocityGradeDerivativeField (i : ℕ) : Field P T (velocityTimeCoefficients (T := T) (N := N) (a
    := a) i) :=
  Field.assembleFamily N (fun j => rawTimeDerivative T ((a j).high+(a j).mean))
    (fun j => rawTimeDerivative T (a j).corrector)
    (fun j hj => ((G j hj).high.add (G j hj).mean).timeDerivativeField hT
      ((G j hj).highDerivative.add (G j hj).meanDerivative)
      ((G j hj).high_time.add (G j hj).mean_time))
    (fun j hj => (G j hj).corrector.timeDerivativeField hT (G j hj).correctorDerivative
      (G j hj).corrector_time) i


-- @@ L71-75 verbatim
theorem velocityGrade_time (i : ℕ) :
    TimeDerivative hT.le (velocityGradeField hT G i) (velocityGradeDerivativeField hT G i) :=
  TimeDerivative.assembleFamily N _ _ _ _ _ _ _ _
    (fun j hj => ((G j hj).high_time.add (G j hj).mean_time))
    (fun j hj => (G j hj).corrector_time) i


-- @@ L77-79 verbatim
/-- Velocity field, given by `Field.evaluateFamily (N+1) κ _ (velocityGradeField hT G)`. -/
def velocityField (κ : ℝ) : Field P T (fieldSum (N+1) κ (assembledVelocity N a)) :=
  Field.evaluateFamily (N+1) κ _ (velocityGradeField hT G)


-- @@ L81-85 verbatim
/-- Velocity derivative field, given by `Field.evaluateFamily (N+1) κ _
(velocityGradeDerivativeField hT G)`. -/
def velocityDerivativeField (κ : ℝ) :
    Field P T (fieldSum (N+1) κ (velocityTimeCoefficients (T := T) (N := N) (a := a))) :=
  Field.evaluateFamily (N+1) κ _ (velocityGradeDerivativeField hT G)


-- @@ L87-89 verbatim
theorem velocityField_time (κ : ℝ) :
    TimeDerivative hT.le (velocityField hT G κ) (velocityDerivativeField hT G κ) :=
  TimeDerivative.evaluateFamily (N+1) κ _ _ _ _ (velocityGrade_time hT G)


-- @@ L91-91 verbatim
end ProfileRegularity

-- @@ L92-92 verbatim
end EulerPacketCylinderField
