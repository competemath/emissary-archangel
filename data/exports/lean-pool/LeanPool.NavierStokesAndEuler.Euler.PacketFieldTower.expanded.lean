/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField


-- @@ L12-13 verbatim
/-! The actual smooth cylinder paths produced by the packet construction
give coherent continuous Sobolev realizations at every finite order. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L22-23 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion EulerVolterraConvolution


-- @@ L25-25 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}


-- @@ L27-32 verbatim
/-- No Sobolev realizations are hypothesized: each is constructed from the
genuine mixed translation orbit of the prescribed field. -/
def toFieldTower (G : Field P T raw) : EulerAllOrderCorrectionData.FieldTower P T where
  field := G.path
  realization q := sobolevPath P q G.path G.orbit
  value_eq q t := sobolevPath_value P q G.path G.orbit t


-- @@ L34-34 verbatim
@[simp] theorem toFieldTower_field (G : Field P T raw) : G.toFieldTower.field = G.path := rfl


-- @@ L36-37 verbatim
@[simp] theorem toFieldTower_realization (G : Field P T raw) (q : ℕ) :
    G.toFieldTower.realization q = sobolevPath P q G.path G.orbit := rfl


-- @@ L39-40 verbatim
theorem toFieldTower_value (G : Field P T raw) (q : ℕ) (t : Icc (0 : ℝ) T) :
    value P (G.toFieldTower.realization q t) = G.path t := G.toFieldTower.value_eq q t


-- @@ L42-48 verbatim
/-- The common value has the very same pointwise cylinder representative
as the literal packet field. -/
theorem toFieldTower_value_ae (G : Field P T raw) (q : ℕ) (t : Icc (0 : ℝ) T) :
    (value P (G.toFieldTower.realization q t) : LiftDomain P → Space) =ᵐ[liftMeasure P]
      pointField P G.path G.orbit t := by
  rw [G.toFieldTower_value]
  exact pointField_ae P G.path G.orbit t


-- @@ L50-56 verbatim
/-- Genuine time derivatives lift simultaneously to all finite Sobolev
orders, including the one-sided derivatives at the interval endpoints. -/
theorem toFieldTower_hasDerivWithinAt (G : Field P T raw) (H : Field P T raw_t)
    (hT : 0 ≤ T) (hd : TimeDerivative hT G H) (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (G.toFieldTower.realization q))
      (H.toFieldTower.realization q t) (Icc (0 : ℝ) T) t :=
  sobolevPath_hasDerivWithinAt P T hT G.path H.path G.orbit H.orbit hd q t


-- @@ L58-58 verbatim
end EulerPacketCylinderField.Field
