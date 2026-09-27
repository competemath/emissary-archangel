/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic


-- @@ L11-15 verbatim
/-!
# Beta

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open MeasureTheory

-- @@ L20-20 verbatim
open scoped ENNReal NNReal Topology

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace CKN


-- @@ L28-33 verbatim
/-- The gradient quantity β from the manuscript, `eq:alpha-beta`; `Du` is the explicit gradient
  datum. -/
noncomputable def beta (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r⁻¹ * (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^ (1 / 2 : ℝ)


-- @@ L35-35 verbatim
end CKN
