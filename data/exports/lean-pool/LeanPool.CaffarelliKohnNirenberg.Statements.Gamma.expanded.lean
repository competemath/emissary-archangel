/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic


-- @@ L10-14 verbatim
/-!
# Gamma

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory

-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace CKN


-- @@ L27-30 verbatim
/-- The velocity cubic quantity γ from the manuscript, `eq:alpha-beta`. -/
noncomputable def gamma (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r ^ (-2 : ℝ) * (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) ^ (1 / 3 : ℝ)


-- @@ L32-32 verbatim
end CKN
