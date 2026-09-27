/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling


-- @@ L10-14 verbatim
/-!
# Alpha

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

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic.Integration



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace CKN


-- @@ L28-31 verbatim
/-- The velocity energy quantity α from the manuscript, `eq:alpha-beta`. -/
noncomputable def alpha (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r⁻¹ * (timeSliceEnergyEssSup z.1 z.2 r
      (fun w => vec3EuclideanNorm (u w))).toReal) ^ (1 / 2 : ℝ)


-- @@ L33-33 verbatim
end CKN
