/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic


-- @@ L10-14 verbatim
/-!
# Lambda

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


-- @@ L27-32 verbatim
/-- The force quantity λ from the manuscript, `eq:lambda`. -/
noncomputable def lambda (q : ℝ) (f : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r ^ (3 - 5 / q) *
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ)


-- @@ L34-34 verbatim
end CKN
