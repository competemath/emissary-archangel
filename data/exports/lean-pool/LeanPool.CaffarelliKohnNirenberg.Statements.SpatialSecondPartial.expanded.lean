/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial


-- @@ L10-14 verbatim
/-!
# Spatial Second Partial

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open CKN.Foundation.Parabolic



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace CKN


-- @@ L25-28 verbatim
/-- The iterated spatial derivative used in the local energy inequality. -/
def spatialSecondPartial (g : ParabolicPoint → ℝ) (i j : Fin 3)
    (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => spatialPartial g i w) j z


-- @@ L30-30 verbatim
end CKN
