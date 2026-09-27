/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic


-- @@ L10-14 verbatim
/-!
# Spatial Gradient Sq

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open CKN.Foundation.Parabolic



-- @@ L21-21 verbatim
namespace CKN


-- @@ L23-26 verbatim
/-- The squared spatial-gradient density used by paper label `def:sws`. -/
def spatialGradientSq (_u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)


-- @@ L28-28 verbatim
end CKN
