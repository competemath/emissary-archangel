/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.Alpha
public import LeanPool.CaffarelliKohnNirenberg.Statements.Beta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Delta


-- @@ L12-16 verbatim
/-!
# Theta

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic


-- @@ L22-22 verbatim
namespace CKN


-- @@ L24-28 verbatim
/-- The iteration quantity θ from the manuscript, `eq:theta`. -/
noncomputable def theta (κ : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  alpha u z r + beta u Du z r + κ ^ (-4 : ℝ) * (delta p z r) ^ (2 : ℕ)


-- @@ L30-30 verbatim
end CKN
