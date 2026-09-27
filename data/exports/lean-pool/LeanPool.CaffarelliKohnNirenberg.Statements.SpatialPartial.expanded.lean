/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis


-- @@ L12-16 verbatim
/-!
# Spatial Partial

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace CKN


-- @@ L27-30 verbatim
/-- Factor-wise spatial derivative on the ordinary product space described in
  docs/DESIGN_NOTES.md. -/
def spatialPartial (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)


-- @@ L32-32 verbatim
end CKN
