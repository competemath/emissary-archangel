/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add


-- @@ L11-15 verbatim
/-!
# Time Partial

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open CKN.Foundation.Parabolic



-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace CKN


-- @@ L26-28 verbatim
/-- Factor-wise time derivative on the ordinary product space described in docs/DESIGN_NOTES.md. -/
def timePartial (g : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2) 1


-- @@ L30-30 verbatim
end CKN
