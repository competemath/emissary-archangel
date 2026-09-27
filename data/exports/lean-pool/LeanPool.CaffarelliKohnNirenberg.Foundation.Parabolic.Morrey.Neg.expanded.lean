/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic


-- @@ L10-14 verbatim
/-!
# Neg

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory

-- @@ L19-19 verbatim
open scoped ENNReal



-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace CKN.Foundation.Parabolic.Morrey


-- @@ L26-29 verbatim
/-- Negation leaves the parabolic Morrey seminorm invariant. -/
theorem morreyNorm_neg (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => -f z) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]


-- @@ L31-34 verbatim
/-- Absolute value leaves the parabolic Morrey seminorm invariant. -/
theorem morreyNorm_abs (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => |f z|) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_abs]


-- @@ L36-36 verbatim
end CKN.Foundation.Parabolic.Morrey
