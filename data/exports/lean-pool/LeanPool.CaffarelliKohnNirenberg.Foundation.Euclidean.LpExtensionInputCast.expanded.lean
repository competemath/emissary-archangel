/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtension


-- @@ L10-14 verbatim
/-!
# Lp Extension Input Cast

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open scoped ENNReal


-- @@ L20-20 verbatim
namespace CKN.Foundation.Euclidean


-- @@ L22-29 verbatim
/-- Transporting an `LpExtensionInput` along an equality of its constant does not
change its operator. -/
theorem lpExtensionInput_mp_T {p : ℝ≥0∞} {C D : ℝ}
    (hCD : C = D) (h : LpExtensionInput p C)
    (e : LpExtensionInput p C = LpExtensionInput p D) :
    (e.mp h).T = h.T := by
  subst hCD
  rfl


-- @@ L31-31 verbatim
end CKN.Foundation.Euclidean
