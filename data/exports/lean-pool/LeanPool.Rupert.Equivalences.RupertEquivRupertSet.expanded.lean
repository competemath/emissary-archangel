/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import LeanPool.Rupert.Set
import LeanPool.Rupert.Equivalences.Util


-- @@ L11-15 verbatim
/-!
# LeanPool.Rupert.Equivalences.RupertEquivRupertSet

Imported Lean Pool material for `LeanPool.Rupert.Equivalences.RupertEquivRupertSet`.
-/


-- @@ L17-17 verbatim
@[expose] public section

-- @@ L18-18 verbatim
open Matrix


-- @@ L20-34 expanded
theorem rupert_imp_rupert_set {ι : Type} [Finite ι] (v : ι → EuclideanSpace ℝ (Fin 3)) :
    IsRupert v → IsRupertSet (convexHull ℝ (Set.range v)) :=
  by
  intro ⟨innerRot, inner_so3, innerOffset, outerRot, outer_so3, rupert⟩
  use innerRot, inner_so3, innerOffset, outerRot, outer_so3
  intro inner_shadow outerShadow
  let tx := fullTransformAffine innerOffset ⟨innerRot, inner_so3⟩
  have inner_shadow_closed : IsClosed inner_shadow :=
    by
    have inner_shadow_is_txed_convex_hull :
      tx '' (convexHull ℝ (Set.range v)) = convexHull ℝ (tx '' Set.range v) := by
      apply AffineMap.image_convexHull
    change inner_shadow = convexHull ℝ (tx '' Set.range v) at inner_shadow_is_txed_convex_hull
    rw [inner_shadow_is_txed_convex_hull, ← Set.range_comp]
    exact Set.Finite.isClosed_convexHull ℝ (Set.finite_range (tx ∘ v))
  rw [closure_eq_iff_isClosed.mpr inner_shadow_closed]
  exact rupert


-- @@ L36-41 expanded
theorem rupert_set_imp_rupert {ι : Type} (v : ι → EuclideanSpace ℝ (Fin 3)) :
    IsRupertSet (convexHull ℝ (Set.range v)) → IsRupert v :=
  by
  intro ⟨innerRot, inner_so3, innerOffset, outerRot, outer_so3, rupert⟩
  use innerRot, inner_so3, innerOffset, outerRot, outer_so3
  intro _ _ _ _ ha
  exact rupert (subset_closure ha)


-- @@ L43-45 expanded
theorem rupert_iff_rupert_set {ι : Type} [Finite ι] (v : ι → EuclideanSpace ℝ (Fin 3)) :
    IsRupert v ↔ IsRupertSet (convexHull ℝ (Set.range v)) :=
  ⟨rupert_imp_rupert_set v, rupert_set_imp_rupert v⟩

