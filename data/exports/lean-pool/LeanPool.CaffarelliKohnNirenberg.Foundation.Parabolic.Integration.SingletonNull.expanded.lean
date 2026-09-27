/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average


-- @@ L10-14 verbatim
/-!
# Singleton Null

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory Set

-- @@ L19-19 verbatim
open scoped ENNReal



-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace CKN.Foundation.Parabolic.Integration


-- @@ L26-34 verbatim
/-- A single parabolic point has zero Lebesgue volume. -/
theorem volume_singleton_parabolicPoint (z : ParabolicPoint) :
    volume ({z} : Set ParabolicPoint) = 0 := by
  rcases z with ⟨x, t⟩
  rw [volume_parabolicPoint_eq_prod]
  change (volume.prod volume) ({(x, t)} : Set (Vec3 × ℝ)) = 0
  rw [show ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} by simp]
  rw [Measure.prod_prod]
  simp



-- @@ L37-37 verbatim
end CKN.Foundation.Parabolic.Integration
