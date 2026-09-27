/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Mathlib.Topology.UnitInterval


-- @@ L10-14 verbatim
/-!
# LeanPool.WhiteheadTheorem.Shapes.UnitInterval

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.UnitInterval`.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace unitInterval


-- @@ L21-26 verbatim
instance continuousMul : ContinuousMul I where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact Continuous.mul
      (continuous_induced_dom.comp continuous_fst)
      (continuous_induced_dom.comp continuous_snd)


-- @@ L28-29 verbatim
/-- `zeroOne` -/
abbrev zeroOne : Set ℝ := {0, 1}

-- @@ L30-30 verbatim
instance : OfNat zeroOne 0 where ofNat := ⟨0, by norm_num⟩  -- typecheck `0` as an element of {0, 1}

-- @@ L31-31 verbatim
instance : OfNat zeroOne 1 where ofNat := ⟨1, by norm_num⟩


-- @@ L33-33 verbatim
namespace zeroOne


-- @@ L35-36 verbatim
lemma val_eq_zero_or_val_eq_one (t : zeroOne) : t.val = 0 ∨ t.val = 1 := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using t.property


-- @@ L38-42 verbatim
lemma eq_zero_or_eq_one (t : zeroOne) : t = 0 ∨ t = 1 := by
  obtain ht | ht := val_eq_zero_or_val_eq_one t
  all_goals obtain ⟨val, property⟩ := t; subst ht
  · left; rfl
  · right; rfl


-- @@ L44-44 verbatim
end zeroOne


-- @@ L46-52 verbatim
/-- `zeroOneIncl` -/
abbrev zeroOneIncl : C(zeroOne, I) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨x, by
    simp only [Set.mem_Icc]
    obtain hx | hx := hx
    all_goals subst hx; norm_num ⟩
  continuous_toFun := by fun_prop


-- @@ L54-54 verbatim
end unitInterval
