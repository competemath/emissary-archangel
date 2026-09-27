/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
public import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis


-- @@ L12-16 verbatim
/-!
# LeanPool.QuasiBorelSpaces.FlatReal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.FlatReal`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory

-- @@ L21-21 verbatim
open MeasureSpace


-- @@ L23-26 verbatim
/-- Reals with the Lebesgue measure and a discrete ωCPO structure. -/
structure FlatReal where
  /-- The underlying real number. -/
  val : ℝ


-- @@ L28-28 verbatim
namespace FlatReal


-- @@ L30-30 verbatim
instance : Inhabited FlatReal := ⟨⟨0⟩⟩


-- @@ L32-33 verbatim
instance : MeasurableSpace FlatReal :=
  MeasurableSpace.comap FlatReal.val (inferInstance : MeasurableSpace ℝ)


-- @@ L35-36 verbatim
noncomputable instance : MeasureSpace FlatReal where
  volume := Measure.map FlatReal.mk volume


-- @@ L38-38 verbatim
namespace R


-- @@ L40-43 verbatim
@[simp, fun_prop]
lemma measurable_mk : Measurable FlatReal.mk := by
  rw [measurable_comap_iff]
  apply measurable_id


-- @@ L45-47 verbatim
@[simp, fun_prop]
lemma measurable_val : Measurable FlatReal.val := by
  apply comap_measurable


-- @@ L49-49 verbatim
end R


-- @@ L51-59 verbatim
noncomputable instance : SigmaFinite (volume : Measure FlatReal) :=
  MeasurableEquiv.sigmaFinite_map {
    toFun := FlatReal.mk
    invFun := FlatReal.val
    left_inv _ := rfl
    right_inv _ := rfl
    measurable_toFun := by simp only [Equiv.coe_fn_mk, R.measurable_mk]
    measurable_invFun := by simp only [Equiv.coe_fn_symm_mk, R.measurable_val]
  }


-- @@ L61-61 verbatim
instance : QuasiBorelSpace FlatReal := QuasiBorelSpace.ofMeasurableSpace


-- @@ L63-67 verbatim
instance : PartialOrder FlatReal where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ _ := h₁


-- @@ L69-73 verbatim
/-- `FlatReal` is trivially an ωCPO: chains are constant by discreteness. -/
instance : OmegaCompletePartialOrder FlatReal where
  ωSup c := c 0
  le_ωSup c n := by rw [(OrderHomClass.mono c) (Nat.zero_le n)]
  ωSup_le c x hx := by rw [hx 0]


-- @@ L75-79 verbatim
/-- `FlatReal` is trivially an ωQBS. -/
instance : OmegaQuasiBorelSpace FlatReal where
  isHom_ωSup := by
    change QuasiBorelSpace.IsHom fun c : OmegaCompletePartialOrder.Chain FlatReal ↦ c 0
    fun_prop


-- @@ L81-82 verbatim
instance : TopologicalSpace FlatReal :=
  TopologicalSpace.induced val inferInstance


-- @@ L84-86 verbatim
instance : BorelSpace FlatReal where
  measurable_eq := by
    simp only [instMeasurableSpace, inferInstance, Real.measurableSpace, ← borel_comap]


-- @@ L88-94 verbatim
instance : PolishSpace FlatReal :=
  Equiv.polishSpace_induced (α := FlatReal) (β := ℝ) {
    toFun := val
    invFun := mk
    left_inv _ := rfl
    right_inv _ := rfl
  }


-- @@ L96-97 verbatim
instance : StandardBorelSpace FlatReal where
  polish := ⟨inferInstance, inferInstance, inferInstance⟩


-- @@ L99-100 verbatim
@[simp]
lemma le_iff_eq {x y : FlatReal} : x ≤ y ↔ x = y := by rfl


-- @@ L102-102 verbatim
open OmegaCompletePartialOrder


-- @@ L104-123 verbatim
@[simp, fun_prop]
lemma ωScottContinuous_of
    {A : Type*} [OmegaCompletePartialOrder A] (f : FlatReal → A)
    : ωScottContinuous f := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · simp_all
  · simp only [ωSup]
    apply le_antisymm
    · apply le_ωSup_of_le 0
      change f (c 0) ≤ f (c 0)
      exact le_rfl
    · simp only [ωSup_le_iff, Chain.coe_map, Function.comp_apply]
      intro i
      apply le_of_eq
      change f (c i) = f (c 0)
      congr 1
      symm
      apply (OrderHomClass.mono c)
      simp only [zero_le]


-- @@ L125-125 verbatim
end FlatReal
