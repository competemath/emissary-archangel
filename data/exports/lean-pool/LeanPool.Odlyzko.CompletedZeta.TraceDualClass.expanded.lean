/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

public import LeanPool.Odlyzko.Theta.TraceDualIdeal
public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.ArithMult.Init


-- @@ L17-17 verbatim
/-! TODO: Add doc-string. -/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open NumberField

-- @@ L24-24 verbatim
open scoped nonZeroDivisors


-- @@ L26-26 verbatim
namespace NumberField.Odlyzko


-- @@ L28-28 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L30-35 verbatim
open Classical in
/-- A codifferent class used in the Odlyzko-bound argument. -/
noncomputable def codifferentClass : ClassGroup (𝓞 K) :=
  ClassGroup.mk K
    (traceDualIdealUnit K
      (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))


-- @@ L37-48 verbatim
open Classical in
theorem mk_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (traceDualIdealUnit K I) =
      codifferentClass K * (ClassGroup.mk K I)⁻¹ := by
  rw [codifferentClass, ← map_inv (ClassGroup.mk K), ← map_mul]
  apply congrArg (ClassGroup.mk K)
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val,
    coe_traceDualIdealUnit, coe_traceDualIdealUnit]
  exact FractionalIdeal.dual_eq_mul_inv ℤ ℚ
    (I : FractionalIdeal (𝓞 K)⁰ K)


-- @@ L50-59 verbatim
open Classical in
/-- A trace dual class equiv used in the Odlyzko-bound argument. -/
noncomputable def traceDualClassEquiv :
    ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) where
  toFun C := codifferentClass K * C⁻¹
  invFun C := codifferentClass K * C⁻¹
  left_inv C := by
    simp
  right_inv C := by
    simp


-- @@ L61-68 verbatim
open Classical in
/-- A class group inv equiv used in the Odlyzko-bound argument. -/
noncomputable def classGroupInvEquiv :
    ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) where
  toFun C := C⁻¹
  invFun C := C⁻¹
  left_inv C := inv_inv C
  right_inv C := inv_inv C


-- @@ L70-75 verbatim
open Classical in
/-- A trace dual inverse class equiv used in the Odlyzko-bound argument. -/
noncomputable def traceDualInverseClassEquiv :
    ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (classGroupInvEquiv K).trans
    ((traceDualClassEquiv K).trans (classGroupInvEquiv K))


-- @@ L77-83 verbatim
open Classical in
@[simp]
theorem traceDualInverseClassEquiv_apply
    (C : ClassGroup (𝓞 K)) :
    traceDualInverseClassEquiv K C =
      (traceDualClassEquiv K C⁻¹)⁻¹ :=
  rfl


-- @@ L85-90 verbatim
open Classical in
theorem mk_traceDualIdealUnit_eq_traceDualClassEquiv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (traceDualIdealUnit K I) =
      traceDualClassEquiv K (ClassGroup.mk K I) :=
  mk_traceDualIdealUnit K I


-- @@ L92-92 verbatim
variable [IsTotallyComplex K]


-- @@ L94-94 verbatim
end NumberField.Odlyzko
