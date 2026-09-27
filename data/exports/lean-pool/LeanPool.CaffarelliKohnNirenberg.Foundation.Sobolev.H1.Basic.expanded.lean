/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic


-- @@ L10-26 verbatim
/-!
# Representative-level `H¹`

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port is the exact `p = 2` facade over the independent CKN
representative-level `W1pFunction` API.

## Main definitions

* `MemL2On` and `GradMemL2On`: scalar and coordinatewise `L²` membership.
* `H1Function`: a concrete scalar representative with a chosen weak gradient.

## Main results

* `H1Function.restrict`: restriction to an open subset.
* The conversion lemmas preserve values and gradients definitionally.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open scoped ENNReal


-- @@ L32-32 verbatim
namespace CKN


-- @@ L34-36 verbatim
/-- Scalar `L²` membership on a restricted domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u


-- @@ L38-41 verbatim
/-- Coordinatewise gradient `L²` membership on a restricted domain. -/
abbrev GradMemL2On {d : ℕ}
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du


-- @@ L43-52 verbatim
/-- A concrete scalar representative and a chosen coordinate weak gradient in
`L²(U)`. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  /-- Chosen scalar representative of the H¹ function. -/
  toFun : Vec d → ℝ
  /-- Chosen weak gradient of the H¹ representative. -/
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad


-- @@ L54-56 verbatim
instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun


-- @@ L58-60 verbatim
/-- Representative-level membership of a concrete function in `H¹(U)`. -/
def MemH1 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H1Function U, v.toFun = u


-- @@ L62-62 verbatim
namespace H1Function


-- @@ L64-72 verbatim
@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl


-- @@ L74-78 verbatim
/-- The coordinate weak-derivative identity stored in an `H1Function`. -/
theorem hasWeakPartialDerivOn {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i


-- @@ L80-84 verbatim
/-- The `i`th chosen gradient component belongs to `L²(U)`. -/
theorem grad_memL2 {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (i : Fin d) :
    MemL2On U (fun x => u.grad x i) :=
  u.gradMemL2 i


-- @@ L86-89 verbatim
/-- The underlying representative belongs to representative-level `H¹(U)`. -/
theorem memH1 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MemH1 U u.toFun :=
  ⟨u, rfl⟩


-- @@ L91-98 verbatim
/-- Regard an `H1Function` as the corresponding `W1pFunction` at `p = 2`. -/
def toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient


-- @@ L100-104 verbatim
@[simp]
theorem toW1pFunction_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toFun = u.toFun :=
  rfl


-- @@ L106-110 verbatim
@[simp]
theorem toW1pFunction_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.grad = u.grad :=
  rfl


-- @@ L112-116 verbatim
@[simp]
theorem toW1pFunction_apply {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (x : Vec d) :
    u.toW1pFunction x = u x :=
  rfl


-- @@ L118-118 verbatim
end H1Function


-- @@ L120-120 verbatim
namespace W1pFunction


-- @@ L122-129 verbatim
/-- Regard a `W1pFunction` at `p = 2` as the corresponding `H1Function`. -/
def toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient


-- @@ L131-135 verbatim
@[simp]
theorem toH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toFun = u.toFun :=
  rfl


-- @@ L137-141 verbatim
@[simp]
theorem toH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.grad = u.grad :=
  rfl


-- @@ L143-147 verbatim
@[simp]
theorem toH1Function_apply {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) (x : Vec d) :
    u.toH1Function x = u x :=
  rfl


-- @@ L149-149 verbatim
end W1pFunction


-- @@ L151-151 verbatim
namespace H1Function


-- @@ L153-157 verbatim
@[simp]
theorem toH1Function_toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toH1Function = u := by
  apply H1Function.ext <;> rfl


-- @@ L159-163 verbatim
/-- Restrict an `H1Function` to an open subset. -/
def restrict {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    H1Function V :=
  (u.toW1pFunction.restrict hVOpen hVU).toH1Function


-- @@ L165-169 verbatim
@[simp]
theorem restrict_toFun {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).toFun = u.toFun :=
  rfl


-- @@ L171-175 verbatim
@[simp]
theorem restrict_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).grad = u.grad :=
  rfl


-- @@ L177-182 verbatim
@[simp]
theorem restrict_apply {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U)
    (x : Vec d) :
    u.restrict hVOpen hVU x = u x :=
  rfl


-- @@ L184-184 verbatim
end H1Function


-- @@ L186-186 verbatim
namespace W1pFunction


-- @@ L188-192 verbatim
@[simp]
theorem toW1pFunction_toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toW1pFunction = u := by
  apply W1pFunction.ext <;> rfl


-- @@ L194-194 verbatim
end W1pFunction


-- @@ L196-196 verbatim
end CKN
