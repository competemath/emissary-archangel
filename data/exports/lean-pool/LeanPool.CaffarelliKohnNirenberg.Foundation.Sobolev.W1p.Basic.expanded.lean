/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality


-- @@ L11-27 verbatim
/-!
# Representative-level `W^{1,p}`

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port stores concrete value and gradient
representatives and uses the `CKN` weak-gradient API.

## Main definitions

* `MemLpOn` and `GradMemLpOn`: scalar and coordinatewise `L^p` membership.
* `W1pFunction`: a concrete representative with a chosen weak gradient.
* `MemW1p`: representative-level membership in `W^{1,p}`.

## Main results

* `W1pFunction.restrict`: restriction to an open subset.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open scoped ENNReal


-- @@ L33-33 verbatim
namespace CKN


-- @@ L35-38 verbatim
/-- Scalar `L^p` membership on a restricted domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)


-- @@ L40-43 verbatim
/-- Coordinatewise gradient `L^p` membership on a restricted domain. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)


-- @@ L45-53 verbatim
/-- A concrete representative and a chosen coordinate weak gradient. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  /-- Chosen scalar representative of the W¹ᵖ function. -/
  toFun : Vec d → ℝ
  /-- Chosen weak gradient of the W¹ᵖ representative. -/
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad


-- @@ L55-57 verbatim
instance {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} :
    CoeFun (W1pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toFun


-- @@ L59-62 verbatim
/-- Representative-level membership of a concrete function in `W^{1,p}`. -/
def MemW1p {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  ∃ v : W1pFunction U p, v.toFun = u


-- @@ L64-70 verbatim
/-- Restriction preserves scalar `L^p` membership. -/
theorem memLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemLpOn U p u) :
    MemLpOn V p u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set
    MeasureTheory.volume hVU)


-- @@ L72-78 verbatim
/-- Restriction preserves coordinatewise gradient `L^p` membership. -/
theorem gradMemLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemLpOn U p Du) :
    GradMemLpOn V p Du := by
  intro i
  exact memLpOn_mono hVU (hDu i)


-- @@ L80-80 verbatim
namespace W1pFunction


-- @@ L82-91 verbatim
@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u v : W1pFunction U p}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl


-- @@ L93-98 verbatim
/-- The chosen coordinate weak derivative stored in a W1p representative. -/
theorem hasWeakPartialDerivOn {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i


-- @@ L100-105 verbatim
/-- The `i`th chosen gradient component belongs to `L^p(U)`. -/
theorem grad_memLp {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (i : Fin d) :
    MemLpOn U p (fun x => u.grad x i) :=
  u.gradMemLp i


-- @@ L107-111 verbatim
/-- The underlying representative belongs to representative-level `W^{1,p}`. -/
theorem memW1p {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞} (u : W1pFunction U p) :
    MemW1p U p u.toFun :=
  ⟨u, rfl⟩


-- @@ L113-121 verbatim
/-- Restrict a representative-level Sobolev function to an open subset. -/
def restrict {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    W1pFunction V p where
  toFun := u.toFun
  grad := u.grad
  memLp := memLpOn_mono hVU u.memLp
  gradMemLp := gradMemLpOn_mono hVU u.gradMemLp
  hasWeakGradient := u.hasWeakGradient.restrict hVOpen hVU


-- @@ L123-123 verbatim
end W1pFunction


-- @@ L125-125 verbatim
end CKN
