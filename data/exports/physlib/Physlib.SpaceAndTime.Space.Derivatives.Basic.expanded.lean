/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Physlib.Mathematics.Distribution.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.Analysis.InnerProductSpace.Calculus

-- @@ L13-54 verbatim
/-!

# Derivatives on Space

## i. Overview

In this module we define derivatives of functions and distributions on space `Space d`,
in the standard directions.

## ii. Key results

- `deriv` : The derivative of a function on space in a given direction.
- `distDeriv` : The derivative of a distribution on space in a given direction.

## iii. Table of contents

- A. Derivatives of functions on `Space d`
  - A.1. Basic equalities
  - A.2. Derivative of the constant function
  - A.3. Derivative distributes over addition
  - A.4. Derivative distributes over scalar multiplication
  - A.5. Two spatial derivatives commute
  - A.6. Derivative of a component
  - A.7. Derivative of a component squared
  - A.8. Derivivatives of components
  - A.9. Derivative of a norm squared
    - A.9.1. Differentiability of the norm squared function
    - A.9.2. Derivative of the norm squared function
  - A.10. Derivative of the inner product
    - A.10.1. Differentiability of the inner product function
    - A.10.2. Derivative of the inner product function
    - A.10.3. Derivative of the inner product on one side
  - A.11. Differentiability of derivatives
- B. Derivatives of distributions on `Space d`
  - B.1. The definition
  - B.2. Basic equality
  - B.3. Commutation of derivatives

## iv. References

* None.
-/


-- @@ L56-56 verbatim
@[expose] public section


-- @@ L58-58 verbatim
open Physlib


-- @@ L60-60 verbatim
namespace Space


-- @@ L62-66 verbatim
/-!

## A. Derivatives of functions on `Space d`

-/


-- @@ L68-71 verbatim
/-- Given a function `f : Space d → M` the derivative of `f` in direction `μ`. -/
noncomputable def deriv {M d} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) : Space d → M :=
  (fun x => fderiv ℝ f x (basis μ))


-- @@ L73-74 verbatim
@[inherit_doc deriv]
macro "∂[" i:term "]" : term => `(deriv $i)


-- @@ L76-80 verbatim
/-!

### A.1. Basic equalities

-/


-- @@ L82-84 verbatim
lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by rfl


-- @@ L86-88 verbatim
lemma deriv_eq_fderiv_fun [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) :
    deriv μ f = fun x => fderiv ℝ (fun x => f x) x (basis μ) := by rfl


-- @@ L90-92 verbatim
lemma deriv_eq_fderiv_basis [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by rfl


-- @@ L94-98 expanded
lemma fderiv_eq_sum_deriv {M d} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M] (f : Space d → M)
    (x y : Space d) : fderiv ℝ f x y = ∑ i : Fin d, y i • (deriv i) f x :=
  by
  conv_lhs => rw [← basis.sum_repr y]
  simp [deriv_eq_fderiv_basis]


-- @@ L100-107 verbatim
open Manifold in
/-- The spatial-derivative in terms of the derivative of functions between
  manifolds. -/
lemma deriv_eq_mfderiv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = mfderiv 𝓘(ℝ, Space d) 𝓘(ℝ, M) f x (basis μ) := by
  rw [deriv_eq_fderiv_basis, ← mfderiv_eq_fderiv]
  rfl


-- @@ L109-116 verbatim
open Manifold in
lemma mdifferentiable_manifoldStructure_iff_differentiable {M d} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {f : Space d → M} {x : Space d} :
    MDifferentiableAt (𝓡 d) 𝓘(ℝ, M) f x ↔ DifferentiableAt ℝ f x := by
  refine ⟨fun h => mdifferentiableAt_iff_differentiableAt.mp <| h.comp (I' := 𝓡 d) x
    (modelDiffeo.symm.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt,
    fun h => (mdifferentiableAt_iff_differentiableAt.mpr h).comp (I' := 𝓘(ℝ, Space d)) x
      (modelDiffeo.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt⟩


-- @@ L118-120 verbatim
TODO "Make the version of the derivative described through
  `deriv_eq_mfderiv_manifoldStructure` the definition of `deriv` and prove the
  equivalence with the current definition, under suitable conditions."


-- @@ L122-142 verbatim
open Manifold in
set_option backward.isDefEq.respectTransparency false in
/-- The spatial-derivative in terms of the derivative of functions between
  manifolds with the manifold structure `Space.manifoldStructure d`. -/
lemma deriv_eq_mfderiv_manifoldStructure {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = mfderiv (𝓡 d) 𝓘(ℝ, M) f x (EuclideanSpace.single μ 1) := by
  by_cases hf : DifferentiableAt ℝ f x
  · rw [deriv_eq_mfderiv]
    change _ = mfderiv (𝓡 d) 𝓘(ℝ, M)
      (f ∘ modelDiffeo) x (EuclideanSpace.single μ 1)
    rw [mfderiv_comp (I' := 𝓘(ℝ, Space d)) _ hf.mdifferentiableAt
      (modelDiffeo.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt]
    simp only [Function.comp_apply, modelDiffeo_apply, mfderiv_eq_fderiv,
      ContinuousLinearMap.coe_comp]
    rw [basis_eq_mfderiv_modelDiffeo_single]
    rfl
  · rw [deriv_eq, fderiv_zero_of_not_differentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt <|
      mdifferentiable_manifoldStructure_iff_differentiable.mp.mt hf]
    simp


-- @@ L144-148 verbatim
/-!

### A.2. Derivative of the constant function

-/


-- @@ L150-153 verbatim
@[simp]
lemma deriv_const [NormedAddCommGroup M] [NormedSpace ℝ M] (m : M) (μ : Fin d) :
    deriv μ (fun _ => m) t = 0 := by
  simp [deriv]


-- @@ L155-159 verbatim
/-!

### A.3. Derivative distributes over addition and subtraction

-/


-- @@ L161-167 expanded
/-- Derivatives on space distribute over addition. -/
@[to_fun]
lemma deriv_add [NormedAddCommGroup M] [NormedSpace ℝ M] (f1 f2 : Space d → M)
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    (deriv u) (f1 + f2) = (deriv u) f1 + (deriv u) f2 :=
  by
  ext x
  simp [deriv_eq, fderiv_add (hf1 x) (hf2 x)]


-- @@ L169-174 expanded
/-- Derivatives on space distribute coordinate-wise over addition. -/
lemma deriv_coord_add (f1 f2 : Space d → EuclideanSpace ℝ (Fin d)) (hf1 : Differentiable ℝ f1)
    (hf2 : Differentiable ℝ f2) :
    ((deriv u) (fun x => f1 x i + f2 x i)) =
      ((deriv u) (fun x => f1 x i)) + ((deriv u) (fun x => f2 x i)) :=
  deriv_add (fun x => f1 x i) (fun x => f2 x i) (by fun_prop) (by fun_prop)


-- @@ L176-182 expanded
/-- Derivatives on space distribute over subtraction. -/
@[to_fun]
lemma deriv_sub [NormedAddCommGroup M] [NormedSpace ℝ M] (f1 f2 : Space d → M)
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    (deriv u) (f1 - f2) = (deriv u) f1 - (deriv u) f2 :=
  by
  ext x
  simp [deriv_eq, fderiv_sub (hf1 x) (hf2 x)]


-- @@ L184-188 verbatim
/-!

### A.4. Derivative distributes over scalar multiplication

-/


-- @@ L190-195 expanded
/-- Space derivatives on scalar product of functions. -/
lemma deriv_smul [NormedAddCommGroup M] [NormedSpace ℝ M] [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 M] {c : Space d → 𝕜} {f : Space d → M}
    (hc : DifferentiableAt ℝ c x) (hf : DifferentiableAt ℝ f x) :
    (deriv u) (c • f) x = c x • (deriv u) f x + (deriv u) c x • f x := by
  simp [deriv_eq, fderiv_smul hc hf]


-- @@ L197-202 expanded
/-- Space derivatives on scalar times function. -/
lemma deriv_const_smul [NormedAddCommGroup M] [NormedSpace ℝ M] [Semiring R] [Module R M]
    [SMulCommClass ℝ R M] [ContinuousConstSMul R M] {f : Space d → M} (c : R)
    (h : Differentiable ℝ f) : (deriv u) (c • f) = c • (deriv u) f :=
  by
  ext x
  simp [deriv_eq, fderiv_const_smul (h x) c]


-- @@ L204-208 expanded
/-- Coordinate-wise scalar multiplication on space derivatives. -/
lemma deriv_coord_smul (f : Space d → EuclideanSpace ℝ (Fin d)) (k : ℝ) (hf : Differentiable ℝ f) :
    (deriv u) (fun x => k * f x i) x = k * (deriv u) (fun x => f x i) x :=
  congrFun (deriv_const_smul (f := fun x => f x i) k (by fun_prop)) x


-- @@ L210-214 verbatim
/-!

### A.5. Two spatial derivatives commute

-/


-- @@ L216-225 expanded
/-- Derivatives on space commute with one another. -/
lemma deriv_commute [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Space d → M)
    (hf : ContDiff ℝ 2 f) : (deriv u) ((deriv v) f) = (deriv v) ((deriv u) f) :=
  by
  simp only [deriv_eq_fderiv_fun]
  ext x
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [(hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq]
  repeat fun_prop


-- @@ L227-231 verbatim
/-!

### A.6. Derivative of a component

-/


-- @@ L233-238 expanded
@[simp]
lemma deriv_component_same (μ : Fin d) (x : Space d) : (deriv μ) (fun x => x μ) x = 1 :=
  by
  simp only [← Space.coord_apply, ← Space.coordCLM_apply]
  simp only [deriv_eq, ContinuousLinearMap.fderiv]
  simp [Space.coordCLM, Space.coord]


-- @@ L240-244 verbatim
lemma deriv_component_diff (μ ν : Fin d) (x : Space d) (h : μ ≠ ν) :
    (deriv μ (fun x => x ν) x) = 0 := by
  simp only [← Space.coord_apply, ← Space.coordCLM_apply]
  simp only [deriv_eq, ContinuousLinearMap.fderiv]
  simpa [Space.coordCLM, Space.coord, basis_apply] using h


-- @@ L246-250 verbatim
lemma deriv_component (μ ν : Fin d) (x : Space d) :
    (deriv ν (fun x => x μ) x) = if ν = μ then 1 else 0 := by
  obtain rfl | h' := eq_or_ne ν μ
  · simp
  · simp [deriv_component_diff ν μ x h', h']


-- @@ L252-256 verbatim
/-!

### A.7. Derivative of a component squared

-/


-- @@ L258-261 verbatim
lemma deriv_component_sq {d : ℕ} {ν μ : Fin d} (x : Space d) :
    (deriv ν (fun x => (x μ) ^ 2) x) = if ν = μ then 2 * x μ else 0:= by
  rw [deriv_eq, fderiv_fun_pow 2 (eval_differentiable μ x)]
  simp [← deriv_eq, deriv_component, mul_ite]


-- @@ L263-267 verbatim
/-!

### A.8. Derivivatives of components

-/


-- @@ L269-275 verbatim
lemma deriv_euclid {d ν μ} {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (x : Space d) :
    deriv ν (fun x => f x μ) x = deriv ν (fun x => f x) x μ := by
  rw [deriv_eq_fderiv_basis]
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) x (basis ν) = _
  rw [fderiv_comp x (EuclideanSpace.proj μ).differentiableAt (hf x)]
  simp [-EuclideanSpace.coe_proj, ← deriv_eq_fderiv_basis]


-- @@ L277-283 verbatim
lemma deriv_lorentz_vector {d ν μ} {f : Space d → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (x : Space d) :
    deriv ν (fun x => f x μ) x = deriv ν (fun x => f x) x μ := by
  rw [deriv_eq_fderiv_basis]
  change fderiv ℝ (Lorentz.Vector.coordCLM μ ∘ fun x => f x) x (basis ν) = _
  rw [fderiv_comp x (Lorentz.Vector.coordCLM μ).differentiableAt (hf x)]
  simp [← deriv_eq_fderiv_basis, Lorentz.Vector.coordCLM_apply]


-- @@ L285-289 verbatim
/-!

### A.9. Derivative of a norm squared

-/


-- @@ L291-295 verbatim
/-!

#### A.9.1. Differentiability of the norm squared function

-/

-- @@ L296-298 verbatim
@[fun_prop]
lemma norm_sq_differentiable : Differentiable ℝ (fun x : Space d => ‖x‖ ^ 2) :=
  (contDiff_norm_sq ℝ).differentiable one_ne_zero


-- @@ L300-304 verbatim
/-!

#### A.9.2. Derivative of the norm squared function

-/


-- @@ L306-308 verbatim
lemma deriv_norm_sq (x : Space d) (i : Fin d) :
    deriv i (fun x => ‖x‖ ^ 2) x = 2 * x i := by
  simp [deriv_eq, fderiv_norm_sq_apply]


-- @@ L310-314 verbatim
/-!

### A.10. Derivative of the inner product

-/


-- @@ L316-316 verbatim
open InnerProductSpace


-- @@ L318-322 verbatim
/-!

#### A.10.1. Differentiability of the inner product function

-/


-- @@ L324-328 verbatim
/-- The inner product is differentiable. -/
@[fun_prop]
lemma inner_differentiable {d : ℕ} :
    Differentiable ℝ (fun y : Space d => ⟪y, y⟫_ℝ) :=
  differentiable_id.inner ℝ differentiable_id


-- @@ L330-333 verbatim
@[fun_prop]
lemma inner_differentiableAt {d : ℕ} (x : Space d) :
    DifferentiableAt ℝ (fun y : Space d => ⟪y, y⟫_ℝ) x :=
  inner_differentiable x


-- @@ L335-341 verbatim
@[fun_prop]
lemma inner_apply_differentiableAt {d : ℕ} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {f : M → Space d} {g : M → Space d} (x : M)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y : M => ⟪f y, g y⟫_ℝ) x :=
  hf.inner ℝ hg


-- @@ L343-349 verbatim
@[fun_prop]
lemma inner_apply_differentiable {d : ℕ} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {f : M → Space d} {g : M → Space d}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y : M => ⟪f y, g y⟫_ℝ) :=
  hf.inner ℝ hg

-- @@ L350-353 verbatim
@[fun_prop]
lemma inner_contDiff {n : WithTop ℕ∞} {d : ℕ} :
    ContDiff ℝ n (fun y : Space d => ⟪y, y⟫_ℝ) :=
  contDiff_id.inner ℝ contDiff_id


-- @@ L355-361 verbatim
@[fun_prop]
lemma inner_apply_contDiff {n : WithTop ℕ∞} {d : ℕ} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {f : M → Space d} {g : M → Space d}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun y : M => ⟪f y, g y⟫_ℝ) :=
  hf.inner ℝ hg

-- @@ L362-366 verbatim
/-!

#### A.10.2. Derivative of the inner product function

-/


-- @@ L368-370 verbatim
lemma deriv_eq_inner_self (x : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x, x⟫_ℝ) x = 2 * x i := by
  simpa only [real_inner_self_eq_norm_sq] using deriv_norm_sq x i


-- @@ L372-376 verbatim
/-!

#### A.10.3. Derivative of the inner product on one side

-/


-- @@ L378-381 verbatim
@[simp]
lemma deriv_inner_left {d} (x1 x2 : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x, x2⟫_ℝ) x1 = x2 i := by
  simp [deriv_eq, fderiv_inner_apply ℝ differentiableAt_fun_id (differentiableAt_const x2)]


-- @@ L383-386 verbatim
@[simp]
lemma deriv_inner_right {d} (x1 x2 : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x1, x⟫_ℝ) x2 = x1 i := by
  simp [deriv_eq, fderiv_inner_apply ℝ (differentiableAt_const x1) differentiableAt_fun_id]

-- @@ L387-391 verbatim
/-!

### A.11. Differentiability of derivatives

-/


-- @@ L393-398 verbatim
lemma deriv_differentiable {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} {f : Space d → M}
    (hf : ContDiff ℝ 2 f) (i : Fin d) :
    Differentiable ℝ (deriv i f) := by
  unfold deriv
  fun_prop


-- @@ L400-400 verbatim
open ContDiff


-- @@ L402-405 verbatim
lemma deriv_contDiff {d} {f : Space d → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n fun x i => deriv i f x := by
  unfold deriv
  fun_prop


-- @@ L407-411 verbatim
/-!

## B. Derivatives of distributions on `Space d`

-/


-- @@ L413-413 verbatim
open Distribution SchwartzMap


-- @@ L415-419 verbatim
/-!

### B.1. The definition

-/

-- @@ L420-435 expanded
/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] (μ : Fin d) :
    (Distribution ℝ (Space d) M) →ₗ[ℝ] Distribution ℝ (Space d) M
    where
  toFun
    f :=
    let ev : (Space d →L[ℝ] M) →L[ℝ] M :=
      { toFun v := v (basis μ)
        map_add' v1 v2 := by simp only [_root_.add_apply]
        map_smul' a v := by simp }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by simp
  map_smul' a f := by simp


-- @@ L437-438 verbatim
@[inherit_doc distDeriv]
macro "∂ᵈ[" i:term "]" : term => `(distDeriv $i)


-- @@ L440-444 verbatim
/-!

### B.2. Basic equality

-/


-- @@ L446-449 expanded
lemma distDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] (μ : Fin d)
    (f : Distribution ℝ (Space d) M) (ε : 𝓢(Space d, ℝ)) :
    ((distDeriv μ) f) ε = fderivD ℝ f ε (basis μ) := by simp [distDeriv, Distribution.fderivD]


-- @@ L451-455 verbatim
/-!

### B.3. Commutation of derivatives

-/


-- @@ L457-466 expanded
lemma schwartMap_fderiv_comm {d} (μ ν : Fin d) (x : Space d) (η : 𝓢(Space d, ℝ)) :
    ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis μ))
          ((fderivCLM ℝ (Space d) ℝ)
            ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis ν)) ((fderivCLM ℝ (Space d) ℝ) η))))
        x =
      ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis ν))
          ((fderivCLM ℝ (Space d) ℝ)
            ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis μ)) ((fderivCLM ℝ (Space d) ℝ) η))))
        x :=
  by
  change (deriv μ) ((deriv ν) ⇑η) x = (deriv ν) ((deriv μ) ⇑η) x
  exact congrFun (deriv_commute _ (η.smooth 2)) x


-- @@ L468-474 expanded
lemma distDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] (μ ν : Fin d)
    (f : Distribution ℝ (Space d) M) :
    ((distDeriv ν) ((distDeriv μ) f)) = ((distDeriv μ) ((distDeriv ν) f)) :=
  by
  ext η
  simp [distDeriv, Distribution.fderivD]
  congr 1
  exact SchwartzMap.ext fun x => schwartMap_fderiv_comm μ ν x η


-- @@ L476-476 verbatim
end Space
