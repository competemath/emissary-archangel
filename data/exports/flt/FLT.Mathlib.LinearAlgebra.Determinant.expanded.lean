/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
module

public import FLT.Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Central.Defs
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Determinant
import FLT.Mathlib.RingTheory.SimpleRing.TensorProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleRing.Principal


-- @@ L21-25 verbatim
/-!
# Determinant

Material destined for Mathlib.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
variable (k : Type*) [Field k] {D : Type*} [Ring D] [Algebra k D]

-- @@ L30-30 verbatim
open scoped TensorProduct


-- @@ L32-36 verbatim
lemma mulLeft_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (x : K ⊗[k] D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulLeft K (e x) = e ∘ₗ LinearMap.mulLeft K x ∘ₗ e.symm := by
  apply LinearMap.ext
  simp


-- @@ L38-42 verbatim
lemma mulRight_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (x : K ⊗[k] D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulRight K (e x) = e ∘ₗ LinearMap.mulRight K x ∘ₗ e.symm := by
  apply LinearMap.ext
  simp


-- @@ L44-48 verbatim
lemma mulLeft_conj_ofLinear (K : Type*) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K) :
    (((Matrix.ofLinearEquiv K ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K K).symm.toLinearMap
    ∘ₗ (LinearMap.mulLeft K N) ∘ₗ ((Matrix.ofLinearEquiv K) ≪≫ₗ Matrix.transposeLinearEquiv
    (Fin n) (Fin n) K K).toLinearMap)) = LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N) i).comp
    (LinearMap.proj i) := rfl


-- @@ L50-58 verbatim
lemma mulRight_conj_ofLinear (K : Type*) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K) :
    ((Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ
    LinearMap.mulRight K N ∘ₗ (Matrix.ofLinearEquiv K).toLinearMap :
    (Fin n → Fin n → K) →ₗ[K] (Fin n) → Fin n → K) =
    LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N.transpose) i).comp (LinearMap.proj i) := by
  apply LinearMap.ext
  intro M
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]


-- @@ L60-60 verbatim
variable [Algebra.IsCentral k D] [IsSimpleRing D] [FiniteDimensional k D]


-- @@ L62-69 verbatim
/-- This is instance is in a repo on brauergroup which has been PRed into mathlib
at https://github.com/leanprover-community/mathlib4/pull/26377 .
  The associated FLT issue is #631.
  For now it's in `import FLT.Mathlib.RingTheory.SimpleRing.TensorProduct`.
-/
instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (B ⊗[k] A) :=
  inferInstance


-- @@ L71-74 verbatim
instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (A ⊗[k] B) :=
  IsSimpleRing.of_ringEquiv
    (Algebra.TensorProduct.comm k B A).toRingEquiv inferInstance


-- @@ L76-100 verbatim
lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det := by
  let K' := AlgebraicClosure k
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K' (K' ⊗[k] D)
  have h1 : (LinearMap.mulLeft k d).baseChange K' = LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  have h2 : (LinearMap.mulRight k d).baseChange K' = LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  apply FaithfulSMul.algebraMap_injective k K'
  rw [LinearMap.det_baseChange (LinearMap.mulLeft k d) |>.symm, LinearMap.det_baseChange
    (LinearMap.mulRight k d) |>.symm, h1, h2]
  have h5 : LinearMap.det (LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulLeft K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulLeft _ _) e.toLinearEquiv, mulLeft_conj]
    rfl
  have h6: LinearMap.det (LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulRight K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulRight _ _) e.toLinearEquiv, mulRight_conj]
    rfl
  rw [h5, h6, ← LinearMap.det_conj (LinearMap.mulRight K' (e (1 ⊗ₜ[k] d))) <|
    (Matrix.ofLinearEquiv K').symm, LinearEquiv.symm_symm, mulRight_conj_ofLinear,
    LinearMap.det_pi, ← LinearMap.det_conj (LinearMap.mulLeft K' (e (1 ⊗ₜ[k] d))) <|
    (((Matrix.ofLinearEquiv K') ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K' K')).symm,
    LinearEquiv.symm_symm, mulLeft_conj_ofLinear, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]


-- @@ L102-105 verbatim
lemma IsSimpleRing.mulLeft_det_eq_mulRight_det' (d : Dˣ) :
    (LinearEquiv.mulLeft k d).det = (LinearEquiv.mulRight k d).det := by
  ext
  simp [mulLeft_det_eq_mulRight_det]



-- @@ L108-110 verbatim
/-!
### Auxiliary lemmas about linear equivalences and matrices
-/

-- @@ L111-111 verbatim
section LinearEquiv


-- @@ L113-113 verbatim
variable {F : Type*} [CommRing F]

-- @@ L114-114 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L115-115 verbatim
variable {V : Type*} [AddCommGroup V] [Module F V]


-- @@ L117-119 verbatim
lemma LinearEquiv.det_ne_zero
  {F : Type*} [CommRing F] [Nontrivial F] {V : Type*} [AddCommGroup V] [Module F V]
  (e : V ≃ₗ[F] V) : e.toLinearMap.det ≠ 0 := (isUnit_det' e).ne_zero


-- @@ L121-123 verbatim
lemma Matrix.toLinearEquiv_toLinearMap
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (toLinearEquiv b M h).toLinearMap = Matrix.toLin b b M := rfl


-- @@ L125-129 verbatim
lemma LinearEquiv.det_toLinearEquiv
    (b : Module.Basis ι F V) {M : Matrix ι ι F} (h : IsUnit M.det) :
    LinearEquiv.det (M.toLinearEquiv b h) = h.unit := by
  refine Units.val_inj.mp ?_
  simp [Matrix.toLinearEquiv_toLinearMap]


-- @@ L131-131 verbatim
end LinearEquiv
