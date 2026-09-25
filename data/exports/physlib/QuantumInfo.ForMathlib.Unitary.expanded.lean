/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import QuantumInfo.ForMathlib.HermitianMat.Unitary


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
open BigOperators

-- @@ L15-15 verbatim
open Classical


-- @@ L17-17 verbatim
namespace LinearMap

-- @@ L18-18 verbatim
section unitary


-- @@ L20-20 verbatim
variable {𝕜 : Type*} [RCLike 𝕜]

-- @@ L21-21 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- @@ L22-22 verbatim
variable [FiniteDimensional 𝕜 E]


-- @@ L24-24 verbatim
open Module.End


-- @@ L26-29 verbatim
@[simp]
theorem unitary_star_apply_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    (star U.val) (U.val v) = v := by
  rw [← mul_apply, (Unitary.mem_iff.mp U.prop).left, one_apply]


-- @@ L31-34 verbatim
@[simp]
theorem unitary_apply_star_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    U.val ((star U.val) v) = v := by
  rw [← mul_apply, (Unitary.mem_iff.mp U.prop).right, one_apply]


-- @@ L36-51 verbatim
/-- Conjugating a linear map by a unitary operator gives a map whose μ-eigenspace is
  isomorphic (same dimension) as those of the original linear map. -/
noncomputable def conj_unitary_eigenspace_equiv (T : E →ₗ[𝕜] E) (U : unitary (E →ₗ[𝕜] E)) (μ : 𝕜) :
    eigenspace T μ ≃ₗ[𝕜] eigenspace (U.val * T * star (U.val)) μ where
  toFun v := ⟨U.val v.val, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simp [hv]⟩
  invFun v := ⟨(star U.val) v, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simpa using congrArg ((star U.val) ·) hv⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv _ := by simp
  right_inv _ := by simp


-- @@ L53-53 verbatim
end unitary

-- @@ L54-54 verbatim
namespace IsSymmetric


-- @@ L56-56 verbatim
open Module.End


-- @@ L58-58 verbatim
variable {𝕜 : Type*} [RCLike 𝕜]

-- @@ L59-59 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- @@ L60-60 verbatim
variable [FiniteDimensional 𝕜 E]

-- @@ L61-61 verbatim
variable {T : E →ₗ[𝕜] E}


-- @@ L63-69 verbatim
/-- A symmetric operator conjugated by a unitary is symmetric. -/
theorem conj_unitary_IsSymmetric (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    (U.val * T * star U.val).IsSymmetric := by
  intro i j
  rw [mul_assoc, mul_apply, ← LinearMap.adjoint_inner_right]
  rw [mul_apply, mul_apply, mul_apply, ← LinearMap.adjoint_inner_left U.val]
  exact hT (star U.val <| i) (star U.val j)


-- @@ L71-71 verbatim
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)


-- @@ L73-90 verbatim
/-- There is an equivalence between the eigenvalues of a finite dimensional symmetric operator,
and the eigenvalues of that operator conjugated by a unitary. -/
def conj_unitary_eigenvalue_equiv (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    { σ : Equiv.Perm (Fin n) //
      (hT.conj_unitary_IsSymmetric U).eigenvalues hn = hT.eigenvalues hn ∘ σ } := by
  set hS := hT.conj_unitary_IsSymmetric U
  suffices heq : hS.eigenvalues hn = hT.eigenvalues hn from ⟨1, by simp [heq]⟩
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedGE
    (hS.eigenvalues_antitone hn).sortedGE_ofFn (hT.eigenvalues_antitone hn).sortedGE_ofFn
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
  refine Multiset.ext.mpr fun a ↦ ?_
  have h (R : E →ₗ[𝕜] E) (hR : R.IsSymmetric) :
      (Finset.univ.val.map (hR.eigenvalues hn)).count a
        = Module.finrank 𝕜 (eigenspace R (a : 𝕜)) := by
    rw [Multiset.count_map, ← hR.card_filter_eigenvalues_eq hn ↑a, Finset.card_def]
    congr 1; ext; simp [eq_comm]
  rw [h _ hS, h _ hT, (conj_unitary_eigenspace_equiv T U ↑a).finrank_eq]


-- @@ L92-92 verbatim
end IsSymmetric

-- @@ L93-93 verbatim
end LinearMap
