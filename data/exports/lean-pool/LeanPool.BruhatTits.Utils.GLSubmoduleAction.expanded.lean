/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import LeanPool.BruhatTits.Utils.Matrix


-- @@ L10-12 verbatim
/-!
# LeanPool.BruhatTits.Utils.GLSubmoduleAction
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open Module


-- @@ L18-18 verbatim
variable {K : Type*} [Field K]

-- @@ L19-19 verbatim
variable {R : Subring K}


-- @@ L21-21 verbatim
namespace BruhatTits

-- @@ L22-22 verbatim
open Pointwise


-- @@ L24-24 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L26-42 verbatim
lemma scalar_smul_GL_smul (M : Submodule R (ι → K))
    (a : K) (g : GL ι K) : a • g • M = g • a • M := by
  ext x
  simp only [Matrix.GeneralLinearGroup.mem_smul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨a • z, ?_, ?_⟩
    · use z, hz
      rfl
    · simp [Matrix.mulVec_smul]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simp only [DistribSMul.toLinearMap_apply, Matrix.mulVec_smul]
    refine ⟨g.val.mulVec z, ?_, rfl⟩
    simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul]
    use z, hz


-- @@ L44-48 verbatim
lemma smul_GL_mono {M L : Submodule R (ι → K)} (g : GL ι K) (hML : M ≤ L) : g • M ≤ g • L := by
  intro x
  simp only [Matrix.GeneralLinearGroup.mem_smul, forall_exists_index, and_imp]
  rintro y hy rfl
  use y, (hML hy)


-- @@ L50-53 verbatim
lemma smul_le_iff {M L : Submodule R (ι → K)} (g : GL ι K) : g • M ≤ g • L ↔ M ≤ L := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_GL_mono _ h⟩
  rw [← one_smul (GL ι K) M, ← one_smul (GL ι K) L, ← inv_mul_cancel g, mul_smul, mul_smul]
  exact smul_GL_mono _ h


-- @@ L55-57 verbatim
lemma smul_eq_iff (g : GL ι K) (M L : Submodule R (ι → K)) :
    g • M = g • L ↔ M = L := by
  simp_all


-- @@ L59-67 verbatim
lemma smul_lt_iff (g : GL ι K) (M L : Submodule R (ι → K)) : g • M < g • L ↔ M < L := by
  constructor
  · intro h
    by_contra hnotlt
    simp [eq_of_le_of_not_lt ((smul_le_iff g).mp (le_of_lt h)) hnotlt] at h
  · intro h
    by_contra hnotlt
    have := eq_of_le_of_not_lt ((smul_le_iff g).mpr (le_of_lt h)) hnotlt
    simp_all


-- @@ L69-69 verbatim
end BruhatTits
