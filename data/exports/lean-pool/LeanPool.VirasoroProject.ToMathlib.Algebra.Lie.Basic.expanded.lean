/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Algebra.Lie.Basic


-- @@ L10-12 verbatim
/-!
# LeanPool.VirasoroProject.ToMathlib.Algebra.Lie.Basic
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
universe u

-- @@ L17-17 verbatim
variable (𝕜 : Type*) [CommRing 𝕜]

-- @@ L18-18 verbatim
variable (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]


-- @@ L20-27 verbatim
/-- `⁅·,·⁆` as a bilinear map. -/
def LieAlgebra.bracketHom : 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓰 where
  toFun := fun X ↦ {
    toFun := fun Y ↦ ⁅X, Y⁆
    map_add' := by simp
    map_smul' := by simp }
  map_add' X Y := by simp_all only [add_lie]; exact rfl
  map_smul' c X := by simp_all only [smul_lie, RingHom.id_apply]; exact rfl


-- @@ L29-30 verbatim
@[simp]
lemma LieAlgebra.bracketHom_apply {X Y : 𝓰} : LieAlgebra.bracketHom 𝕜 𝓰 X Y = ⁅X, Y⁆ := rfl


-- @@ L32-44 verbatim
/-- Construct an isomorphism of Lie algebras from a pair of inverse Lie algebra homomorphisms. -/
def LieEquiv.mkOfCompEqId {R : Type*} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
    {f : L →ₗ⁅R⁆ L'} {g : L' →ₗ⁅R⁆ L}
    (leftInv : g.comp f = LieHom.id) (rightInv : f.comp g = LieHom.id) :
    L ≃ₗ⁅R⁆ L' where
  toFun := f
  map_add' := by simp
  map_smul' := by simp
  map_lie' := by simp
  invFun := g
  left_inv := LieHom.congr_fun leftInv
  right_inv := LieHom.congr_fun rightInv
