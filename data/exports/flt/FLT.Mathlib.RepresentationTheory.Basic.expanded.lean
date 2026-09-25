/-
Copyright (c) 2024 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic


-- @@ L11-15 verbatim
/-!
# Basic

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open LinearMap

-- @@ L20-20 verbatim
open scoped TensorProduct


-- @@ L22-22 verbatim
namespace Representation


-- @@ L24-25 verbatim
variable {R V G ι : Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]


-- @@ L27-27 verbatim
variable (ρ : Representation R G V) (𝓑 : Module.Basis ι R V)


-- @@ L29-31 verbatim
omit [Module.Free R V] [Module.Finite R V] in
@[simp]
lemma comp_def (g h : G) : ρ g ∘ₗ ρ h = ρ g * ρ h := rfl


-- @@ L33-45 verbatim
/-- A representation `ρ : G → GL(V)` of `G` on a finite free `R`-module `V` together with
a basis `𝓑` of `V` gives rise to a group homomorphism `G → GL_ι(R)` via the matrix of `ρ g`
in the basis `𝓑`. -/
noncomputable def glMapOfBasis
  : G →* Matrix.GeneralLinearGroup ι R where
    toFun g := {
      val := LinearMap.toMatrix 𝓑 𝓑 (ρ g)
      inv := LinearMap.toMatrix 𝓑 𝓑 (ρ g⁻¹)
      val_inv := by rw [← toMatrix_comp, comp_def, ← map_mul]; simp
      inv_val := by rw [← toMatrix_comp, comp_def, ← map_mul]; simp
    }
    map_one' := by aesop
    map_mul' := by rintro x y; simp [LinearMap.toMatrix_mul]; norm_cast


-- @@ L47-53 verbatim
/-- Base change of a representation along a commutative `R`-algebra `R'`: extends
`ρ : G → GL(V)` to `R' ⊗[R] V`. -/
noncomputable def baseChange (R' : Type*) [CommRing R'] [Algebra R R'] (ρ : Representation R G V)
    : Representation R' G (R' ⊗[R] V) where
  toFun g := LinearMap.baseChange R' (ρ g)
  map_one' := by aesop
  map_mul' := by aesop


-- @@ L55-56 verbatim
/-- Notation `ρ ⊗ᵣ ρ'` for the tensor product of two representations. -/
scoped notation ρ "⊗ᵣ" ρ' => tprod ρ ρ'

-- @@ L57-58 verbatim
/-- Notation `R' ⊗ᵣ' ρ` for the base change of `ρ` along `R → R'`. -/
scoped notation R' "⊗ᵣ'" ρ => baseChange R' ρ


-- @@ L60-60 verbatim
end Representation
