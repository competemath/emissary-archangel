/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs


-- @@ L10-42 verbatim
/-!
# Cyclic triple sums

Cyclic triple sums are meant as auxiliary tools for proving properties like Jacobi
identities and Lie algebra 2-cocycle conditions.

## Main definitions

* `cyclicTripleSum`: An auxiliary function given by
  ⟨x,y,z⟩ ↦ φ(x,β(y,z)) + φ(y,β(z,x)) + φ(z,β(x,y)) where φ and β are two-variable functions
  on a set V with values in sets W and V, respectively.
* `cyclicTripleSumHom`: A trilinear function given by
  ⟨x,y,z⟩ ↦ φ(x,β(y,z)) + φ(y,β(z,x)) + φ(z,β(x,y)) where φ and β are bilinear functions on V
  with values in sets W and V, respectively. This function can be used in calculations towards
  the Jacobi identity in Lie algebras and the Lie algebra 2-cocycle condition.

## Main statements

A number of easy but convenient auxiliary properties towards trilinearity
of `cyclicTripleSumHom β φ` (which is mathematically trivial but should not be repeated
too often in Lean) are proven for the cyclic triple sums:
* `cyclicTripleSum_map_add_of_bilin`: If the functions φ and β are bilinear, then the cyclic triple
  sum is additive in its last variable. Additivity in the first and second variable are similarly
  obtained (the results immediately after).
* `cyclicTripleSum_map_smul_of_bilin`: If the functions φ and β are bilinear, then the cyclic triple
  sum respects scalar multiplication in its last variable. Scalar multiplication in the first and
  second variable are similarly obtained (the results immediately after).

## Tags

Jacobi identity, Lie algebra 2-cocycle condition

-/


-- @@ L44-44 verbatim
@[expose] public section


-- @@ L46-46 verbatim
namespace VirasoroProject


-- @@ L48-48 verbatim
section cyclicTripleSum


-- @@ L50-50 verbatim
/-! ### Cyclic triple sums as tools for Jacobi identities and 2-cocycle conditions -/


-- @@ L52-52 verbatim
variable {V W : Type*}


-- @@ L54-60 verbatim
/-- An auxiliary function for proofs of Jacobi identities etc.

Given functions β : V × V → V and φ : V × V → W where W has additive structure,
`cyclicTripleSum β φ` is the function of three variables on V defined by:
⟨x,y,z⟩ ↦ φ(x,β(y,z)) + φ(y,β(z,x)) + φ(z,β(x,y)). -/
def cyclicTripleSum [Add W] (β : V → V → V) (φ : V → V → W) (x y z : V) : W :=
  φ x (β y z) + φ y (β z x) + φ z (β x y)


-- @@ L62-63 verbatim
lemma cyclicTripleSum_apply [Add W] (β : V → V → V) (φ : V → V → W) (x y z : V) :
    cyclicTripleSum β φ x y z = φ x (β y z) + φ y (β z x) + φ z (β x y) := rfl


-- @@ L65-65 verbatim
variable [AddCommMonoid W]


-- @@ L67-70 verbatim
lemma cyclicTripleSum_cyclic (β : V → V → V) (φ : V → V → W) (x y z : V) :
    cyclicTripleSum β φ x y z = cyclicTripleSum β φ y z x := by
  simp only [cyclicTripleSum]
  ac_rfl


-- @@ L72-74 verbatim
lemma cyclicTripleSum_cyclic' (β : V → V → V) (φ : V → V → W) (x y z : V) :
    cyclicTripleSum β φ x y z = cyclicTripleSum β φ z x y := by
  simp_rw [cyclicTripleSum_cyclic]


-- @@ L76-81 verbatim
lemma cyclicTripleSum_map_add_fst_of_map_add [Add V] (β : V → V → V) (φ : V → V → W)
    (h : ∀ x y z₁ z₂ : V, cyclicTripleSum β φ x y (z₁ + z₂)
      = cyclicTripleSum β φ x y z₁ + cyclicTripleSum β φ x y z₂) (x₁ x₂ y z : V) :
    cyclicTripleSum β φ (x₁ + x₂) y z
      = cyclicTripleSum β φ x₁ y z + cyclicTripleSum β φ x₂ y z := by
  simpa only [cyclicTripleSum_cyclic _ _ _ y] using h y z x₁ x₂


-- @@ L83-88 verbatim
lemma cyclicTripleSum_map_add_snd_of_map_add [Add V] (β : V → V → V) (φ : V → V → W)
    (h : ∀ x y z₁ z₂ : V, cyclicTripleSum β φ x y (z₁ + z₂)
      = cyclicTripleSum β φ x y z₁ + cyclicTripleSum β φ x y z₂) (x y₁ y₂ z : V) :
    cyclicTripleSum β φ x (y₁ + y₂) z
      = cyclicTripleSum β φ x y₁ z + cyclicTripleSum β φ x y₂ z := by
  simpa only [cyclicTripleSum_cyclic' _ _ x] using h z x y₁ y₂


-- @@ L90-95 verbatim
lemma cyclicTripleSum_map_smul_fst_of_map_smul {R : Type*} [SMul R V] [SMul R W]
    (β : V → V → V) (φ : V → V → W)
    (h : ∀ c : R, ∀ x y z : V,
      cyclicTripleSum β φ x y (c • z) = c • cyclicTripleSum β φ x y z) (c : R) (x y z : V) :
    cyclicTripleSum β φ (c • x) y z = c • cyclicTripleSum β φ x y z := by
  simpa only [cyclicTripleSum_cyclic _ _ _ y] using h c y z x


-- @@ L97-102 verbatim
lemma cyclicTripleSum_map_smul_snd_of_map_smul {R : Type*} [SMul R V] [SMul R W]
    (β : V → V → V) (φ : V → V → W)
    (h : ∀ c : R, ∀ x y z : V,
      cyclicTripleSum β φ x y (c • z) = c • cyclicTripleSum β φ x y z) (c : R) (x y z : V) :
    cyclicTripleSum β φ x (c • y) z = c • cyclicTripleSum β φ x y z := by
  simpa only [cyclicTripleSum_cyclic' _ _ x] using h c z x y


-- @@ L104-104 verbatim
end cyclicTripleSum


-- @@ L106-106 verbatim
section cyclicTripleSumAdditive


-- @@ L108-108 verbatim
variable {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]


-- @@ L110-116 verbatim
lemma _root_.VirasoroProject.cyclicTripleSum_map_add_of_bilin
    (β : V →+ V →+ V) (φ : V →+ V →+ W) (x y z₁ z₂ : V) :
    cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y (z₁ + z₂)
      = cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y z₁
        + cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y z₂ := by
  simp only [cyclicTripleSum, map_add, AddMonoidHom.add_apply]
  ac_rfl


-- @@ L118-124 verbatim
lemma _root_.VirasoroProject.cyclicTripleSum_map_add_snd_of_bilin
    (β : V →+ V →+ V) (φ : V →+ V →+ W) (x y₁ y₂ z : V) :
    cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x (y₁ + y₂) z
      = cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y₁ z
        + cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y₂ z := by
  apply cyclicTripleSum_map_add_snd_of_map_add
  exact cyclicTripleSum_map_add_of_bilin β φ


-- @@ L126-132 verbatim
lemma _root_.VirasoroProject.cyclicTripleSum_map_add_fst_of_bilin
    (β : V →+ V →+ V) (φ : V →+ V →+ W) (x₁ x₂ y z : V) :
    cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) (x₁ + x₂) y z
      = cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x₁ y z
        + cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x₂ y z := by
  apply cyclicTripleSum_map_add_fst_of_map_add
  exact cyclicTripleSum_map_add_of_bilin β φ


-- @@ L134-134 verbatim
variable {𝕜} [CommSemiring 𝕜]

-- @@ L135-135 verbatim
variable [Module 𝕜 V] [Module 𝕜 W]


-- @@ L137-142 verbatim
lemma _root_.VirasoroProject.cyclicTripleSum_map_smul_of_bilin
    (β : V →ₗ[𝕜] V →ₗ[𝕜] V) (φ : V →ₗ[𝕜] V →ₗ[𝕜] W)
    (c : 𝕜) (x y z : V) :
    cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y (c • z)
      = c • cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y z := by
  simp [cyclicTripleSum]


-- @@ L144-150 verbatim
lemma _root_.VirasoroProject.cyclicTripleSum_map_smul_fst_of_bilin
    (β : V →ₗ[𝕜] V →ₗ[𝕜] V) (φ : V →ₗ[𝕜] V →ₗ[𝕜] W)
    (c : 𝕜) (x y z : V) :
    cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) (c • x) y z
      = c • cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y z := by
  apply cyclicTripleSum_map_smul_fst_of_map_smul
  exact cyclicTripleSum_map_smul_of_bilin β φ


-- @@ L152-158 verbatim
lemma _root_.VirasoroProject.cyclicTripleSum_map_smul_snd_of_bilin
    (β : V →ₗ[𝕜] V →ₗ[𝕜] V) (φ : V →ₗ[𝕜] V →ₗ[𝕜] W)
    (c : 𝕜) (x y z : V) :
    cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x (c • y) z
      = c • cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y z := by
  apply cyclicTripleSum_map_smul_snd_of_map_smul
  exact cyclicTripleSum_map_smul_of_bilin β φ


-- @@ L160-160 verbatim
end cyclicTripleSumAdditive


-- @@ L162-164 verbatim
section cyclicTripleSumBilin

-- TODO: Does a more convenient coercion exist? Should this be made to a literal coercion?

-- @@ L165-179 verbatim
/-- "Coerce" a bilinear map into a biadditive map. -/
def _root_.LinearMap.toBiadditive
    {V₁ V₂ V₃ : Type*} [AddCommMonoid V₁] [AddCommMonoid V₂] [AddCommMonoid V₃]
    {R₁ R₂ R₃ : Type*} [CommSemiring R₁] [CommSemiring R₂] [CommSemiring R₃]
    {σ : R₁ →+* R₃} {τ : R₂ →+* R₃}
    [Module R₁ V₁] [Module R₂ V₂] [Module R₃ V₃]
    (f : V₁ →ₛₗ[σ] V₂ →ₛₗ[τ] V₃) :
    V₁ →+ V₂ →+ V₃ where
  toFun := fun x ↦ {
    toFun := fun y ↦ f x y
    map_zero' := by simp
    map_add' := by simp
  }
  map_zero' := by ext y; simp
  map_add' x₁ x₂ := by ext y; simp


-- @@ L181-181 verbatim
variable {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]

-- @@ L182-182 verbatim
variable {𝕜 : Type*} [CommSemiring 𝕜]

-- @@ L183-183 verbatim
variable [Module 𝕜 V] [Module 𝕜 W]


-- @@ L185-209 verbatim
/-- An auxiliary trilinear map for proofs of Jacobi identities.

Given bilinear functions β : V × V → V and φ : V × V → W, `cyclicTripleSumHom β φ` is the
trilinear function on V defined by: ⟨x,y,z⟩ ↦ φ(x,β(y,z)) + φ(y,β(z,x)) + φ(z,β(x,y)). -/
noncomputable def _root_.VirasoroProject.cyclicTripleSumHom
    (β : V →ₗ[𝕜] V →ₗ[𝕜] V) (φ : V →ₗ[𝕜] V →ₗ[𝕜] W) :
    V →ₗ[𝕜] V →ₗ[𝕜] V →ₗ[𝕜] W where
  toFun := fun x ↦
    { toFun := fun y ↦
        { toFun := fun z ↦ cyclicTripleSum (fun a ↦ ⇑(β a)) (fun a ↦ ⇑(φ a)) x y z
          map_add' z₁ z₂ :=
            cyclicTripleSum_map_add_of_bilin β.toBiadditive φ.toBiadditive x y z₁ z₂
          map_smul' c z := cyclicTripleSum_map_smul_of_bilin β φ c x y z }
      map_add' y₁ y₂ := by
        ext z
        exact cyclicTripleSum_map_add_snd_of_bilin β.toBiadditive φ.toBiadditive x y₁ y₂ z
      map_smul' c y := by
        ext z
        exact cyclicTripleSum_map_smul_snd_of_bilin β φ c x y z }
  map_add' x₁ x₂ := by
    ext y z
    exact cyclicTripleSum_map_add_fst_of_bilin β.toBiadditive φ.toBiadditive x₁ x₂ y z
  map_smul' c x := by
    ext y z
    exact cyclicTripleSum_map_smul_fst_of_bilin β φ c x y z


-- @@ L211-213 verbatim
lemma _root_.VirasoroProject.cyclicTripleSumHom_apply
    (β : V →ₗ[𝕜] V →ₗ[𝕜] V) (φ : V →ₗ[𝕜] V →ₗ[𝕜] W) (x y z : V) :
    cyclicTripleSumHom β φ x y z = φ x (β y z) + φ y (β z x) + φ z (β x y) := rfl


-- @@ L215-215 verbatim
end cyclicTripleSumBilin


-- @@ L217-217 verbatim
end VirasoroProject -- namespace
