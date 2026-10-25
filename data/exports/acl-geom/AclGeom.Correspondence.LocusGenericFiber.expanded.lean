/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Closure.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange


-- @@ L12-35 verbatim
/-!
# The generic fibre of a projection of tuple loci

For tuples `v` and `w` in a field `Ω` over `k`, the projection of the locus of `(v, w)` to the
locus of `v` corresponds to the inclusion `k[v] ⊆ k[v, w]` of generated rings; for the literal
coordinate rings this is `locusCoordinateRingEquiv_comp_quotientMapₐ`. Its generic fibre is the
spectrum of `k(v) ⊗[k[v]] k[v, w]`, which is the scheme pullback along the generic point
`Spec k(v) → Spec k[v]` by `AlgebraicGeometry.pullbackSpecIso`.

For finite `w`, `exists_pairGenericFiber_algEquiv` identifies this ring with the subalgebra
`k(v)[w]` of `Ω`, sending `a ⊗ b` to `a * b`. It also proves that the generic fibre is finite over
`k(v)`, as an algebra and as a morphism of schemes, exactly when every coordinate of `w` is
algebraic over `k(v)`. This is the generic-finiteness clause of blueprint (8.1). The first tuple,
base field and ambient field are arbitrary.

The identification uses flatness of the fraction field `k(v)` over `k[v]`
(`IsLocalization.flat`) and the base-change isomorphism `IsLocalization.algebraLid`, through one
private helper stated for abstract rings.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/


-- @@ L37-37 verbatim
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

-- @@ L38-38 verbatim
open AlgebraicGeometry


-- @@ L40-40 verbatim
namespace AclGeom


-- @@ L42-60 verbatim
/-- Tensoring an injective algebra map into a field with a fraction field of the base ring keeps
the multiplication map injective. -/
private theorem injective_productLeftAlgHom {A K B Ω : Type*} [CommRing A] [Field K] [CommRing B]
    [Field Ω] [Algebra A K] [IsFractionRing A K] [Algebra A B] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] (g : B →ₐ[A] Ω) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Ω) g) := by
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have h₁ := Module.Flat.lTensor_preserves_injective_linearMap (M := K) g.toLinearMap hg
  have h₂ := (IsLocalization.algebraLid (nonZeroDivisors A) K Ω).injective
  -- The multiplication map is the base change of `g` followed by the base-change isomorphism.
  have heq (t : K ⊗[A] B) : Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Ω) g t =
      IsLocalization.algebraLid (nonZeroDivisors A) K Ω (g.toLinearMap.lTensor K t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      change algebraMap K Ω a * g b = a • g b
      rw [Algebra.smul_def]
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  intro s t hst
  exact h₁ (h₂ ((heq s).symm.trans (hst.trans (heq t))))


-- @@ L62-62 verbatim
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {α β : Type*} (v : α → Ω) (w : β → Ω)


-- @@ L64-64 verbatim
local notation "𝔄" => Algebra.adjoin k (Set.range v)

-- @@ L65-65 verbatim
local notation "𝔅" => Algebra.adjoin k (Set.range (Sum.elim v w))

-- @@ L66-66 verbatim
local notation "𝔎" => IntermediateField.adjoin k (Set.range v)


-- @@ L68-121 verbatim
/-- **The generic fibre of a tuple projection.** For a finite tuple `w`, the generic fibre ring
`k(v) ⊗[k[v]] k[v, w]` is `k(v)`-isomorphic to the subalgebra `k(v)[w]` of `Ω`, sending `a ⊗ b`
to `a * b`. Its finite dimension over `k(v)` and finiteness of its spectrum projection are each
equivalent to coordinatewise algebraicity of `w` over `k(v)`. The tuple `v` is arbitrary. -/
theorem exists_pairGenericFiber_algEquiv [Finite β] :
    letI : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono (s := Set.range v)
      (t := Set.range (Sum.elim v w)) (Set.range_subset_iff.2 fun i ↦ ⟨Sum.inl i, rfl⟩))).toAlgebra
    ∃ e : 𝔎 ⊗[𝔄] 𝔅 ≃ₐ[𝔎] Algebra.adjoin 𝔎 (Set.range w),
      (∀ (a : 𝔎) (b : 𝔅), (e (a ⊗ₜ b) : Ω) = (a : Ω) * (b : Ω)) ∧
      (FiniteDimensional 𝔎 (𝔎 ⊗[𝔄] 𝔅) ↔ ∀ j, w j ∈ racl k (Set.range v)) ∧
      (IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝔎 (𝔎 ⊗[𝔄] 𝔅)))) ↔
        ∀ j, w j ∈ racl k (Set.range v)) := by
  -- Term-mode `letI` inlines its value; the same structure is declared locally here.
  let _ : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono (s := Set.range v)
    (t := Set.range (Sum.elim v w)) (Set.range_subset_iff.2 fun i ↦ ⟨Sum.inl i, rfl⟩))).toAlgebra
  let g : 𝔅 →ₐ[𝔄] Ω := { (Subalgebra.val 𝔅).toRingHom with commutes' := fun _ ↦ rfl }
  let φ := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId 𝔎 Ω) g
  have hB : 𝔅 ≤ (Algebra.adjoin 𝔎 (Set.range w)).restrictScalars k := by
    refine Algebra.adjoin_le (Set.range_subset_iff.2 fun i ↦ ?_)
    rcases i with a | j
    · exact Subalgebra.algebraMap_mem (Algebra.adjoin 𝔎 (Set.range w))
        (⟨v a, IntermediateField.subset_adjoin k _ ⟨a, rfl⟩⟩ : 𝔎)
    · exact (Algebra.subset_adjoin (R := 𝔎) (s := Set.range w) ⟨j, rfl⟩ :
        w j ∈ Algebra.adjoin 𝔎 (Set.range w))
  have hrange : φ.range = Algebra.adjoin 𝔎 (Set.range w) := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        change (a : Ω) * (b : Ω) ∈ Algebra.adjoin 𝔎 (Set.range w)
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (hB b.2)
      | add s t hs ht => rw [map_add]; exact add_mem hs ht
    · refine Algebra.adjoin_le (Set.range_subset_iff.2 fun j ↦
        ⟨1 ⊗ₜ ⟨w j, Algebra.subset_adjoin ⟨Sum.inr j, rfl⟩⟩, ?_⟩)
      change (1 : Ω) * w j = w j
      exact one_mul _
  let e := (AlgEquiv.ofInjective φ (injective_productLeftAlgHom g Subtype.val_injective)).trans
    (Subalgebra.equivOfEq _ _ hrange)
  have hfd : FiniteDimensional 𝔎 (Algebra.adjoin 𝔎 (Set.range w)) ↔
      ∀ j, w j ∈ racl k (Set.range v) := by
    constructor
    · intro _ j
      exact (mem_racl_iff k).2 ((isAlgebraic_algHom_iff (Algebra.adjoin 𝔎 (Set.range w)).val
        Subtype.val_injective).2 (IsAlgebraic.of_finite 𝔎
          (⟨w j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ : Algebra.adjoin 𝔎 (Set.range w))))
    · intro h
      exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range w)
        (Set.forall_mem_range.2 fun j ↦ ((mem_racl_iff k).1 (h j)).isIntegral)
  have hT : FiniteDimensional 𝔎 (𝔎 ⊗[𝔄] 𝔅) ↔
      FiniteDimensional 𝔎 (Algebra.adjoin 𝔎 (Set.range w)) :=
    ⟨fun _ ↦ e.toLinearEquiv.finiteDimensional, fun _ ↦ e.symm.toLinearEquiv.finiteDimensional⟩
  refine ⟨e, fun _ _ ↦ rfl, hT.trans hfd, ?_⟩
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  exact hT.trans hfd


-- @@ L123-123 verbatim
end AclGeom
