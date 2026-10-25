/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.ComponentGeometry
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra


-- @@ L10-49 verbatim
/-!
# Dominating components of the fiber product of canonical tuple loci

For tuples `x`, `y`, `z` in a field `Ω` over `k`, let `W`, `C`, `D` be the spectra of the canonical
coordinate rings `k[y] ⊆ k[x, y]`, `k[y] ⊆ k[y, z]` inside `Ω` (`locusCoordinateRingEquiv`), and
`C ×_W D` their actual scheme fiber product with its projection `π` to `W`.  The irreducible
components of `C ×_W D` with dense image under `π` are exactly the images, under Mathlib's
`pullbackSpecIso`, of the zero loci of the contracted minimal primes of `k(x, y) ⊗[k(y)] k(y, z)`
(`locusPullback_dominatingComponents`).  Only the tuples are data.

This is the middle-dominance clause of the geometric fiber-product bridge of blueprint §8.1
(#5). `LocusEndDominance` proves its endpoint-density criterion under the source's four tuple
closure hypotheses, for arbitrary subsets of the actual pullback. `LocusQuotient` matches the
literal relative quotient maps, and `LocusQuotientComponents` transports the components and
projection density to their spectrum and to the full incidence quotient identified by
`LocusIncidence`. `LocusJointComponent` identifies the actual joint evaluation kernel as a
middle-dominating component when each coordinate of `z` is algebraic over `k(y)`. It also proves
`locusIncidence_dominatingComponents_eq_jointLoci`: for finite outer tuples in an algebraically
closed ambient field, with both `x` and `z` algebraic over `k(y)`, these components are exactly
the joint loci of realizations with the two original pair ideals. The middle tuple and the base
field remain arbitrary.

`TupleComposition` proves relational associativity of finite-tuple germs, nonempty composition
for equal middle ideals, and the equality between composite carrier ideals and endpoint
contractions of middle-dominating incidence components, in an algebraically closed ambient
field. `TupleCompositionField` derives target rank one and proves finiteness of the actual
generated joint field over the endpoint field and over both end fields, under the relevant
finite-index and algebraicity hypotheses. These field results work over arbitrary base and
ambient fields.

`LocusComponentField` identifies each actual middle-dominating component's coordinate ring and
fraction field with the realized joint generated ring and compositum, including polynomial
representative formulas. The remaining source obligations are recorded in the book's hard-kernel
chapter and the current frontier of `PROJECT_GOAL.md`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/


-- @@ L51-51 verbatim
universe u


-- @@ L53-53 verbatim
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

-- @@ L54-54 verbatim
open AlgebraicGeometry CategoryTheory Limits


-- @@ L56-56 verbatim
namespace AclGeom


-- @@ L58-118 verbatim
/-- `dominatingComponents_tensorProduct_fractionRing` transported to the actual scheme pullback
`Spec B ×_{Spec A} Spec C`, with its actual projection to `Spec A`, along the homeomorphism of
`pullbackSpecIso`.  It is stated for arbitrary rings, so that the identification of points is
checked once, generically. -/
private theorem pullbackSpec_dominatingComponents
    {A B C K L M : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra A C] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra C M] [IsFractionRing C M]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra A M] [Algebra K M] [IsScalarTower A C M] [IsScalarTower A K M] :
    {Z : Set ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A C)))) |
      Z ∈ irreducibleComponents _ ∧
        closure ((pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).base '' Z) =
          Set.univ} =
      (fun Q : Ideal (L ⊗[K] M) ↦ Scheme.homeoOfIso (pullbackSpecIso A B C).symm ''
        (PrimeSpectrum.zeroLocus (Ideal.comap
          ((IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L M).symm.toRingHom.comp
            (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B L)
              (IsScalarTower.toAlgHom A C M)).toRingHom) Q : Set (B ⊗[A] C)) :
          Set (Spec (CommRingCat.of (B ⊗[A] C))))) '' minimalPrimes (L ⊗[K] M) := by
  have hG : (fun Q : Ideal (L ⊗[K] M) ↦ (PrimeSpectrum.zeroLocus (Ideal.comap
        ((IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L M).symm.toRingHom.comp
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B L)
            (IsScalarTower.toAlgHom A C M)).toRingHom) Q : Set (B ⊗[A] C)) :
          Set (Spec (CommRingCat.of (B ⊗[A] C))))) '' minimalPrimes (L ⊗[K] M) =
      {Z : Set (Spec (CommRingCat.of (B ⊗[A] C))) | Z ∈ irreducibleComponents _ ∧
        closure ((Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C)))).base '' Z) =
          Set.univ} :=
    dominatingComponents_tensorProduct_fractionRing
  set e := pullbackSpecIso A B C
  set h := Scheme.homeoOfIso e.symm
  -- The projection to `Spec A` is `Spec` of the structure map of the tensor product.
  have hπ : e.inv ≫ pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C))) := by
    rw [pullbackSpecIso_inv_fst'_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  have hπp : ∀ p, (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).base (h p) =
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C)))).base p := fun p ↦ by
    rw [← hπ, Scheme.Hom.comp_apply]
    rfl
  ext Z
  constructor
  · rintro ⟨hZ, hd⟩
    have hZ' : h ⁻¹' Z ∈ irreducibleComponents (Spec (CommRingCat.of (B ⊗[A] C))) :=
      preimage_mem_irreducibleComponents hZ h.isOpenEmbedding
        (let ⟨p, hp⟩ := hZ.1.nonempty; ⟨p, hp, h.surjective p⟩)
    have himg : (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C)))).base '' (h ⁻¹' Z) =
        (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).base '' Z := by
      conv_rhs => rw [← h.image_preimage Z, Set.image_image]
      exact Set.image_congr fun p _ ↦ (hπp p).symm
    obtain ⟨Q, hQ, hQZ⟩ := (Set.ext_iff.1 hG (h ⁻¹' Z)).2 ⟨hZ', himg ▸ hd⟩
    exact ⟨Q, hQ, (congrArg (h '' ·) hQZ).trans (h.image_preimage Z)⟩
  · rintro ⟨Q, hQ, rfl⟩
    have hmem := (Set.ext_iff.1 hG _).1 ⟨Q, hQ, rfl⟩
    refine ⟨(congrArg (· ∈ irreducibleComponents _) (h.image_eq_preimage_symm _)).mpr
      (preimage_mem_irreducibleComponents hmem.1 h.symm.isOpenEmbedding
        (let ⟨p, hp⟩ := hmem.1.1.nonempty; ⟨p, hp, h.symm.surjective p⟩)), ?_⟩
    exact (congrArg closure ((Set.image_image _ _ _).trans
      (Set.image_congr fun p _ ↦ hπp p))).trans hmem.2


-- @@ L120-121 verbatim
variable {k : Type*} {Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {α β γ : Type*}
  (x : α → Ω) (y : β → Ω) (z : γ → Ω)


-- @@ L123-123 verbatim
local notation "𝔄" => Algebra.adjoin k (Set.range y)

-- @@ L124-124 verbatim
local notation "𝔅" => Algebra.adjoin k (Set.range (Sum.elim x y))

-- @@ L125-125 verbatim
local notation "ℭ" => Algebra.adjoin k (Set.range (Sum.elim y z))

-- @@ L126-126 verbatim
local notation "𝔎" => IntermediateField.adjoin k (Set.range y)

-- @@ L127-127 verbatim
local notation "𝔏" => IntermediateField.adjoin k (Set.range (Sum.elim x y))

-- @@ L128-128 verbatim
local notation "𝔐" => IntermediateField.adjoin k (Set.range (Sum.elim y z))


-- @@ L130-176 verbatim
/-- **Dominating components of the fiber product of canonical tuple loci.**  The irreducible
components of `Spec k[x, y] ×_{Spec k[y]} Spec k[y, z]` whose image under the projection to
`Spec k[y]` is dense are exactly the images, under the homeomorphism given by
`pullbackSpecIso`, of the zero loci of the contractions of the minimal primes of
`k(x, y) ⊗[k(y)] k(y, z)`. -/
theorem locusPullback_dominatingComponents :
    letI : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
      (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toAlgebra
    letI : Algebra 𝔄 ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
      (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toAlgebra
    letI : Algebra 𝔎 𝔏 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
      (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toRingHom.toAlgebra
    letI : Algebra 𝔎 𝔐 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
      (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toRingHom.toAlgebra
    letI : Algebra 𝔄 𝔏 := ((algebraMap 𝔎 𝔏).comp (algebraMap 𝔄 𝔎)).toAlgebra
    letI : Algebra 𝔄 𝔐 := ((algebraMap 𝔎 𝔐).comp (algebraMap 𝔄 𝔎)).toAlgebra
    haveI : IsScalarTower 𝔄 𝔎 𝔏 := .of_algebraMap_eq' rfl
    haveI : IsScalarTower 𝔄 𝔎 𝔐 := .of_algebraMap_eq' rfl
    haveI : IsScalarTower 𝔄 𝔅 𝔏 := .of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower 𝔄 ℭ 𝔐 := .of_algebraMap_eq fun _ ↦ rfl
    {Z : Set ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap 𝔄 𝔅)))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝔄 ℭ)))) |
      Z ∈ irreducibleComponents _ ∧
        closure ((pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝔄 𝔅))).base '' Z) =
          Set.univ} =
      (fun Q : Ideal (𝔏 ⊗[𝔎] 𝔐) ↦ Scheme.homeoOfIso (pullbackSpecIso 𝔄 𝔅 ℭ).symm ''
        (PrimeSpectrum.zeroLocus (Ideal.comap
          ((IsLocalization.algebraTensorEquiv (nonZeroDivisors 𝔄) 𝔎 𝔏 𝔐).symm.toRingHom.comp
            (Algebra.TensorProduct.map (IsScalarTower.toAlgHom 𝔄 𝔅 𝔏)
              (IsScalarTower.toAlgHom 𝔄 ℭ 𝔐)).toRingHom) Q : Set (𝔅 ⊗[𝔄] ℭ)) :
          Set (Spec (CommRingCat.of (𝔅 ⊗[𝔄] ℭ))))) '' minimalPrimes (𝔏 ⊗[𝔎] 𝔐) := by
  -- Term-mode `letI` inlines its values; the same structures are declared locally here.
  let _ : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toAlgebra
  let _ : Algebra 𝔄 ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toAlgebra
  let _ : Algebra 𝔎 𝔏 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
    (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toRingHom.toAlgebra
  let _ : Algebra 𝔎 𝔐 := (IntermediateField.inclusion (IntermediateField.adjoin.mono k _ _
    (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toRingHom.toAlgebra
  let _ : Algebra 𝔄 𝔏 := ((algebraMap 𝔎 𝔏).comp (algebraMap 𝔄 𝔎)).toAlgebra
  let _ : Algebra 𝔄 𝔐 := ((algebraMap 𝔎 𝔐).comp (algebraMap 𝔄 𝔎)).toAlgebra
  have : IsScalarTower 𝔄 𝔎 𝔏 := .of_algebraMap_eq' rfl
  have : IsScalarTower 𝔄 𝔎 𝔐 := .of_algebraMap_eq' rfl
  have : IsScalarTower 𝔄 𝔅 𝔏 := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower 𝔄 ℭ 𝔐 := .of_algebraMap_eq fun _ ↦ rfl
  exact pullbackSpec_dominatingComponents


-- @@ L178-178 verbatim
end AclGeom
