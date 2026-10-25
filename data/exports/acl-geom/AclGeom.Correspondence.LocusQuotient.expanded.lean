/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.Family
import Mathlib.RingTheory.TensorProduct.Maps


-- @@ L9-56 verbatim
/-!
# Literal relative coordinate rings of tuple loci

For tuples `x`, `y`, `z` in a field `Ω` over `k`, the literal coordinate rings of the loci of `y`,
`(x, y)` and `(y, z)` are the quotients `k[Y] ⧸ I(y)`, `k[X, Y] ⧸ I(x, y)` and `k[Y, Z] ⧸ I(y, z)`
of polynomial rings by vanishing ideals. Contracting a vanishing ideal along a renaming of
variables gives the vanishing ideal of the reindexed tuple (`idealOf_eq_comap_rename`), so the
inclusions of the variables `Y` induce the literal relative maps
`k[Y] ⧸ I(y) → k[X, Y] ⧸ I(x, y)` and `k[Y] ⧸ I(y) → k[Y, Z] ⧸ I(y, z)`.

The identifications `locusCoordinateRingEquiv` of these quotients with the generated subalgebras
of `Ω` carry the literal relative maps to the inclusions `k[y] ⊆ k[x, y]` and `k[y] ⊆ k[y, z]`
(`locusCoordinateRingEquiv_comp_quotientMapₐ`). Hence the literal relative tensor product
`k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z)` is `k`-isomorphic to
`k[x, y] ⊗[k[y]] k[y, z]`, factorwise on pure tensors and compatibly with the two base maps
(`exists_locusQuotientTensor_algEquiv`). The isomorphism is the heterobasic tensor map
`Algebra.TensorProduct.mapRingHom` of the three identifications. Only the tuples are data, and
the index types, the base field and the ambient field may lie in independent universes.

This is the literal-quotient step of the geometric fiber-product bridge of blueprint §8.1 (8.4c,
8.6) (#5). `LocusQuotientComponents` consumes this equivalence to identify the literal spectrum
components and actual projection-density criteria. `LocusIncidence` identifies the full
incidence quotient by the sum of the two extended pair ideals; `LocusQuotientComponents` also
proves its component and projection-density criteria. `LocusJointComponent` identifies the
actual joint evaluation kernel as a middle-dominating component when each coordinate of `z` is
algebraic over `k(y)`. It also proves `locusIncidence_dominatingComponents_eq_jointLoci`: for
finite outer tuples in an algebraically closed ambient field, with both `x` and `z` algebraic
over `k(y)`, these components are exactly the joint loci of realizations with the two original
pair ideals. The middle tuple and the base field remain arbitrary.

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


-- @@ L58-58 verbatim
open scoped TensorProduct

-- @@ L59-59 verbatim
open MvPolynomial


-- @@ L61-61 verbatim
namespace AclGeom


-- @@ L63-63 verbatim
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]


-- @@ L65-73 verbatim
/-- Contracting the vanishing ideal of a tuple along a renaming of variables gives the vanishing
ideal of the reindexed tuple. -/
theorem idealOf_eq_comap_rename {ι κ : Type*} {a : ι → Ω} {b : κ → Ω} {g : κ → ι}
    (h : a ∘ g = b) :
    idealOf k b =
      (idealOf k a).comap (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k) := by
  subst h
  ext p
  rw [Ideal.mem_comap, mem_idealOf_iff, mem_idealOf_iff, aeval_rename]


-- @@ L75-86 verbatim
/-- The coordinate-ring identification carries the map of literal coordinate rings induced by a
renaming of variables to the inclusion of the generated subalgebras. -/
theorem locusCoordinateRingEquiv_comp_quotientMapₐ {ι κ : Type*} {a : ι → Ω} {b : κ → Ω}
    {g : κ → ι} (h : a ∘ g = b) :
    (locusCoordinateRingEquiv (k := k) a).toAlgHom.comp
        (Ideal.quotientMapₐ (idealOf k a) (rename g) (idealOf_eq_comap_rename h).le) =
      (Subalgebra.inclusion (Algebra.adjoin_mono (s := Set.range b) (t := Set.range a)
          (Set.range_subset_iff.2 fun i ↦ ⟨g i, congrFun h i⟩))).comp
        (locusCoordinateRingEquiv (k := k) b).toAlgHom := by
  subst h
  refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun i ↦ Subtype.ext ?_)
  simp [Ideal.quotient_map_mkₐ]


-- @@ L88-127 verbatim
/-- Isomorphisms of the base rings and of both factors that are compatible with the structure
maps give an isomorphism of tensor products over the two base rings. It acts factorwise on pure
tensors, commutes with the base maps, and is linear over a ring acting on the left factors. -/
private theorem exists_tensorProduct_algEquiv {k R S T R' S' T' : Type*} [CommRing k]
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [CommRing R'] [CommRing S'] [CommRing T'] [Algebra R' S'] [Algebra R' T']
    [Algebra k S] [Algebra k S'] [SMulCommClass R k S] [SMulCommClass R' k S']
    (eR : R ≃+* R') (eS : S ≃ₐ[k] S') (eT : T ≃+* T')
    (hS : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (hT : ∀ r, eT (algebraMap R T r) = algebraMap R' T' (eR r)) :
    ∃ Φ : S ⊗[R] T ≃ₐ[k] S' ⊗[R'] T', (∀ s t, Φ (s ⊗ₜ t) = eS s ⊗ₜ eT t) ∧
      ∀ r, Φ (algebraMap R (S ⊗[R] T) r) = algebraMap R' (S' ⊗[R'] T') (eR r) := by
  have hS' (r : R') : eS.symm (algebraMap R' S' r) = algebraMap R S (eR.symm r) := by
    rw [AlgEquiv.symm_apply_eq, hS, eR.apply_symm_apply]
  have hT' (r : R') : eT.symm (algebraMap R' T' r) = algebraMap R T (eR.symm r) := by
    rw [eT.symm_apply_eq, hT, eR.apply_symm_apply]
  let f := Algebra.TensorProduct.mapRingHom (eR : R →+* R') (eS : S →+* S') (eT : T →+* T')
    (RingHom.ext hS) (RingHom.ext hT)
  let g := Algebra.TensorProduct.mapRingHom (eR.symm : R' →+* R) (eS.symm : S' →+* S)
    (eT.symm : T' →+* T) (RingHom.ext hS') (RingHom.ext hT')
  have hf (s : S) (t : T) : f (s ⊗ₜ t) = eS s ⊗ₜ eT t :=
    Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ s t
  have hg (s : S') (t : T') : g (s ⊗ₜ t) = eS.symm s ⊗ₜ eT.symm t :=
    Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ s t
  have hfg : f.comp g = RingHom.id _ := RingHom.ext fun w ↦ by
    induction w using TensorProduct.inductionOn with
    | tmul s t =>
      rw [RingHom.comp_apply, hg, hf, eS.apply_symm_apply, eT.apply_symm_apply, RingHom.id_apply]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hgf : g.comp f = RingHom.id _ := RingHom.ext fun w ↦ by
    induction w using TensorProduct.inductionOn with
    | tmul s t =>
      rw [RingHom.comp_apply, hf, hg, eS.symm_apply_apply, eT.symm_apply_apply, RingHom.id_apply]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom f g hfg hgf) fun c ↦ ?_, hf,
    fun r ↦ ?_⟩
  · change f (algebraMap k S c ⊗ₜ[R] (1 : T)) = algebraMap k S' c ⊗ₜ[R'] (1 : T')
    rw [hf, map_one, AlgEquiv.commutes]
  · change f (algebraMap R S r ⊗ₜ[R] (1 : T)) = algebraMap R' S' (eR r) ⊗ₜ[R'] (1 : T')
    rw [hf, map_one, hS]


-- @@ L129-129 verbatim
variable {α β γ : Type*} (x : α → Ω) (y : β → Ω) (z : γ → Ω)


-- @@ L131-131 verbatim
local notation "𝒜" => MvPolynomial β k ⧸ idealOf k y

-- @@ L132-132 verbatim
local notation "ℬ" => MvPolynomial (α ⊕ β) k ⧸ idealOf k (Sum.elim x y)

-- @@ L133-133 verbatim
local notation "𝒞" => MvPolynomial (β ⊕ γ) k ⧸ idealOf k (Sum.elim y z)

-- @@ L134-134 verbatim
local notation "𝔄" => Algebra.adjoin k (Set.range y)

-- @@ L135-135 verbatim
local notation "𝔅" => Algebra.adjoin k (Set.range (Sum.elim x y))

-- @@ L136-136 verbatim
local notation "ℭ" => Algebra.adjoin k (Set.range (Sum.elim y z))


-- @@ L138-179 verbatim
/-- **Literal relative tensor product of tuple loci.** The literal relative tensor product
`k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z)`, with base maps induced by the inclusions of
the variables `Y`, is `k`-isomorphic to `k[x, y] ⊗[k[y]] k[y, z]` by an isomorphism that applies
`locusCoordinateRingEquiv` to both factors of a pure tensor and to the base. -/
theorem exists_locusQuotientTensor_algEquiv :
    letI : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
      (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
        rfl).le).toAlgebra
    letI : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
      (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
        rfl).le).toAlgebra
    letI : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
      (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toAlgebra
    letI : Algebra 𝔄 ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
      (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toAlgebra
    haveI : IsScalarTower k 𝒜 ℬ := .of_algHom _
    haveI : IsScalarTower k 𝔄 𝔅 := .of_algHom _
    ∃ Φ : ℬ ⊗[𝒜] 𝒞 ≃ₐ[k] 𝔅 ⊗[𝔄] ℭ,
      (∀ (a : ℬ) (b : 𝒞), Φ (a ⊗ₜ b) =
        locusCoordinateRingEquiv (Sum.elim x y) a ⊗ₜ locusCoordinateRingEquiv (Sum.elim y z) b) ∧
      ∀ q : 𝒜, Φ (algebraMap 𝒜 (ℬ ⊗[𝒜] 𝒞) q) =
        algebraMap 𝔄 (𝔅 ⊗[𝔄] ℭ) (locusCoordinateRingEquiv y q) := by
  -- Term-mode `letI` inlines its values; the same structures are declared locally here.
  let _ : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
    (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
      rfl).le).toAlgebra
  let _ : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
    (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
      rfl).le).toAlgebra
  let _ : Algebra 𝔄 𝔅 := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range x y ▸ Set.subset_union_right))).toAlgebra
  let _ : Algebra 𝔄 ℭ := (Subalgebra.inclusion (Algebra.adjoin_mono
    (Set.Sum.elim_range y z ▸ Set.subset_union_left))).toAlgebra
  have : IsScalarTower k 𝒜 ℬ := .of_algHom _
  have : IsScalarTower k 𝔄 𝔅 := .of_algHom _
  exact exists_tensorProduct_algEquiv (locusCoordinateRingEquiv (k := k) y).toRingEquiv
    (locusCoordinateRingEquiv (k := k) (Sum.elim x y))
    (locusCoordinateRingEquiv (k := k) (Sum.elim y z)).toRingEquiv
    (AlgHom.congr_fun (locusCoordinateRingEquiv_comp_quotientMapₐ (k := k) (a := Sum.elim x y)
      (b := y) (g := Sum.inr) rfl))
    (AlgHom.congr_fun (locusCoordinateRingEquiv_comp_quotientMapₐ (k := k) (a := Sum.elim y z)
      (b := y) (g := Sum.inl) rfl))


-- @@ L181-181 verbatim
end AclGeom
