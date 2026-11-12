/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute


-- @@ L10-16 verbatim
/-!
# Corepresentability of the module forgetful functor

This module corepresents the forgetful functor on modules by the free rank-one module and
constructs the corresponding natural isomorphism. It also records a dual-eigenspace obstruction
to a uniform finite-dimensional analogue over an infinite field.
-/


-- @@ L18-18 verbatim
open _root_.Module


-- @@ L20-20 verbatim
universe u


-- @@ L22-22 verbatim
namespace RepresentationTheory.Module.Corepresentability


-- @@ L24-28 verbatim
/-- Linear maps from a semiring to a module are linearly equivalent to elements of that module. -/
noncomputable def linearMapFromRingEquiv
    (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [_root_.Module R M] :
    (R →ₗ[R] M) ≃ₗ[ℕ] M :=
  LinearMap.ringLmapEquivSelf R ℕ M


-- @@ L30-30 verbatim
open CategoryTheory Opposite


-- @@ L32-32 verbatim
section Corepresentable


-- @@ L34-34 verbatim
variable (R : Type u) [Ring R]


-- @@ L36-38 verbatim
/-- Equivalence between maps from the free rank-one module and elements of the target module. -/
def freeModuleHomEquiv (M : ModuleCat.{u} R) : (ModuleCat.of R R ⟶ M) ≃ M :=
  ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ M).toEquiv


-- @@ L40-43 verbatim
/-- The equivalence from free-module homomorphisms to module elements is evaluation at one. -/
@[simp]
theorem freeModuleHomEquiv_apply (M : ModuleCat.{u} R) (f : ModuleCat.of R R ⟶ M) :
    freeModuleHomEquiv R M f = ModuleCat.Hom.hom f 1 := rfl


-- @@ L45-49 verbatim
/-- The inverse equivalence sends an element to the homomorphism determined by that element. -/
@[simp]
theorem freeModuleHomEquiv_symm_apply (M : ModuleCat.{u} R) (m : M) :
    (freeModuleHomEquiv R M).symm m =
      ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ M).symm m) := rfl


-- @@ L51-56 verbatim
/-- A chosen corepresentation of the module forgetful functor by the free rank-one module. -/
@[source_ref "Chapter7/Example7.5.3" (role := primary)]
def forgetCorepresentableByFreeModule :
    (forget (ModuleCat.{u} R)).CorepresentableBy (ModuleCat.of R R) where
  homEquiv {M} := freeModuleHomEquiv R M
  homEquiv_comp _ _ := rfl


-- @@ L58-62 verbatim
/-- The hom equivalence of the chosen corepresentation is evaluation of a map from the free module
at one. -/
@[simp]
theorem forgetCorepresentableByFreeModule_homEquiv (M : ModuleCat.{u} R) :
    (forgetCorepresentableByFreeModule R).homEquiv (Y := M) = freeModuleHomEquiv R M := rfl


-- @@ L64-66 verbatim
/-- The forgetful functor from modules is corepresentable. -/
instance forget_isCorepresentable : (forget (ModuleCat.{u} R)).IsCorepresentable :=
  (forgetCorepresentableByFreeModule R).isCorepresentable


-- @@ L68-73 verbatim
/-- The coyoneda functor of the free rank-one module is naturally isomorphic to the forgetful
functor. -/
@[source_ref "Chapter7/Example7.5.3" (role := primary)]
def freeModuleCoyonedaIsoForget :
    coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat.{u} R) :=
  Functor.corepresentableByEquiv (forgetCorepresentableByFreeModule R)


-- @@ L75-79 verbatim
/-- The natural transformation from the coyoneda functor of the free rank-one module to the
forgetful functor. -/
def freeModuleCoyonedaToForget :
    coyoneda.obj (op (ModuleCat.of R R)) ⟶ forget (ModuleCat.{u} R) :=
  (freeModuleCoyonedaIsoForget R).hom


-- @@ L81-85 verbatim
/-- The natural transformation from the forgetful functor to the coyoneda functor of the free
rank-one module. -/
def forgetToFreeModuleCoyoneda :
    forget (ModuleCat.{u} R) ⟶ coyoneda.obj (op (ModuleCat.of R R)) :=
  (freeModuleCoyonedaIsoForget R).inv


-- @@ L87-90 verbatim
/-- The forward map of the natural isomorphism is the evaluation comparison transformation. -/
@[simp]
theorem freeModuleCoyonedaIsoForget_hom :
    (freeModuleCoyonedaIsoForget R).hom = freeModuleCoyonedaToForget R := rfl


-- @@ L92-95 verbatim
/-- The inverse map of the natural isomorphism constructs a homomorphism from a module element. -/
@[simp]
theorem freeModuleCoyonedaIsoForget_inv :
    (freeModuleCoyonedaIsoForget R).inv = forgetToFreeModuleCoyoneda R := rfl


-- @@ L97-101 verbatim
/-- The component of the comparison transformation sends a homomorphism to its value at one. -/
@[simp]
theorem freeModuleCoyonedaToForget_app (M : ModuleCat.{u} R)
    (f : ModuleCat.of R R ⟶ M) :
    (freeModuleCoyonedaToForget R).app M f = ModuleCat.Hom.hom f 1 := rfl


-- @@ L103-108 verbatim
/-- The reverse comparison transformation sends an element to its associated homomorphism from the
free module. -/
@[simp]
theorem forgetToFreeModuleCoyoneda_app (M : ModuleCat.{u} R) (m : M) :
    (forgetToFreeModuleCoyoneda R).app M m =
      ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ M).symm m) := rfl


-- @@ L110-114 verbatim
/-- Constructing a homomorphism from its value at one returns the original homomorphism. -/
theorem forgetToFreeModuleCoyoneda_app_freeModuleCoyonedaToForget
    (M : ModuleCat.{u} R) (f : ModuleCat.of R R ⟶ M) :
    (forgetToFreeModuleCoyoneda R).app M ((freeModuleCoyonedaToForget R).app M f) = f :=
  (freeModuleHomEquiv R M).symm_apply_apply f


-- @@ L116-120 verbatim
/-- Evaluating the homomorphism constructed from a module element recovers that element. -/
theorem freeModuleCoyonedaToForget_app_forgetToFreeModuleCoyoneda
    (M : ModuleCat.{u} R) (m : M) :
    (freeModuleCoyonedaToForget R).app M ((forgetToFreeModuleCoyoneda R).app M m) = m :=
  (freeModuleHomEquiv R M).apply_symm_apply m


-- @@ L122-125 verbatim
/-- The two comparison transformations compose to the identity on the coyoneda functor. -/
theorem freeModuleCoyonedaToForget_comp_forgetToFreeModuleCoyoneda :
    freeModuleCoyonedaToForget R ≫ forgetToFreeModuleCoyoneda R = 𝟙 _ :=
  (freeModuleCoyonedaIsoForget R).hom_inv_id


-- @@ L127-130 verbatim
/-- The two comparison transformations compose to the identity on the forgetful functor. -/
theorem forgetToFreeModuleCoyoneda_comp_freeModuleCoyonedaToForget :
    forgetToFreeModuleCoyoneda R ≫ freeModuleCoyonedaToForget R = 𝟙 _ :=
  (freeModuleCoyonedaIsoForget R).inv_hom_id


-- @@ L132-135 verbatim
/-- Evaluation at one commutes with postcomposition of module homomorphisms. -/
theorem hom_apply_one_comp {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (f : ModuleCat.of R R ⟶ M) :
    ModuleCat.Hom.hom (f ≫ g) 1 = g (ModuleCat.Hom.hom f 1) := rfl


-- @@ L137-144 verbatim
/-- The homomorphism associated to an image element is obtained by postcomposing the associated
homomorphism. -/
theorem freeModuleHomOf_apply_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) (m : M) :
    ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ N).symm (g m)) =
      ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ M).symm m) ≫ g := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun r => ?_
  simp


-- @@ L146-150 verbatim
/-- The corepresenting hom equivalence agrees with the standard hom and linear-map equivalences. -/
theorem forgetCorepresentableByFreeModule_homEquiv_eq (M : ModuleCat.{u} R) :
    (forgetCorepresentableByFreeModule R).homEquiv (Y := M) =
      ModuleCat.homEquiv.trans (linearMapFromRingEquiv R M).toEquiv :=
  rfl


-- @@ L152-156 verbatim
/-- Any object corepresenting the module forgetful functor is isomorphic to the free rank-one
module. -/
def corepresentingObjectIsoFreeModule {X : ModuleCat.{u} R}
    (e : (forget (ModuleCat.{u} R)).CorepresentableBy X) : ModuleCat.of R R ≅ X :=
  (forgetCorepresentableByFreeModule R).uniqueUpToIso e


-- @@ L158-158 verbatim
end Corepresentable


-- @@ L160-160 verbatim
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [_root_.Module k V]


-- @@ L162-165 verbatim
/-- The submodule of linear functionals that are eigenvectors for precomposition by an
endomorphism. -/
def dualEigenspace (S : _root_.Module.End k V) (μ : k) : Submodule k (V →ₗ[k] k) :=
  LinearMap.ker (LinearMap.lcomp k k S - μ • LinearMap.id)


-- @@ L167-172 verbatim
/-- A linear functional lies in the dual eigenspace exactly when precomposition scales it by the
chosen scalar. -/
theorem mem_dualEigenspace_iff (S : _root_.Module.End k V) (μ : k) (φ : V →ₗ[k] k) :
    φ ∈ dualEigenspace S μ ↔ φ ∘ₗ S = μ • φ := by
  simp only [dualEigenspace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.lcomp_apply', sub_eq_zero]


-- @@ L174-199 verbatim
/-- The dual eigenspace is trivial when the corresponding scalar is not an eigenvalue. -/
theorem dualEigenspace_eq_bot_of_not_hasEigenvalue [FiniteDimensional k V]
    (S : _root_.Module.End k V) (μ : k) (hμ : ¬ S.HasEigenvalue μ) :
    dualEigenspace S μ = ⊥ := by
  have hker : LinearMap.ker (S - μ • (1 : _root_.Module.End k V)) = ⊥ := by
    have h : S.eigenspace μ = ⊥ := not_ne_iff.mp hμ
    rwa [_root_.Module.End.eigenspace_def] at h
  have hsurj : Function.Surjective (S - μ • (1 : _root_.Module.End k V)) :=
    LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)
  have hlcomp : Function.Injective
      (LinearMap.lcomp k k (S - μ • (1 : _root_.Module.End k V))) :=
    LinearMap.lcomp_injective_of_surjective _ hsurj
  rw [Submodule.eq_bot_iff]
  intro φ hφ
  rw [mem_dualEigenspace_iff] at hφ
  have hcomp : φ ∘ₗ (S - μ • (1 : _root_.Module.End k V)) = 0 := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      _root_.Module.End.one_apply, map_sub, map_smul, LinearMap.zero_apply]
    have hv := LinearMap.congr_fun hφ v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hv
    rw [hv]; ring
  have h0 : LinearMap.lcomp k k (S - μ • (1 : _root_.Module.End k V)) φ
      = LinearMap.lcomp k k (S - μ • (1 : _root_.Module.End k V)) 0 := by
    rw [map_zero, LinearMap.lcomp_apply', hcomp]
  exact hlcomp h0


-- @@ L201-208 verbatim
/-- Over an infinite field, a finite-dimensional endomorphism has a scalar whose dual eigenspace is
trivial. -/
theorem exists_dualEigenspace_eq_bot [Infinite k] [FiniteDimensional k V]
    (S : _root_.Module.End k V) : ∃ μ : k, dualEigenspace S μ = ⊥ := by
  have hfin : Set.Finite S.HasEigenvalue := S.finite_hasEigenvalue
  obtain ⟨μ, hμ⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff] at hμ
  exact ⟨μ, dualEigenspace_eq_bot_of_not_hasEigenvalue S μ hμ⟩


-- @@ L210-221 verbatim
/-- A finite-dimensional endomorphism over an infinite field cannot have every dual eigenspace of
dimension one. -/
@[source_ref "Chapter7/Example7.5.3" (role := supporting)]
theorem not_forall_finrank_dualEigenspace_eq_one [Infinite k] [FiniteDimensional k V]
    (S : _root_.Module.End k V) :
    ¬ (∀ μ : k, finrank k (dualEigenspace S μ) = 1) := by
  intro h
  obtain ⟨μ, hμ⟩ := exists_dualEigenspace_eq_bot S
  have : finrank k (dualEigenspace S μ) = 0 := by
    rw [hμ]; exact finrank_bot k (V →ₗ[k] k)
  rw [h μ] at this
  exact one_ne_zero this


-- @@ L223-223 verbatim
end RepresentationTheory.Module.Corepresentability
