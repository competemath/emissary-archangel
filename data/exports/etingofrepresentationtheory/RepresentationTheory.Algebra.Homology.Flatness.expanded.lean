/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ModulePairing.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Complex.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L15-15 verbatim
open CategoryTheory


-- @@ L17-17 verbatim
namespace RepresentationTheory.Algebra.Homology.Flatness


-- @@ L19-19 verbatim
open scoped Polynomial


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
section IsFlat


-- @@ L25-25 verbatim
variable (A : Type u) [Ring A] (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M]


-- @@ L27-30 verbatim
/-- A proposition on an additive commutative group equipped with a module structure over the opposite of a ring. -/
def Module.OppositeRingModuleProperty : Prop :=
  ∀ S : ShortComplex (ModuleCat.{u} A), S.ShortExact →
    (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ M))).ShortExact


-- @@ L32-32 verbatim
variable {A M}


-- @@ L34-39 verbatim
/-- The displayed functor sends a short exact complex to a short exact complex. -/
theorem Module.OppositeRingModuleProperty.map_shortExact
    (h : Module.OppositeRingModuleProperty A M) {S : ShortComplex (ModuleCat.{u} A)}
    (hS : S.ShortExact) :
    (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ M))).ShortExact :=
  h S hS


-- @@ L41-47 verbatim
/-- The displayed functor sends an exact short complex to an exact short complex. -/
theorem Module.OppositeRingModuleProperty.map_exact
    (h : Module.OppositeRingModuleProperty A M) {S : ShortComplex (ModuleCat.{u} A)}
    (hS : S.Exact) :
    (S.map (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ M))).Exact := by
  have h' := ((Functor.exact_tfae (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ M))).out 0 1).mp h
  exact h' S hS


-- @@ L49-53 verbatim
/-- The displayed functor preserves homology. -/
theorem Module.OppositeRingModuleProperty.preservesHomology
    (h : Module.OppositeRingModuleProperty A M) :
    (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ M)).PreservesHomology :=
  ((Functor.exact_tfae (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A (ModuleCat.of Aᵐᵒᵖ M))).out 0 2).mp h


-- @@ L55-55 verbatim
end IsFlat


-- @@ L57-64 verbatim
/-- A projective module over an opposite ring satisfies the opposite-ring module property. -/
@[source_ref "Chapter8/Problem8.1.3" (role := primary)]
theorem Module.Projective.oppositeRingModuleProperty
    (A : Type u) [Ring A] (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [Module.Projective Aᵐᵒᵖ M] : Module.OppositeRingModuleProperty A M :=
  fun _ hS =>
    RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact
      A (ModuleCat.of Aᵐᵒᵖ M) hS


-- @@ L66-69 verbatim
/-- A projective module over a commutative ring is flat. -/
theorem Module.Projective.flat (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Projective A M] : Module.Flat A M :=
  Module.Flat.of_projective


-- @@ L71-75 verbatim
/-- Localization of a commutative ring at a submonoid is flat as a module. -/
@[source_ref "Chapter8/Problem8.1.3" (role := primary)]
theorem Localization.flat (A : Type*) [CommRing A] (S : Submonoid A) :
    Module.Flat A (Localization S) :=
  IsLocalization.flat (Localization S) S


-- @@ L77-109 verbatim
/-- Every linear map from the displayed localization to the polynomial ring over the complex numbers is zero. -/
theorem linearMap_localizationAwayX_to_polynomial_eq_zero
    (f : Localization.Away (Polynomial.X : ℂ[X]) →ₗ[ℂ[X]] ℂ[X]) : f = 0 := by
  set L := Localization.Away (Polynomial.X : ℂ[X]) with hL
  have hf1 : f 1 = 0 := by
    have hdvd : ∀ n : ℕ, (Polynomial.X : ℂ[X]) ^ n ∣ f 1 := by
      intro n
      have hu : IsUnit (algebraMap ℂ[X] L ((Polynomial.X : ℂ[X]) ^ n)) :=
        IsLocalization.map_units L
          (⟨(Polynomial.X : ℂ[X]) ^ n, n, rfl⟩ : Submonoid.powers (Polynomial.X : ℂ[X]))
      obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
      refine ⟨f y, ?_⟩
      have h1 : (1 : L) = (Polynomial.X : ℂ[X]) ^ n • y := by
        rw [Algebra.smul_def, hy]
      calc f 1 = f ((Polynomial.X : ℂ[X]) ^ n • y) := by rw [← h1]
        _ = (Polynomial.X : ℂ[X]) ^ n • f y := by rw [map_smul]
        _ = (Polynomial.X : ℂ[X]) ^ n * f y := by rw [smul_eq_mul]
    by_contra h
    have hle := Polynomial.natDegree_le_of_dvd (hdvd ((f 1).natDegree + 1)) h
    rw [Polynomial.natDegree_X_pow] at hle
    omega
  refine LinearMap.ext fun m => ?_
  obtain ⟨⟨a, s⟩, hms⟩ := IsLocalization.surj (Submonoid.powers (Polynomial.X : ℂ[X])) m
  obtain ⟨k, hk⟩ := s.2
  have hs0 : (s : ℂ[X]) ≠ 0 := by
    rw [← hk]; exact pow_ne_zero k Polynomial.X_ne_zero
  have key : (s : ℂ[X]) * f m = 0 := by
    have : (s : ℂ[X]) • f m = a • f 1 := by
      rw [← map_smul, ← map_smul, Algebra.smul_def, Algebra.smul_def, mul_one,
        mul_comm (algebraMap ℂ[X] L s) m, hms]
    rw [smul_eq_mul, smul_eq_mul] at this
    rw [this, hf1, mul_zero]
  simpa [hs0] using mul_eq_zero.mp key


-- @@ L111-134 verbatim
/-- Localization away from the polynomial variable over the complex numbers is flat but not projective. -/
@[source_ref "Chapter8/Problem8.1.3" (role := primary)]
theorem localizationAwayX_flat_not_projective :
    Module.Flat ℂ[X] (Localization.Away (Polynomial.X : ℂ[X])) ∧
      ¬ Module.Projective ℂ[X] (Localization.Away (Polynomial.X : ℂ[X])) := by
  refine ⟨Localization.flat ℂ[X] (Submonoid.powers (Polynomial.X : ℂ[X])), ?_⟩
  set L := Localization.Away (Polynomial.X : ℂ[X]) with hL
  intro hproj
  rw [Module.projective_def] at hproj
  obtain ⟨s, hs⟩ := hproj
  have hs1 : s (1 : L) = 0 := by
    refine Finsupp.ext fun q => ?_
    have hzero : (Finsupp.lapply q ∘ₗ s : L →ₗ[ℂ[X]] ℂ[X]) = 0 :=
      linearMap_localizationAwayX_to_polynomial_eq_zero (Finsupp.lapply q ∘ₗ s)
    have := LinearMap.congr_fun hzero (1 : L)
    simpa [Finsupp.lapply_apply] using this
  have h1 : (1 : L) = 0 := by
    have := hs (1 : L)
    rw [hs1, map_zero] at this
    exact this.symm
  have hle : Submonoid.powers (Polynomial.X : ℂ[X]) ≤ nonZeroDivisors ℂ[X] :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero)
  have hinj := IsLocalization.injective L hle
  exact one_ne_zero (hinj (by rw [map_one, map_zero]; exact h1))


-- @@ L136-136 verbatim
end RepresentationTheory.Algebra.Homology.Flatness
