/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.Smooth


-- @@ L10-22 verbatim
/-!
# Polynomial algebras are standard smooth of their rank

The free presentation of `MvPolynomial ι R` (generators `ι`, no relations) is a
submersive presentation of dimension `Nat.card ι`; hence `MvPolynomial ι R` is
standard smooth of relative dimension `Nat.card ι` over `R`, and `Polynomial R`
is standard smooth of relative dimension `1`.

These are the missing base instances for the λ-line chart computation of the
`Y(ρ̄)` smoothness leaf (T-YR-6 (b1)); `IsStandardSmoothOfRelativeDimension`'s
`.trans` and `.localization_away` then give relative dimension 1 for localized
polynomial algebras.
-/


-- @@ L24-24 verbatim
namespace Algebra


-- @@ L26-26 verbatim
open MvPolynomial


-- @@ L28-28 verbatim
variable (R : Type*) [CommRing R] (ι : Type) [Finite ι]


-- @@ L30-43 verbatim
/-- The free submersive presentation of the polynomial algebra: `ι` generators,
no relations, trivially invertible (empty) Jacobian. -/
noncomputable def SubmersivePresentation.mvPolynomialFree :
    SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  toGenerators := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Generators.ker_mvPolynomial]
  map := PEmpty.elim
  map_inj := fun a => a.elim
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian,
      LinearMap.det_eq_one_of_subsingleton, map_one]
    exact isUnit_one


-- @@ L45-48 verbatim
@[simp]
lemma SubmersivePresentation.mvPolynomialFree_dimension :
    (SubmersivePresentation.mvPolynomialFree R ι).dimension = Nat.card ι := by
  simp [Presentation.dimension]


-- @@ L50-55 verbatim
/-- The polynomial algebra on a finite type is standard smooth of relative
dimension its cardinality. -/
theorem IsStandardSmoothOfRelativeDimension.mvPolynomial :
    IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (SubmersivePresentation.mvPolynomialFree R ι).isStandardSmoothOfRelativeDimension
    (SubmersivePresentation.mvPolynomialFree_dimension R ι)


-- @@ L57-67 verbatim
/-- The univariate polynomial algebra is standard smooth of relative
dimension one. -/
theorem IsStandardSmoothOfRelativeDimension.polynomial :
    IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  haveI h : IsStandardSmoothOfRelativeDimension 1 R
      (MvPolynomial PUnit.{1} R) := by
    have h0 := IsStandardSmoothOfRelativeDimension.mvPolynomial R PUnit.{1}
    rwa [Nat.card_unique] at h0
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (e := (MvPolynomial.pUnitAlgEquiv R :
      MvPolynomial PUnit.{1} R ≃ₐ[R] Polynomial R))


-- @@ L69-84 verbatim
/-- A localization of the one-variable polynomial algebra away from an element
is standard smooth of relative dimension one over the base (the λ-line chart
shape: `R[λ][1/p(λ)]`). -/
theorem IsStandardSmoothOfRelativeDimension.localizationAway_mvPolynomialFinOne
    (p : MvPolynomial (Fin 1) R) :
    IsStandardSmoothOfRelativeDimension 1 R (Localization.Away p) := by
  haveI h1 : IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial (Fin 1) R) := by
    have h0 := IsStandardSmoothOfRelativeDimension.mvPolynomial R (Fin 1)
    simpa using h0
  haveI h2 : IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 1) R)
      (Localization.Away p) :=
    IsStandardSmoothOfRelativeDimension.localization_away p
  have h3 := IsStandardSmoothOfRelativeDimension.trans
    (n := 1) (m := 0) (R := R) (S := MvPolynomial (Fin 1) R)
    (T := Localization.Away p)
  simpa using h3


-- @@ L86-86 verbatim
end Algebra


-- @@ L88-88 verbatim
namespace AlgebraicGeometry


-- @@ L90-90 verbatim
open Algebra


-- @@ L92-92 verbatim
universe u


-- @@ L94-106 verbatim
/-- **[T-YR-6 (b2a)]** The `Spec` of a standard-smooth algebra map is smooth of
the same relative dimension. -/
theorem smoothOfRelativeDimension_spec_map_algebraMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  exact RingHom.locally_of
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
    (algebraMap R S)
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr
      ‹Algebra.IsStandardSmoothOfRelativeDimension n R S›)


-- @@ L108-108 verbatim
end AlgebraicGeometry
