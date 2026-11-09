/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.LowDegreeResidueLocalExact


-- @@ L8-14 verbatim
/-!
# A finite-projective kernel near an exact residue fibre

This file spreads surjectivity of the low-degree replacement from a residue
field to a principal neighborhood and records arbitrary base change for its
finite-projective kernel.
-/


-- @@ L16-16 verbatim
open CategoryTheory


-- @@ L18-18 verbatim
universe u v w


-- @@ L20-20 verbatim
namespace ModularCurves


-- @@ L22-22 verbatim
variable {R : Type u} [CommRing R]

-- @@ L23-24 verbatim
variable {P Q : Type v} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]


-- @@ L26-33 verbatim
/-- Finiteness of a kernel descends across a bijective kernel base-change comparison. -/
theorem Module.Finite.ker_baseChange_of_bijective
    (A : Type w) [CommRing A] [Algebra R A]
    (f : P →ₗ[R] Q) [Module.Finite R (LinearMap.ker f)]
    (h : Function.Bijective (kerBaseChangeComparison A f)) :
    Module.Finite A (LinearMap.ker (f.baseChange A)) := by
  let e := LinearEquiv.ofBijective (kerBaseChangeComparison A f) h
  exact Module.Finite.equiv e


-- @@ L35-42 verbatim
/-- Projectivity of a kernel descends across a bijective kernel base-change comparison. -/
theorem Module.Projective.ker_baseChange_of_bijective
    (A : Type w) [CommRing A] [Algebra R A]
    (f : P →ₗ[R] Q) [Module.Projective R (LinearMap.ker f)]
    (h : Function.Bijective (kerBaseChangeComparison A f)) :
    Module.Projective A (LinearMap.ker (f.baseChange A)) := by
  let e := LinearEquiv.ofBijective (kerBaseChangeComparison A f) h
  exact Module.Projective.of_equiv' e


-- @@ L44-44 verbatim
namespace LowDegreeFiniteReplacement


-- @@ L46-46 verbatim
variable {R : Type u} [CommRing R]


-- @@ L48-63 verbatim
/-- A linear map is surjective near `p`, with a finite-projective kernel that commutes
with every further algebra base change. -/
def HasAwayFiniteProjectiveKernelAt
    {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (p : Ideal R) : Prop :=
  ∃ r : R, r ∉ p ∧
    Function.Surjective (f.baseChange (Localization.Away r)) ∧
    Module.Finite (Localization.Away r)
      (LinearMap.ker (f.baseChange (Localization.Away r))) ∧
    Module.Projective (Localization.Away r)
      (LinearMap.ker (f.baseChange (Localization.Away r))) ∧
    ∀ (A : Type*) [CommRing A] [Algebra (Localization.Away r) A],
      Function.Bijective
        (kerBaseChangeComparison A
          (f.baseChange (Localization.Away r)))


-- @@ L65-65 verbatim
section Noetherian


-- @@ L67-67 verbatim
variable [IsNoetherianRing R]


-- @@ L69-73 verbatim
local instance residueLocalFiniteProjectiveHZeroFinite
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R (LinearMap.ker S.f.hom)] :
    Module.Finite R (HZero S.moduleCatToCycles) :=
  Module.Finite.ker_moduleCatToCycles S


-- @@ L75-78 verbatim
local instance residueLocalFiniteProjectiveHOneFinite
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.homology] :
    Module.Finite R (HOne S.moduleCatToCycles) :=
  Module.Finite.quotient_range_moduleCatToCycles S


-- @@ L80-102 verbatim
/-- If a short complex is exact over a residue field, its finite-projective replacement is
surjective on a principal neighborhood, with finite-projective kernel commuting with every
further base change. -/
theorem exists_away_finiteProjective_kernel_of_residueField_exact
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Flat R S.X₁]
    [Module.Flat R (LinearMap.ker S.g.hom)]
    [Module.Finite R (LinearMap.ker S.f.hom)]
    [Module.Finite R S.homology]
    (p : Ideal R) [p.IsPrime]
    (hbij : Function.Bijective
      (kerBaseChangeComparison p.ResidueField S.g.hom))
    (hexact : Function.Exact
      (S.f.hom.baseChange p.ResidueField)
      (S.g.hom.baseChange p.ResidueField)) :
    HasAwayFiniteProjectiveKernelAt
      (kZeroToKOne S.moduleCatToCycles) p := by
  letI : Module.Projective R (KZero S.moduleCatToCycles) :=
    kZero_projective S.moduleCatToCycles
  exact LinearMap.exists_away_finiteProjective_ker_of_residueField_surjective
    (kZeroToKOne S.moduleCatToCycles) p
    (shortComplexBaseChange_kZeroToKOne_surjective_of_exact
      S p.ResidueField hbij hexact)


-- @@ L104-104 verbatim
end Noetherian


-- @@ L106-136 verbatim
/-- The principal neighborhood in `HasAwayFiniteProjectiveKernelAt` remains
surjective with finite-projective kernel after every further algebra base change. -/
theorem HasAwayFiniteProjectiveKernelAt.exists_away_forall_baseChange
    {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (p : Ideal R)
    (h : HasAwayFiniteProjectiveKernelAt.{u, w} f p) :
    ∃ r : R, r ∉ p ∧
      ∀ (A : Type w) [CommRing A] [Algebra (Localization.Away r) A],
        Function.Surjective
            ((f.baseChange (Localization.Away r)).baseChange A) ∧
          Module.Finite A
            (LinearMap.ker
              ((f.baseChange (Localization.Away r)).baseChange A)) ∧
          Module.Projective A
            (LinearMap.ker
              ((f.baseChange (Localization.Away r)).baseChange A)) ∧
          Function.Bijective
            (kerBaseChangeComparison A
              (f.baseChange (Localization.Away r))) := by
  obtain ⟨r, hr, hsurj, hfinite, hprojective, hcomparison⟩ := h
  refine ⟨r, hr, ?_⟩
  intro A _ _
  letI : Module.Finite (Localization.Away r)
      (LinearMap.ker (f.baseChange (Localization.Away r))) := hfinite
  letI : Module.Projective (Localization.Away r)
      (LinearMap.ker (f.baseChange (Localization.Away r))) := hprojective
  exact ⟨LinearMap.baseChange_surjective A hsurj,
    Module.Finite.ker_baseChange_of_bijective A _ (hcomparison A),
    Module.Projective.ker_baseChange_of_bijective A _ (hcomparison A),
    hcomparison A⟩


-- @@ L138-138 verbatim
end LowDegreeFiniteReplacement

-- @@ L139-139 verbatim
end ModularCurves
