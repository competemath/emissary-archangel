/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.BaseChangeKerCoker


-- @@ L12-18 verbatim
/-!
# Finiteness in long homology sequences

Over a Noetherian ring, each exact pair in the long homology sequence of a short exact
sequence of complexes transfers finite generation from the two surrounding terms to the
middle term.
-/


-- @@ L20-20 verbatim
open CategoryTheory


-- @@ L22-22 verbatim
universe u v w


-- @@ L24-24 verbatim
namespace ModularCurves.CategoryTheory.ShortComplex.ShortExact


-- @@ L26-26 verbatim
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

-- @@ L27-27 verbatim
variable {ι : Type w} {c : ComplexShape ι}

-- @@ L28-28 verbatim
variable {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)}


-- @@ L30-38 verbatim
/-- In a short exact sequence of complexes, finite homology of the third complex in one
degree and of the second complex in the following degree imply finite homology of the first
complex in the following degree. -/
theorem finite_homology_X1 (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    [Module.Finite R (S.X₃.homology i)] [Module.Finite R (S.X₂.homology j)] :
    Module.Finite R (S.X₁.homology j) :=
  Module.Finite.of_exact_of_finite _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ i j hij))


-- @@ L40-49 verbatim
/-- At a degree with no predecessor, finite homology of the middle complex implies finite
homology of the first complex. -/
theorem finite_homology_X1_of_not_rel (hS : S.ShortExact) (j : ι)
    (hj : ∀ i, ¬ c.Rel i j) [Module.Finite R (S.X₂.homology j)] :
    Module.Finite R (S.X₁.homology j) := by
  letI := hS.mono_f
  letI : Mono (HomologicalComplex.homologyMap S.f j) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f j hj
  exact Module.Finite.of_injective (HomologicalComplex.homologyMap S.f j).hom
    ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap S.f j)).mp inferInstance)


-- @@ L51-58 verbatim
/-- In a short exact sequence of complexes, finite homology of the first and third
complexes in one degree implies finite homology of the second complex in that degree. -/
theorem finite_homology_X2 (hS : S.ShortExact) (i : ι)
    [Module.Finite R (S.X₁.homology i)] [Module.Finite R (S.X₃.homology i)] :
    Module.Finite R (S.X₂.homology i) :=
  Module.Finite.of_exact_of_finite _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ i))


-- @@ L60-68 verbatim
/-- In a short exact sequence of complexes, finite homology of the second complex in one
degree and of the first complex in the following degree imply finite homology of the third
complex in the first degree. -/
theorem finite_homology_X3 (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    [Module.Finite R (S.X₂.homology i)] [Module.Finite R (S.X₁.homology j)] :
    Module.Finite R (S.X₃.homology i) :=
  Module.Finite.of_exact_of_finite _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ i j hij))


-- @@ L70-82 verbatim
/-- In a short exact sequence of cochain complexes indexed by the natural numbers, finite
homology of the middle and third complexes in every degree implies finite homology of the
first complex in every degree. -/
theorem finite_homology_X1_up_nat
    {S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)} (hS : S.ShortExact)
    [∀ n, Module.Finite R (S.X₂.homology n)] [∀ n, Module.Finite R (S.X₃.homology n)]
    (n : ℕ) : Module.Finite R (S.X₁.homology n) := by
  cases n with
  | zero =>
      apply finite_homology_X1_of_not_rel hS 0
      simp [ComplexShape.up_Rel]
  | succ n =>
      exact finite_homology_X1 hS n (n + 1) (by simp [ComplexShape.up_Rel])


-- @@ L84-84 verbatim
end ModularCurves.CategoryTheory.ShortComplex.ShortExact
