/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import LeanPool.LocalComplexGeometry.Noetherian.Ruckert
public import LeanPool.LocalComplexGeometry.Nullstellensatz.ZeroSetGerms
public import Mathlib.Analysis.InnerProductSpace.Basic
import LeanPool.LocalComplexGeometry.Nullstellensatz.PreparedPrime
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L15-21 verbatim
/-!
# Rückert's local analytic Nullstellensatz

The prepared-prime argument supplies the prime zero-set theorem in every
dimension.  This module exposes its unconditional ideal-theoretic and
representative-level consequences.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
open Filter

-- @@ L26-26 verbatim
open scoped BigOperators Topology



-- @@ L29-29 verbatim
namespace LocalComplexGeometry


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-39 verbatim
/-- The ideal of germs vanishing on the local zero set of an arbitrary ideal
is its radical. -/
theorem analyticNullstellensatz_ideal {n : ℕ}
    (I : Ideal (HolomorphicGerm n)) :
    vanishingIdeal (idealZeroSetGerm I) = I.radical :=
  vanishingIdeal_idealZeroSetGerm_eq_radical
    (primeZeroSetProperty_all n) I


-- @@ L41-46 verbatim
/-- A descriptive alias for the unconditional ideal form of the local
analytic Nullstellensatz. -/
theorem vanishingIdeal_idealZeroSetGerm_eq_radical_unconditional {n : ℕ}
    (I : Ideal (HolomorphicGerm n)) :
    vanishingIdeal (idealZeroSetGerm I) = I.radical :=
  analyticNullstellensatz_ideal I


-- @@ L48-65 verbatim
/-- Rückert's local analytic Nullstellensatz for a finite family of analytic
representatives.  A germ vanishing on their local common zero set has a
positive power in the ideal they generate. -/
theorem localAnalyticNullstellensatz_core
    {n s : ℕ}
    {f : Fin s → ComplexEuclidean n → ℂ}
    {g : ComplexEuclidean n → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hg : AnalyticAt ℂ g 0)
    (hzero : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean n),
      (∀ i, f i x = 0) → g x = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ h : Fin s → ComplexEuclidean n → ℂ,
        (∀ i, AnalyticAt ℂ (h i) 0) ∧
        (fun x ↦ g x ^ N) =ᶠ[𝓝 0]
          fun x ↦ ∑ i, h i x * f i x :=
  localAnalyticNullstellensatz_of_primeZeroSetProperty
    (primeZeroSetProperty_all n) hf hg hzero


-- @@ L67-77 verbatim
/-- Empty-family form: an analytic representative which is locally zero has
a positive power which is locally zero. -/
theorem localAnalyticNullstellensatz_empty
    {n : ℕ}
    {g : ComplexEuclidean n → ℂ}
    (hg : AnalyticAt ℂ g 0)
    (hzero : g =ᶠ[𝓝 (0 : ComplexEuclidean n)] (fun _ ↦ 0)) :
    ∃ N : ℕ, 0 < N ∧
      (fun x ↦ g x ^ N) =ᶠ[𝓝 0] (fun _ ↦ 0) :=
  localAnalyticNullstellensatz_empty_of_primeZeroSetProperty
    (primeZeroSetProperty_all n) hg hzero


-- @@ L79-79 verbatim
end


-- @@ L81-81 verbatim
end LocalComplexGeometry
