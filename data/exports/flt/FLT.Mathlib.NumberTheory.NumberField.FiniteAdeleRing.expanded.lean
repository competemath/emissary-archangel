/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

-- if I can get all imports as FLT.Mathlib then I can upstream
module

public import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import FLT.Mathlib.LinearAlgebra.Countable
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLT.NumberField.Completion.Finite
import FLT.NumberField.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace


-- @@ L19-23 verbatim
/-!
# Finite Adele Ring

Material destined for Mathlib.
-/


-- @@ L25-31 verbatim
@[expose] public section

/-

# The finite adele ring of a number field is locally compact.

-/

-- @@ L32-32 verbatim
open scoped TensorProduct


-- @@ L34-34 verbatim
universe u


-- @@ L36-38 verbatim
open NumberField IsDedekindDomain RestrictedProduct

-- 𝔸 notation

-- @@ L39-39 verbatim
open scoped NumberField.AdeleRing


-- @@ L41-41 verbatim
section Instances


-- @@ L43-43 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L45-45 verbatim
open HeightOneSpectrum


-- @@ L47-47 verbatim
namespace IsDedekindDomain.FiniteAdeleRing


-- @@ L49-54 verbatim
open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
instance : LocallyCompactSpace 𝔸ᶠ[K] :=
  haveI : Fact (∀ (i : HeightOneSpectrum (𝓞 K)),
      IsOpen (adicCompletionIntegers K i : Set (adicCompletion K i))) :=
    ⟨isOpenAdicCompletionIntegers K⟩
  inferInstanceAs <| LocallyCompactSpace (Πʳ _, [_, _])


-- @@ L56-58 verbatim
instance : CompactSpace (integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.1 <|
  isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous


-- @@ L60-61 verbatim
lemma isCompact_integralAdeles : IsCompact (X := 𝔸ᶠ[K]) (integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (integralAdeles (𝓞 K) K)))


-- @@ L63-64 verbatim
instance : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (Πʳ _, [_, _])


-- @@ L66-67 verbatim
instance : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.secondCountableTopology (isOpenAdicCompletionIntegers K)


-- @@ L69-72 verbatim
lemma HeightOneSpectrum.nonempty {R : Type*} [CommRing R] (hR : ¬ IsField R) [Nontrivial R] :
    Nonempty (HeightOneSpectrum R) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  exact ⟨⟨I, inferInstance, by rintro rfl; exact hR (Ring.isField_iff_maximal_bot.mpr hI)⟩⟩


-- @@ L74-79 verbatim
instance {R : Type*} [CommRing R] [Algebra.IsIntegral ℤ R] [FaithfulSMul ℤ R] :
    Nonempty (HeightOneSpectrum R) :=
  have := (FaithfulSMul.algebraMap_injective ℤ R).nontrivial
  HeightOneSpectrum.nonempty fun h ↦
    Int.not_isField
      (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ R) h)


-- @@ L81-83 verbatim
instance : Nontrivial (FiniteAdeleRing (𝓞 K) K) :=
  RingHom.domain_nontrivial (FiniteAdeleRing.evalAlgebraMap _ _
    (Nonempty.some inferInstance)).toRingHom


-- @@ L85-85 verbatim
end IsDedekindDomain.FiniteAdeleRing


-- @@ L87-87 verbatim
end Instances
