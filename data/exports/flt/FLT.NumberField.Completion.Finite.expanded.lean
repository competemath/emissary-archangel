/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLT.DedekindDomain.AdicValuation
public import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLT.Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
public import FLT.Mathlib.LinearAlgebra.Countable


-- @@ L18-22 verbatim
/-!

# Completion of a number field at a finite place

-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L28-28 verbatim
open NumberField


-- @@ L30-31 verbatim
example (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Finite ((𝓞 K) ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI


-- @@ L33-33 verbatim
open IsDedekindDomain


-- @@ L35-35 verbatim
variable (v : HeightOneSpectrum (𝓞 K))


-- @@ L37-37 verbatim
open IsLocalRing


-- @@ L39-42 verbatim
instance NumberField.instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot


-- @@ L44-46 verbatim
open scoped Valued in
instance : Finite (𝓀[v.adicCompletion K]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers K)))


-- @@ L48-51 verbatim
instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance
    (v.valuedAdicCompletion_surjective K)


-- @@ L53-56 verbatim
lemma NumberField.isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isCompact_iff_compactSpace]
  exact instCompactSpaceAdicCompletionIntegers K v


-- @@ L58-60 verbatim
lemma NumberField.isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _


-- @@ L62-65 verbatim
instance Rat.adicCompletion.locallyCompactSpace (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding
  |>.locallyCompactSpace


-- @@ L67-73 verbatim
instance (v : HeightOneSpectrum (𝓞 K)) :
    WeaklyLocallyCompactSpace (v.adicCompletion K) where
  exists_compact_mem_nhds x :=
    open Pointwise in
    ⟨x +ᵥ ((v.adicCompletionIntegers K) : Set (v.adicCompletion K)),
      (isCompact_iff_compactSpace.mpr <| instCompactSpaceAdicCompletionIntegers K v).vadd x,
      ((isOpenAdicCompletionIntegers K v).vadd x).mem_nhds (Set.mem_vadd_set.mpr ⟨0, by simp⟩)⟩


-- @@ L75-78 verbatim
instance (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (v.adicCompletion K) := inferInstance

-- does this exist upstream? Should do.

-- @@ L79-80 verbatim
example (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (v.adicCompletion K) :=
  inferInstance
