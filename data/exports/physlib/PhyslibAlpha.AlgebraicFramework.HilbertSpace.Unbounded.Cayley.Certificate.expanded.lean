/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.BoundedIntegralAlgebra
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Cayley.Measure


-- @@ L11-31 verbatim
/-!

# The bounded-unitary spectral interface

The bounded spectral theorem itself does not need the Cayley support condition from
`Cayley/Measure.lean`: that condition is only needed once a bounded unitary's spectral measure is
going to be pulled back to the real line. This file records the general output any construction
of a bounded normal/unitary spectral measure must supply (`BoundedNormalSpectralData`,
`BoundedUnitarySpectralData`), independently of how that measure is actually built — kept general
so an arbitrary bounded normal operator can consume the same interface, not only Cayley unitaries.

`BoundedUnitarySpectralData` additionally exposes the real spectral measure obtained by pulling
its (Cayley-supported) complex measure back through `cayleyInverseMap`, together with the exact
uniqueness statement: a real spectral measure is determined by its Cayley pushforward.

- `BoundedNormalSpectralData` : a spectral measure reconstructing a bounded normal operator `U`
  in the weak identity-integral sense, with an integral-determined extensionality principle.
- `BoundedUnitarySpectralData` : the same, plus the support condition needed to invert the Cayley
  map, and the resulting `realSpectralMeasure`.

-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
open scoped InnerProductSpace


-- @@ L39-39 verbatim
namespace QuantumMechanics

-- @@ L40-40 verbatim
namespace WOTSpectralMeasure


-- @@ L42-42 verbatim
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L44-44 verbatim
/-! ## A. Bounded normal spectral data -/


-- @@ L46-52 verbatim
/-- A bounded normal spectral certificate for `U`: a genuine weak-operator spectral measure
reconstructing `U`. -/
structure BoundedNormalSpectralData (U : H →L[ℂ] H) where
  /-- The spectral measure. -/
  spectralMeasure : WOTSpectralMeasure ℂ H
  reconstruction : ∀ x y : H,
    spectralMeasure.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ


-- @@ L54-54 verbatim
namespace BoundedNormalSpectralData


-- @@ L56-56 verbatim
variable {U : H →L[ℂ] H}


-- @@ L58-71 verbatim
@[ext]
theorem ext {D E : BoundedNormalSpectralData U}
    (h : D.spectralMeasure = E.spectralMeasure) : D = E := by
  cases D with
  | mk μ hμ =>
    cases E with
    | mk ν hν =>
      cases h
      rfl

/- A bounded-integral equality is a convenient representation-independent uniqueness criterion.
The stronger hypothesis is intentional: reconstruction of only the identity multiplier does not
by itself expose the spectral projections, whereas equality for all bounded Borel multipliers does.
    -/

-- @@ L72-79 verbatim
theorem ext_of_boundedIntegral_eq {D E : BoundedNormalSpectralData U}
    (h : ∀ (f : ℂ → ℂ) (hf : Measurable f)
      (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C),
      D.spectralMeasure.boundedIntegral f hf hfb =
        E.spectralMeasure.boundedIntegral f hf hfb) :
    D = E := by
  apply ext
  exact WOTSpectralMeasure.ext_of_boundedIntegral_eq h


-- @@ L81-81 verbatim
end BoundedNormalSpectralData


-- @@ L83-83 verbatim
/-! ## B. Bounded unitary spectral data -/


-- @@ L85-98 verbatim
/-- The exact output required from the bounded unitary spectral theorem.

The support equation records both facts needed to invert the Cayley map: the measure is on the
unit circle and has no mass at `1`, the point representing infinity. The reconstruction equation
is weak-operator reconstruction for the bounded unitary itself. This is deliberately a data
structure rather than an axiom-producing definition: constructing it for an arbitrary unitary is
the bounded spectral theorem proper. -/
structure BoundedUnitarySpectralData (u : H ≃ₗᵢ[ℂ] H) where
  /-- The spectral measure. -/
  spectralMeasure : WOTSpectralMeasure ℂ H
  support_away_one : ∀ S : Set ℂ, MeasurableSet S →
    spectralMeasure S = spectralMeasure (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
  reconstruction : ∀ x y : H,
    spectralMeasure.complexWeakIntegral id x y = ⟪y, u x⟫_ℂ


-- @@ L100-100 verbatim
namespace BoundedUnitarySpectralData


-- @@ L102-102 verbatim
variable {u : H ≃ₗᵢ[ℂ] H}


-- @@ L104-112 verbatim
@[ext]
theorem ext {D E : BoundedUnitarySpectralData u}
    (h : D.spectralMeasure = E.spectralMeasure) : D = E := by
  cases D with
  | mk μ hμ hμ' =>
    cases E with
    | mk ν hν hν' =>
      cases h
      rfl


-- @@ L114-121 verbatim
theorem ext_of_boundedIntegral_eq {D E : BoundedUnitarySpectralData u}
    (h : ∀ (f : ℂ → ℂ) (hf : Measurable f)
      (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C),
      D.spectralMeasure.boundedIntegral f hf hfb =
        E.spectralMeasure.boundedIntegral f hf hfb) :
    D = E := by
  apply ext
  exact WOTSpectralMeasure.ext_of_boundedIntegral_eq h


-- @@ L123-123 verbatim
variable {u : H ≃ₗᵢ[ℂ] H} (D : BoundedUnitarySpectralData u)


-- @@ L125-127 verbatim
/-- Pull the bounded unitary measure back to the real line. -/
def realSpectralMeasure : WOTSpectralMeasure ℝ H :=
  WOTSpectralMeasure.cayleyInverseMap D.spectralMeasure


-- @@ L129-152 verbatim
lemma cayleyMap_realSpectralMeasure :
    WOTSpectralMeasure.cayleyMap D.realSpectralMeasure = D.spectralMeasure := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ((D.realSpectralMeasure.map cayley measurable_cayley) S) = D.spectralMeasure S
  rw [D.realSpectralMeasure.map_apply cayley measurable_cayley hS]
  change ((D.spectralMeasure.map cayleyInverse measurable_cayleyInverse)
      (cayley ⁻¹' S)) = D.spectralMeasure S
  rw [D.spectralMeasure.map_apply cayleyInverse measurable_cayleyInverse
    (hS.preimage measurable_cayley)]
  have hL : MeasurableSet (cayleyInverse ⁻¹' cayley ⁻¹' S) :=
    (hS.preimage measurable_cayley).preimage measurable_cayleyInverse
  rw [D.support_away_one _ hL, D.support_away_one S hS]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hunit⟩
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, cayley_cayleyInverse hunit.1 hunit.2] using hz
  · rintro ⟨hz, hunit⟩
    have hz' : cayley (cayleyInverse z) = z := cayley_cayleyInverse hunit.1 hunit.2
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, hz'] using hz


-- @@ L154-164 verbatim
/-- The real measure recovered from bounded Cayley data is unique among real measures with the
same Cayley pushforward. -/
lemma realSpectralMeasure_eq_of_cayleyMap_eq
    {μS : WOTSpectralMeasure ℝ H}
    (hμ : WOTSpectralMeasure.cayleyMap μS = D.spectralMeasure) :
    D.realSpectralMeasure = μS := by
  apply WOTSpectralMeasure.cayleyMap_injective
  calc
    WOTSpectralMeasure.cayleyMap D.realSpectralMeasure = D.spectralMeasure :=
      D.cayleyMap_realSpectralMeasure
    _ = WOTSpectralMeasure.cayleyMap μS := hμ.symm


-- @@ L166-166 verbatim
end BoundedUnitarySpectralData

-- @@ L167-167 verbatim
end WOTSpectralMeasure

-- @@ L168-168 verbatim
end QuantumMechanics


-- @@ L170-170 verbatim
end
