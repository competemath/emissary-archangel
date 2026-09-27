/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous


-- @@ L10-32 verbatim
/-!
# Translation invariance for contour winding numbers

This file records the basic translation-invariance API for the generalized winding number.
Translating both the curve and the distinguished point by the same complex number leaves the index
principal value unchanged, so the winding number and null-homology are invariant.

These lemmas are bookkeeping for the roadmap's curve and cycle layer. The geometry of the
generalized winding number is local at a crossing or sector, and finite-decomposition arguments
frequently translate the crossing point to the origin before applying the model computation.

## Main results

* `Contour.windingNumber_translate` — translating the curve and base point together preserves
  the generalized winding number.
* `Contour.IsNullHomologous.translate` — null-homology is preserved by translating both the
  curve and the ambient set.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/


-- @@ L34-34 verbatim
public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
open Filter Topology


-- @@ L40-40 verbatim
namespace TauCeti.Contour


-- @@ L42-42 verbatim
variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ c : ℂ} {Ω : Set ℂ}


-- @@ L44-46 verbatim
/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the translation statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)


-- @@ L48-59 verbatim
/-- The generalized winding number is invariant under simultaneous translation of the curve and
the base point. -/
theorem windingNumber_translate (c : ℂ) :
    windingNumber (fun t => γ t + c) a b (z₀ + c) = windingNumber γ a b z₀ := by
  rw [windingNumber_eq_cauchyPVAt, windingNumber_eq_cauchyPVAt]
  congr 1
  rw [cauchyPVAt_congr_along_curve (γ := fun t => γ t + c)
    (f := κ[z₀ + c]) (g := fun z => κ[z₀] (z - c)) (z₀ := z₀ + c)]
  · exact cauchyPVAt_translate (γ := γ) (a := a) (b := b) (f := κ[z₀]) (z₀ := z₀) c
  · intro t _
    congr 1
    ring


-- @@ L61-71 verbatim
/-- Null-homology is preserved by translating the curve and the ambient set together. -/
theorem IsNullHomologous.translate (h : IsNullHomologous γ a b Ω) (c : ℂ) :
    IsNullHomologous (fun t => γ t + c) a b ((fun z => z + c) '' Ω) := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have hz_sub : z - c ∉ Ω := by
    intro hzΩ
    exact hz ⟨z - c, hzΩ, by ring⟩
  have hpoint : z = (z - c) + c := by ring
  rw [hpoint, windingNumber_translate c]
  exact h (z - c) hz_sub


-- @@ L73-73 verbatim
end TauCeti.Contour


-- @@ L75-75 verbatim
end
