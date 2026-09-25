/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule

-- @@ L9-36 verbatim
/-!

# Dirichlet submodule

## i. Overview

In this module we define the Dirichlet submodule of `SpaceDHilbertSpaceOn Ω μ` consisting of
equivalence classes of Schwartz maps which vanish on `frontier Ω`. The frontier (or boundary)
of a set `Ω` contains all points whose neighborhoods always intersect with both `Ω` and `Ωᶜ`.

These serve as a convenient dense domain for operators acting on wavefunctions satisfying
homogeneous Dirichlet boundary conditions on `Ω`.

## ii. Key results

- `DirichletSubmoduleOn Ω μ`: The subspace of `SchwartzSubmodule d μ` consisting of Schwartz maps
  which vanish on the frontier of `Ω`.

## iii. Table of contents

- A. Definitions
- B. Contained in SchwartzSubmoduleOn
- C. Density

## iv. References

* None.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
noncomputable section

-- @@ L41-41 verbatim
namespace QuantumMechanics

-- @@ L42-42 verbatim
namespace SpaceDHilbertSpaceOn


-- @@ L44-44 verbatim
open MeasureTheory SchwartzMap SpaceDHilbertSpace


-- @@ L46-46 verbatim
variable {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d)) [μ.HasTemperateGrowth]


-- @@ L48-50 verbatim
/-!
## A. Definitions
-/


-- @@ L52-57 verbatim
/-- The Schwartz maps which vanish on `frontier Ω`. -/
def DirichletSchwartzMap : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) | ∀ x : frontier Ω, f x = 0}
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all


-- @@ L59-62 verbatim
/-- The submodule of the Hilbert space on `Ω` consisting of the equivalence classes
  of Schwartz maps which vanish on `frontier Ω`. -/
abbrev DirichletSubmoduleOn : Submodule ℂ (SpaceDHilbertSpaceOn Ω μ) :=
  (DirichletSchwartzMap Ω).map (subspaceProjection Ω μ ∘ₗ schwartzIncl μ)


-- @@ L64-64 verbatim
namespace DirichletSubmoduleOn


-- @@ L66-70 verbatim
variable {Ω μ} in
lemma mem_iff {ψ : SpaceDHilbertSpaceOn Ω μ} :
    ψ ∈ DirichletSubmoduleOn Ω μ ↔
      ∃ f : DirichletSchwartzMap Ω, subspaceProjection Ω μ (schwartzIncl μ f) = ψ := by
  simp


-- @@ L72-74 verbatim
/-!
## B. Contained in SchwartzSubmoduleOn
-/


-- @@ L76-79 verbatim
lemma le_schwartzSubmoduleOn : DirichletSubmoduleOn Ω μ ≤ SchwartzSubmoduleOn Ω μ := by
  intro ψ hψ
  obtain ⟨f, hf⟩ := mem_iff.mp hψ
  apply SchwartzSubmoduleOn.mem_iff.mpr ⟨⟨schwartzIncl μ f, by simp⟩, hf⟩


-- @@ L81-83 verbatim
/-!
## C. Density
-/


-- @@ L85-86 verbatim
TODO "Prove that `DirichletSubmoduleOn Ω μ` is dense in `SpaceDHilbertSpaceOn Ω μ`
  (perhaps with some assumptions on Ω and μ)."


-- @@ L88-88 verbatim
end DirichletSubmoduleOn

-- @@ L89-89 verbatim
end SpaceDHilbertSpaceOn

-- @@ L90-90 verbatim
end QuantumMechanics

-- @@ L91-91 verbatim
end
