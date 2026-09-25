/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Physlib.Meta.Sorry

-- @@ L11-15 verbatim
/-!

## The Microcanonical Ensemble

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
section ThermodynamicEnsemble


-- @@ L21-38 verbatim
/-- The Hamiltonian for a microcanonical ensemble, parameterized by any extrinsic parameters of data
    D. Since it's an arbitrary type, 'T' would be nice, but we use 'D' for data to avoid confusion
    with temperature. We define Hamiltonians as an energy function on a real manifold, whose
    dimension n possibly depends on the data D. Energy is a WithTop ℝ, ⊤ is used to mean "excluded
    as a possibility in phase space". This formalization does exclude the possibility of discrete
    degrees of freedom; it is not _completely_ general. A better formalization could have an
    arbitrary measurable space.
-/
structure MicroHamiltonian (D : Type) where
  /-- For extrinsic parameters D (e.g. the number of particles of different chemical species,
    the shape of the box), how many continuous degrees of freedom are there? -/
  dim : D → Type
  /-- The number of degrees of freedom is finite. -/
  [dimFin : ∀ d, Fintype (dim d)]
  /-- Given the configuration, what is its energy? -/
  H : {d : D} → (dim d → ℝ) → WithTop ℝ
  --The energy function must be measurable (else the partition function integral is meaningless).
  measurable_H : ∀ d, Measurable (@H d)


-- @@ L40-42 verbatim
/-- The dimFin to the instance cache is added so that things like the measure can be synthesized -/
instance microHamiltonianFintype {D} (H : MicroHamiltonian D) (d : D) : Fintype (H.dim d) :=
  H.dimFin d


-- @@ L44-46 verbatim
/-- The standard microcanonical ensemble Hamiltonian, where the data is the particle number N and
  the volume V. -/
abbrev NVEHamiltonian := MicroHamiltonian (ℕ × ℝ)


-- @@ L48-49 verbatim
/-- Helper to get the number in an N-V Hamiltonian -/
def NVEHamiltonian.N : (ℕ × ℝ) → ℕ := Prod.fst


-- @@ L51-52 verbatim
/-- Helper to get the volume in an N-V Hamiltonian -/
def NVEHamiltonian.V : (ℕ × ℝ) → ℝ := Prod.snd
