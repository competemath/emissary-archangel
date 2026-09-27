/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-19 verbatim
/-!
# The planar circular restricted three-body Hamiltonian

This file gives the exact definitions occurring in the Poincaré nonintegrability challenge and
establishes their elementary structural properties. It deliberately does not import the challenge
module: the solution and challenge environments must remain separately exportable for comparator.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace LeanPool.PoincareThreeBody


-- @@ L25-25 verbatim
open Set


-- @@ L27-28 verbatim
/-- Planar canonical phase space, ordered as `(x, y, pₓ, pᵧ)`. -/
abbrev PhaseSpace := Fin 4 → ℝ


-- @@ L30-32 verbatim
/-- Squared distance from the primary of mass `μ` at `(1 - μ, 0)`. -/
def firstPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) : ℝ :=
  (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2


-- @@ L34-36 verbatim
/-- Squared distance from the primary of mass `1 - μ` at `(-μ, 0)`. -/
def secondPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) : ℝ :=
  (s 0 + μ) ^ 2 + (s 1) ^ 2


-- @@ L38-40 verbatim
/-- The collision-free joint mass-parameter/phase-space domain. -/
def collisionFree : Set (ℝ × PhaseSpace) :=
  {z | firstPrimaryDistanceSq z.1 z.2 ≠ 0 ∧ secondPrimaryDistanceSq z.1 z.2 ≠ 0}


-- @@ L42-44 verbatim
/-- The collision-free domain with the mass parameter restricted to `|μ| < δ`. -/
def parameterDomain (δ : ℝ) : Set (ℝ × PhaseSpace) :=
  {z | |z.1| < δ ∧ z ∈ collisionFree}


-- @@ L46-49 verbatim
/-- The Newtonian potential in the rotating frame. -/
noncomputable def potential (μ : ℝ) (s : PhaseSpace) : ℝ :=
  μ / Real.sqrt (firstPrimaryDistanceSq μ s) +
    (1 - μ) / Real.sqrt (secondPrimaryDistanceSq μ s)


-- @@ L51-53 verbatim
/-- The planar circular restricted three-body Hamiltonian in rotating canonical coordinates. -/
noncomputable def hamiltonian (μ : ℝ) (s : PhaseSpace) : ℝ :=
  ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 - potential μ s


-- @@ L55-57 verbatim
/-- The coordinate basis vector in the concrete phase space. -/
def coordinateVector (i : Fin 4) : PhaseSpace :=
  fun j ↦ if j = i then 1 else 0


-- @@ L59-66 verbatim
/-- The canonical Poisson bracket in coordinates `(x, y, pₓ, pᵧ)`. -/
noncomputable def poissonBracket (F G : PhaseSpace → ℝ) (s : PhaseSpace) : ℝ :=
  let dF := fderiv ℝ F s
  let dG := fderiv ℝ G s
  dF (coordinateVector 0) * dG (coordinateVector 2) -
      dF (coordinateVector 2) * dG (coordinateVector 0) +
    (dF (coordinateVector 1) * dG (coordinateVector 3) -
      dF (coordinateVector 3) * dG (coordinateVector 1))


-- @@ L68-70 verbatim
/-- Joint real analyticity in the mass parameter and phase variables. -/
def IsJointlyAnalytic (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  AnalyticOnNhd ℝ (Function.uncurry F) (parameterDomain δ)


-- @@ L72-74 verbatim
/-- A first-integral family Poisson-commutes with the Hamiltonian throughout the domain. -/
noncomputable def IsFirstIntegralFamily (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∀ z ∈ parameterDomain δ, poissonBracket (F z.1) (hamiltonian z.1) z.2 = 0


-- @@ L76-80 verbatim
/-- Functional independence of the phase differentials at some point. -/
noncomputable def IsIndependentSomewhere (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∃ z ∈ parameterDomain δ,
    LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian z.1) z.2, fderiv ℝ (F z.1) z.2]


-- @@ L82-85 verbatim
lemma firstPrimaryDistanceSq_nonneg (μ : ℝ) (s : PhaseSpace) :
    0 ≤ firstPrimaryDistanceSq μ s := by
  simp only [firstPrimaryDistanceSq]
  positivity


-- @@ L87-90 verbatim
lemma secondPrimaryDistanceSq_nonneg (μ : ℝ) (s : PhaseSpace) :
    0 ≤ secondPrimaryDistanceSq μ s := by
  simp only [secondPrimaryDistanceSq]
  positivity


-- @@ L92-94 verbatim
lemma firstPrimaryDistanceSq_pos {μ : ℝ} {s : PhaseSpace}
    (h : firstPrimaryDistanceSq μ s ≠ 0) : 0 < firstPrimaryDistanceSq μ s :=
  lt_of_le_of_ne (firstPrimaryDistanceSq_nonneg μ s) (Ne.symm h)


-- @@ L96-98 verbatim
lemma secondPrimaryDistanceSq_pos {μ : ℝ} {s : PhaseSpace}
    (h : secondPrimaryDistanceSq μ s ≠ 0) : 0 < secondPrimaryDistanceSq μ s :=
  lt_of_le_of_ne (secondPrimaryDistanceSq_nonneg μ s) (Ne.symm h)


-- @@ L100-103 verbatim
lemma mem_collisionFree_iff {μ : ℝ} {s : PhaseSpace} :
    (μ, s) ∈ collisionFree ↔
      firstPrimaryDistanceSq μ s ≠ 0 ∧ secondPrimaryDistanceSq μ s ≠ 0 :=
  Iff.rfl


-- @@ L105-107 verbatim
lemma mem_parameterDomain_iff {δ μ : ℝ} {s : PhaseSpace} :
    (μ, s) ∈ parameterDomain δ ↔ |μ| < δ ∧ (μ, s) ∈ collisionFree :=
  Iff.rfl


-- @@ L109-110 verbatim
@[simp] lemma coordinateVector_same (i : Fin 4) : coordinateVector i i = 1 := by
  simp [coordinateVector]


-- @@ L112-113 verbatim
@[simp] lemma coordinateVector_apply {i j : Fin 4} (h : j ≠ i) : coordinateVector i j = 0 := by
  simp [coordinateVector, h]


-- @@ L115-118 verbatim
lemma poissonBracket_self (F : PhaseSpace → ℝ) (s : PhaseSpace) :
    poissonBracket F F s = 0 := by
  simp only [poissonBracket]
  ring


-- @@ L120-123 verbatim
lemma hamiltonian_isFirstIntegralFamily (δ : ℝ) :
    IsFirstIntegralFamily δ hamiltonian := by
  intro z hz
  exact poissonBracket_self (hamiltonian z.1) z.2


-- @@ L125-129 verbatim
lemma hamiltonian_zero (s : PhaseSpace) :
    hamiltonian 0 s =
      ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 -
        1 / Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2) := by
  simp [hamiltonian, potential, firstPrimaryDistanceSq, secondPrimaryDistanceSq]


-- @@ L131-136 verbatim
lemma IsFirstIntegralFamily.poissonBracket_zero_at_mass_zero {δ : ℝ}
    {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ) (hF : IsFirstIntegralFamily δ F)
    {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    poissonBracket (F 0) (hamiltonian 0) s = 0 := by
  apply hF (0, s)
  exact ⟨by simpa using hδ, hs⟩


-- @@ L138-141 verbatim
lemma hamiltonian_not_independent (δ : ℝ) : ¬IsIndependentSomewhere δ hamiltonian := by
  rintro ⟨z, hz, hlinear⟩
  have hindex : (0 : Fin 2) = 1 := hlinear.injective (by simp)
  norm_num at hindex


-- @@ L143-143 verbatim
end LeanPool.PoincareThreeBody
