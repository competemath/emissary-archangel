/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable


-- @@ L10-14 verbatim
/-!
# Pointwise Energy

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter

-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace CKN


-- @@ L27-29 verbatim
/-- The time derivative on the explicit space-time product carrier. -/
def timePartialProd (g : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  timePartial (show ParabolicPoint → ℝ from g) z


-- @@ L31-33 verbatim
/-- The spatial derivative on the explicit space-time product carrier. -/
def spatialPartialProd (g : Vec3 × ℝ → ℝ) (i : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  spatialPartial (show ParabolicPoint → ℝ from g) i z


-- @@ L35-38 verbatim
/-- The iterated spatial derivative on the explicit product carrier. -/
def spatialSecondPartialProd (g : Vec3 × ℝ → ℝ)
    (i j : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  spatialSecondPartial (show ParabolicPoint → ℝ from g) i j z


-- @@ L40-49 verbatim
/-- The right-hand energy density in the local energy inequality. -/
def localEnergyRhs
    (u : Vec3 × ℝ → Vec3) (p : Vec3 × ℝ → ℝ)
    (f : Vec3 × ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ)
  (z : Vec3 × ℝ) : ℝ :=
  (vec3EuclideanNorm (u z)) ^ 2 *
      (timePartialProd ψ z + ∑ i, spatialSecondPartialProd ψ i i z)
    + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
        ∑ i, u z i * spatialPartialProd ψ i z
    + 2 * (∑ i, f z i * u z i) * ψ z


-- @@ L51-65 verbatim
/-- The suitable-solution energy inequality, with its density named. -/
theorem suitableWeakSolution_energyInequality
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
      ∫ z in spaceTimeSet Ω I, localEnergyRhs u p f ψ z := by
  rcases hsol with ⟨_, _, _, _, _, _, _, _, henergy⟩
  simpa only [localEnergyRhs, timePartialProd, spatialSecondPartialProd,
    spatialPartialProd] using (henergy ψ hψ hψ_nonneg).2.2


-- @@ L67-67 verbatim
end CKN
