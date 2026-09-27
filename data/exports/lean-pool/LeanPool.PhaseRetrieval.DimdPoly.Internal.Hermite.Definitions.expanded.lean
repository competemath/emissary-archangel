/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # Definitions.lean
  Core shared definitions for the Hermite phase-retrieval scaffold.

  Scaffolding notes:
  - `Basis/first_true_level_basis.md`
  - `Reduction/circle_reduction.md`
  - `BlockDecomposition/block_decomposition.md`

  The goal of this file is only to pin down the common language of the
  development. Proofs come later.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Nat.Dist
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Combinatorics.Matroid.Init


-- @@ L26-26 verbatim
/-! # Definitions -/


-- @@ L28-28 verbatim
@[expose] public section



-- @@ L31-31 verbatim
open Complex MeasureTheory Real Finset

-- @@ L32-32 verbatim
open scoped BigOperators ComplexConjugate Topology


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace HermiteLEAN


-- @@ L38-39 verbatim
/-- The circle period used throughout the Hermite development. -/
def T : ℝ := 2 * Real.pi


-- @@ L41-43 verbatim
lemma T_pos : 0 < T := by
  dsimp [T]
  positivity


-- @@ L45-45 verbatim
instance : Fact (0 < T) := ⟨T_pos⟩


-- @@ L47-48 verbatim
/-- The normalized circle used for Fourier analysis. -/
abbrev Circle := AddCircle T


-- @@ L50-51 verbatim
/-- Positive part. -/
def posPart (x : ℝ) : ℝ := max x 0


-- @@ L53-54 verbatim
/-- The signed modulus defect imported from the Fock-space argument. -/
def rho (w : ℂ) : ℝ := |‖(1 : ℂ) + w‖ - 1|


-- @@ L56-57 verbatim
/-- The distinguished basis vector `Φ₀(z) = \bar z`. -/
def phi0 (z : ℂ) : ℂ := conj z


-- @@ L59-71 verbatim
/-- The first true-level Hermite basis vector `Φₙ`.

We index from `0`, with `phi 0 = Phi_0` and for `n ≥ 1`

`phi n z = z^(n-1) * (|z|² - n) / sqrt(n!)`.
-/
def phi : ℕ → ℂ → ℂ
  | 0 => phi0
  | n + 1 =>
      fun z =>
        z ^ n *
          (((‖z‖ ^ 2 - (Nat.succ n : ℝ)) /
              Real.sqrt ((Nat.factorial (Nat.succ n) : ℕ) : ℝ)) : ℂ)


-- @@ L73-76 verbatim
/-- The weighted inner product on `L²_γ(ℂ)`. -/
def weightedInner (F G : ℂ → ℂ) : ℂ :=
  (1 / Real.pi : ℂ) *
    ∫ z, F z * conj (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ)


-- @@ L78-80 verbatim
/-- The weighted squared norm on `L²_γ(ℂ)`. -/
def weightedNormSq (F : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) * ∫ z, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)


-- @@ L82-83 verbatim
/-- The weighted norm on `L²_γ(ℂ)`. -/
def weightedNorm (F : ℂ → ℂ) : ℝ := Real.sqrt (weightedNormSq F)


-- @@ L85-86 verbatim
/-- The pointwise modulus defect relative to a background function `F₀`. -/
def modulusDefect (F0 G : ℂ → ℂ) (z : ℂ) : ℝ := |‖F0 z + G z‖ - ‖F0 z‖|


-- @@ L88-91 verbatim
/-- The weighted squared defect norm relative to a background function `F₀`. -/
def weightedDefectNormSq (F0 G : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) *
    ∫ z, (modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)


-- @@ L93-94 verbatim
/-- The weighted defect norm relative to a background function `F₀`. -/
def weightedDefectNorm (F0 G : ℂ → ℂ) : ℝ := Real.sqrt (weightedDefectNormSq F0 G)


-- @@ L96-97 verbatim
/-- The orthogonal complement to `Φ₀`, expressed via the weighted inner product. -/
def Phi0Perp : Set (ℂ → ℂ) := {F | weightedInner F phi0 = 0}


-- @@ L99-101 verbatim
/-- A finite orthogonal Hermite perturbation `G_a = ∑ a_n Φ_{n+1}`. -/
def hermiteSum {D : ℕ} (a : Fin D → ℂ) (z : ℂ) : ℂ :=
  ∑ n : Fin D, a n * phi (n.1 + 1) z


-- @@ L103-105 verbatim
/-- The coefficient-side squared norm for a finite Hermite perturbation. -/
def hermiteCoeffNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  ∑ n : Fin D, ‖a n‖ ^ 2


-- @@ L107-108 verbatim
/-- The unit circle point of radius `r` and argument `t`. -/
def circlePoint (r : ℝ) (t : Circle) : ℂ := (r : ℂ) * (fourier (1 : ℤ) t : ℂ)


-- @@ L110-118 verbatim
/-- The coefficient appearing in the circle reduction for `Φ_{n+1}`.

This formula is only intended for `r > 0`; the radius-zero case is handled
separately later on.
-/
def circleCoeff {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (n : Fin D) : ℂ :=
  a n *
    ((((r ^ n.1) * (r ^ 2 - ((n.1 + 1 : ℕ) : ℝ))) /
        (r * Real.sqrt ((Nat.factorial (n.1 + 1) : ℕ) : ℝ)) : ℝ) : ℂ)


-- @@ L120-122 verbatim
/-- The positive-frequency trigonometric polynomial on the circle attached to `G_a`. -/
def circlePolynomial {D : ℕ} (a : Fin D → ℂ) (r : ℝ) : Circle → ℂ :=
  fun t => ∑ n : Fin D, circleCoeff a r n * fourier ((n.1 + 1 : ℕ) : ℤ) t


-- @@ L124-126 verbatim
/-- A generic positive-frequency trigonometric polynomial. -/
def positiveTrigonometricPolynomial (E : Finset ℕ) (c : ℕ → ℂ) : Circle → ℂ :=
  fun t => Finset.sum E (fun n => c n * fourier (n : ℤ) t)


-- @@ L128-129 verbatim
/-- Consecutive positive frequencies `[N, N + L - 1]`. -/
def frequencyBand (N L : ℕ) : Finset ℕ := Finset.Icc N (N + L - 1)


-- @@ L131-133 verbatim
/-- The circle `L²` norm squared with respect to normalized Haar measure. -/
def circleL2Sq (f : Circle → ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle


-- @@ L135-137 verbatim
/-- The circle defect against the constant `1`. -/
def circleRhoNormSq (f : Circle → ℂ) : ℝ :=
  ∫ t, (rho (f t)) ^ 2 ∂AddCircle.haarAddCircle


-- @@ L139-141 verbatim
/-- The pointwise circle modulus defect relative to a background function `F₀`. -/
def circleModulusDefect (F0 G : Circle → ℂ) (t : Circle) : ℝ :=
  |‖F0 t + G t‖ - ‖F0 t‖|


-- @@ L143-145 verbatim
/-- The circle squared defect norm relative to a background function `F₀`. -/
def circleDefectNormSq (F0 G : Circle → ℂ) : ℝ :=
  ∫ t, (circleModulusDefect F0 G t) ^ 2 ∂AddCircle.haarAddCircle


-- @@ L147-148 verbatim
/-- The annulus `A_j = { z : j ≤ |z| < j + 1 }`. -/
def annulus (j : ℕ) : Set ℂ := {z | (j : ℝ) ≤ ‖z‖ ∧ ‖z‖ < ((j + 1 : ℕ) : ℝ)}


-- @@ L150-153 verbatim
/-- The weighted squared mass of a function on annulus `A_j`. -/
def annulusIntegralSq (F : ℂ → ℂ) (j : ℕ) : ℝ :=
  (1 / Real.pi) *
    ∫ z in annulus j, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)


-- @@ L155-156 verbatim
/-- The square block `I_ℓ = { n : ℓ² ≤ n < (ℓ + 1)² }`. -/
def squareBlock (ℓ : ℕ) : Finset ℕ := Finset.Ico (ℓ ^ 2) ((ℓ + 1) ^ 2)


-- @@ L158-159 verbatim
/-- The block index of a positive Hermite mode. -/
def blockIndex (n : ℕ) : ℕ := Nat.sqrt n


-- @@ L161-163 verbatim
/-- The `ℓ`-th block of a finite Hermite perturbation. -/
def blockPiece {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℂ → ℂ :=
  fun z => ∑ n : Fin D, if blockIndex (n.1 + 1) = ℓ then a n * phi (n.1 + 1) z else 0


-- @@ L165-169 verbatim
/-- The local part `V_j` built from blocks at distance at most `M` from `j`. -/
def localPiece {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) : ℂ → ℂ :=
  fun z =>
    ∑ n : Fin D,
      if Nat.dist (blockIndex (n.1 + 1)) j ≤ M then a n * phi (n.1 + 1) z else 0


-- @@ L171-173 verbatim
/-- The distant remainder `R_j = G - V_j`. -/
def remainderPiece {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) : ℂ → ℂ :=
  fun z => hermiteSum a z - localPiece a M j z


-- @@ L175-177 verbatim
/-- The coefficient-side squared norm of one block. -/
def blockCoeffNormSq {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℝ :=
  ∑ n : Fin D, if blockIndex (n.1 + 1) = ℓ then ‖a n‖ ^ 2 else 0


-- @@ L179-180 verbatim
/-- The formal Hermite expansion associated to a coefficient sequence. -/
def h1Series (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * phi n z


-- @@ L182-184 verbatim
/-- The model space `H₁`, encoded as the closed span of the Hermite family. -/
def H1 : Set (ℂ → ℂ) :=
  ((Submodule.span ℂ (Set.range phi)).topologicalClosure : Set (ℂ → ℂ))


-- @@ L186-189 verbatim
/-- The closed span of the higher Hermite modes `Φ₁, Φ₂, ...`. -/
def H1Orthogonal : Set (ℂ → ℂ) :=
  ((Submodule.span ℂ (Set.range fun n : ℕ => phi (n + 1))).topologicalClosure :
    Set (ℂ → ℂ))


-- @@ L191-193 verbatim
/-- The Gaussian tail appearing in the leakage coefficient. -/
def gaussianTail (c : ℝ) (M : ℕ) : ℝ :=
  ∑' m : ℕ, Real.exp (-c * (posPart ((((m + M + 1 : ℕ) : ℝ) - 4))) ^ 2)


-- @@ L195-196 verbatim
/-- The leakage coefficient `η_M`. -/
def etaCoeff (Cblk cblk : ℝ) (M : ℕ) : ℝ := 2 * Cblk * gaussianTail cblk M


-- @@ L198-198 verbatim
end HermiteLEAN
