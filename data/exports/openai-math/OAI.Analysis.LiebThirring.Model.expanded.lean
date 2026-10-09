import Mathlib


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-13 verbatim
/-!
The form domain is H¹(R;C), represented by an L² function together with its L²
weak derivative. Null-set changes do not affect any definition below.
`negativeMoment` is the extended nonnegative sum over negative eigenvalues,
counting multiplicities: equivalently the supremum over all finite orthonormal
families of weak eigenfunctions of the form. This does not assume in advance
finiteness of the moment or a finite number of eigenvalues.
-/



-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
open MeasureTheory

-- @@ L18-18 verbatim
open scoped ENNReal Matrix.Norms.L2Operator

-- @@ L19-19 verbatim
open Matrix


-- @@ L21-21 verbatim
namespace SharpLiebThirring


-- @@ L23-29 verbatim
structure H1 where
  val : ℝ → ℂ
  grad : ℝ → ℂ
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  weak_derivative : ∀ φ : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    (∫ x : ℝ, val x * deriv φ x) = -(∫ x : ℝ, grad x * φ x)


-- @@ L31-31 verbatim
def l2Pairing (u v : H1) : ℂ := ∫ x : ℝ, star (u.val x) * v.val x


-- @@ L33-36 verbatim
/-- The polarized form of -d²/dx² - W, on exactly H¹. -/
def schrodingerForm (W : ℝ → ℝ) (u v : H1) : ℂ :=
  (∫ x : ℝ, star (u.grad x) * v.grad x) -
    ∫ x : ℝ, (W x : ℂ) * star (u.val x) * v.val x


-- @@ L38-40 verbatim
/-- Weak eigenfunction at the negative energy -k². -/
def IsNegativeEigenfunction (W : ℝ → ℝ) (k : ℝ) (u : H1) : Prop :=
  0 < k ∧ ∀ v : H1, schrodingerForm W v u = -(k ^ 2 : ℝ) * l2Pairing v u


-- @@ L42-43 verbatim
def IsOrthonormalFamily {N : ℕ} (u : Fin N → H1) : Prop :=
  ∀ i j, l2Pairing (u i) (u j) = if i = j then 1 else 0


-- @@ L45-49 verbatim
/-- An unlimited finite-family-size supremum, in ℝ≥0∞, includes the entire sum. -/
def negativeMoment (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (u : Fin N → H1) (k : Fin N → ℝ)
    (_ : IsOrthonormalFamily u) (_ : ∀ i, IsNegativeEigenfunction W (k i) (u i)),
      ∑ i, (ENNReal.ofReal (k i)) ^ (2 * γ)


-- @@ L51-54 verbatim
/-- The moment retaining at most one negative eigenvalue. -/
def oneStateMoment (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (u : H1) (k : ℝ) (_ : l2Pairing u u = 1)
    (_ : IsNegativeEigenfunction W k u), (ENNReal.ofReal k) ^ (2 * γ)


-- @@ L56-57 verbatim
def Admissible (γ : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ᵐ x : ℝ, 0 ≤ W x) ∧ MemLp W (ENNReal.ofReal (γ + 1 / 2)) volume


-- @@ L59-60 verbatim
def potentialMass (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (ENNReal.ofReal (W x)) ^ (γ + 1 / 2)


-- @@ L62-63 verbatim
def semiclassicalConstant (γ : ℝ) : ℝ :=
  Real.Gamma (γ + 1) / (2 * Real.sqrt Real.pi * Real.Gamma (γ + 3 / 2))


-- @@ L65-66 verbatim
def sharpConstant (γ : ℝ) : ℝ :=
  2 * ((γ - 1 / 2) / (γ + 1 / 2)) ^ (γ - 1 / 2) * semiclassicalConstant γ


-- @@ L68-70 verbatim
def optimalConstant (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (_ : Admissible γ W) (_ : 0 < potentialMass γ W),
    negativeMoment γ W / potentialMass γ W


-- @@ L72-74 verbatim
def oneStateConstant (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (_ : Admissible γ W) (_ : 0 < potentialMass γ W),
    oneStateMoment γ W / potentialMass γ W


-- @@ L76-78 verbatim
def equalityPotential (γ : ℝ) (x : ℝ) : ℝ :=
  let r := (γ - 1 / 2)⁻¹
  (r + 1) * (Real.cosh (r * x))⁻¹ ^ 2


-- @@ L80-90 verbatim
/-- The full spectral bound, optimal constants, and attainment at the explicit potential. -/
def MainClaim : Prop :=
  ∀ γ : ℝ, 1 / 2 < γ → γ < 3 / 2 →
    (∀ W : ℝ → ℝ, Admissible γ W →
      negativeMoment γ W ≤ ENNReal.ofReal (sharpConstant γ) * potentialMass γ W) ∧
    optimalConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
    oneStateConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
    Admissible γ (equalityPotential γ) ∧
    0 < potentialMass γ (equalityPotential γ) ∧
    negativeMoment γ (equalityPotential γ) =
      ENNReal.ofReal (sharpConstant γ) * potentialMass γ (equalityPotential γ)


-- @@ L92-92 verbatim
end SharpLiebThirring

-- @@ L93-93 verbatim
end


-- @@ L95-95 verbatim
end OAI
