module

public import SpherePacking.ForMathlib.FunctionsBoundedAtInfty
public import SpherePacking.ForMathlib.MDifferentiableFunProp
public import SpherePacking.ForMathlib.SlashActions
public import SpherePacking.ForMathlib.UpperHalfPlane
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.IsCuspForm
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.Tactic.TendstoCont


-- @@ L12-17 verbatim
/-!
# Jacobi theta definitions

Define Jacobi theta functions `Θ₂`, `Θ₃`, `Θ₄` and their fourth powers `H₂`, `H₃`, `H₄`.
Also record their realization as specializations of `jacobiTheta₂`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open scoped Real MatrixGroups ModularForm

-- @@ L22-22 verbatim
open UpperHalfPlane hiding I

-- @@ L23-24 verbatim
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups


-- @@ L26-26 verbatim
local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

-- @@ L27-27 verbatim
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n


-- @@ L29-30 verbatim
/-- Define Θ₂, Θ₃, Θ₄ as series. -/
noncomputable def Θ₂_term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)

-- @@ L31-31 verbatim
noncomputable def Θ₃_term (n : ℤ) (τ : ℍ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)

-- @@ L32-32 verbatim
noncomputable def Θ₄_term (n : ℤ) (τ : ℍ) : ℂ := (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)

-- @@ L33-33 verbatim
noncomputable def Θ₂ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₂_term n τ

-- @@ L34-34 verbatim
noncomputable def Θ₃ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₃_term n τ

-- @@ L35-35 verbatim
noncomputable def Θ₄ (τ : ℍ) : ℂ := ∑' n : ℤ, Θ₄_term n τ

-- @@ L36-36 verbatim
noncomputable def H₂ (τ : ℍ) : ℂ := (Θ₂ τ) ^ 4

-- @@ L37-37 verbatim
noncomputable def H₃ (τ : ℍ) : ℂ := (Θ₃ τ) ^ 4

-- @@ L38-38 verbatim
noncomputable def H₄ (τ : ℍ) : ℂ := (Θ₄ τ) ^ 4


-- @@ L40-44 verbatim
/-- Theta functions as specializations of `jacobiTheta₂`. -/
theorem Θ₂_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₂_term n τ = cexp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [Θ₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf


-- @@ L46-47 verbatim
theorem Θ₂_as_jacobiTheta₂ (τ : ℍ) : Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  simp_rw [Θ₂, Θ₂_term_as_jacobiTheta₂_term, tsum_mul_left, jacobiTheta₂]


-- @@ L49-51 verbatim
theorem Θ₃_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₃_term n τ = jacobiTheta₂_term n 0 τ := by
  simp [Θ₃_term, jacobiTheta₂_term]


-- @@ L53-54 verbatim
theorem Θ₃_as_jacobiTheta₂ (τ : ℍ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, Θ₃_term_as_jacobiTheta₂_term, jacobiTheta₂]


-- @@ L56-59 verbatim
theorem Θ₄_term_as_jacobiTheta₂_term (τ : ℍ) (n : ℤ) :
    Θ₄_term n τ = jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [Θ₄_term, jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
  ring_nf


-- @@ L61-62 verbatim
theorem Θ₄_as_jacobiTheta₂ (τ : ℍ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, Θ₄_term_as_jacobiTheta₂_term, jacobiTheta₂]
