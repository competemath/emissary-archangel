module
public import Mathlib.Analysis.InnerProductSpace.PiL2



-- @@ L5-17 verbatim
/-!
# Radialization helpers

These definitions are only meant to provide a convenient bridge between the paper's
one-variable notation `r ↦ g(r)` (with `r = ‖x‖`) and the Lean functions `g : ℝ²⁴ → ℂ`.

We model the one-variable profile by restricting to the first coordinate axis:
`r ↦ g(axisVec r)`.

## Main definitions
* `axisVec`
* `radialProfile`
-/


-- @@ L19-19 verbatim
namespace SpherePacking.Dim24


-- @@ L21-26 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-
We work in a `noncomputable` section: this file is purely analytic and not intended
for computation.
-/

-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-32 verbatim
/-- The first axis vector `(r, 0, 0, ..., 0) ∈ ℝ²⁴`. -/
@[expose]
public noncomputable def axisVec (r : ℝ) : ℝ²⁴ :=
  EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 24) 0 r


-- @@ L34-36 verbatim
/-- The axis vector at `0` is `0`. -/
@[simp] public lemma axisVec_zero : axisVec (0 : ℝ) = 0 := by
  simp [axisVec]


-- @@ L38-41 verbatim
/-- The squared norm of `axisVec r` is `r ^ 2` (as a natural power). -/
public lemma norm_axisVec_sq (r : ℝ) : ‖axisVec r‖ ^ (2 : ℕ) = r ^ (2 : ℕ) := by
  -- `axisVec r = (r,0,...,0)`, so its Euclidean norm is `‖r‖`.
  simp [axisVec]


-- @@ L43-46 verbatim
/-- Restrict a function on `ℝ²⁴` to the first axis, to obtain a one-variable radial profile. -/
@[expose]
public noncomputable def radialProfile {α : Type*} (g : ℝ²⁴ → α) (r : ℝ) : α :=
  g (axisVec r)


-- @@ L48-50 verbatim
/-- Unfolding lemma for `radialProfile`. -/
@[simp] public lemma radialProfile_apply {α : Type*} (g : ℝ²⁴ → α) (r : ℝ) :
    radialProfile g r = g (axisVec r) := rfl


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end SpherePacking.Dim24
