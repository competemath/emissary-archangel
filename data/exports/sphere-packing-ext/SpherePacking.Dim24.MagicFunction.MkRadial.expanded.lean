module
public import SpherePacking.ForMathlib.RadialSchwartz.OneSided



-- @@ L5-9 verbatim
/-!
# Radial Schwartz-map constructor (dimension 24)

This is shared by both the `a`- and `b`-eigenfunction developments.
-/


-- @@ L11-11 verbatim
namespace SpherePacking.Dim24


-- @@ L13-13 verbatim
open scoped SchwartzMap

-- @@ L14-14 verbatim
open SchwartzMap


-- @@ L16-16 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-29 verbatim
/-- Build a radial Schwartz map on `ℝ²⁴` from a one-variable function.

The hypotheses ensure smoothness after multiplying by the cutoff function and provide
one-sided Schwartz decay on `x ≥ 0`. -/
@[expose] public def mkRadial (f : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ RadialSchwartz.cutoffC r * f r))
    (hdec : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ²⁴, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg
    (F := ℝ²⁴) f hg hdec


-- @@ L31-36 verbatim
@[simp] lemma mkRadial_apply (f : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ RadialSchwartz.cutoffC r * f r))
    (hdec : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (x : ℝ²⁴) :
    mkRadial f hg hdec x = f (‖x‖ ^ 2) := by
  simp [mkRadial]


-- @@ L38-38 verbatim
end


-- @@ L40-40 verbatim
end SpherePacking.Dim24
