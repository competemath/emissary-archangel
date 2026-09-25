module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.Radial



-- @@ L6-17 verbatim
/-!
# Applying Laplace representations to `a`, `b`, and `f`

This file records the basic radial rewriting lemmas for `a`, `b`, and `f` in terms of the
one-variable profiles `aProfile` and `bProfile`. These rewrites are used when applying analytic
continuation formulas to prove the Cohn-Elkies sign conditions.

## Main statements
* `LaplaceTmp.LaplaceApply.a_apply`
* `LaplaceTmp.LaplaceApply.b_apply`
* `LaplaceTmp.LaplaceApply.f_apply`
-/


-- @@ L19-19 verbatim
namespace SpherePacking.Dim24.LaplaceTmp.LaplaceApply


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-25 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- Basic radial application lemmas for `a`, `b`, and `f`.


-- @@ L27-29 verbatim
/-- Rewrite `a x` in terms of the one-variable profile `aProfile`. -/
public lemma a_apply (x : ℝ²⁴) : a x = aProfile (‖x‖ ^ (2 : ℕ)) := by
  simp [Dim24.a, Dim24.aAux]


-- @@ L31-33 verbatim
/-- Rewrite `b x` in terms of the one-variable profile `bProfile`. -/
public lemma b_apply (x : ℝ²⁴) : b x = bProfile (‖x‖ ^ (2 : ℕ)) := by
  simp [Dim24.b]


-- @@ L35-40 verbatim
/-- Rewrite `f x` as a linear combination of `aProfile (‖x‖^2)` and `bProfile (‖x‖^2)`. -/
public lemma f_apply (x : ℝ²⁴) :
    f x =
      (- (Real.pi * Complex.I) / (113218560 : ℂ)) * aProfile (‖x‖ ^ (2 : ℕ)) -
        (Complex.I / ((262080 : ℂ) * Real.pi)) * bProfile (‖x‖ ^ (2 : ℕ)) := by
  simp [Dim24.f, a_apply, b_apply]


-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end SpherePacking.Dim24.LaplaceTmp.LaplaceApply
