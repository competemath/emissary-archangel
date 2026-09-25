module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.AtZero
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge.HarmonicMeanZero24Gauss


-- @@ L7-15 verbatim
/-!
# Mean-zero bridge: mean-value at the origin

This step file isolates the mean-value statement for harmonic polynomials at the origin, phrased
in terms of `sphereAvg24`.

## Main statements
* `MeanZeroHarmonics24Steps.sphereAvg24_eq_evalPk24_at_zero_of_harmonic_step`
-/


-- @@ L17-17 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L23-23 verbatim
open Uniqueness.BS81.LP


-- @@ L25-25 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L27-27 verbatim
namespace MeanZeroHarmonics24Steps


-- @@ L29-69 verbatim
/-- Mean-value property at the origin, phrased using `sphereAvg24` and `evalPk24`. -/
public theorem sphereAvg24_eq_evalPk24_at_zero_of_harmonic_step
    (k : ℕ) (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.Harm k) :
    sphereAvg24 (fun x : ℝ²⁴ =>
      evalPk24 (k := k) (y := x)
        (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) =
      evalPk24 (k := k) (y := (0 : ℝ²⁴))
        (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) := by
  by_cases hk0 : k = 0
  · subst hk0
    -- Degree `0` homogeneous polynomials are constant, so both sides are that constant.
    set p : MvPolynomial (Fin 24) ℝ :=
      (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk 0).1
    have hpHom : p.IsHomogeneous 0 := by
      simpa [p] using
        (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 24) (R := ℝ) 0 (p := p)).1
          (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk 0).2
    have hpC : p = MvPolynomial.C (p.coeff 0) := by
      have : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).2 hpHom
      simpa using (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := p)).1 this
    have hconst (x : ℝ²⁴) :
        evalPk24 (k := 0) (y := x)
            (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk 0) = p.coeff 0 := by
      -- Avoid looping `simp` rewrites through `p.coeff 0`.
      change evalPoly24 (y := x) p = p.coeff 0
      unfold evalPoly24
      rw [hpC]
      simp
    simp [hconst, sphereAvg24_const]
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    have hR :
        evalPk24 (k := k) (y := (0 : ℝ²⁴))
            (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) = 0 :=
      evalPk24_at_zero_eq_zero_of_degree_pos_step k hk1 ↑h
    have hL :
        sphereAvg24 (fun x : ℝ²⁴ =>
          evalPk24 (k := k) (y := x)
            (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) = 0 := by
      simpa using
        (sphereAvg24_harmonic_degree_pos_eq_zero_gauss (k := k) hk1 h)
    simp [hL, hR]


-- @@ L71-71 verbatim
end MeanZeroHarmonics24Steps

-- @@ L72-72 verbatim
end


-- @@ L74-74 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
