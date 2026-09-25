module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Prelude
import SpherePacking.Contour.Segments



-- @@ L6-16 verbatim
/-!
# Curve-integral representations for `I₁'` through `I₄'`

We rewrite the real integrals `RealIntegrals.I₁'`, ..., `RealIntegrals.I₄'` as contour
integrals along straight segments in `ℂ`. These formulas are used in the contour deformation
step for the `I₁/I₂` and `I₃/I₄` permutation identities.

## Main statements
* `I₁'_eq_curveIntegral_segment`, `I₂'_eq_curveIntegral_segment`
* `I₃'_eq_curveIntegral_segment`, `I₄'_eq_curveIntegral_segment`
-/


-- @@ L18-18 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L20-20 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L21-21 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L22-22 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open MagicFunction.Parametrisations

-- @@ L27-27 verbatim
open MagicFunction

-- @@ L28-28 verbatim
open scoped Interval



-- @@ L31-47 verbatim
/-- `I₁' r` as a contour integral along the segment from `-1` to `-1 + i`. -/
public lemma I₁'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Φ₁' r) z) := by
  rw [RealIntegrals.I₁']
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' r)) (-1 : ℂ) ((-1 : ℂ) + Complex.I)]
  have hba : (((-1 : ℂ) + Complex.I) - (-1 : ℂ)) = (Complex.I : ℂ) :=
    SpherePacking.Contour.dir_z₁line
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le zero_le_one] using ht
  have hzlin : AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + Complex.I) t = z₁' t :=
    SpherePacking.Contour.lineMap_z₁_eq_z₁' (t := t) htIcc
  simp [scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₁, RealIntegrals.ComplexIntegrands.Φ₁',
    Φ₁', hba, hzlin]


-- @@ L49-65 verbatim
/-- `I₂' r` as a contour integral along the segment from `-1 + i` to `i`. -/
public lemma I₂'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Φ₁' r) z) := by
  rw [RealIntegrals.I₂']
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' r)) ((-1 : ℂ) + Complex.I) Complex.I]
  have hba : (Complex.I - ((-1 : ℂ) + Complex.I)) = (1 : ℂ) :=
    SpherePacking.Contour.dir_z₂line
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le zero_le_one] using ht
  have hzlin : AffineMap.lineMap ((-1 : ℂ) + Complex.I) Complex.I t = z₂' t :=
    SpherePacking.Contour.lineMap_z₂_eq_z₂' (t := t) htIcc
  simp [scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₂, RealIntegrals.ComplexIntegrands.Φ₂',
    RealIntegrals.ComplexIntegrands.Φ₁', Φ₁', hba, hzlin]


-- @@ L67-83 verbatim
/-- `I₃' r` as a contour integral along the segment from `1` to `1 + i`. -/
public lemma I₃'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₃' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (Φ₃' r) z) := by
  rw [RealIntegrals.I₃']
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₃' r)) (1 : ℂ) ((1 : ℂ) + Complex.I)]
  have hba : (((1 : ℂ) + Complex.I) - (1 : ℂ)) = (Complex.I : ℂ) :=
    SpherePacking.Contour.dir_z₃line
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le zero_le_one] using ht
  have hzlin : AffineMap.lineMap (1 : ℂ) ((1 : ℂ) + Complex.I) t = z₃' t :=
    SpherePacking.Contour.lineMap_z₃_eq_z₃' (t := t) htIcc
  simp [scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₃, RealIntegrals.ComplexIntegrands.Φ₃',
    Φ₃', hba, hzlin]


-- @@ L85-101 verbatim
/-- `I₄' r` as a contour integral along the segment from `1 + i` to `i`. -/
public lemma I₄'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Φ₃' r) z) := by
  rw [RealIntegrals.I₄']
  rw [curveIntegral_segment (ω := scalarOneForm (Φ₃' r)) ((1 : ℂ) + Complex.I) Complex.I]
  have hba : (Complex.I - ((1 : ℂ) + Complex.I)) = (-1 : ℂ) :=
    SpherePacking.Contour.dir_z₄line
  refine intervalIntegral.integral_congr (μ := (volume : Measure ℝ)) ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le zero_le_one] using ht
  have hzlin : AffineMap.lineMap ((1 : ℂ) + Complex.I) Complex.I t = z₄' t :=
    SpherePacking.Contour.lineMap_z₄_eq_z₄' (t := t) htIcc
  simp [scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₄, RealIntegrals.ComplexIntegrands.Φ₄',
    RealIntegrals.ComplexIntegrands.Φ₃', Φ₃', hba, hzlin]


-- @@ L103-110 verbatim
/-- A combined segment representation of `I₃' r + I₄' r`. -/
public lemma I₃'_add_I₄'_eq_curveIntegral_segments (r : ℝ) :
    RealIntegrals.I₃' r + RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
          scalarOneForm (Φ₃' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Φ₃' r) z := by
  simp [I₃'_eq_curveIntegral_segment (r := r), I₄'_eq_curveIntegral_segment (r := r)]



-- @@ L113-113 verbatim
end


-- @@ L115-115 verbatim
end SpherePacking.Dim24.AFourier
