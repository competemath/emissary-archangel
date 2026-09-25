module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Kissing.Normalize


-- @@ L6-19 verbatim
/-!
# From kissing configurations to spherical codes in dimension 24

We scale a kissing configuration `X ⊆ ℝ²⁴` by `1/2` to obtain a `(24, M, 1/2)` spherical code.
This is the normalization step connecting the repo's `IsKissingConfiguration` interface with the
BS81 theorems stated for `(24, M, 1/2)` spherical codes on `Ω₂₄`.

## Main statements
* `normalizeKissing_isSphericalCode24`
* `ncard_normalizeKissing_eq`

## References
* `paper/BS81/sources.tex`, Theorem 1 and §4 (we use only the rescaling by `1/2`).
-/


-- @@ L21-21 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open scoped RealInnerProductSpace

-- @@ L26-28 verbatim
open Uniqueness.RigidityClassify.CE
  (IsKissingConfiguration normalizeKissing norm_normalize_eq_one_of_norm_eq_two
    inner_normalize_le_half_of_norm_eq_two_of_norm_sub_ge_two)


-- @@ L30-30 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L32-53 verbatim
/-- Normalizing a kissing configuration in `ℝ²⁴` yields a `(24, M, 1/2)` spherical code. -/
public theorem normalizeKissing_isSphericalCode24
    (X : Set ℝ²⁴) (hX : IsKissingConfiguration X) :
    IsSphericalCode 24 (normalizeKissing X) (1 / 2 : ℝ) := by
  refine ⟨?finite, ?norm_one, ?inner_le⟩
  · -- `normalizeKissing X` is the image of a finite set.
    have hfin : X.Finite := Set.finite_coe_iff.mp hX.1
    simpa [normalizeKissing] using hfin.image (fun x : ℝ²⁴ => (1 / 2 : ℝ) • x)
  · intro u hu
    rcases hu with ⟨x, hxX, rfl⟩
    exact norm_normalize_eq_one_of_norm_eq_two (hx := hX.2.1 x hxX)
  · intro u v hu hv huv
    rcases hu with ⟨x, hxX, rfl⟩
    rcases hv with ⟨y, hyX, rfl⟩
    have hne : x ≠ y := by
      intro hxy
      apply huv
      simp [hxy]
    have hdist : (2 : ℝ) ≤ ‖x - y‖ := hX.2.2 hxX hyX hne
    exact
      inner_normalize_le_half_of_norm_eq_two_of_norm_sub_ge_two
        (x := x) (y := y) (hX.2.1 x hxX) (hX.2.1 y hyX) hdist


-- @@ L55-63 verbatim
/-- Scaling by `1/2` is injective, so `normalizeKissing` preserves `Set.ncard`. -/
public theorem ncard_normalizeKissing_eq
    (X : Set ℝ²⁴) :
    Set.ncard (normalizeKissing X) = Set.ncard X := by
  have hinj : Function.Injective (fun x : ℝ²⁴ => (1 / 2 : ℝ) • x) := by
    intro x y hxy
    exact (IsUnit.smul_left_cancel (a := (1 / 2 : ℝ)) (isUnit_iff_ne_zero.2 (by simp))).1 hxy
  simpa [normalizeKissing] using
    Set.ncard_image_of_injective (s := X) (f := fun x : ℝ²⁴ => (1 / 2 : ℝ) • x) hinj


-- @@ L65-65 verbatim
end


-- @@ L67-67 verbatim
end SpherePacking.Dim24.Uniqueness.BS81
