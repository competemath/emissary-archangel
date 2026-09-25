module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs


-- @@ L7-23 verbatim
/-!
# Normalizing kissing configurations

This is the first step towards the Bannai-Sloane uniqueness theorem: we convert a kissing
configuration on the radius-`2` sphere to a spherical code on the unit sphere by scaling by
`1 / 2`.

The key estimates are that norms become `1` and that pairwise inner products are bounded by
`1 / 2` under the kissing-configuration separation condition.

## Main definitions
* `Uniqueness.RigidityClassify.CE.normalizeKissing`

## Main statements
* `Uniqueness.RigidityClassify.CE.norm_normalize_eq_one_of_norm_eq_two`
* `Uniqueness.RigidityClassify.CE.inner_normalize_le_half_of_norm_eq_two_of_norm_sub_ge_two`
-/



-- @@ L26-26 verbatim
namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Pointwise


-- @@ L32-32 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L34-37 verbatim
/-- The normalized unit-sphere code associated to a radius-2 configuration `X`: scale by `1/2`. -/
@[expose]
public def normalizeKissing (X : Set ℝ²⁴) : Set ℝ²⁴ :=
  (fun x : ℝ²⁴ => (1 / 2 : ℝ) • x) '' X


-- @@ L39-42 verbatim
/-- Membership in `normalizeKissing` is membership in the image under scaling by `1 / 2`. -/
@[simp] public lemma mem_normalizeKissing {X : Set ℝ²⁴} {y : ℝ²⁴} :
    y ∈ normalizeKissing X ↔ ∃ x ∈ X, (1 / 2 : ℝ) • x = y := by
  rfl


-- @@ L44-50 verbatim
/-- If `‖x‖ = 2`, then `‖(1/2) • x‖ = 1`. -/
public lemma norm_normalize_eq_one_of_norm_eq_two {x : ℝ²⁴} (hx : ‖x‖ = (2 : ℝ)) :
    ‖(1 / 2 : ℝ) • x‖ = (1 : ℝ) := by
  calc
    ‖(1 / 2 : ℝ) • x‖ = |(1 / 2 : ℝ)| * ‖x‖ := by simp [norm_smul]
    _ = (1 / 2 : ℝ) * (2 : ℝ) := by simp [hx]
    _ = (1 : ℝ) := by norm_num


-- @@ L52-88 verbatim
/--
If `‖x‖ = ‖y‖ = 2` and `‖x - y‖ ≥ 2`, then the normalized inner product is at most `1 / 2`.
-/
public lemma inner_normalize_le_half_of_norm_eq_two_of_norm_sub_ge_two
    {x y : ℝ²⁴} (hx : ‖x‖ = (2 : ℝ)) (hy : ‖y‖ = (2 : ℝ)) (hxy : (2 : ℝ) ≤ ‖x - y‖) :
    (⟪(1 / 2 : ℝ) • x, (1 / 2 : ℝ) • y⟫ : ℝ) ≤ (1 / 2 : ℝ) := by
  -- Work with squared distances.
  have hxy2 : (4 : ℝ) ≤ ‖x - y‖ ^ 2 := by
    -- `2 ≤ ‖x-y‖` ⇒ `4 ≤ ‖x-y‖^2`
    nlinarith
  -- Expand `‖x-y‖^2` and solve for `⟪x,y⟫`.
  have hsub :
      ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (⟪x, y⟫ : ℝ) + ‖y‖ ^ 2 := by
    -- `norm_sub_sq_real` is the polarization identity.
    simpa using norm_sub_sq_real x y
  have hinner : (⟪x, y⟫ : ℝ) ≤ (2 : ℝ) := by
    -- Plug in `‖x‖=‖y‖=2` and use `‖x-y‖^2 ≥ 4`.
    have hx2 : ‖x‖ ^ 2 = (4 : ℝ) := by nlinarith [hx]
    have hy2 : ‖y‖ ^ 2 = (4 : ℝ) := by nlinarith [hy]
    -- `4 ≤ (4 - 2⟪x,y⟫ + 4)` ⇒ `⟪x,y⟫ ≤ 2`.
    nlinarith [hxy2, hsub, hx2, hy2]
  -- Scale the inner product.
  -- `⟪(1/2)x,(1/2)y⟫ = (1/4)⟪x,y⟫ ≤ 1/2`.
  have hscale :
      (⟪(1 / 2 : ℝ) • x, (1 / 2 : ℝ) • y⟫ : ℝ) = (1 / 4 : ℝ) * (⟪x, y⟫ : ℝ) := by
    have h1 :
        (⟪(1 / 2 : ℝ) • x, (1 / 2 : ℝ) • y⟫ : ℝ) =
          (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ * (⟪x, y⟫ : ℝ)) := by
      simp [one_div, real_inner_smul_left, real_inner_smul_right]
    have hmul : (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ := by norm_num
    calc
      (⟪(1 / 2 : ℝ) • x, (1 / 2 : ℝ) • y⟫ : ℝ)
          = (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ * (⟪x, y⟫ : ℝ)) := h1
      _ = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) * (⟪x, y⟫ : ℝ) := by ring_nf
      _ = (4 : ℝ)⁻¹ * (⟪x, y⟫ : ℝ) := by simp [hmul]
      _ = (1 / 4 : ℝ) * (⟪x, y⟫ : ℝ) := by norm_num
  nlinarith [hinner, hscale]


-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
