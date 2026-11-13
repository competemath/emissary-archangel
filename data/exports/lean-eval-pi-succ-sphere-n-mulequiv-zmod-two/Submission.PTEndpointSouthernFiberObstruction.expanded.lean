import Mathlib
import Submission.EndpointPTCutoffExistence


-- @@ L4-15 verbatim
/-!
# A southern-fiber obstruction for endpoint PT cutoffs

The horizontal projection of a normalized endpoint Pontryagin--Thom collapse
has two sheets.  This file records a small but useful obstruction to deleting
the southern sheet by merely choosing a small nonzero horizontal target.

If a path starts on a positively labelled zero-fiber component, ends outside
the cutoff support, and its normalized horizontal coordinate remains on one
nonnegative meridian, then every nonzero target on that meridian of norm less
than one has a southern-sheet preimage along the path.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
open Set Function Metric

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L24-24 verbatim
variable {n : ℕ}


-- @@ L26-26 verbatim
namespace FiberSign.PTCutoff


-- @@ L28-28 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L31-31 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L33-96 verbatim
/-- A path from the positive fiber to the zero region of a PT cutoff, whose
normalized horizontal projection stays on a fixed nonnegative meridian, must
meet the southern point over every target of radius strictly between zero and
one on that meridian. -/
theorem exists_southPointOf_preimage_of_nonnegative_meridian
    (κ : PTCutoff S) (e : F) (he : ‖e‖ = 1) (γ : C(I, E))
    (hγ₀ : γ 0 ∈ S.positivePart) (hγ₁ : κ (γ 1) = 0)
    (hmeridian : ∀ t : I, ∃ a : ℝ, 0 ≤ a ∧
      initCLM n (sphereMap S κ (γ t) : E) = a • e)
    {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃ t : I, (sphereMap S κ (γ t) : E) = southPointOf (ρ • e) := by
  let v : I → ℝ := fun t => vertC (sphereMap S κ (γ t) : E)
  have hvcont : Continuous v := by
    dsimp [v]
    exact contDiff_vertC.continuous.comp
      (continuous_subtype_val.comp
        ((map_continuous (sphereMap S κ)).comp γ.continuous))
  have hv₀ : v 0 = 1 := by
    dsimp [v]
    rw [show sphereMap S κ (γ 0) =
        SignedFramedLevelCobordism.SignedSlabCutoff.signedPTNorthPole from
      sphereMap_of_positivePart S κ hγ₀]
    exact vertC_eLast
  have hv₁ : v 1 = -1 := by
    dsimp [v]
    rw [show sphereMap S κ (γ 1) = southPole n from
      sphereMap_of_zero S κ hγ₁]
    exact vertC_southPole
  have hrad : 0 < 1 - ρ ^ 2 := by nlinarith
  have hsqrt₀ : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.mpr hrad
  have hsqrtsq : (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 - ρ ^ 2 :=
    Real.sq_sqrt hrad.le
  let z : ℝ := -Real.sqrt (1 - ρ ^ 2)
  have hzmem : z ∈ Icc (v 1) (v 0) := by
    rw [hv₀, hv₁]
    dsimp [z]
    constructor <;> nlinarith
  obtain ⟨t, -, ht⟩ :=
    intermediate_value_Icc' (show (0 : I) ≤ 1 by simp)
      hvcont.continuousOn hzmem
  obtain ⟨a, ha₀, hinit⟩ := hmeridian t
  change vertC (sphereMap S κ (γ t) : E) = z at ht
  have hsplit := norm_sq_split (sphereMap S κ (γ t) : E)
  rw [UnitSphere.norm_coe, hinit, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ha₀, he, mul_one, ht] at hsplit
  have ha : a = ρ := by
    dsimp [z] at hsplit
    nlinarith
  have hinit_target :
      initCLM n (sphereMap S κ (γ t) : E) = ρ • e := by
    rw [hinit, ha]
  have hcases :=
    (init_eq_iff (UnitSphere.norm_coe (sphereMap S κ (γ t))) (ρ • e)).mp
      hinit_target
  have htarget_norm : ‖ρ • e‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_pos hρ₀]
  rcases hcases with hnorth | hsouth
  · have hnorthpos : 0 < vertC (northPoint (ρ • e)) :=
      vertC_northPoint_pos (by rw [htarget_norm]; exact hρ₁)
    have hvert := ht
    rw [hnorth] at hvert
    dsimp [z] at hvert
    nlinarith
  · exact ⟨t, hsouth⟩


-- @@ L98-110 verbatim
/-- It is enough to check the meridian condition before normalization, on the
defining map of the framed level set. -/
lemma normalized_nonnegative_meridian_of_levelMap
    (κ : PTCutoff S) (e : F) {x : E} {c : ℝ} (hc : 0 ≤ c)
    (hg : X.g x = c • e) :
    ∃ a : ℝ, 0 ≤ a ∧
      initCLM n (sphereMap S κ x : E) = a • e := by
  let a : ℝ := (‖raw S κ x‖⁻¹ * κ x) * c
  refine ⟨a, ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (κ.range x).1) hc
  · change normalizedHorizontalRaw S κ x = a • e
    rw [normalizedHorizontalRaw_eq S κ x, hg, smul_smul]


-- @@ L112-112 verbatim
end FiberSign.PTCutoff


-- @@ L114-114 verbatim
end Submission
