import Mathlib
import Submission.NormalizeMoves
import Submission.PTRelativeTransversality
import Submission.SignedPTCobordism


-- @@ L6-19 verbatim
/-!
# A signed PT slab as a smooth collared sphere homotopy

`SignedSlabCutoff.slabPTCM` is naturally defined only on `I × E`.  Relative
transversality, on the other hand, consumes a smooth sphere map on the whole
space-time vector space, constant on the two infinite time collars.  The
collar-flat ramp gives the missing adapter: first retract the time coordinate
smoothly to `[0,1]`, then normalize the already nonvanishing signed PT raw
vector.

The compact support of the slab cutoff also gives a spatially uniform south
pole exterior after this retraction.  Thus no additional compactness or
transversality assumption is hidden in the adapter.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
open Set Function Metric

-- @@ L28-28 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L30-30 verbatim
variable {n : ℕ}

-- @@ L31-31 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L32-32 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L34-34 verbatim
namespace SignedFramedLevelCobordism.SignedSlabCutoff


-- @@ L36-36 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L37-37 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L39-39 verbatim
variable (C : SignedFramedLevelCobordism S₀ S₁)

-- @@ L40-40 verbatim
variable (χ : SignedSlabCutoff C)


-- @@ L42-45 verbatim
/-- Smoothly retract the unrestricted time coordinate to the PT slab. -/
def collaredSpaceTime (_C : SignedFramedLevelCobordism S₀ S₁)
    (_χ : SignedSlabCutoff _C) (v : A) : A :=
  spaceTime (initCLM (n + 1) v) (normRamp (vertC v))


-- @@ L47-49 verbatim
@[simp] lemma initCLM_collaredSpaceTime (v : A) :
    initCLM (n + 1) (collaredSpaceTime C χ v) = initCLM (n + 1) v := by
  simp [collaredSpaceTime, initCLM_spaceTime]


-- @@ L51-53 verbatim
@[simp] lemma vertC_collaredSpaceTime (v : A) :
    vertC (collaredSpaceTime C χ v) = normRamp (vertC v) := by
  simp [collaredSpaceTime, vertC_spaceTime]


-- @@ L55-63 verbatim
lemma contDiff_collaredSpaceTime : ContDiff ℝ ∞ (collaredSpaceTime C χ) := by
  have heq : collaredSpaceTime C χ = fun v : A =>
      embedCLM (n + 1) (initCLM (n + 1) v) +
        normRamp (vertC v) • eLast (n + 1) := by
    funext v
    exact spaceTime_eq_affine _ _
  rw [heq]
  exact ((embedCLM (n + 1)).contDiff.comp (initCLM (n + 1)).contDiff).add
    ((contDiff_normRamp.comp contDiff_vertC).smul contDiff_const)


-- @@ L65-68 verbatim
lemma collaredSpaceTime_mem_timeSlab (v : A) :
    vertC (collaredSpaceTime C χ v) ∈ Icc (0 : ℝ) 1 := by
  rw [vertC_collaredSpaceTime]
  exact ⟨normRamp_nonneg _, normRamp_le_one _⟩


-- @@ L70-72 verbatim
/-- The globally nonvanishing raw PT vector after smooth time retraction. -/
def collaredRaw (v : A) : E :=
  raw C χ (collaredSpaceTime C χ v)


-- @@ L74-75 verbatim
lemma contDiff_collaredRaw : ContDiff ℝ ∞ (collaredRaw C χ) :=
  (contDiff_raw C χ).comp (contDiff_collaredSpaceTime C χ)


-- @@ L77-78 verbatim
lemma collaredRaw_ne_zero (v : A) : collaredRaw C χ v ≠ 0 :=
  raw_ne_zero_of_mem_timeSlab C χ (collaredSpaceTime_mem_timeSlab C χ v)


-- @@ L80-82 verbatim
/-- Ambient representative of the normalized collared PT map. -/
def collaredSphereVec (v : A) : E :=
  ‖collaredRaw C χ v‖⁻¹ • collaredRaw C χ v


-- @@ L84-85 verbatim
lemma norm_collaredSphereVec (v : A) : ‖collaredSphereVec C χ v‖ = 1 := by
  exact norm_normalize (collaredRaw_ne_zero C χ v)


-- @@ L87-94 verbatim
lemma contDiff_collaredSphereVec : ContDiff ℝ ∞ (collaredSphereVec C χ) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  have hr : ContDiffAt ℝ ∞ (collaredRaw C χ) v :=
    (contDiff_collaredRaw C χ).contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun q => ‖collaredRaw C χ q‖) v :=
    hr.norm ℝ (collaredRaw_ne_zero C χ v)
  exact (hn.inv (norm_ne_zero_iff.mpr (collaredRaw_ne_zero C χ v))).smul hr


-- @@ L96-99 verbatim
/-- The actual sphere-valued map on unrestricted space-time. -/
def collaredSphere (v : A) : UnitSphere E :=
  ⟨collaredSphereVec C χ v,
    mem_sphere_zero_iff_norm.mpr (norm_collaredSphereVec C χ v)⟩


-- @@ L101-102 verbatim
@[simp] lemma collaredSphere_coe (v : A) :
    (collaredSphere C χ v : E) = collaredSphereVec C χ v := rfl


-- @@ L104-128 verbatim
/-- Compact support of the slab selector becomes a spatially uniform exact
south-pole exterior, uniformly over the unrestricted time variable. -/
lemma collaredSphere_exterior_south :
    ∃ R : ℝ, ∀ v : A,
      R < ‖initCLM (n + 1) v‖ → collaredSphere C χ v = southPole n := by
  obtain ⟨R, hR⟩ := χ.compact_support.isBounded.subset_closedBall (0 : A)
  refine ⟨R, ?_⟩
  intro v hv
  let q := collaredSpaceTime C χ v
  have hχq : χ q = 0 := by
    by_contra hne
    have hqmem : q ∈ tsupport χ := subset_tsupport χ hne
    have hqball := hR hqmem
    rw [mem_closedBall, dist_zero_right] at hqball
    have hsplit := norm_sq_split q
    have hinit : initCLM (n + 1) q = initCLM (n + 1) v := by
      simpa [q] using initCLM_collaredSpaceTime C χ v
    rw [hinit] at hsplit
    nlinarith [norm_nonneg q, norm_nonneg (initCLM (n + 1) v),
      sq_nonneg (vertC q)]
  apply Subtype.ext
  change collaredSphereVec C χ v = (-eLast n : E)
  have hraw : collaredRaw C χ v = -eLast n := by
    simp [collaredRaw, raw, q, hχq]
  rw [collaredSphereVec, hraw, norm_neg, norm_eLast, inv_one, one_smul]


-- @@ L130-138 verbatim
lemma collaredSphere_collar_zero (x : E) (t : ℝ) (ht : t ≤ 1 / 4) :
    collaredSphere C χ (spaceTime x t) =
      collaredSphere C χ (spaceTime x 0) := by
  apply Subtype.ext
  change collaredSphereVec C χ (spaceTime x t) =
    collaredSphereVec C χ (spaceTime x 0)
  simp [collaredSphereVec, collaredRaw, collaredSpaceTime,
    vertC_spaceTime, initCLM_spaceTime, normRamp_of_le_quarter ht,
    normRamp_of_le_quarter (by norm_num : (0 : ℝ) ≤ 1 / 4)]


-- @@ L140-148 verbatim
lemma collaredSphere_collar_one (x : E) (t : ℝ) (ht : 3 / 4 ≤ t) :
    collaredSphere C χ (spaceTime x t) =
      collaredSphere C χ (spaceTime x 1) := by
  apply Subtype.ext
  change collaredSphereVec C χ (spaceTime x t) =
    collaredSphereVec C χ (spaceTime x 1)
  simp [collaredSphereVec, collaredRaw, collaredSpaceTime,
    vertC_spaceTime, initCLM_spaceTime, normRamp_of_three_quarter_le ht,
    normRamp_of_three_quarter_le (by norm_num : (3 / 4 : ℝ) ≤ 1)]


-- @@ L150-157 verbatim
/-- A signed PT slab cutoff supplies the full smooth relative-transversality
input, not merely a continuous homotopy on `I × E`. -/
def toCollaredSphereHomotopy : CollaredSphereHomotopy n where
  sphere := collaredSphere C χ
  smooth := contDiff_collaredSphereVec C χ
  exterior_south := collaredSphere_exterior_south C χ
  collar_zero := collaredSphere_collar_zero C χ
  collar_one := collaredSphere_collar_one C χ


-- @@ L159-159 verbatim
end SignedFramedLevelCobordism.SignedSlabCutoff


-- @@ L161-161 verbatim
end Submission
