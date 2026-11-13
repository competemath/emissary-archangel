import Mathlib
import Submission.FiberSign
import Submission.MorsePerturb
import Submission.SphereClose


-- @@ L6-19 verbatim
/-!
# A signed Pontryagin--Thom collapse over a cobordism slab

The sign on a framed cobordism separates its compact slab fiber into a positive
and a negative part.  This file constructs a compactly supported smooth cutoff
which is exactly one on the positive part and exactly zero on the negative part.
The associated raw Thom vector cannot vanish anywhere over the time slab: a zero
would force both the defining map and the last coordinate to vanish, hence force
the cutoff to be `1/2` at a signed zero-fiber point, contradicting its prescribed
value there.

This is the global nonvanishing input needed to turn the local Morse-event models
into a sphere-valued Pontryagin--Thom homotopy.
-/


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
open Set Function Metric

-- @@ L26-26 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
namespace SignedFramedLevelCobordism


-- @@ L32-33 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L35-35 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L36-36 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)

-- @@ L37-37 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L39-43 verbatim
/-- The time-slab fiber is closed. -/
lemma isClosed_cobordismFiber : IsClosed C.cobordism.fiber := by
  rw [FramedLevelCobordism.fiber]
  exact (isClosed_singleton.preimage C.cobordism.smooth.continuous).inter
    (isClosed_Icc.preimage contDiff_vertC.continuous)


-- @@ L45-48 verbatim
/-- The time-slab fiber is compact. -/
lemma isCompact_cobordismFiber : IsCompact C.cobordism.fiber :=
  Metric.isCompact_of_isClosed_isBounded C.isClosed_cobordismFiber
    C.cobordism.isBounded_fiber


-- @@ L50-54 verbatim
/-- The closed positive part of the signed zero fiber in the time slab.  The
weak inequality is equivalent to strict positivity because the sign is nonzero
on the zero fiber. -/
def positiveSlabFiber : Set A :=
  {v | v ∈ C.cobordism.fiber ∧ 0 ≤ C v}


-- @@ L56-58 verbatim
/-- The closed negative part of the signed zero fiber in the time slab. -/
def negativeSlabFiber : Set A :=
  {v | v ∈ C.cobordism.fiber ∧ C v ≤ 0}


-- @@ L60-62 verbatim
lemma isClosed_positiveSlabFiber : IsClosed C.positiveSlabFiber := by
  rw [positiveSlabFiber]
  exact C.isClosed_cobordismFiber.inter (isClosed_Ici.preimage C.continuous)


-- @@ L64-66 verbatim
lemma isClosed_negativeSlabFiber : IsClosed C.negativeSlabFiber := by
  rw [negativeSlabFiber]
  exact C.isClosed_cobordismFiber.inter (isClosed_Iic.preimage C.continuous)


-- @@ L68-70 verbatim
lemma isCompact_positiveSlabFiber : IsCompact C.positiveSlabFiber :=
  C.isCompact_cobordismFiber.of_isClosed_subset
    C.isClosed_positiveSlabFiber (fun _ hv => hv.1)


-- @@ L72-74 verbatim
lemma isCompact_negativeSlabFiber : IsCompact C.negativeSlabFiber :=
  C.isCompact_cobordismFiber.of_isClosed_subset
    C.isClosed_negativeSlabFiber (fun _ hv => hv.1)


-- @@ L76-81 verbatim
lemma disjoint_signedSlabFibers :
    Disjoint C.positiveSlabFiber C.negativeSlabFiber := by
  rw [Set.disjoint_left]
  rintro v ⟨hv, hp⟩ ⟨-, hn⟩
  have hz : C v = 0 := le_antisymm hn hp
  exact C.nonzero v hv.1 hz


-- @@ L83-91 verbatim
/-- A compactly supported smooth scalar which selects precisely the positive
part of the signed slab fiber. -/
structure SignedSlabCutoff where
  toFun : A → ℝ
  smooth : ContDiff ℝ ∞ toFun
  range : ∀ v, toFun v ∈ Icc (0 : ℝ) 1
  positive_one : ∀ v ∈ C.positiveSlabFiber, toFun v = 1
  negative_zero : ∀ v ∈ C.negativeSlabFiber, toFun v = 0
  compact_support : HasCompactSupport toFun


-- @@ L93-93 verbatim
namespace SignedSlabCutoff


-- @@ L95-96 verbatim
instance : CoeFun (SignedSlabCutoff C) fun _ => A → ℝ :=
  ⟨SignedSlabCutoff.toFun⟩


-- @@ L98-121 verbatim
/-- Smooth Urysohn separation of the two signed pieces, with compact support. -/
theorem nonempty : Nonempty (SignedSlabCutoff C) := by
  have hopen : IsOpen C.negativeSlabFiberᶜ :=
    C.isClosed_negativeSlabFiber.isOpen_compl
  have hsub : C.positiveSlabFiber ⊆ C.negativeSlabFiberᶜ := by
    intro v hp hn
    exact Set.disjoint_left.mp C.disjoint_signedSlabFibers hp hn
  obtain ⟨δ, hδpos, hδsub⟩ :=
    C.isCompact_positiveSlabFiber.exists_cthickening_subset_open hopen hsub
  let U : Set A := Metric.thickening δ C.positiveSlabFiber
  have hKU : C.positiveSlabFiber ⊆ U :=
    Metric.self_subset_thickening hδpos _
  have hUc : IsCompact (closure U) := by
    apply IsCompact.of_isClosed_subset C.isCompact_positiveSlabFiber.cthickening
      isClosed_closure
    exact closure_minimal
      (Metric.thickening_subset_cthickening _ _) Metric.isClosed_cthickening
  obtain ⟨χ⟩ := SmoothCutoff.exists_of_isClosed_isOpen
    C.isClosed_positiveSlabFiber Metric.isOpen_thickening hKU hUc
  refine ⟨⟨χ, χ.smooth, χ.range, χ.eq_one, ?_, χ.compact_support⟩⟩
  intro v hv
  apply χ.eq_zero
  intro hvU
  exact hδsub (Metric.thickening_subset_cthickening _ _ hvU) hv


-- @@ L123-127 verbatim
/-- The unnormalized signed Thom vector.  Its horizontal component is the
defining map multiplied by the positive cutoff, and its last coordinate moves
from the south pole (`χ = 0`) to the north pole (`χ = 1`). -/
def raw (χ : SignedSlabCutoff C) (v : A) : E :=
  χ v • embedCLM n (C.cobordism.G v) + (2 * χ v - 1) • eLast n


-- @@ L129-132 verbatim
lemma raw_last (χ : SignedSlabCutoff C) (v : A) :
    raw C χ v (Fin.last n) = 2 * χ v - 1 := by
  rw [raw]
  simp [embedCLM_apply_last, eLast]


-- @@ L134-137 verbatim
lemma initCLM_raw (χ : SignedSlabCutoff C) (v : A) :
    initCLM n (raw C χ v) = χ v • C.cobordism.G v := by
  rw [raw, map_add, map_smul, map_smul, initCLM_embedCLM, initCLM_eLast,
    smul_zero, add_zero]


-- @@ L139-141 verbatim
lemma contDiff_raw (χ : SignedSlabCutoff C) : ContDiff ℝ ∞ (raw C χ) := by
  exact (χ.smooth.smul ((embedCLM n).contDiff.comp C.cobordism.smooth)).add
    (((contDiff_const.mul χ.smooth).sub contDiff_const).smul contDiff_const)


-- @@ L143-163 verbatim
/-- The signed Thom vector is nonzero at every point whose time coordinate lies
in `[0,1]`. -/
lemma raw_ne_zero_of_mem_timeSlab (χ : SignedSlabCutoff C) {v : A}
    (hv : vertC v ∈ Icc (0 : ℝ) 1) : raw C χ v ≠ 0 := by
  intro hzero
  have hlast := congrArg (fun z : E => z (Fin.last n)) hzero
  rw [raw_last C χ, PiLp.zero_apply] at hlast
  have hχ : χ v = 1 / 2 := by linarith
  have hhoriz := congrArg (initCLM n) hzero
  rw [initCLM_raw C χ, map_zero] at hhoriz
  have hχ0 : χ v ≠ 0 := by rw [hχ]; norm_num
  have hG : C.cobordism.G v = 0 := (smul_eq_zero.mp hhoriz).resolve_left hχ0
  have hvfib : v ∈ C.cobordism.fiber := ⟨hG, hv.1, hv.2⟩
  rcases lt_trichotomy (C v) 0 with hneg | heq | hpos
  · have hz := χ.negative_zero v ⟨hvfib, hneg.le⟩
    rw [hχ] at hz
    norm_num at hz
  · exact C.nonzero v hG heq
  · have ho := χ.positive_one v ⟨hvfib, hpos.le⟩
    rw [hχ] at ho
    norm_num at ho


-- @@ L165-168 verbatim
lemma raw_of_positiveFiber (χ : SignedSlabCutoff C) {v : A}
    (hv : v ∈ C.positiveSlabFiber) : raw C χ v = eLast n := by
  simp [raw, χ.positive_one v hv, hv.1.1]
  norm_num


-- @@ L170-172 verbatim
lemma raw_of_negativeFiber (χ : SignedSlabCutoff C) {v : A}
    (hv : v ∈ C.negativeSlabFiber) : raw C χ v = -eLast n := by
  simp [raw, χ.negative_zero v hv]


-- @@ L174-179 verbatim
lemma raw_of_not_mem_tsupport (χ : SignedSlabCutoff C) {v : A}
    (hv : v ∉ tsupport χ) : raw C χ v = -eLast n := by
  have hχ : χ v = 0 := by
    by_contra h
    exact hv (subset_tsupport χ h)
  simp [raw, hχ]


-- @@ L181-181 verbatim
/-! ## Framing on the positive fiber -/


-- @@ L183-199 verbatim
/-- Before normalization, the horizontal derivative on the positive fiber is
exactly the original cobordism framing. -/
theorem fderiv_initCLM_raw_of_positiveFiber (χ : SignedSlabCutoff C) {v : A}
    (hv : v ∈ C.positiveSlabFiber) :
    fderiv ℝ (fun q => initCLM n (raw C χ q)) v =
      fderiv ℝ C.cobordism.G v := by
  have hfun : (fun q => initCLM n (raw C χ q)) =
      fun q => χ q • C.cobordism.G q := by
    funext q
    exact initCLM_raw C χ q
  rw [hfun]
  have hχd : DifferentiableAt ℝ χ v :=
    χ.smooth.differentiable infty_ne_zero |>.differentiableAt
  have hGd : DifferentiableAt ℝ C.cobordism.G v :=
    C.cobordism.smooth.differentiable infty_ne_zero |>.differentiableAt
  rw [fderiv_fun_smul hχd hGd, hv.1.1, χ.positive_one v hv]
  simp


-- @@ L201-203 verbatim
/-- Horizontal north-pole coordinates of the normalized signed raw vector. -/
def normalizedHorizontalRaw (χ : SignedSlabCutoff C) (v : A) : F :=
  initCLM n (‖raw C χ v‖⁻¹ • raw C χ v)


-- @@ L205-208 verbatim
lemma normalizedHorizontalRaw_eq (χ : SignedSlabCutoff C) (v : A) :
    normalizedHorizontalRaw C χ v =
      (‖raw C χ v‖⁻¹ * χ v) • C.cobordism.G v := by
  rw [normalizedHorizontalRaw, map_smul, initCLM_raw C χ, smul_smul]


-- @@ L210-235 verbatim
/-- Normalization leaves the horizontal framing unchanged on the positive
fiber; the radial derivative only affects the last target coordinate. -/
theorem fderiv_normalizedHorizontalRaw_of_positiveFiber
    (χ : SignedSlabCutoff C) {v : A} (hv : v ∈ C.positiveSlabFiber) :
    fderiv ℝ (normalizedHorizontalRaw C χ) v =
      fderiv ℝ C.cobordism.G v := by
  have hfun : normalizedHorizontalRaw C χ = fun q =>
      (‖raw C χ q‖⁻¹ * χ q) • C.cobordism.G q := by
    funext q
    exact normalizedHorizontalRaw_eq C χ q
  rw [hfun]
  have hraw0 : raw C χ v ≠ 0 := by
    rw [raw_of_positiveFiber C χ hv]
    exact (norm_ne_zero_iff.mp (by rw [norm_eLast]; norm_num))
  have hrnorm : DifferentiableAt ℝ (fun q => ‖raw C χ q‖) v :=
    (contDiff_raw C χ).differentiable infty_ne_zero |>.differentiableAt |>.norm
      ℝ hraw0
  have hscalar : DifferentiableAt ℝ
      (fun q => ‖raw C χ q‖⁻¹ * χ q) v :=
    (hrnorm.inv (norm_ne_zero_iff.mpr hraw0)).mul
      (χ.smooth.differentiable infty_ne_zero |>.differentiableAt)
  have hGd : DifferentiableAt ℝ C.cobordism.G v :=
    C.cobordism.smooth.differentiable infty_ne_zero |>.differentiableAt
  rw [fderiv_fun_smul hscalar hGd, hv.1.1,
    raw_of_positiveFiber C χ hv, norm_eLast, χ.positive_one v hv]
  simp


-- @@ L237-241 verbatim
theorem surjective_fderiv_normalizedHorizontalRaw_of_positiveFiber
    (χ : SignedSlabCutoff C) {v : A} (hv : v ∈ C.positiveSlabFiber) :
    Function.Surjective (fderiv ℝ (normalizedHorizontalRaw C χ) v) := by
  rw [fderiv_normalizedHorizontalRaw_of_positiveFiber C χ hv]
  exact C.cobordism.regular v hv.1.1


-- @@ L243-243 verbatim
/-! ## The normalized sphere-valued slab homotopy -/


-- @@ L245-247 verbatim
/-- Space-time inclusion with the time variable restricted to the unit interval. -/
def slabSpaceTime (p : I × E) : A :=
  spaceTime p.2 (p.1 : ℝ)


-- @@ L249-256 verbatim
lemma continuous_slabSpaceTime : Continuous (slabSpaceTime (n := n)) := by
  have heq : slabSpaceTime (n := n) = fun p : I × E =>
      embedCLM (n + 1) p.2 + (p.1 : ℝ) • eLast (n + 1) := by
    funext p
    exact spaceTime_eq_affine p.2 (p.1 : ℝ)
  rw [heq]
  exact ((embedCLM (n + 1)).continuous.comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const)


-- @@ L258-261 verbatim
/-- The signed raw collapse as a continuous map on `I × ℝⁿ⁺¹`. -/
def slabRawCM (χ : SignedSlabCutoff C) : C(I × E, E) where
  toFun p := raw C χ (slabSpaceTime p)
  continuous_toFun := (contDiff_raw C χ).continuous.comp continuous_slabSpaceTime


-- @@ L263-267 verbatim
lemma slabRawCM_ne_zero (χ : SignedSlabCutoff C) (p : I × E) :
    slabRawCM C χ p ≠ 0 := by
  apply raw_ne_zero_of_mem_timeSlab C χ
  rw [slabSpaceTime, vertC_spaceTime]
  exact p.1.2


-- @@ L269-271 verbatim
/-- The normalized signed Pontryagin--Thom map on the whole cobordism slab. -/
def slabPTCM (χ : SignedSlabCutoff C) : C(I × E, UnitSphere E) :=
  normalizeMap (slabRawCM C χ) (slabRawCM_ne_zero C χ)


-- @@ L273-275 verbatim
/-- The north pole used by the signed collapse. -/
def signedPTNorthPole : UnitSphere E :=
  ⟨eLast n, by rw [mem_sphere_zero_iff_norm, norm_eLast]⟩


-- @@ L277-278 verbatim
@[simp] lemma signedPTNorthPole_coe :
    (signedPTNorthPole (n := n) : E) = eLast n := rfl


-- @@ L280-283 verbatim
/-- The normalized collapse on a fixed end slice. -/
def endpointPTCM (χ : SignedSlabCutoff C) (t : I) : C(E, UnitSphere E) :=
  (slabPTCM C χ).comp
    ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩


-- @@ L285-292 verbatim
/-- The compactly supported signed construction gives an explicit homotopy
between its incoming and outgoing Pontryagin--Thom collapses. -/
def slabPTHomotopy (χ : SignedSlabCutoff C) :
    ContinuousMap.Homotopy (endpointPTCM C χ 0) (endpointPTCM C χ 1) where
  toFun := slabPTCM C χ
  continuous_toFun := map_continuous (slabPTCM C χ)
  map_zero_left _ := rfl
  map_one_left _ := rfl


-- @@ L294-299 verbatim
lemma slabPTCM_of_positiveFiber (χ : SignedSlabCutoff C) {p : I × E}
    (hp : slabSpaceTime p ∈ C.positiveSlabFiber) :
    slabPTCM C χ p = signedPTNorthPole := by
  apply Subtype.ext
  change ‖raw C χ (slabSpaceTime p)‖⁻¹ • raw C χ (slabSpaceTime p) = eLast n
  rw [raw_of_positiveFiber C χ hp, norm_eLast, inv_one, one_smul]


-- @@ L301-306 verbatim
lemma slabPTCM_of_negativeFiber (χ : SignedSlabCutoff C) {p : I × E}
    (hp : slabSpaceTime p ∈ C.negativeSlabFiber) :
    slabPTCM C χ p = southPole n := by
  apply Subtype.ext
  change ‖raw C χ (slabSpaceTime p)‖⁻¹ • raw C χ (slabSpaceTime p) = -eLast n
  rw [raw_of_negativeFiber C χ hp, norm_neg, norm_eLast, inv_one, one_smul]


-- @@ L308-308 verbatim
end SignedSlabCutoff


-- @@ L310-310 verbatim
end SignedFramedLevelCobordism


-- @@ L312-312 verbatim
end Submission
