import Mathlib
import Submission.LevelSet
import Submission.PTAssembly
import Submission.SphereClose
import Submission.TubeCircle


-- @@ L7-30 verbatim
/-!
# The local Thom collapse around the standard twist-`k` circle

This file turns the explicit tube coordinates from `Submission.TubeCircle` into
the local data needed by the inverse Pontryagin--Thom construction.  The main
point is that no choice of an angular branch is made: the normal coordinate map
`wCoord k` is smooth on `tubeGood`, and a global smooth cutoff is obtained from
the squared distance to the circle.

The declarations proved here provide the four local contracts used by the
collapse construction:

* `tubeCutoff` is globally smooth, is one on the radius-`1/4` tube and zero
  outside the radius-`1/3` tube;
* the inner and outer tube regions lie in `tubeGood`, so `wCoord` is smooth on
  all points where the cutoff is active;
* the zero fiber of `wCoord` on `tubeGood` is exactly the standard circle;
* the differential of `wCoord` sends the prescribed normal frame to the
  standard basis.  In particular it is surjective along the circle.

The last item is the framed regular-value calculation.  It is phrased directly
in terms of `fderiv`, so it can be consumed both by a sphere-valued Thom collapse
and by a later `FramedLevelSet` package.
-/


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace Submission


-- @@ L36-36 verbatim
open Set Function Metric Filter Topology.Homotopy

-- @@ L37-37 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L39-39 verbatim
variable {m : ℕ}


-- @@ L41-41 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L42-42 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L44-44 verbatim
/-! ## A smooth cutoff supported in the explicit tube -/


-- @@ L46-49 verbatim
/-- Smooth scalar profile which is `1` up to squared radius `1/16` and `0` from
squared radius `1/9` onwards. -/
def tubeCutoffScalar (s : ℝ) : ℝ :=
  Real.smoothTransition ((16 - 144 * s) / 7)


-- @@ L51-52 verbatim
lemma tubeCutoffScalar_nonneg (s : ℝ) : 0 ≤ tubeCutoffScalar s :=
  Real.smoothTransition.nonneg _


-- @@ L54-55 verbatim
lemma tubeCutoffScalar_le_one (s : ℝ) : tubeCutoffScalar s ≤ 1 :=
  Real.smoothTransition.le_one _


-- @@ L57-61 verbatim
lemma tubeCutoffScalar_of_le {s : ℝ} (hs : s ≤ 1 / 16) :
    tubeCutoffScalar s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 ≤ (16 - 144 * s) / 7
  linarith


-- @@ L63-67 verbatim
lemma tubeCutoffScalar_of_ge {s : ℝ} (hs : 1 / 9 ≤ s) :
    tubeCutoffScalar s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  change (16 - 144 * s) / 7 ≤ 0
  linarith


-- @@ L69-71 verbatim
lemma contDiff_tubeCutoffScalar : ContDiff ℝ ∞ tubeCutoffScalar := by
  apply Real.smoothTransition.contDiff.comp
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_id)).div_const 7)


-- @@ L73-76 verbatim
/-- Global radial cutoff around the standard circle.  Although `tubeDistSq`
contains a square root, the composition is identically zero near the singular
axis and is therefore globally smooth. -/
def tubeCutoff (v : E) : ℝ := tubeCutoffScalar (tubeDistSq v)


-- @@ L78-79 verbatim
lemma tubeCutoff_nonneg (v : E) : 0 ≤ tubeCutoff v :=
  tubeCutoffScalar_nonneg _


-- @@ L81-82 verbatim
lemma tubeCutoff_le_one (v : E) : tubeCutoff v ≤ 1 :=
  tubeCutoffScalar_le_one _


-- @@ L84-86 verbatim
lemma tubeCutoff_of_le {v : E} (hv : tubeDistSq v ≤ 1 / 16) :
    tubeCutoff v = 1 :=
  tubeCutoffScalar_of_le hv


-- @@ L88-90 verbatim
lemma tubeCutoff_of_ge {v : E} (hv : 1 / 9 ≤ tubeDistSq v) :
    tubeCutoff v = 0 :=
  tubeCutoffScalar_of_ge hv


-- @@ L92-93 verbatim
/-- The radius-`r` tube, expressed using the globally defined squared distance. -/
def tubeRegion (r : ℝ) : Set E := {v | tubeDistSq v < r ^ 2}


-- @@ L95-96 verbatim
lemma mem_tubeRegion_iff {r : ℝ} {v : E} :
    v ∈ tubeRegion r ↔ tubeDistSq v < r ^ 2 := Iff.rfl


-- @@ L98-108 verbatim
/-- Any tube of radius strictly less than one misses the singular circle axis. -/
lemma tubeRegion_subset_tubeGood {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    tubeRegion (m := m) r ⊆ tubeGood := by
  intro v hv
  have hd : tubeDistSq v < r ^ 2 := hv
  have hs : (rad v - 1) ^ 2 ≤ tubeDistSq v := sq_rad_le_tubeDistSq v
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hrad : 0 < rad v := by
    have hn := rad_nonneg v
    nlinarith [sq_nonneg (rad v - 1)]
  exact (Real.sqrt_pos.mp hrad)


-- @@ L110-112 verbatim
lemma innerTube_subset_tubeGood :
    tubeRegion (m := m) (1 / 4) ⊆ tubeGood :=
  tubeRegion_subset_tubeGood (by norm_num) (by norm_num)


-- @@ L114-116 verbatim
lemma outerTube_subset_tubeGood :
    tubeRegion (m := m) (1 / 3) ⊆ tubeGood :=
  tubeRegion_subset_tubeGood (by norm_num) (by norm_num)


-- @@ L118-123 verbatim
lemma tubeCutoff_eq_one_on_inner {v : E} (hv : v ∈ tubeRegion (m := m) (1 / 4)) :
    tubeCutoff v = 1 := by
  apply tubeCutoff_of_le
  have : tubeDistSq v < (1 / 4 : ℝ) ^ 2 := hv
  norm_num at this ⊢
  exact this.le


-- @@ L125-130 verbatim
lemma tubeCutoff_eq_zero_off_outer {v : E} (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeCutoff v = 0 := by
  apply tubeCutoff_of_ge
  have : (1 / 3 : ℝ) ^ 2 ≤ tubeDistSq v := not_lt.mp hv
  norm_num at this ⊢
  exact this


-- @@ L132-133 verbatim
lemma continuous_rad : Continuous (rad (m := m)) :=
  Real.continuous_sqrt.comp contDiff_radSq.continuous


-- @@ L135-137 verbatim
lemma continuous_tubeDistSq : Continuous (tubeDistSq (m := m)) := by
  have hnormsq : Continuous fun v : E => ‖v‖ ^ 2 := continuous_norm.pow 2
  exact (hnormsq.add continuous_const).sub (continuous_const.mul continuous_rad)


-- @@ L139-163 verbatim
/-- The cutoff is genuinely globally smooth, including along the circle axis
where the raw distance formula contains `sqrt (x₀²+x₁²)`.  Near that axis the
distance is bigger than the outer cutoff radius, hence the function is locally
constant zero. -/
theorem contDiff_tubeCutoff : ContDiff ℝ ∞ (tubeCutoff (m := m)) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v ∈ tubeGood
  · have hd : ContDiffAt ℝ ∞ (tubeDistSq (m := m)) v :=
      contDiffOn_tubeDistSq.contDiffAt (isOpen_tubeGood.mem_nhds hv)
    exact contDiff_tubeCutoffScalar.contDiffAt.comp v hd
  · have hrs : radSq v = 0 := by
      have hn := radSq_nonneg v
      have : ¬0 < radSq v := hv
      linarith
    have hr : rad v = 0 := by rw [rad, hrs, Real.sqrt_zero]
    have hd : 1 ≤ tubeDistSq v := by
      rw [tubeDistSq, hr]
      nlinarith [sq_nonneg ‖v‖]
    have hgt : 1 / 9 < tubeDistSq v := by linarith
    have hnhds : {x : E | 1 / 9 < tubeDistSq x} ∈ 𝓝 v :=
      (isOpen_lt continuous_const continuous_tubeDistSq).mem_nhds hgt
    apply (contDiffAt_const (x := v) (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hnhds] with x hx
    exact tubeCutoff_of_ge hx.le


-- @@ L165-169 verbatim
/-- The horizontal chart of the local Thom collapse.  It is the normal coordinate
inside the radius-`1/4` tube and is smoothly switched off before reaching the
singular axis. -/
def tubeCollapseHorizontal (k : ℕ) (v : E) : F :=
  tubeCutoff v • wCoord k v


-- @@ L171-192 verbatim
theorem contDiff_tubeCollapseHorizontal (k : ℕ) :
    ContDiff ℝ ∞ (tubeCollapseHorizontal (m := m) k) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v ∈ tubeGood
  · have hw : ContDiffAt ℝ ∞ (wCoord (m := m) k) v :=
      (contDiffOn_wCoord k).contDiffAt (isOpen_tubeGood.mem_nhds hv)
    exact contDiff_tubeCutoff.contDiffAt.smul hw
  · have hrs : radSq v = 0 := by
      have hn := radSq_nonneg v
      have : ¬0 < radSq v := hv
      linarith
    have hr : rad v = 0 := by rw [rad, hrs, Real.sqrt_zero]
    have hd : 1 ≤ tubeDistSq v := by
      rw [tubeDistSq, hr]
      nlinarith [sq_nonneg ‖v‖]
    have hgt : 1 / 9 < tubeDistSq v := by linarith
    have hnhds : {x : E | 1 / 9 < tubeDistSq x} ∈ 𝓝 v :=
      (isOpen_lt continuous_const continuous_tubeDistSq).mem_nhds hgt
    apply (contDiffAt_const (x := v) (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hnhds] with x hx
    rw [tubeCollapseHorizontal, tubeCutoff_of_ge hx.le, zero_smul]


-- @@ L194-197 verbatim
lemma tubeCollapseHorizontal_eq_wCoord_of_mem_inner (k : ℕ) {v : E}
    (hv : v ∈ tubeRegion (m := m) (1 / 4)) :
    tubeCollapseHorizontal k v = wCoord k v := by
  rw [tubeCollapseHorizontal, tubeCutoff_eq_one_on_inner hv, one_smul]


-- @@ L199-199 verbatim
/-! ## The local zero fiber -/


-- @@ L201-203 verbatim
/-- The geometric standard circle, without choosing a quotient model for its
angle parameter. -/
def standardCircle : Set E := Set.range (circleAt (m := m))


-- @@ L205-206 verbatim
lemma circleAt_mem_standardCircle (θ : ℝ) :
    circleAt (m := m) θ ∈ standardCircle := ⟨θ, rfl⟩


-- @@ L208-210 verbatim
lemma radSq_circleAt (θ : ℝ) : radSq (circleAt (m := m) θ) = 1 := by
  rw [radSq, circleAt_apply_zero, circleAt_apply_one]
  linear_combination Real.sin_sq_add_cos_sq θ


-- @@ L212-215 verbatim
lemma circleAt_mem_tubeGood (θ : ℝ) : circleAt (m := m) θ ∈ tubeGood := by
  change 0 < radSq (circleAt (m := m) θ)
  rw [radSq_circleAt]
  norm_num


-- @@ L217-219 verbatim
lemma tubeMap_zero (k : ℕ) (θ : ℝ) :
    tubeMap (m := m) k θ 0 = circleAt θ := by
  simp [tubeMap]


-- @@ L221-225 verbatim
lemma wCoord_circleAt (k : ℕ) (θ : ℝ) :
    wCoord (m := m) k (circleAt θ) = 0 := by
  have hA : 0 < tubeA (m := m) k θ (0 : F) := by simp [tubeA]
  have h := wCoord_tubeMap (m := m) k θ hA
  simpa [tubeMap_zero] using h


-- @@ L227-239 verbatim
/-- On its smooth domain, the zero fiber of the explicit normal-coordinate map
is exactly the standard circle. -/
theorem wCoord_eq_zero_iff_standardCircle (k : ℕ) {v : E} (hv : v ∈ tubeGood) :
    wCoord k v = 0 ↔ v ∈ standardCircle := by
  constructor
  · intro hw
    obtain ⟨θ, hc, hs⟩ := exists_angle hv
    refine ⟨θ, ?_⟩
    have hrec := tubeMap_wCoord (m := m) k hv hc hs
    rw [hw, tubeMap_zero] at hrec
    exact hrec
  · rintro ⟨θ, rfl⟩
    exact wCoord_circleAt k θ


-- @@ L241-247 verbatim
/-- The active (inner-tube) fiber of the horizontal collapse chart is exactly the
standard circle. -/
theorem tubeCollapseHorizontal_eq_zero_iff_standardCircle (k : ℕ) {v : E}
    (hv : v ∈ tubeRegion (m := m) (1 / 4)) :
    tubeCollapseHorizontal k v = 0 ↔ v ∈ standardCircle := by
  rw [tubeCollapseHorizontal_eq_wCoord_of_mem_inner k hv]
  exact wCoord_eq_zero_iff_standardCircle k (innerTube_subset_tubeGood hv)


-- @@ L249-252 verbatim
lemma tubeDistSq_circleAt (θ : ℝ) :
    tubeDistSq (circleAt (m := m) θ) = 0 := by
  have hA : 0 < tubeA (m := m) 0 θ (0 : F) := by simp [tubeA]
  simpa [tubeMap_zero] using tubeDistSq_tubeMap (m := m) 0 θ hA


-- @@ L254-259 verbatim
lemma standardCircle_subset_innerTube :
    standardCircle (m := m) ⊆ tubeRegion (1 / 4) := by
  rintro _ ⟨θ, rfl⟩
  change tubeDistSq (circleAt (m := m) θ) < (1 / 4 : ℝ) ^ 2
  rw [tubeDistSq_circleAt]
  norm_num


-- @@ L261-264 verbatim
lemma norm_circleAt (θ : ℝ) : ‖circleAt (m := m) θ‖ = 1 := by
  have hsq : ‖circleAt (m := m) θ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_circleAt_self]
  nlinarith [norm_nonneg (circleAt (m := m) θ)]


-- @@ L266-266 verbatim
/-! ## Smoothness where the local collapse is active -/


-- @@ L268-270 verbatim
lemma contDiffOn_wCoord_outerTube (k : ℕ) :
    ContDiffOn ℝ ∞ (wCoord (m := m) k) (tubeRegion (1 / 3)) :=
  (contDiffOn_wCoord k).mono outerTube_subset_tubeGood


-- @@ L272-272 verbatim
/-! ## Differential and prescribed frame evaluation -/


-- @@ L274-276 verbatim
/-- Linear reconstruction from normal coordinates in the prescribed frame. -/
def normalSumCLM (k : ℕ) (θ : ℝ) : F →L[ℝ] E :=
  ∑ i, (EuclideanSpace.proj i : F →L[ℝ] ℝ).smulRight (nuVec k θ i)


-- @@ L278-280 verbatim
@[simp] lemma normalSumCLM_apply (k : ℕ) (θ : ℝ) (w : F) :
    normalSumCLM (m := m) k θ w = ∑ i, w i • nuVec k θ i := by
  simp [normalSumCLM]


-- @@ L282-289 verbatim
lemma normalSumCLM_single (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) :
    normalSumCLM (m := m) k θ (EuclideanSpace.single i 1) = nuVec k θ i := by
  rw [normalSumCLM_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [PiLp.single_apply, if_neg hji, zero_smul]
  · simp


-- @@ L291-292 verbatim
/-- The affine normal slice at a fixed point of the circle. -/
def normalSlice (k : ℕ) (θ : ℝ) (w : F) : E := tubeMap k θ w


-- @@ L294-296 verbatim
lemma normalSlice_eq (k : ℕ) (θ : ℝ) (w : F) :
    normalSlice (m := m) k θ w = circleAt θ + normalSumCLM k θ w := by
  rw [normalSlice, tubeMap, normalSumCLM_apply]


-- @@ L298-300 verbatim
lemma normalSlice_zero (k : ℕ) (θ : ℝ) :
    normalSlice (m := m) k θ 0 = circleAt θ := by
  rw [normalSlice, tubeMap_zero]


-- @@ L302-312 verbatim
lemma hasFDerivAt_normalSlice (k : ℕ) (θ : ℝ) (w : F) :
    HasFDerivAt (normalSlice (m := m) k θ) (normalSumCLM k θ) w := by
  have h : HasFDerivAt (fun u : F =>
      circleAt (m := m) θ + normalSumCLM k θ u) (normalSumCLM k θ) w :=
    (normalSumCLM (m := m) k θ).hasFDerivAt.const_add (circleAt θ)
  have heq : normalSlice (m := m) k θ = fun w : F =>
      circleAt θ + normalSumCLM k θ w := by
    funext u
    exact normalSlice_eq k θ u
  rw [heq]
  exact h


-- @@ L314-324 verbatim
lemma contDiff_normalSlice (k : ℕ) (θ : ℝ) :
    ContDiff ℝ ∞ (normalSlice (m := m) k θ) := by
  have h : ContDiff ℝ ∞ fun w : F =>
      circleAt (m := m) θ + normalSumCLM k θ w :=
    contDiff_const.add (normalSumCLM (m := m) k θ).contDiff
  have heq : normalSlice (m := m) k θ = fun w : F =>
      circleAt θ + normalSumCLM k θ w := by
    funext u
    exact normalSlice_eq k θ u
  rw [heq]
  exact h


-- @@ L326-334 verbatim
/-- The exact left-inverse identity holds on a neighbourhood of the origin in
each fixed normal slice. -/
lemma wCoord_normalSlice_eventuallyEq (k : ℕ) (θ : ℝ) :
    (fun w : F => wCoord k (normalSlice k θ w)) =ᶠ[𝓝 0] fun w => w := by
  filter_upwards [Metric.ball_mem_nhds (0 : F) (by norm_num : (0 : ℝ) < 1 / 2)]
    with w hw
  have hwnorm : ‖w‖ < 1 / 2 := by
    simpa [dist_zero_right] using hw
  exact wCoord_tubeMap k θ (tubeA_pos k θ hwnorm)


-- @@ L336-339 verbatim
lemma contDiffAt_wCoord_circleAt (k : ℕ) (θ : ℝ) :
    ContDiffAt ℝ ∞ (wCoord (m := m) k) (circleAt θ) :=
  (contDiffOn_wCoord k).contDiffAt
    (isOpen_tubeGood.mem_nhds (circleAt_mem_tubeGood θ))


-- @@ L341-358 verbatim
/-- Differentiating the exact tube-coordinate round trip gives a left inverse for
the normal reconstruction map. -/
theorem fderiv_wCoord_comp_normalSumCLM (k : ℕ) (θ : ℝ) :
    (fderiv ℝ (wCoord (m := m) k) (circleAt θ)).comp (normalSumCLM k θ)
      = ContinuousLinearMap.id ℝ F := by
  have hwDiff : DifferentiableAt ℝ (wCoord (m := m) k) (circleAt θ) :=
    (contDiffAt_wCoord_circleAt k θ).differentiableAt (by simp)
  have hwDeriv : HasFDerivAt (wCoord (m := m) k)
      (fderiv ℝ (wCoord k) (circleAt θ)) (normalSlice k θ 0) := by
    simpa only [normalSlice_zero] using hwDiff.hasFDerivAt
  have hcomp := hwDeriv.comp (0 : F) (hasFDerivAt_normalSlice k θ 0)
  have heq : ((wCoord (m := m) k) ∘ normalSlice k θ) =ᶠ[𝓝 0] id := by
    change (fun w : F => wCoord k (normalSlice k θ w)) =ᶠ[𝓝 0] fun w => w
    exact wCoord_normalSlice_eventuallyEq k θ
  have hsame : HasFDerivAt ((wCoord (m := m) k) ∘ normalSlice k θ)
      (ContinuousLinearMap.id ℝ F) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : F)).congr_of_eventuallyEq heq
  exact hcomp.unique hsame


-- @@ L360-368 verbatim
/-- **Prescribed frame evaluation.**  The differential of the local normal
coordinate map sends the `i`-th twist-`k` normal vector to the `i`-th standard
basis vector. -/
theorem fderiv_wCoord_nuVec (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) :
    fderiv ℝ (wCoord (m := m) k) (circleAt θ) (nuVec k θ i)
      = EuclideanSpace.single i 1 := by
  have h := congrArg (fun L : F →L[ℝ] F => L (EuclideanSpace.single i 1))
    (fderiv_wCoord_comp_normalSumCLM (m := m) k θ)
  simpa [normalSumCLM_single] using h


-- @@ L370-378 verbatim
/-- Thus zero is a regular value of the local coordinate chart along the whole
standard circle. -/
theorem surjective_fderiv_wCoord_circleAt (k : ℕ) (θ : ℝ) :
    Function.Surjective (fderiv ℝ (wCoord (m := m) k) (circleAt θ)) := by
  intro y
  refine ⟨normalSumCLM k θ y, ?_⟩
  have h := congrArg (fun L : F →L[ℝ] F => L y)
    (fderiv_wCoord_comp_normalSumCLM (m := m) k θ)
  exact h


-- @@ L380-381 verbatim
lemma isOpen_tubeRegion (r : ℝ) : IsOpen (tubeRegion (m := m) r) :=
  isOpen_lt continuous_tubeDistSq continuous_const


-- @@ L383-388 verbatim
lemma tubeCollapseHorizontal_eventuallyEq_wCoord (k : ℕ) (θ : ℝ) :
    tubeCollapseHorizontal (m := m) k =ᶠ[𝓝 (circleAt θ)] wCoord k := by
  have hmem : circleAt (m := m) θ ∈ tubeRegion (1 / 4) :=
    standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)
  filter_upwards [(isOpen_tubeRegion (m := m) (1 / 4)).mem_nhds hmem] with v hv
  exact tubeCollapseHorizontal_eq_wCoord_of_mem_inner k hv


-- @@ L390-393 verbatim
lemma fderiv_tubeCollapseHorizontal_circleAt (k : ℕ) (θ : ℝ) :
    fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ)
      = fderiv ℝ (wCoord k) (circleAt θ) :=
  (tubeCollapseHorizontal_eventuallyEq_wCoord k θ).fderiv_eq


-- @@ L395-400 verbatim
theorem fderiv_tubeCollapseHorizontal_nuVec (k : ℕ) (θ : ℝ)
    (i : Fin (m + 2)) :
    fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ) (nuVec k θ i)
      = EuclideanSpace.single i 1 := by
  rw [fderiv_tubeCollapseHorizontal_circleAt]
  exact fderiv_wCoord_nuVec k θ i


-- @@ L402-406 verbatim
theorem surjective_fderiv_tubeCollapseHorizontal_circleAt (k : ℕ) (θ : ℝ) :
    Function.Surjective
      (fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ)) := by
  rw [fderiv_tubeCollapseHorizontal_circleAt]
  exact surjective_fderiv_wCoord_circleAt k θ


-- @@ L408-413 verbatim
/-- The continuous linear normal-coordinate projection prescribed by the twist
frame at angle `θ`. -/
def normalCoordCLM (k : ℕ) (θ : ℝ) : E →L[ℝ] F :=
  (EuclideanSpace.equiv (Fin (m + 2)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (InnerProductSpace.toDual ℝ E) (nuVec k θ i))


-- @@ L415-417 verbatim
@[simp] lemma normalCoordCLM_apply (k : ℕ) (θ : ℝ) (x : E) (i : Fin (m + 2)) :
    normalCoordCLM k θ x i = ⟪nuVec k θ i, x⟫ := by
  rfl


-- @@ L419-425 verbatim
lemma normalCoordCLM_nuVec (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) :
    normalCoordCLM (m := m) k θ (nuVec k θ i) = EuclideanSpace.single i 1 := by
  apply (WithLp.equiv 2 _).injective
  funext j
  change normalCoordCLM (m := m) k θ (nuVec k θ i) j = _
  rw [normalCoordCLM_apply, inner_nuVec_nuVec]
  simp [PiLp.single_apply]


-- @@ L427-434 verbatim
lemma normalCoordCLM_surjective (k : ℕ) (θ : ℝ) :
    Function.Surjective (normalCoordCLM (m := m) k θ) := by
  intro y
  refine ⟨∑ i, y i • nuVec k θ i, ?_⟩
  rw [map_sum]
  simp_rw [map_smul, normalCoordCLM_nuVec]
  have hy := (EuclideanSpace.basisFun (Fin (m + 2)) ℝ).sum_repr y
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using hy


-- @@ L436-436 verbatim
/-! ## A sphere-valued Thom collapse -/


-- @@ L438-441 verbatim
/-- The horizontal isometric coordinate inclusion into the target ambient
`ℝ^{m+3}`; its last coordinate is zero. -/
def targetHorizontalCLM : F →L[ℝ] E :=
  ∑ i, (EuclideanSpace.proj i : F →L[ℝ] ℝ).smulRight (coordVec i.castSucc)


-- @@ L443-445 verbatim
@[simp] lemma targetHorizontalCLM_apply (w : F) :
    targetHorizontalCLM (m := m) w = ∑ i, w i • coordVec i.castSucc := by
  simp [targetHorizontalCLM]


-- @@ L447-452 verbatim
lemma castSucc_ne_last (i : Fin (m + 2)) :
    (i.castSucc : Fin (m + 3)) ≠ Fin.last (m + 2) := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_last] at h'
  omega


-- @@ L454-463 verbatim
@[simp] lemma targetHorizontalCLM_coord (w : F) (i : Fin (m + 2)) :
    targetHorizontalCLM (m := m) w i.castSucc = w i := by
  rw [targetHorizontalCLM_apply, sum_coord]
  rw [Finset.sum_eq_single i]
  · simp [coordVec_apply]
  · intro j _ hji
    change w j * coordVec j.castSucc i.castSucc = 0
    rw [coordVec_apply, if_neg, mul_zero]
    exact fun h => hji (Fin.ext (congrArg Fin.val h).symm)
  · simp


-- @@ L465-472 verbatim
@[simp] lemma targetHorizontalCLM_last (w : F) :
    targetHorizontalCLM (m := m) w (Fin.last (m + 2)) = 0 := by
  rw [targetHorizontalCLM_apply, sum_coord]
  apply Finset.sum_eq_zero
  intro i _
  change w i * coordVec i.castSucc (Fin.last (m + 2)) = 0
  rw [coordVec_apply, if_neg, mul_zero]
  exact (castSucc_ne_last i).symm


-- @@ L474-480 verbatim
lemma targetHorizontalCLM_injective :
    Function.Injective (targetHorizontalCLM (m := m)) := by
  intro x y h
  apply (WithLp.equiv 2 _).injective
  funext i
  have hi := congrArg (fun z : E => z i.castSucc) h
  simpa using hi


-- @@ L482-487 verbatim
/-- Unnormalized sphere-collapse vector.  On the circle this is the north pole;
off the outer tube it is the south pole.  The horizontal component records the
cut-off normal coordinate. -/
def tubeCollapseRaw (k : ℕ) (v : E) : E :=
  targetHorizontalCLM (tubeCollapseHorizontal k v)
    + (2 * tubeCutoff v - 1) • eVert


-- @@ L489-495 verbatim
lemma tubeCollapseRaw_last (k : ℕ) (v : E) :
    tubeCollapseRaw k v (Fin.last (m + 2)) = 2 * tubeCutoff v - 1 := by
  rw [tubeCollapseRaw]
  change targetHorizontalCLM (tubeCollapseHorizontal k v) (Fin.last (m + 2))
      + (2 * tubeCutoff v - 1) * eVert (Fin.last (m + 2)) = _
  rw [targetHorizontalCLM_last, eVert_apply_last]
  ring


-- @@ L497-503 verbatim
lemma tubeCollapseRaw_coord (k : ℕ) (v : E) (i : Fin (m + 2)) :
    tubeCollapseRaw k v i.castSucc = tubeCollapseHorizontal k v i := by
  rw [tubeCollapseRaw]
  change targetHorizontalCLM (tubeCollapseHorizontal k v) i.castSucc
      + (2 * tubeCutoff v - 1) * eVert i.castSucc = _
  rw [targetHorizontalCLM_coord, eVert_apply_ne (castSucc_ne_last i)]
  ring


-- @@ L505-513 verbatim
lemma tubeGood_of_tubeCutoff_ne_zero {v : E} (hv : tubeCutoff v ≠ 0) :
    v ∈ tubeGood := by
  have hd : tubeDistSq v < 1 / 9 := by
    by_contra h
    exact hv (tubeCutoff_of_ge (not_lt.mp h))
  apply outerTube_subset_tubeGood
  change tubeDistSq v < (1 / 3 : ℝ) ^ 2
  norm_num at hd ⊢
  exact hd


-- @@ L515-535 verbatim
lemma tubeCollapseRaw_ne_zero (k : ℕ) (v : E) : tubeCollapseRaw k v ≠ 0 := by
  intro hzero
  have hlast := congrArg (fun z : E => z (Fin.last (m + 2))) hzero
  rw [tubeCollapseRaw_last, PiLp.zero_apply] at hlast
  have hc : tubeCutoff v = 1 / 2 := by linarith
  have hc0 : tubeCutoff v ≠ 0 := by rw [hc]; norm_num
  have hhoriz : tubeCollapseHorizontal k v = 0 := by
    apply (WithLp.equiv 2 _).injective
    funext i
    have hi := congrArg (fun z : E => z i.castSucc) hzero
    rw [tubeCollapseRaw_coord, PiLp.zero_apply] at hi
    exact hi
  have hw : wCoord k v = 0 := by
    rw [tubeCollapseHorizontal, hc] at hhoriz
    exact (smul_eq_zero.mp hhoriz).resolve_left (by norm_num)
  have hvGood : v ∈ tubeGood := tubeGood_of_tubeCutoff_ne_zero hc0
  have hvCircle : v ∈ standardCircle :=
    (wCoord_eq_zero_iff_standardCircle k hvGood).mp hw
  have hvInner : v ∈ tubeRegion (1 / 4) := standardCircle_subset_innerTube hvCircle
  have hc1 : tubeCutoff v = 1 := tubeCutoff_eq_one_on_inner hvInner
  linarith


-- @@ L537-544 verbatim
theorem contDiff_tubeCollapseRaw (k : ℕ) :
    ContDiff ℝ ∞ (tubeCollapseRaw (m := m) k) := by
  have hh : ContDiff ℝ ∞ fun v : E =>
      targetHorizontalCLM (tubeCollapseHorizontal k v) :=
    targetHorizontalCLM.contDiff.comp (contDiff_tubeCollapseHorizontal k)
  have hv : ContDiff ℝ ∞ fun v : E => (2 * tubeCutoff v - 1) • eVert (m := m) :=
    ((contDiff_const.mul contDiff_tubeCutoff).sub contDiff_const).smul contDiff_const
  exact hh.add hv


-- @@ L546-548 verbatim
/-- Ambient normalized representative of the sphere-valued Thom collapse. -/
def tubeThomVec (k : ℕ) (v : E) : E :=
  ‖tubeCollapseRaw k v‖⁻¹ • tubeCollapseRaw k v


-- @@ L550-552 verbatim
lemma norm_tubeThomVec (k : ℕ) (v : E) : ‖tubeThomVec k v‖ = 1 := by
  rw [tubeThomVec, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (tubeCollapseRaw_ne_zero k v))


-- @@ L554-562 verbatim
theorem contDiff_tubeThomVec (k : ℕ) :
    ContDiff ℝ ∞ (tubeThomVec (m := m) k) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  have hr : ContDiffAt ℝ ∞ (tubeCollapseRaw (m := m) k) v :=
    (contDiff_tubeCollapseRaw (m := m) k).contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun x => ‖tubeCollapseRaw k x‖) v :=
    hr.norm ℝ (tubeCollapseRaw_ne_zero k v)
  exact (hn.inv (norm_ne_zero_iff.mpr (tubeCollapseRaw_ne_zero k v))).smul hr


-- @@ L564-568 verbatim
/-- The actual sphere-valued local Thom collapse. -/
def tubeThomCollapse (k : ℕ) (v : E) : UnitSphere E :=
  ⟨tubeThomVec k v, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_tubeThomVec k v⟩


-- @@ L570-573 verbatim
lemma norm_eVert : ‖eVert (m := m)‖ = 1 := by
  have hsq : ‖eVert (m := m)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_eVert_self]
  nlinarith [norm_nonneg (eVert (m := m))]


-- @@ L575-577 verbatim
/-- North pole selected as the regular value of the collapse. -/
def tubeNorth : UnitSphere E :=
  ⟨eVert, by rw [mem_sphere_zero_iff_norm, norm_eVert]⟩


-- @@ L579-581 verbatim
/-- South pole/basepoint of the collapse. -/
def tubeSouth : UnitSphere E :=
  ⟨-eVert, by rw [mem_sphere_zero_iff_norm, norm_neg, norm_eVert]⟩


-- @@ L583-583 verbatim
@[simp] lemma tubeNorth_coe : ((tubeNorth (m := m) : UnitSphere E) : E) = eVert := rfl


-- @@ L585-585 verbatim
@[simp] lemma tubeSouth_coe : ((tubeSouth (m := m) : UnitSphere E) : E) = -eVert := rfl


-- @@ L587-589 verbatim
lemma tubeCollapseHorizontal_circleAt (k : ℕ) (θ : ℝ) :
    tubeCollapseHorizontal (m := m) k (circleAt θ) = 0 := by
  rw [tubeCollapseHorizontal, wCoord_circleAt, smul_zero]


-- @@ L591-597 verbatim
lemma tubeCollapseRaw_circleAt (k : ℕ) (θ : ℝ) :
    tubeCollapseRaw (m := m) k (circleAt θ) = eVert := by
  rw [tubeCollapseRaw, tubeCollapseHorizontal_circleAt, map_zero, zero_add]
  have hmem : circleAt (m := m) θ ∈ tubeRegion (1 / 4) :=
    standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)
  rw [tubeCutoff_eq_one_on_inner hmem]
  norm_num


-- @@ L599-601 verbatim
lemma tubeThomVec_circleAt (k : ℕ) (θ : ℝ) :
    tubeThomVec (m := m) k (circleAt θ) = eVert := by
  rw [tubeThomVec, tubeCollapseRaw_circleAt, norm_eVert, inv_one, one_smul]


-- @@ L603-606 verbatim
@[simp] theorem tubeThomCollapse_circleAt (k : ℕ) (θ : ℝ) :
    tubeThomCollapse (m := m) k (circleAt θ) = tubeNorth := by
  apply Subtype.ext
  exact tubeThomVec_circleAt k θ


-- @@ L608-615 verbatim
lemma tubeCollapseRaw_off_outer (k : ℕ) {v : E}
    (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeCollapseRaw k v = -eVert := by
  have hc : tubeCutoff v = 0 := tubeCutoff_eq_zero_off_outer hv
  have hh : tubeCollapseHorizontal k v = 0 := by
    rw [tubeCollapseHorizontal, hc, zero_smul]
  rw [tubeCollapseRaw, hh, map_zero, zero_add, hc]
  norm_num


-- @@ L617-621 verbatim
lemma tubeThomVec_off_outer (k : ℕ) {v : E}
    (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeThomVec k v = -eVert := by
  rw [tubeThomVec, tubeCollapseRaw_off_outer k hv, norm_neg, norm_eVert,
    inv_one, one_smul]


-- @@ L623-627 verbatim
theorem tubeThomCollapse_off_outer (k : ℕ) {v : E}
    (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeThomCollapse k v = tubeSouth := by
  apply Subtype.ext
  exact tubeThomVec_off_outer k hv


-- @@ L629-662 verbatim
/-- The north-pole fiber of the sphere-valued collapse is exactly the standard
circle, globally (not merely after restricting to the inner tube). -/
theorem tubeThomCollapse_eq_north_iff (k : ℕ) {v : E} :
    tubeThomCollapse k v = tubeNorth ↔ v ∈ standardCircle := by
  constructor
  · intro hcollapse
    have hvec : tubeThomVec k v = eVert := congrArg Subtype.val hcollapse
    have hraw : tubeCollapseRaw k v ≠ 0 := tubeCollapseRaw_ne_zero k v
    have hnorm : ‖tubeCollapseRaw k v‖ ≠ 0 := norm_ne_zero_iff.mpr hraw
    have hinv : ‖tubeCollapseRaw k v‖⁻¹ ≠ 0 := inv_ne_zero hnorm
    have hhoriz : tubeCollapseHorizontal k v = 0 := by
      apply (WithLp.equiv 2 _).injective
      funext i
      have hi := congrArg (fun z : E => z i.castSucc) hvec
      change ‖tubeCollapseRaw k v‖⁻¹ * tubeCollapseRaw k v i.castSucc
          = eVert i.castSucc at hi
      rw [tubeCollapseRaw_coord, eVert_apply_ne (castSucc_ne_last i)] at hi
      exact (mul_eq_zero.mp hi).resolve_left hinv
    have hc0 : tubeCutoff v ≠ 0 := by
      intro hc
      have hlast := congrArg (fun z : E => z (Fin.last (m + 2))) hvec
      change ‖tubeCollapseRaw k v‖⁻¹
          * tubeCollapseRaw k v (Fin.last (m + 2)) = eVert (Fin.last (m + 2)) at hlast
      rw [tubeCollapseRaw_last, eVert_apply_last, hc] at hlast
      have hpos : 0 < ‖tubeCollapseRaw k v‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hraw)
      norm_num at hlast
      linarith
    have hw : wCoord k v = 0 := by
      rw [tubeCollapseHorizontal] at hhoriz
      exact (smul_eq_zero.mp hhoriz).resolve_left hc0
    exact (wCoord_eq_zero_iff_standardCircle k
      (tubeGood_of_tubeCutoff_ne_zero hc0)).mp hw
  · rintro ⟨θ, rfl⟩
    exact tubeThomCollapse_circleAt k θ


-- @@ L664-667 verbatim
theorem tubeThomCollapse_fiber (k : ℕ) :
    {v : E | tubeThomCollapse k v = tubeNorth} = standardCircle := by
  ext v
  exact tubeThomCollapse_eq_north_iff k


-- @@ L669-669 verbatim
/-! ## Cubical representative and stable homotopy class -/


-- @@ L671-674 verbatim
theorem continuous_tubeThomCollapse (k : ℕ) :
    Continuous (tubeThomCollapse (m := m) k) := by
  apply Continuous.subtype_mk
  exact (contDiff_tubeThomVec (m := m) k).continuous


-- @@ L676-678 verbatim
/-- Continuous-map packaging of the ambient collapse. -/
def tubeThomCollapseCM (k : ℕ) : C(E, UnitSphere E) :=
  ⟨tubeThomCollapse k, continuous_tubeThomCollapse k⟩


-- @@ L680-683 verbatim
/-- Affine expansion of the unit cube to `[-3,3]^{m+3}`.  The factor is chosen so
that every boundary face lies far outside the radius-`1/3` tube. -/
def cubeToTubeAmbient (t : I^(Fin (m + 3))) : E :=
  WithLp.toLp 2 fun i => 6 * (t i : ℝ) - 3


-- @@ L685-686 verbatim
@[simp] lemma cubeToTubeAmbient_apply (t : I^(Fin (m + 3))) (i : Fin (m + 3)) :
    cubeToTubeAmbient (m := m) t i = 6 * (t i : ℝ) - 3 := rfl


-- @@ L688-698 verbatim
theorem continuous_cubeToTubeAmbient :
    Continuous (cubeToTubeAmbient (m := m)) := by
  have h : cubeToTubeAmbient (m := m) = fun t =>
      (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm
        (fun i => 6 * (t i : ℝ) - 3) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const


-- @@ L700-718 verbatim
lemma radSq_add_coordSq_le_normSq (v : E) {j : Fin (m + 3)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    radSq v + v j ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [normSq_eq_sum_sq]
  have hsub : ({0, 1, j} : Finset (Fin (m + 3))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hsum : ∑ i ∈ ({0, 1, j} : Finset (Fin (m + 3))), v i ^ 2
      = radSq v + v j ^ 2 := by
    have hset : ({0, 1, j} : Finset (Fin (m + 3))) = {j, 0, 1} := by
      ext i
      simp [or_comm, or_left_comm, or_assoc]
    rw [hset, Finset.sum_insert (by simp [hj0, hj1]),
      Finset.sum_insert
        (by simp : (0 : Fin (m + 3)) ∉ ({1} : Finset (Fin (m + 3)))),
      Finset.sum_singleton]
    unfold radSq
    ring
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => sq_nonneg _


-- @@ L720-726 verbatim
lemma coordSq_le_tubeDistSq_of_ne (v : E) {j : Fin (m + 3)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    v j ^ 2 ≤ tubeDistSq v := by
  have hcoord := radSq_add_coordSq_le_normSq v hj0 hj1
  have hrsq := rad_sq v
  rw [tubeDistSq]
  nlinarith [sq_nonneg (rad v - 1)]


-- @@ L728-735 verbatim
lemma cubeToTubeAmbient_boundary_abs {t : I^(Fin (m + 3))}
    {j : Fin (m + 3)} (hj : t j = 0 ∨ t j = 1) :
    |cubeToTubeAmbient (m := m) t j| = 3 := by
  rcases hj with hj | hj
  · rw [cubeToTubeAmbient_apply, hj, Set.Icc.coe_zero]
    norm_num
  · rw [cubeToTubeAmbient_apply, hj, Set.Icc.coe_one]
    norm_num


-- @@ L737-770 verbatim
/-- Every boundary point of the expanded cube is outside the outer tube. -/
theorem cubeToTubeAmbient_boundary_off_outer {t : I^(Fin (m + 3))}
    (ht : t ∈ Cube.boundary (Fin (m + 3))) :
    cubeToTubeAmbient (m := m) t ∉ tubeRegion (1 / 3) := by
  obtain ⟨j, hj⟩ := ht
  have habs := cubeToTubeAmbient_boundary_abs (m := m) hj
  have hsq : cubeToTubeAmbient (m := m) t j ^ 2 = 9 := by
    nlinarith [sq_abs (cubeToTubeAmbient (m := m) t j)]
  have hd : 1 / 9 ≤ tubeDistSq (cubeToTubeAmbient (m := m) t) := by
    by_cases hj0 : j = 0
    · subst j
      have hrsq := rad_sq (cubeToTubeAmbient (m := m) t)
      have hr0 := rad_nonneg (cubeToTubeAmbient (m := m) t)
      have hrad : 3 ≤ rad (cubeToTubeAmbient (m := m) t) := by
        rw [radSq] at hrsq
        nlinarith [sq_nonneg (cubeToTubeAmbient (m := m) t 1)]
      have hdist := sq_rad_le_tubeDistSq (cubeToTubeAmbient (m := m) t)
      nlinarith [sq_nonneg (rad (cubeToTubeAmbient (m := m) t) - 1)]
    · by_cases hj1 : j = 1
      · subst j
        have hrsq := rad_sq (cubeToTubeAmbient (m := m) t)
        have hr0 := rad_nonneg (cubeToTubeAmbient (m := m) t)
        have hrad : 3 ≤ rad (cubeToTubeAmbient (m := m) t) := by
          rw [radSq] at hrsq
          nlinarith [sq_nonneg (cubeToTubeAmbient (m := m) t 0)]
        have hdist := sq_rad_le_tubeDistSq (cubeToTubeAmbient (m := m) t)
        nlinarith [sq_nonneg (rad (cubeToTubeAmbient (m := m) t) - 1)]
      · have hdist := coordSq_le_tubeDistSq_of_ne
          (cubeToTubeAmbient (m := m) t) hj0 hj1
        nlinarith
  intro hin
  change tubeDistSq (cubeToTubeAmbient (m := m) t) < (1 / 3 : ℝ) ^ 2 at hin
  norm_num at hin
  exact (not_lt_of_ge hd) hin


-- @@ L772-776 verbatim
/-- The cube boundary is sent to the south-pole basepoint. -/
theorem tubeThomCollapse_cube_boundary (k : ℕ) {t : I^(Fin (m + 3))}
    (ht : t ∈ Cube.boundary (Fin (m + 3))) :
    tubeThomCollapse k (cubeToTubeAmbient t) = tubeSouth :=
  tubeThomCollapse_off_outer k (cubeToTubeAmbient_boundary_off_outer ht)


-- @@ L778-783 verbatim
/-- Cubical generalized loop represented by the explicit twist-`k` Thom collapse. -/
def tubeThomGenLoop (k : ℕ) :
    Ω^ (Fin (m + 3)) (UnitSphere E) tubeSouth :=
  ⟨(tubeThomCollapseCM k).comp
      ⟨cubeToTubeAmbient, continuous_cubeToTubeAmbient⟩,
    fun t ht => tubeThomCollapse_cube_boundary k ht⟩


-- @@ L785-786 verbatim
@[simp] lemma tubeThomGenLoop_apply (k : ℕ) (t : I^(Fin (m + 3))) :
    tubeThomGenLoop (m := m) k t = tubeThomCollapse k (cubeToTubeAmbient t) := rfl


-- @@ L788-791 verbatim
/-- The explicit stable homotopy class of the twist-`k` circle collapse. -/
def tubeThomClass (k : ℕ) :
    HomotopyGroup (Fin (m + 3)) (UnitSphere E) tubeSouth :=
  ⟦tubeThomGenLoop k⟧


-- @@ L793-795 verbatim
/-- The two standard representatives used by the final parity argument. -/
def tubeThomClassZero :
    HomotopyGroup (Fin (m + 3)) (UnitSphere E) tubeSouth := tubeThomClass 0


-- @@ L797-798 verbatim
def tubeThomClassOne :
    HomotopyGroup (Fin (m + 3)) (UnitSphere E) tubeSouth := tubeThomClass 1


-- @@ L800-803 verbatim
lemma eVert_eq_eLast : eVert (m := m) = eLast (m + 2) := by
  apply (WithLp.equiv 2 _).injective
  funext j
  simp [eVert, coordVec, eLast, PiLp.single_apply]


-- @@ L805-809 verbatim
lemma tubeSouth_eq_southPole :
    (tubeSouth (m := m) : UnitSphere E) = southPole (m + 2) := by
  apply Subtype.ext
  show -eVert (m := m) = -eLast (m + 2)
  rw [eVert_eq_eLast]


-- @@ L811-817 verbatim
/-- The explicit cubical tube loop with the canonical `southPole` basepoint
used by `StableSpherePi`.  Only the boundary proof changes; the underlying
continuous map is definitionally `tubeThomGenLoop`. -/
def tubeThomStableGenLoop (k : ℕ) :
    Ω^ (Fin (m + 3)) (UnitSphere E) (southPole (m + 2)) :=
  ⟨(tubeThomGenLoop (m := m) k).1, fun t ht =>
    ((tubeThomGenLoop (m := m) k).2 t ht).trans tubeSouth_eq_southPole⟩


-- @@ L819-823 verbatim
@[simp] theorem tubeThomStableGenLoop_apply (k : ℕ)
    (t : I^(Fin (m + 3))) :
    tubeThomStableGenLoop (m := m) k t =
      tubeThomCollapse k (cubeToTubeAmbient t) :=
  rfl


-- @@ L825-828 verbatim
/-- The same class in the canonical `StableSpherePi` abbreviation used by the
final assembly. -/
def tubeThomStableClass (k : ℕ) : StableSpherePi (m + 2) :=
  ⟦tubeThomStableGenLoop k⟧


-- @@ L830-830 verbatim
def tubeThomStableClassZero : StableSpherePi (m + 2) := tubeThomStableClass 0


-- @@ L832-832 verbatim
def tubeThomStableClassOne : StableSpherePi (m + 2) := tubeThomStableClass 1


-- @@ L834-838 verbatim
theorem tubeThomGenLoop_north_fiber (k : ℕ) (t : I^(Fin (m + 3))) :
    tubeThomGenLoop (m := m) k t = tubeNorth ↔
      cubeToTubeAmbient t ∈ standardCircle := by
  rw [tubeThomGenLoop_apply]
  exact tubeThomCollapse_eq_north_iff k


-- @@ L840-842 verbatim
/-- A cubical parameter for every point of the standard circle. -/
def circleCubePoint (θ : ℝ) : I^(Fin (m + 3)) := fun i =>
  Set.projIcc (0 : ℝ) 1 zero_le_one ((circleAt (m := m) θ i + 3) / 6)


-- @@ L844-851 verbatim
lemma circleCubePoint_coe (θ : ℝ) (i : Fin (m + 3)) :
    ((circleCubePoint (m := m) θ i : I) : ℝ) = (circleAt θ i + 3) / 6 := by
  have habs : |circleAt (m := m) θ i| ≤ 1 := by
    rw [← norm_circleAt (m := m) θ]
    exact abs_coordinate_le_norm (circleAt (m := m) θ) i
  have hb := abs_le.mp habs
  rw [circleCubePoint, Set.coe_projIcc, min_eq_right (by linarith),
    max_eq_right (by linarith)]


-- @@ L853-859 verbatim
lemma cubeToTubeAmbient_circleCubePoint (θ : ℝ) :
    cubeToTubeAmbient (m := m) (circleCubePoint θ) = circleAt θ := by
  apply (WithLp.equiv 2 _).injective
  funext i
  change 6 * (((circleCubePoint (m := m) θ i : I) : ℝ)) - 3 = circleAt θ i
  rw [circleCubePoint_coe]
  ring


-- @@ L861-864 verbatim
@[simp] theorem tubeThomGenLoop_circleCubePoint (k : ℕ) (θ : ℝ) :
    tubeThomGenLoop (m := m) k (circleCubePoint θ) = tubeNorth := by
  rw [tubeThomGenLoop_apply, cubeToTubeAmbient_circleCubePoint]
  exact tubeThomCollapse_circleAt k θ


-- @@ L866-866 verbatim
/-! ### Framing/parity contract exposed to the delta calculation -/


-- @@ L868-871 verbatim
/-- The parity carried by the twist-`k` normal framing.  The differential theorem
`fderiv_tubeCollapseHorizontal_nuVec` is the geometric realization of this
declared twist. -/
def tubeTwistParity (k : ℕ) : ZMod 2 := k


-- @@ L873-873 verbatim
@[simp] theorem tubeTwistParity_zero : tubeTwistParity 0 = 0 := rfl


-- @@ L875-875 verbatim
@[simp] theorem tubeTwistParity_one : tubeTwistParity 1 = 1 := rfl


-- @@ L877-891 verbatim
/-- Packaged local regular-fiber data needed when the north fiber is converted to
a `FramedLevelSet` component. -/
structure TubeNorthFiberContract (k : ℕ) where
  fiber_eq : {v : E | tubeThomCollapse (m := m) k v = tubeNorth} =
    standardCircle (m := m)
  localMapSmooth : ContDiff ℝ ∞ (tubeCollapseHorizontal (m := m) k)
  localFiber : ∀ {v : E}, v ∈ tubeRegion (m := m) (1 / 4) →
    (tubeCollapseHorizontal (m := m) k v = 0 ↔ v ∈ standardCircle)
  regular : ∀ θ, Function.Surjective
    (fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ))
  frame : ∀ θ (i : Fin (m + 2)),
    fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ) (nuVec k θ i)
      = EuclideanSpace.single i 1
  parity : ZMod 2
  parity_eq : parity = k


-- @@ L893-901 verbatim
/-- The explicit collapse satisfies the full local regular-fiber/framing contract. -/
def tubeNorthFiberContract (k : ℕ) : TubeNorthFiberContract (m := m) k where
  fiber_eq := tubeThomCollapse_fiber k
  localMapSmooth := contDiff_tubeCollapseHorizontal k
  localFiber := fun hv => tubeCollapseHorizontal_eq_zero_iff_standardCircle k hv
  regular := surjective_fderiv_tubeCollapseHorizontal_circleAt k
  frame := fderiv_tubeCollapseHorizontal_nuVec k
  parity := tubeTwistParity k
  parity_eq := rfl


-- @@ L903-904 verbatim
@[simp] theorem tubeNorthFiberContract_parity (k : ℕ) :
    (tubeNorthFiberContract (m := m) k).parity = (k : ZMod 2) := rfl


-- @@ L906-909 verbatim
theorem tubeNorthFiberContract_zero_one_parity_ne :
    (tubeNorthFiberContract (m := m) 0).parity ≠
      (tubeNorthFiberContract (m := m) 1).parity := by
  norm_num


-- @@ L911-911 verbatim
end Submission
