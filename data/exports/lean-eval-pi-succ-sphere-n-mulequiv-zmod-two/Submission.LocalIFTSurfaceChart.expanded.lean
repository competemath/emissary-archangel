import Mathlib
import Submission.MorseGenericity2D


-- @@ L4-12 verbatim
/-!
# Constructing local IFT surface charts

This file constructs the two free coordinates on the zero surface of a regular
framed cobordism.  The free coordinates are the kernel coordinates supplied by
the complemented-kernel implicit function theorem.  A compactly supported
smooth cutoff will then turn the local parametrization into the globally smooth
map required by `IFTSurfaceChart`, without changing it near the origin.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Function Metric Filter

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-23 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L24-24 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L25-25 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L27-27 verbatim
namespace LocalIFTSurfaceChart


-- @@ L29-43 verbatim
/-- Rank-nullity identifies the kernel of a regular cobordism differential as
the required two-dimensional free-coordinate space. -/
theorem finrank_ker_fderiv (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    Module.finrank ℝ (fderiv ℝ C.G v).ker = 2 := by
  let D : E' →L[ℝ] F := fderiv ℝ C.G v
  have hrange : D.toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr hreg
  have hrank := D.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hrank
  have hF : Module.finrank ℝ F = n := finrank_euclideanSpace_fin
  have hE : Module.finrank ℝ E' = n + 2 := finrank_euclideanSpace_fin
  change Module.finrank ℝ D.toLinearMap.ker = 2
  rw [hF, hE] at hrank
  omega


-- @@ L45-51 verbatim
/-- A continuous linear identification of the free two-dimensional parameter
space with the kernel of the regular differential. -/
def kernelEquiv (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    E₂ ≃L[ℝ] (fderiv ℝ C.G v).ker :=
  ContinuousLinearEquiv.ofFinrankEq <| by
    rw [finrank_euclideanSpace_fin, finrank_ker_fderiv C hreg]


-- @@ L53-64 verbatim
/-- The complemented-kernel implicit-function package at a regular fiber
point.  Its right coordinate is the canonical projection to the differential
kernel chosen by Mathlib. -/
def implicitData (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ImplicitFunctionData ℝ E' F (fderiv ℝ C.G v).ker := by
  let D : E' →L[ℝ] F := fderiv ℝ C.G v
  have hstrict : HasStrictFDerivAt C.G D v :=
    C.smooth.hasStrictFDerivAt (by simp)
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hreg
  exact hstrict.implicitFunctionDataOfComplemented C.G D hrange
    D.ker_closedComplemented_of_finiteDimensional_range


-- @@ L66-71 verbatim
/-- The raw local parametrization supplied by the implicit function theorem.
It is intentionally kept separate from its later compactly supported smooth
extension. -/
def rawParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) (u : E₂) : E' :=
  (implicitData C hreg).implicitFunction (C.G v) (kernelEquiv C hreg u)


-- @@ L73-76 verbatim
@[simp] theorem implicitData_leftFun (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    (implicitData C hreg).leftFun = C.G :=
  rfl


-- @@ L78-81 verbatim
@[simp] theorem implicitData_pt (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    (implicitData C hreg).pt = v :=
  rfl


-- @@ L83-86 verbatim
@[simp] theorem implicitData_rightFun_pt (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    (implicitData C hreg).rightFun v = 0 := by
  simp [implicitData]


-- @@ L88-98 verbatim
private theorem parameter_tendsto (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    Tendsto (fun u : E₂ => (C.G v, kernelEquiv C hreg u)) (nhds 0)
      (nhds ((implicitData C hreg).prodFun (implicitData C hreg).pt)) := by
  have hconst : ContinuousAt (fun _ : E₂ => C.G v) 0 := continuousAt_const
  have h := hconst.prodMk (kernelEquiv C hreg).continuous.continuousAt
  have hbase : (implicitData C hreg).prodFun (implicitData C hreg).pt =
      (C.G v, kernelEquiv C hreg (0 : E₂)) := by
    simp [ImplicitFunctionData.prodFun]
  rw [hbase]
  exact h


-- @@ L100-107 verbatim
@[simp] theorem rawParam_zero (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    rawParam C hreg 0 = v := by
  let d := implicitData C hreg
  have hleft :=
    d.toOpenPartialHomeomorph.left_inv d.pt_mem_toOpenPartialHomeomorph_source
  simpa [rawParam, d, ImplicitFunctionData.implicitFunction_apply,
    ImplicitFunctionData.toOpenPartialHomeomorph_apply] using hleft


-- @@ L109-117 verbatim
/-- The raw parameter map lies in the desired zero fiber on a neighborhood of
the origin. -/
theorem eventually_rawParam_fiber (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) (hreg : Surjective (fderiv ℝ C.G v)) :
    ∀ᶠ u : E₂ in nhds 0, C.G (rawParam C hreg u) = 0 := by
  let d := implicitData C hreg
  have h := (parameter_tendsto C hreg).eventually d.leftFun_implicitFunction
  filter_upwards [h] with u hu
  simpa [d, rawParam, hv] using hu


-- @@ L119-128 verbatim
/-- The canonical kernel projection recovers the raw parameter exactly near
the origin. -/
theorem eventually_rightFun_rawParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ∀ᶠ u : E₂ in nhds 0,
      (implicitData C hreg).rightFun (rawParam C hreg u) = kernelEquiv C hreg u := by
  let d := implicitData C hreg
  have h := (parameter_tendsto C hreg).eventually d.rightFun_implicitFunction
  filter_upwards [h] with u hu
  simpa [d, rawParam] using hu


-- @@ L130-135 verbatim
/-- Ambient linear coordinates whose restriction to the differential kernel is
the chosen `E₂` coordinate system. -/
def ambientCoordinates (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) : E' →L[ℝ] E₂ :=
  (kernelEquiv C hreg).symm.toContinuousLinearMap.comp
    (implicitData C hreg).rightDeriv


-- @@ L137-151 verbatim
/-- The ambient coordinates recover the raw surface parameter exactly near the
origin. -/
theorem eventually_ambientCoordinates_rawParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ∀ᶠ u : E₂ in nhds 0,
      ambientCoordinates C hreg (rawParam C hreg u - v) = u := by
  filter_upwards [eventually_rightFun_rawParam C hreg] with u hu
  change (kernelEquiv C hreg).symm
      ((implicitData C hreg).rightDeriv (rawParam C hreg u - v)) = u
  calc
    _ = (kernelEquiv C hreg).symm
        ((implicitData C hreg).rightFun (rawParam C hreg u)) := by
      rfl
    _ = (kernelEquiv C hreg).symm (kernelEquiv C hreg u) := by rw [hu]
    _ = u := (kernelEquiv C hreg).symm_apply_apply u


-- @@ L153-158 verbatim
/-- Lift an `E₂` covector through the ambient kernel coordinates. -/
def liftCovector (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    E₂ →L[ℝ] (E' →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E' E₂ ℝ).flip (ambientCoordinates C hreg)).comp
    (innerSL ℝ (E := E₂)).flip


-- @@ L160-165 verbatim
@[simp] theorem liftCovector_apply (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) (q : E₂) (w : E') :
    liftCovector C hreg q w = (innerSL ℝ q) (ambientCoordinates C hreg w) := by
  simp [liftCovector, ContinuousLinearMap.flip_apply, flip_innerSL_real,
    innerSL_apply_apply]
  rfl


-- @@ L167-174 verbatim
/-- Exact local covector recovery for the raw parametrization. -/
theorem eventually_liftCovector_rawParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ∀ᶠ u : E₂ in nhds 0, ∀ q : E₂,
      liftCovector C hreg q (rawParam C hreg u - v) = (innerSL ℝ q) u := by
  filter_upwards [eventually_ambientCoordinates_rawParam C hreg] with u hu
  intro q
  rw [liftCovector_apply, hu]


-- @@ L176-187 verbatim
/-- The product map straightened by the implicit-function package is globally
smooth in the present finite-dimensional setting. -/
theorem contDiff_prodFun (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ContDiff ℝ ∞ (implicitData C hreg).prodFun := by
  let d := implicitData C hreg
  have hright : ContDiff ℝ ∞ d.rightFun := by
    change ContDiff ℝ ∞
      (fun x : E' => d.rightDeriv (x - v))
    exact d.rightDeriv.contDiff.comp (contDiff_id.sub contDiff_const)
  change ContDiff ℝ ∞ (fun x : E' => (C.G x, d.rightFun x))
  exact C.smooth.prodMk hright


-- @@ L189-205 verbatim
/-- The raw parametrization tends to its center. -/
theorem continuousAt_rawParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ContinuousAt (rawParam C hreg) 0 := by
  let d := implicitData C hreg
  have hs : ContinuousAt d.toOpenPartialHomeomorph.symm (d.prodFun d.pt) := by
    exact d.toOpenPartialHomeomorph.continuousAt_symm
      d.map_pt_mem_toOpenPartialHomeomorph_target
  have ht := hs.tendsto.comp (parameter_tendsto C hreg)
  change Tendsto (rawParam C hreg) (nhds 0) (nhds (rawParam C hreg 0))
  convert ht using 1
  · ext u
    rfl
  · rw [rawParam_zero C hreg]
    have hleft :=
      d.toOpenPartialHomeomorph.left_inv d.pt_mem_toOpenPartialHomeomorph_source
    simpa [d, ImplicitFunctionData.toOpenPartialHomeomorph_apply] using hleft.symm


-- @@ L207-216 verbatim
/-- Parameters at which the local inverse is inside its target and the
derivative of the straightening map is still a continuous linear
equivalence. -/
def smoothDomain (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) : Set E₂ :=
  {u | (C.G v, kernelEquiv C hreg u) ∈
      (implicitData C hreg).toOpenPartialHomeomorph.target ∧
    ∃ A : E' ≃L[ℝ] (F × (fderiv ℝ C.G v).ker),
      (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker)) =
        fderiv ℝ (implicitData C hreg).prodFun (rawParam C hreg u)}


-- @@ L218-262 verbatim
/-- The inverse remains smooth on a genuine neighborhood of the origin. -/
theorem smoothDomain_mem_nhds (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    smoothDomain C hreg ∈ nhds (0 : E₂) := by
  let d := implicitData C hreg
  have htarget : {u : E₂ | (C.G v, kernelEquiv C hreg u) ∈
      d.toOpenPartialHomeomorph.target} ∈ nhds (0 : E₂) :=
    (parameter_tendsto C hreg).eventually
      (d.toOpenPartialHomeomorph.open_target.mem_nhds
        d.map_pt_mem_toOpenPartialHomeomorph_target)
  obtain ⟨A₀, hA₀⟩ := d.isInvertible_fderiv_prodFun
  have hinvertible_nhds :
      {L : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker) |
        ∃ A : E' ≃L[ℝ] (F × (fderiv ℝ C.G v).ker),
          (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker)) = L} ∈
        nhds (fderiv ℝ d.prodFun v) := by
    change Set.range (fun A : E' ≃L[ℝ]
      (F × (fderiv ℝ C.G v).ker) =>
        (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker))) ∈
      nhds (fderiv ℝ d.prodFun v)
    have h := A₀.nhds
    rw [hA₀] at h
    have hdpt : d.pt = v := rfl
    rw [hdpt] at h
    exact h
  have hderiv_at_center :
      {x : E' | ∃ A : E' ≃L[ℝ] (F × (fderiv ℝ C.G v).ker),
        (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker)) =
          fderiv ℝ d.prodFun x} ∈ nhds v := by
    exact (contDiff_prodFun C hreg).continuous_fderiv (by simp) |>.continuousAt
      |>.preimage_mem_nhds hinvertible_nhds
  have hderiv :
      {u : E₂ | ∃ A : E' ≃L[ℝ] (F × (fderiv ℝ C.G v).ker),
        (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker)) =
          fderiv ℝ d.prodFun (rawParam C hreg u)} ∈ nhds (0 : E₂) :=
    by
      have hderiv_at_zero :
          {x : E' | ∃ A : E' ≃L[ℝ] (F × (fderiv ℝ C.G v).ker),
            (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker)) =
              fderiv ℝ d.prodFun x} ∈ nhds (rawParam C hreg 0) := by
        rw [show nhds (rawParam C hreg 0) = nhds v from
          congrArg nhds (rawParam_zero C hreg)]
        exact hderiv_at_center
      exact (continuousAt_rawParam C hreg).preimage_mem_nhds hderiv_at_zero
  exact inter_mem htarget hderiv


-- @@ L264-291 verbatim
/-- On `smoothDomain`, the raw inverse is smooth to every order. -/
theorem contDiffAt_rawParam_of_mem (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ smoothDomain C hreg) :
    ContDiffAt ℝ ∞ (rawParam C hreg) u := by
  let d := implicitData C hreg
  rcases hu with ⟨htarget, A, hA⟩
  let y : F × (fderiv ℝ C.G v).ker :=
    (C.G v, kernelEquiv C hreg u)
  have hprod : ContDiff ℝ ∞ d.prodFun := contDiff_prodFun C hreg
  have hderiv : HasFDerivAt d.prodFun
      (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker))
      (rawParam C hreg u) := by
    rw [hA]
    exact (hprod.differentiable (by simp) (rawParam C hreg u)).hasFDerivAt
  have hderiv' : HasFDerivAt d.toOpenPartialHomeomorph
      (A : E' →L[ℝ] (F × (fderiv ℝ C.G v).ker))
      (d.toOpenPartialHomeomorph.symm y) := by
    simpa [d, y, rawParam, ImplicitFunctionData.implicitFunction_apply] using hderiv
  have hs : ContDiffAt ℝ ∞ d.toOpenPartialHomeomorph.symm y :=
    d.toOpenPartialHomeomorph.contDiffAt_symm htarget hderiv' hprod.contDiffAt
  have hp : ContDiffAt ℝ ∞
      (fun z : E₂ => (C.G v, kernelEquiv C hreg z)) u :=
    contDiffAt_const.prodMk (kernelEquiv C hreg).contDiff.contDiffAt
  have hc := hs.comp u hp
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with z
  rfl


-- @@ L293-297 verbatim
/-- A closed parameter ball contained in the smooth inverse domain. -/
theorem exists_extensionRadius (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E₂) r ⊆ smoothDomain C hreg :=
  Metric.nhds_basis_closedBall.mem_iff.mp (smoothDomain_mem_nhds C hreg)


-- @@ L299-302 verbatim
/-- Outer radius of the standard cutoff used to globalize `rawParam`. -/
def extensionRadius (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) : ℝ :=
  Classical.choose (exists_extensionRadius C hreg)


-- @@ L304-307 verbatim
theorem extensionRadius_pos (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    0 < extensionRadius C hreg :=
  (Classical.choose_spec (exists_extensionRadius C hreg)).1


-- @@ L309-312 verbatim
theorem closedBall_extensionRadius_subset (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    closedBall (0 : E₂) (extensionRadius C hreg) ⊆ smoothDomain C hreg :=
  (Classical.choose_spec (exists_extensionRadius C hreg)).2


-- @@ L314-321 verbatim
/-- A smooth cutoff equal to one on the half-radius ball and supported in the
outer extension ball. -/
def extensionBump (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) : ContDiffBump (0 : E₂) where
  rIn := extensionRadius C hreg / 2
  rOut := extensionRadius C hreg
  rIn_pos := half_pos (extensionRadius_pos C hreg)
  rIn_lt_rOut := half_lt_self (extensionRadius_pos C hreg)


-- @@ L323-326 verbatim
@[simp] theorem extensionBump_rIn (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    (extensionBump C hreg).rIn = extensionRadius C hreg / 2 :=
  rfl


-- @@ L328-331 verbatim
@[simp] theorem extensionBump_rOut (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    (extensionBump C hreg).rOut = extensionRadius C hreg :=
  rfl


-- @@ L333-337 verbatim
theorem tsupport_extensionBump_subset (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    tsupport (extensionBump C hreg) ⊆ smoothDomain C hreg := by
  rw [ContDiffBump.tsupport_eq, extensionBump_rOut]
  exact closedBall_extensionRadius_subset C hreg


-- @@ L339-343 verbatim
/-- The globally smooth extension.  It agrees with the raw IFT inverse on the
inner ball and is the constant center outside the cutoff support. -/
def globalParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) (u : E₂) : E' :=
  v + extensionBump C hreg u • (rawParam C hreg u - v)


-- @@ L345-361 verbatim
theorem contDiff_globalParam (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    ContDiff ℝ ∞ (globalParam C hreg) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ smoothDomain C hreg
  · exact contDiffAt_const.add
      ((extensionBump C hreg).contDiffAt.smul
        ((contDiffAt_rawParam_of_mem C hreg hx).sub contDiffAt_const))
  · have hxt : x ∉ tsupport (extensionBump C hreg) :=
      fun hmem => hx (tsupport_extensionBump_subset C hreg hmem)
    rw [notMem_tsupport_iff_eventuallyEq] at hxt
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hxt] with y hy
    change globalParam C hreg y = v
    rw [globalParam, hy]
    simp


-- @@ L363-371 verbatim
/-- On the inner ball, the global extension is literally the raw local
inverse. -/
theorem globalParam_eq_rawParam_of_mem_closedBall (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ closedBall (0 : E₂) (extensionRadius C hreg / 2)) :
    globalParam C hreg u = rawParam C hreg u := by
  rw [globalParam, (extensionBump C hreg).one_of_mem_closedBall]
  · simp
  · simpa using hu


-- @@ L373-381 verbatim
/-- The straightening map and its local inverse are exact inverses at every
parameter in `smoothDomain`. -/
theorem prodFun_rawParam_of_mem_smoothDomain (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ smoothDomain C hreg) :
    (implicitData C hreg).prodFun (rawParam C hreg u) =
      (C.G v, kernelEquiv C hreg u) := by
  have h := (implicitData C hreg).toOpenPartialHomeomorph.right_inv hu.1
  simpa [rawParam, ImplicitFunctionData.implicitFunction_apply] using h


-- @@ L383-388 verbatim
theorem rawParam_fiber_of_mem_smoothDomain (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ smoothDomain C hreg) :
    C.G (rawParam C hreg u) = 0 := by
  have h := congrArg Prod.fst (prodFun_rawParam_of_mem_smoothDomain C hreg hu)
  simpa [ImplicitFunctionData.prodFun, hv] using h


-- @@ L390-395 verbatim
theorem rightFun_rawParam_of_mem_smoothDomain (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ smoothDomain C hreg) :
    (implicitData C hreg).rightFun (rawParam C hreg u) = kernelEquiv C hreg u := by
  have h := congrArg Prod.snd (prodFun_rawParam_of_mem_smoothDomain C hreg hu)
  simpa [ImplicitFunctionData.prodFun] using h


-- @@ L397-409 verbatim
theorem ambientCoordinates_rawParam_of_mem_smoothDomain
    (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ smoothDomain C hreg) :
    ambientCoordinates C hreg (rawParam C hreg u - v) = u := by
  change (kernelEquiv C hreg).symm
      ((implicitData C hreg).rightDeriv (rawParam C hreg u - v)) = u
  calc
    _ = (kernelEquiv C hreg).symm
        ((implicitData C hreg).rightFun (rawParam C hreg u)) := by rfl
    _ = (kernelEquiv C hreg).symm (kernelEquiv C hreg u) := by
      rw [rightFun_rawParam_of_mem_smoothDomain C hreg hu]
    _ = u := (kernelEquiv C hreg).symm_apply_apply u


-- @@ L411-417 verbatim
theorem liftCovector_rawParam_of_mem_smoothDomain
    (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ smoothDomain C hreg) (q : E₂) :
    liftCovector C hreg q (rawParam C hreg u - v) = (innerSL ℝ q) u := by
  rw [liftCovector_apply,
    ambientCoordinates_rawParam_of_mem_smoothDomain C hreg hu]


-- @@ L419-423 verbatim
/-- The open domain on which the global extension is unchanged from the IFT
inverse. -/
def chartDomain (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) : Set E₂ :=
  ball (0 : E₂) (extensionRadius C hreg / 2)


-- @@ L425-428 verbatim
theorem isOpen_chartDomain (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    IsOpen (chartDomain C hreg) := by
  exact isOpen_ball


-- @@ L430-433 verbatim
theorem chartDomain_mem_nhds (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    chartDomain C hreg ∈ nhds (0 : E₂) := by
  exact ball_mem_nhds _ (half_pos (extensionRadius_pos C hreg))


-- @@ L435-444 verbatim
theorem chartDomain_subset_smoothDomain (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) :
    chartDomain C hreg ⊆ smoothDomain C hreg := by
  intro u hu
  apply closedBall_extensionRadius_subset C hreg
  have hu' : dist u 0 < extensionRadius C hreg / 2 := by
    simpa [chartDomain, dist_comm] using hu
  apply mem_closedBall'.mpr
  simpa [dist_comm] using hu'.le.trans
    (half_le_self (extensionRadius_pos C hreg).le)


-- @@ L446-454 verbatim
theorem globalParam_eq_rawParam_of_mem_chartDomain
    (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {u : E₂}
    (hu : u ∈ chartDomain C hreg) :
    globalParam C hreg u = rawParam C hreg u := by
  apply globalParam_eq_rawParam_of_mem_closedBall C hreg
  apply mem_closedBall'.mpr
  simpa [dist_comm] using (show dist u 0 < extensionRadius C hreg / 2 by
    simpa [chartDomain, dist_comm] using hu).le


-- @@ L456-479 verbatim
/-- The actual production chart centered at an arbitrary regular fiber point. -/
def localChart (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : IFTSurfaceChart C where
  center := v
  domain := chartDomain C (C.regular v hv)
  domain_mem_nhds := chartDomain_mem_nhds C (C.regular v hv)
  param := globalParam C (C.regular v hv)
  param_smooth := contDiff_globalParam C (C.regular v hv)
  param_zero := by
    have hzero : (0 : E₂) ∈ chartDomain C (C.regular v hv) :=
      mem_ball_self (half_pos (extensionRadius_pos C (C.regular v hv)))
    rw [globalParam_eq_rawParam_of_mem_chartDomain C (C.regular v hv) hzero,
      rawParam_zero]
  param_fiber := by
    intro u hu
    rw [globalParam_eq_rawParam_of_mem_chartDomain C (C.regular v hv) hu]
    exact rawParam_fiber_of_mem_smoothDomain C hv (C.regular v hv)
      (chartDomain_subset_smoothDomain C (C.regular v hv) hu)
  liftCovector := liftCovector C (C.regular v hv)
  lift_param := by
    intro q u hu
    rw [globalParam_eq_rawParam_of_mem_chartDomain C (C.regular v hv) hu]
    exact liftCovector_rawParam_of_mem_smoothDomain C (C.regular v hv)
      (chartDomain_subset_smoothDomain C (C.regular v hv) hu) q


-- @@ L481-484 verbatim
@[simp] theorem localChart_center (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) :
    (localChart C hv).center = v :=
  rfl


-- @@ L486-489 verbatim
@[simp] theorem localChart_param (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) :
    (localChart C hv).param = globalParam C (C.regular v hv) :=
  rfl


-- @@ L491-495 verbatim
/-- Every point of the regular zero fiber admits a localized IFT surface
chart. -/
theorem nonempty_iftSurfaceChart (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : Nonempty (IFTSurfaceChart C) :=
  ⟨localChart C hv⟩


-- @@ L497-497 verbatim
/-! ## A compact-core chart neighborhood for finite subcovers -/


-- @@ L499-503 verbatim
/-- A smaller compact parameter core.  The factor four leaves room between
the core and the cutoff boundary. -/
def localCore (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : Set E₂ :=
  closedBall (0 : E₂) (extensionRadius C (C.regular v hv) / 4)


-- @@ L505-511 verbatim
/-- Ambient points in the IFT source whose free coordinate lies in the open
quarter-radius ball. -/
def localAmbient (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : Set E' :=
  (implicitData C (C.regular v hv)).toOpenPartialHomeomorph.source ∩
    (fun x => ambientCoordinates C (C.regular v hv) (x - v)) ⁻¹'
      ball (0 : E₂) (extensionRadius C (C.regular v hv) / 4)


-- @@ L513-515 verbatim
theorem isCompact_localCore (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : IsCompact (localCore C hv) :=
  isCompact_closedBall _ _


-- @@ L517-528 verbatim
theorem localCore_subset_chartDomain (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) :
    localCore C hv ⊆ (localChart C hv).domain := by
  intro u hu
  change u ∈ ball (0 : E₂) (extensionRadius C (C.regular v hv) / 2)
  have hu' : dist u 0 ≤ extensionRadius C (C.regular v hv) / 4 := by
    simpa [localCore, dist_comm] using hu
  have hr : extensionRadius C (C.regular v hv) / 4 <
      extensionRadius C (C.regular v hv) / 2 := by
    linarith [extensionRadius_pos C (C.regular v hv)]
  apply mem_ball'.mpr
  simpa [dist_comm] using hu'.trans_lt hr


-- @@ L530-535 verbatim
theorem isOpen_localAmbient (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : IsOpen (localAmbient C hv) := by
  apply (implicitData C (C.regular v hv)).toOpenPartialHomeomorph.open_source.inter
  apply isOpen_ball.preimage
  exact (ambientCoordinates C (C.regular v hv)).continuous.comp
    (continuous_id.sub continuous_const)


-- @@ L537-543 verbatim
theorem center_mem_localAmbient (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : v ∈ localAmbient C hv := by
  refine ⟨(implicitData C (C.regular v hv)).pt_mem_toOpenPartialHomeomorph_source, ?_⟩
  change ambientCoordinates C (C.regular v hv) (v - v) ∈
    ball (0 : E₂) (extensionRadius C (C.regular v hv) / 4)
  simp only [sub_self, map_zero]
  exact mem_ball_self (div_pos (extensionRadius_pos C (C.regular v hv)) (by norm_num))


-- @@ L545-557 verbatim
/-- Rich local data in exactly the form consumed by compact finite-subcover
arguments. -/
structure LocalChartNeighborhood (C : FramedLevelCobordism n) (v : E') where
  chart : IFTSurfaceChart C
  chart_center : chart.center = v
  ambient : Set E'
  ambient_open : IsOpen ambient
  center_mem_ambient : v ∈ ambient
  core : Set E₂
  compact_core : IsCompact core
  core_subset_domain : core ⊆ chart.domain
  fiber_ambient_subset_param_core :
    {x : E' | C.G x = 0} ∩ ambient ⊆ chart.param '' core


-- @@ L559-577 verbatim
/-- A fiber point in the ambient chart neighborhood is recovered by applying
the raw inverse to its ambient free coordinate. -/
theorem rawParam_ambientCoordinates_eq (C : FramedLevelCobordism n) {v x : E'}
    (hv : C.G v = 0) (hx : C.G x = 0) (hxa : x ∈ localAmbient C hv) :
    rawParam C (C.regular v hv)
      (ambientCoordinates C (C.regular v hv) (x - v)) = x := by
  let d := implicitData C (C.regular v hv)
  let e := kernelEquiv C (C.regular v hv)
  let u : E₂ := ambientCoordinates C (C.regular v hv) (x - v)
  have hpair : (C.G v, e u) = d.prodFun x := by
    apply Prod.ext
    · simpa [d, ImplicitFunctionData.prodFun, hv] using hx.symm
    · change e (e.symm (d.rightDeriv (x - v))) = d.rightFun x
      rw [e.apply_symm_apply]
      rfl
  have hleft := d.toOpenPartialHomeomorph.left_inv hxa.1
  change d.implicitFunction (C.G v) (e u) = x
  rw [ImplicitFunctionData.implicitFunction_apply, hpair]
  exact hleft


-- @@ L579-595 verbatim
theorem fiber_localAmbient_subset_param_localCore
    (C : FramedLevelCobordism n) {v : E'} (hv : C.G v = 0) :
    {x : E' | C.G x = 0} ∩ localAmbient C hv ⊆
      (localChart C hv).param '' localCore C hv := by
  intro x hx
  let u : E₂ := ambientCoordinates C (C.regular v hv) (x - v)
  have huCore : u ∈ localCore C hv := by
    apply mem_closedBall'.mpr
    have huBall := hx.2.2
    change u ∈ ball (0 : E₂)
      (extensionRadius C (C.regular v hv) / 4) at huBall
    exact (mem_ball'.mp huBall).le
  refine ⟨u, huCore, ?_⟩
  change globalParam C (C.regular v hv) u = x
  rw [globalParam_eq_rawParam_of_mem_chartDomain C (C.regular v hv)
    (localCore_subset_chartDomain C hv huCore)]
  exact rawParam_ambientCoordinates_eq C hv hx.1 hx.2


-- @@ L597-608 verbatim
/-- The compact-core local neighborhood attached to a regular fiber point. -/
def localChartNeighborhood (C : FramedLevelCobordism n) {v : E'}
    (hv : C.G v = 0) : LocalChartNeighborhood C v where
  chart := localChart C hv
  chart_center := rfl
  ambient := localAmbient C hv
  ambient_open := isOpen_localAmbient C hv
  center_mem_ambient := center_mem_localAmbient C hv
  core := localCore C hv
  compact_core := isCompact_localCore C hv
  core_subset_domain := localCore_subset_chartDomain C hv
  fiber_ambient_subset_param_core := fiber_localAmbient_subset_param_localCore C hv


-- @@ L610-610 verbatim
end LocalIFTSurfaceChart


-- @@ L612-612 verbatim
end Submission
