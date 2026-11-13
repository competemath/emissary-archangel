import Mathlib
import Submission.MorsePosition
import Submission.FiberSign


-- @@ L5-22 verbatim
/-!
# Quantitative vertical perturbations of framed level cobordisms

This file implements the ambient-replacement layer used before Morse event
analysis.  A scalar amplitude `a` produces the vertical map

`Φₐ(v) = v + a(v) eₜ`.

The derivative is the explicit rank-one operator `I + da ⊗ eₜ`.  Its
surjectivity reduces to the single scalar condition `1 + da(eₜ) ≠ 0`.  Pulling a
cobordism map back along `Φₐ` therefore preserves regularity, spatial boundedness,
and both end presentations whenever `a` vanishes on the time collars.

The second half constructs compactly supported smooth cutoffs and shows that an
arbitrary localized affine time tilt can always be scaled into the quantitative
regularity range.  This is the concrete cutoff/vertical-replacement primitive
needed by the finite-chart Sard argument.
-/


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open Set Function Metric

-- @@ L27-27 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval Manifold


-- @@ L29-29 verbatim
namespace Submission


-- @@ L31-31 verbatim
variable {n : ℕ}


-- @@ L33-33 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L34-34 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L36-36 verbatim
/-! ## The vertical rank-one derivative -/


-- @@ L38-40 verbatim
/-- The vertical shift with scalar amplitude `a`. -/
def verticalShift (a : E' → ℝ) (v : E') : E' :=
  v + a v • timeVec


-- @@ L42-44 verbatim
/-- The derivative model `I + A ⊗ eₜ`. -/
def verticalLinear (A : E' →L[ℝ] ℝ) : E' →L[ℝ] E' :=
  ContinuousLinearMap.id ℝ E' + A.smulRight timeVec


-- @@ L46-48 verbatim
@[simp] theorem verticalLinear_apply (A : E' →L[ℝ] ℝ) (z : E') :
    verticalLinear A z = z + A z • timeVec := by
  simp [verticalLinear]


-- @@ L50-54 verbatim
@[simp] theorem initCLM_timeVec :
    initCLM (n + 1) (timeVec (n := n)) = 0 := by
  ext i
  rw [initCLM_apply]
  simp [timeVec_apply]


-- @@ L56-58 verbatim
@[simp] theorem initCLM_verticalShift (a : E' → ℝ) (v : E') :
    initCLM (n + 1) (verticalShift a v) = initCLM (n + 1) v := by
  simp [verticalShift]


-- @@ L60-62 verbatim
@[simp] theorem tcoord_verticalShift (a : E' → ℝ) (v : E') :
    tcoord (verticalShift a v) = tcoord v + a v := by
  simp [verticalShift]


-- @@ L64-66 verbatim
theorem contDiff_verticalShift {a : E' → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (verticalShift a) := by
  exact contDiff_id.add (ha.smul contDiff_const)


-- @@ L68-73 verbatim
theorem hasFDerivAt_verticalShift {a : E' → ℝ} (ha : Differentiable ℝ a)
    (v : E') :
    HasFDerivAt (verticalShift a) (verticalLinear (fderiv ℝ a v)) v := by
  change HasFDerivAt (fun y => y + a y • timeVec)
    (ContinuousLinearMap.id ℝ E' + (fderiv ℝ a v).smulRight timeVec) v
  exact (hasFDerivAt_id v).add ((ha v).hasFDerivAt.smul_const timeVec)


-- @@ L75-77 verbatim
theorem fderiv_verticalShift {a : E' → ℝ} (ha : Differentiable ℝ a) (v : E') :
    fderiv ℝ (verticalShift a) v = verticalLinear (fderiv ℝ a v) :=
  (hasFDerivAt_verticalShift ha v).fderiv


-- @@ L79-99 verbatim
/-- Explicit right inverse calculation for a vertical rank-one update. -/
theorem surjective_verticalLinear (A : E' →L[ℝ] ℝ)
    (hden : 1 + A timeVec ≠ 0) :
    Surjective (verticalLinear A) := by
  intro y
  let x₀ := spaceInclL (spacePart y)
  let s := (tcoord y - A x₀) / (1 + A timeVec)
  refine ⟨x₀ + s • timeVec, ?_⟩
  have hx₀ : x₀ + tcoord y • timeVec = y := by
    rw [← spaceTime_eq, spaceTime_spacePart]
  have hs : s * (1 + A timeVec) = tcoord y - A x₀ := by
    exact div_mul_cancel₀ _ hden
  have hcoef : s + (A x₀ + s * A timeVec) = tcoord y := by
    linarith
  calc
    verticalLinear A (x₀ + s • timeVec)
        = x₀ + s • timeVec + (A x₀ + s * A timeVec) • timeVec := by
            rw [verticalLinear_apply, map_add, map_smul, smul_eq_mul]
    _ = x₀ + (s + (A x₀ + s * A timeVec)) • timeVec := by
          rw [add_assoc, ← add_smul]
    _ = y := by rw [hcoef, hx₀]


-- @@ L101-108 verbatim
/-- The easy quantitative criterion used for scaled cutoffs. -/
theorem vertical_den_ne_zero_of_norm_lt_one (A : E' →L[ℝ] ℝ)
    (hA : ‖A‖ < 1) : 1 + A timeVec ≠ 0 := by
  intro hzero
  have hval : A timeVec = -1 := by linarith
  have hle := A.le_opNorm (timeVec (n := n))
  rw [norm_timeVec, mul_one, hval, norm_neg, norm_one] at hle
  linarith


-- @@ L110-110 verbatim
/-! ## Pullback of a cobordism by a vertical replacement -/


-- @@ L112-117 verbatim
/-- Quantitative admissibility conditions on a vertical amplitude. -/
structure VerticalAmplitude where
  toFun : E' → ℝ
  smooth : ContDiff ℝ ∞ toFun
  collar_zero : ∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → toFun v = 0
  vertical_regular : ∀ v, 1 + fderiv ℝ toFun v timeVec ≠ 0


-- @@ L119-119 verbatim
namespace VerticalAmplitude


-- @@ L121-122 verbatim
instance : CoeFun (VerticalAmplitude (n := n)) fun _ => E' → ℝ :=
  ⟨VerticalAmplitude.toFun⟩


-- @@ L124-127 verbatim
/-- The actual replaced cobordism map. -/
def pullbackMap (C : FramedLevelCobordism n) (a : VerticalAmplitude (n := n)) :
    E' → F :=
  C.G ∘ verticalShift a


-- @@ L129-132 verbatim
theorem smooth_pullbackMap (C : FramedLevelCobordism n)
    (a : VerticalAmplitude (n := n)) :
    ContDiff ℝ ∞ (a.pullbackMap C) :=
  C.smooth.comp (contDiff_verticalShift a.smooth)


-- @@ L134-137 verbatim
theorem surjective_fderiv_verticalShift (a : VerticalAmplitude (n := n)) (v : E') :
    Surjective (fderiv ℝ (verticalShift a) v) := by
  rw [fderiv_verticalShift (a.smooth.differentiable (by simp))]
  exact surjective_verticalLinear _ (a.vertical_regular v)


-- @@ L139-180 verbatim
/-- Pull back `G` along the vertical replacement.  This is a fully constructed
`FramedLevelCobordism`, not a regularity contract: regularity follows from the
rank-one calculation above and spatial boundedness is unchanged because the map
does not move spatial coordinates. -/
def pullback (C : FramedLevelCobordism n) (a : VerticalAmplitude (n := n)) :
    FramedLevelCobordism n where
  X₀ := C.X₀
  X₁ := C.X₁
  G := a.pullbackMap C
  smooth := a.smooth_pullbackMap C
  spatial_bounded := by
    obtain ⟨R, hR⟩ := C.spatial_bounded
    refine ⟨R, ?_⟩
    intro v hv
    have h := hR (verticalShift a v) hv
    simpa using h
  regular := by
    intro v hv
    have hC : Surjective (fderiv ℝ C.G (verticalShift a v)) := C.regular _ hv
    have hφ : Surjective (fderiv ℝ (verticalShift a) v) :=
      a.surjective_fderiv_verticalShift v
    have hcomp : fderiv ℝ (a.pullbackMap C) v =
        (fderiv ℝ C.G (verticalShift a v)).comp
          (fderiv ℝ (verticalShift a) v) := by
      exact (C.smooth.differentiable (by simp) _).hasFDerivAt.comp v
        ((contDiff_verticalShift a.smooth).differentiable (by simp) v).hasFDerivAt |>.fderiv
    rw [hcomp, ContinuousLinearMap.coe_comp]
    exact hC.comp hφ
  collar_zero := by
    intro x t ht
    have ha : a (spaceTime x t) = 0 :=
      a.collar_zero _ (Or.inl (by
        simpa [tcoord, spaceTime, Fin.snoc_last] using ht))
    rw [pullbackMap, Function.comp_apply, verticalShift, ha, zero_smul, add_zero]
    exact C.collar_zero x t ht
  collar_one := by
    intro x t ht
    have ha : a (spaceTime x t) = 0 :=
      a.collar_zero _ (Or.inr (by
        simpa [tcoord, spaceTime, Fin.snoc_last] using ht))
    rw [pullbackMap, Function.comp_apply, verticalShift, ha, zero_smul, add_zero]
    exact C.collar_one x t ht


-- @@ L182-183 verbatim
@[simp] theorem pullback_X₀ (C : FramedLevelCobordism n)
    (a : VerticalAmplitude (n := n)) : (a.pullback C).X₀ = C.X₀ := rfl


-- @@ L185-186 verbatim
@[simp] theorem pullback_X₁ (C : FramedLevelCobordism n)
    (a : VerticalAmplitude (n := n)) : (a.pullback C).X₁ = C.X₁ := rfl


-- @@ L188-190 verbatim
@[simp] theorem pullback_G (C : FramedLevelCobordism n)
    (a : VerticalAmplitude (n := n)) (v : E') :
    (a.pullback C).G v = C.G (verticalShift a v) := rfl


-- @@ L192-197 verbatim
/-- A north/south label pulls back along exactly the same replacement. -/
def pullbackSide {C : FramedLevelCobordism n} (a : VerticalAmplitude (n := n))
    (L : FiberSide C) : FiberSide (a.pullback C) where
  side := L.side ∘ verticalShift a
  continuous := L.continuous.comp (contDiff_verticalShift a.smooth).continuous
  nonzero_on_fiber := fun v hv => L.nonzero_on_fiber (verticalShift a v) hv


-- @@ L199-201 verbatim
@[simp] theorem pullbackSide_apply {C : FramedLevelCobordism n}
    (a : VerticalAmplitude (n := n)) (L : FiberSide C) (v : E') :
    (a.pullbackSide L).side v = L.side (verticalShift a v) := rfl


-- @@ L203-209 verbatim
/-- The `FiberSide` view of a signed cobordism. -/
def signedFiberSide {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀}
    {S₁ : FiberSign X₁} (C : SignedFramedLevelCobordism S₀ S₁) :
    FiberSide C.cobordism where
  side := C.toFun
  continuous := C.continuous
  nonzero_on_fiber := C.nonzero


-- @@ L211-239 verbatim
/-- Vertical replacement of a signed cobordism.  The sign is pulled back by the
same map, hence remains nonzero; because the replacement is the identity on both
collars, the two prescribed end labels are unchanged. -/
def pullbackSigned {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀}
    {S₁ : FiberSign X₁} (a : VerticalAmplitude (n := n))
    (C : SignedFramedLevelCobordism S₀ S₁) :
    SignedFramedLevelCobordism S₀ S₁ where
  cobordism := a.pullback C.cobordism
  source_eq := by rw [pullback_X₀]; exact C.source_eq
  target_eq := by rw [pullback_X₁]; exact C.target_eq
  toFun := C.toFun ∘ verticalShift a
  continuous := C.continuous.comp (contDiff_verticalShift a.smooth).continuous
  nonzero := fun v hv => C.nonzero (verticalShift a v) hv
  collar_zero := by
    intro x t ht
    have ha : a (spaceTime x t) = 0 :=
      a.collar_zero _ (Or.inl (by
        simpa [tcoord, spaceTime, Fin.snoc_last] using ht))
    change C.toFun (verticalShift a (spaceTime x t)) = S₀ x
    rw [verticalShift, ha, zero_smul, add_zero]
    exact C.collar_zero x t ht
  collar_one := by
    intro x t ht
    have ha : a (spaceTime x t) = 0 :=
      a.collar_zero _ (Or.inr (by
        simpa [tcoord, spaceTime, Fin.snoc_last] using ht))
    change C.toFun (verticalShift a (spaceTime x t)) = S₁ x
    rw [verticalShift, ha, zero_smul, add_zero]
    exact C.collar_one x t ht


-- @@ L241-244 verbatim
@[simp] theorem pullbackSigned_toFun {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (a : VerticalAmplitude (n := n)) (C : SignedFramedLevelCobordism S₀ S₁)
    (v : E') : (a.pullbackSigned C).toFun v = C.toFun (verticalShift a v) := rfl


-- @@ L246-246 verbatim
end VerticalAmplitude


-- @@ L248-248 verbatim
/-! ## Compactly supported smooth cutoffs -/


-- @@ L250-258 verbatim
/-- A concrete smooth Urysohn cutoff: it is one on `K`, zero off `U`, takes
values in `[0,1]`, and has compact support. -/
structure SmoothCutoff (K U : Set E') where
  toFun : E' → ℝ
  smooth : ContDiff ℝ ∞ toFun
  eq_zero : ∀ v ∈ Uᶜ, toFun v = 0
  eq_one : ∀ v ∈ K, toFun v = 1
  range : ∀ v, toFun v ∈ Icc (0 : ℝ) 1
  compact_support : HasCompactSupport toFun


-- @@ L260-260 verbatim
namespace SmoothCutoff


-- @@ L262-263 verbatim
instance {K U : Set E'} : CoeFun (SmoothCutoff K U) fun _ => E' → ℝ :=
  ⟨SmoothCutoff.toFun⟩


-- @@ L265-289 verbatim
/-- Smooth Urysohn produces a compactly supported cutoff whenever the closed core
`K` lies in an open set `U` with compact closure. -/
theorem exists_of_isClosed_isOpen {K U : Set E'} (hK : IsClosed K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUc : IsCompact (closure U)) :
    Nonempty (SmoothCutoff K U) := by
  have hs : IsClosed Uᶜ := hU.isClosed_compl
  have hd : Disjoint Uᶜ K := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    exact hxU (hKU hxK)
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ E') (n := (⊤ : ℕ∞)) hs hK hd
  have hf_smooth : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  have hsupp : HasCompactSupport (⇑f) := by
    have hsupport : support (⇑f) ⊆ U := by
      intro x hx
      by_contra hxU
      exact hx (hf0 hxU)
    have htsupport : tsupport (⇑f) ⊆ closure U :=
      closure_minimal (hsupport.trans subset_closure) isClosed_closure
    exact IsCompact.of_isClosed_subset hUc isClosed_closure htsupport
  exact ⟨⟨⇑f, hf_smooth, hf0, hf1, hf01, hsupp⟩⟩


-- @@ L291-302 verbatim
/-- A standard compactly supported bump which is one on the half-radius closed
ball and zero outside the full-radius open ball. -/
theorem exists_ball (center : E') {r : ℝ} (hr : 0 < r) :
    Nonempty (SmoothCutoff (closedBall center (r / 2)) (ball center r)) := by
  apply exists_of_isClosed_isOpen Metric.isClosed_closedBall Metric.isOpen_ball
  · intro v hv
    rw [mem_closedBall] at hv
    rw [mem_ball]
    linarith
  · apply IsCompact.of_isClosed_subset (isCompact_closedBall center r)
      isClosed_closure
    exact closure_minimal ball_subset_closedBall Metric.isClosed_closedBall


-- @@ L304-312 verbatim
/-- The time coordinate is one-Lipschitz.  This elementary estimate makes the
radius needed to keep a local replacement away from both collars explicit. -/
theorem abs_tcoord_sub_le_norm_sub (v w : E') :
    |tcoord v - tcoord w| ≤ ‖v - w‖ := by
  calc
    |tcoord v - tcoord w| = |tcoord (v - w)| := by rw [tcoord_sub]
    _ = |⟪timeVec, v - w⟫| := by rw [inner_timeVec]
    _ ≤ ‖timeVec (n := n)‖ * ‖v - w‖ := abs_real_inner_le_norm _ _
    _ = ‖v - w‖ := by rw [norm_timeVec, one_mul]


-- @@ L314-325 verbatim
/-- A sufficiently small ball about an interior point is contained in the open
middle slab. -/
theorem ball_subset_middleSlab (center : E') {r : ℝ}
    (hleft : r < tcoord center - 1 / 4)
    (hright : r < 3 / 4 - tcoord center) :
    ball center r ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  intro v hv
  rw [mem_ball, dist_eq_norm] at hv
  have habs : |tcoord v - tcoord center| < r :=
    (abs_tcoord_sub_le_norm_sub v center).trans_lt hv
  have hrange := abs_lt.mp habs
  exact ⟨by linarith, by linarith⟩


-- @@ L327-329 verbatim
/-- Multiply an arbitrary smooth scalar jet by the cutoff. -/
def localize {K U : Set E'} (χ : SmoothCutoff K U) (h : E' → ℝ) : E' → ℝ :=
  fun v => χ v * h v


-- @@ L331-334 verbatim
theorem contDiff_localize {K U : Set E'} (χ : SmoothCutoff K U)
    {h : E' → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (χ.localize h) :=
  χ.smooth.mul hh


-- @@ L336-338 verbatim
theorem localize_eq_zero {K U : Set E'} (χ : SmoothCutoff K U)
    (h : E' → ℝ) {v : E'} (hv : v ∈ Uᶜ) : χ.localize h v = 0 := by
  simp [localize, χ.eq_zero v hv]


-- @@ L340-342 verbatim
theorem localize_eq {K U : Set E'} (χ : SmoothCutoff K U)
    (h : E' → ℝ) {v : E'} (hv : v ∈ K) : χ.localize h v = h v := by
  simp [localize, χ.eq_one v hv]


-- @@ L344-353 verbatim
theorem hasCompactSupport_localize {K U : Set E'} (χ : SmoothCutoff K U)
    (h : E' → ℝ) : HasCompactSupport (χ.localize h) := by
  apply IsCompact.of_isClosed_subset χ.compact_support isClosed_closure
  apply closure_minimal
  · intro v hv
    apply subset_closure
    intro hχ
    apply hv
    simp [localize, hχ]
  · exact isClosed_closure


-- @@ L355-363 verbatim
/-- A cutoff supported in the open middle slab vanishes on both collars. -/
theorem localize_collar_zero {K U : Set E'} (χ : SmoothCutoff K U)
    (hU : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)) (h : E' → ℝ) :
    ∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → χ.localize h v = 0 := by
  intro v hv
  apply χ.localize_eq_zero h
  intro hvU
  have hvt := hU hvU
  rcases hv with hv | hv <;> linarith [hvt.1, hvt.2]


-- @@ L365-365 verbatim
/-! ### Exact localized affine tilts -/


-- @@ L367-369 verbatim
/-- An affine scalar jet centered at `center`. -/
def affineJet (A : E' →L[ℝ] ℝ) (center : E') (c : ℝ) (v : E') : ℝ :=
  A (v - center) + c


-- @@ L371-373 verbatim
theorem contDiff_affineJet (A : E' →L[ℝ] ℝ) (center : E') (c : ℝ) :
    ContDiff ℝ ∞ (affineJet A center c) := by
  exact (A.contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const


-- @@ L375-381 verbatim
/-- The localized affine tilt agrees literally with its requested affine jet on
the cutoff core. -/
theorem localize_affineJet_eq {K U : Set E'} (χ : SmoothCutoff K U)
    (A : E' →L[ℝ] ℝ) (center : E') (c : ℝ) {v : E'} (hv : v ∈ K) :
    χ.localize (affineJet A center c) v = A (v - center) + c := by
  rw [χ.localize_eq _ hv]
  rfl


-- @@ L383-389 verbatim
theorem tcoord_verticalShift_localizedAffine {K U : Set E'}
    (χ : SmoothCutoff K U) (A : E' →L[ℝ] ℝ) (center : E') (c : ℝ)
    {v : E'} (hv : v ∈ K) :
    tcoord (verticalShift (χ.localize (affineJet A center c)) v) =
      tcoord v + A (v - center) + c := by
  rw [tcoord_verticalShift, χ.localize_affineJet_eq A center c hv]
  ring


-- @@ L391-391 verbatim
end SmoothCutoff


-- @@ L393-393 verbatim
/-! ## Automatic small scaling -/


-- @@ L395-395 verbatim
namespace VerticalAmplitude


-- @@ L397-405 verbatim
/-- Any smooth collar-supported amplitude whose derivative has norm below one is
admissible.  The scalar condition is discharged by the rank-one estimate. -/
def ofNormFDerivLtOne (a : E' → ℝ) (ha : ContDiff ℝ ∞ a)
    (hcollar : ∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → a v = 0)
    (hsmall : ∀ v, ‖fderiv ℝ a v‖ < 1) : VerticalAmplitude (n := n) where
  toFun := a
  smooth := ha
  collar_zero := hcollar
  vertical_regular := fun v => vertical_den_ne_zero_of_norm_lt_one _ (hsmall v)


-- @@ L407-435 verbatim
/-- A compactly supported smooth collar-preserving jet has a positive scale
small enough to define a globally regular vertical replacement.  The returned
identity `a = ε • raw` makes the perturbation size available to later estimates. -/
theorem exists_scaled (raw : E' → ℝ) (hraw : ContDiff ℝ ∞ raw)
    (hsupp : HasCompactSupport raw)
    (hcollar : ∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw v = 0) :
    ∃ ε > 0, ∃ a : VerticalAmplitude (n := n),
      a.toFun = fun v => ε * raw v := by
  obtain ⟨K, hK⟩ := hraw.lipschitzWith_of_hasCompactSupport hsupp (by simp)
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hK0 : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  have hεK : ε * (K : ℝ) < 1 := by
    change (1 / (2 * ((K : ℝ) + 1))) * (K : ℝ) < 1
    rw [one_div, inv_mul_eq_div]
    exact (div_lt_one hden).2 (by linarith)
  let scaled : E' → ℝ := fun v => ε * raw v
  have hscaled : ContDiff ℝ ∞ scaled := contDiff_const.mul hraw
  have hfd (v : E') : fderiv ℝ scaled v = ε • fderiv ℝ raw v := by
    exact ((hraw.differentiable (by simp) v).hasFDerivAt.const_mul ε).fderiv
  have hsmall (v : E') : ‖fderiv ℝ scaled v‖ < 1 := by
    rw [hfd, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hderiv : ‖fderiv ℝ raw v‖ ≤ (K : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hK
    exact (mul_le_mul_of_nonneg_left hderiv hε.le).trans_lt hεK
  refine ⟨ε, hε, ofNormFDerivLtOne scaled hscaled ?_ hsmall, rfl⟩
  intro v hv
  simp [scaled, hcollar v hv]


-- @@ L437-448 verbatim
/-- Concrete specialization: every localized smooth jet supported in the middle
slab can be scaled and pulled back to a cobordism with exactly the same ends. -/
theorem exists_pullback_localized {K U : Set E'} (χ : SmoothCutoff K U)
    (hU : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    (h : E' → ℝ) (hh : ContDiff ℝ ∞ h) (C : FramedLevelCobordism n) :
    ∃ ε > 0, ∃ a : VerticalAmplitude (n := n),
      a.toFun = (fun v => ε * χ.localize h v) ∧
      (a.pullback C).X₀ = C.X₀ ∧ (a.pullback C).X₁ = C.X₁ := by
  obtain ⟨ε, hε, a, ha⟩ := exists_scaled (χ.localize h)
    (χ.contDiff_localize hh) (χ.hasCompactSupport_localize h)
    (χ.localize_collar_zero hU h)
  exact ⟨ε, hε, a, ha, rfl, rfl⟩


-- @@ L450-477 verbatim
/-- Fully concrete local tilt.  Around any point whose radius stays inside the
middle slab, the replacement amplitude is literally the requested affine jet on
the half ball, while the resulting cobordism has the original two ends. -/
theorem exists_pullback_affine_at (C : FramedLevelCobordism n) (center : E')
    {r : ℝ} (hr : 0 < r)
    (hleft : r < tcoord center - 1 / 4)
    (hright : r < 3 / 4 - tcoord center)
    (A : E' →L[ℝ] ℝ) (c : ℝ) :
    ∃ ε > 0, ∃ a : VerticalAmplitude (n := n),
      (a.pullback C).X₀ = C.X₀ ∧ (a.pullback C).X₁ = C.X₁ ∧
      ∀ v ∈ closedBall center (r / 2),
        a v = ε * (A (v - center) + c) ∧
        tcoord (verticalShift a v) =
          tcoord v + ε * (A (v - center) + c) := by
  let χ := (SmoothCutoff.exists_ball center hr).some
  have hU := SmoothCutoff.ball_subset_middleSlab center hleft hright
  obtain ⟨ε, hε, a, ha, hX₀, hX₁⟩ :=
    exists_pullback_localized χ hU (SmoothCutoff.affineJet A center c)
      (SmoothCutoff.contDiff_affineJet A center c) C
  refine ⟨ε, hε, a, hX₀, hX₁, ?_⟩
  intro v hv
  have hχ : χ.localize (SmoothCutoff.affineJet A center c) v =
      A (v - center) + c := χ.localize_affineJet_eq A center c hv
  have hav : a v = ε * (A (v - center) + c) := by
    rw [show a.toFun v = ε * χ.localize
      (SmoothCutoff.affineJet A center c) v by rw [ha]]
    rw [hχ]
  exact ⟨hav, by rw [tcoord_verticalShift, hav]⟩


-- @@ L479-479 verbatim
/-! ## Finite composition of local replacements -/


-- @@ L481-486 verbatim
/-- The identity replacement. -/
def zero : VerticalAmplitude (n := n) where
  toFun := 0
  smooth := contDiff_const
  collar_zero := by simp
  vertical_regular := by simp


-- @@ L488-488 verbatim
@[simp] theorem zero_apply (v : E') : (zero (n := n)) v = 0 := rfl


-- @@ L490-492 verbatim
@[simp] theorem verticalShift_zero (v : E') :
    verticalShift (zero (n := n)) v = v := by
  simp [verticalShift]


-- @@ L494-527 verbatim
/-- Composition law for vertical replacements.  `a.after b` first applies `b`
and then `a`; its amplitude is the explicit semidirect sum
`b(v) + a(Φ_b(v))`. -/
def after (a b : VerticalAmplitude (n := n)) : VerticalAmplitude (n := n) where
  toFun := fun v => b v + a (verticalShift b v)
  smooth := b.smooth.add (a.smooth.comp (contDiff_verticalShift b.smooth))
  collar_zero := by
    intro v hv
    have hb : b v = 0 := b.collar_zero v hv
    have hshift : verticalShift b v = v := by simp [verticalShift, hb]
    have ha : a (verticalShift b v) = 0 := by
      rw [hshift]
      exact a.collar_zero v hv
    simp [hb, ha]
  vertical_regular := by
    intro v
    let db := fderiv ℝ b.toFun v
    let da := fderiv ℝ a.toFun (verticalShift b v)
    have hfd : fderiv ℝ (fun w => b w + a (verticalShift b w)) v =
        db + da.comp (verticalLinear db) := by
      have hbder := (b.smooth.differentiable (by simp) v).hasFDerivAt
      have hshiftder := hasFDerivAt_verticalShift
        (b.smooth.differentiable (by simp)) v
      have hader := (a.smooth.differentiable (by simp) (verticalShift b v)).hasFDerivAt
      exact (hbder.add (hader.comp v hshiftder)).fderiv
    rw [hfd]
    have ha : 1 + da timeVec ≠ 0 := a.vertical_regular (verticalShift b v)
    have hb : 1 + db timeVec ≠ 0 := b.vertical_regular v
    have heq : 1 + (db + da.comp (verticalLinear db)) timeVec =
        (1 + da timeVec) * (1 + db timeVec) := by
      simp [verticalLinear_apply]
      ring
    rw [heq]
    exact mul_ne_zero ha hb


-- @@ L529-532 verbatim
theorem verticalShift_after (a b : VerticalAmplitude (n := n)) (v : E') :
    verticalShift (a.after b) v = verticalShift a (verticalShift b v) := by
  simp only [after, verticalShift]
  rw [add_smul, add_assoc]


-- @@ L534-540 verbatim
/-- Pullback by a composite amplitude agrees pointwise with two successive
pullbacks.  This is the bookkeeping lemma for a finite chart-by-chart
perturbation. -/
theorem pullback_after_G (C : FramedLevelCobordism n)
    (a b : VerticalAmplitude (n := n)) (v : E') :
    ((a.after b).pullback C).G v = (b.pullback (a.pullback C)).G v := by
  rw [pullback_G, pullback_G, pullback_G, verticalShift_after]


-- @@ L542-545 verbatim
/-- Compose a finite list of localized replacements. -/
def composeList : List (VerticalAmplitude (n := n)) → VerticalAmplitude (n := n)
  | [] => zero
  | a :: as => (composeList as).after a


-- @@ L547-548 verbatim
@[simp] theorem composeList_nil :
    composeList ([] : List (VerticalAmplitude (n := n))) = zero := rfl


-- @@ L550-552 verbatim
@[simp] theorem composeList_cons (a : VerticalAmplitude (n := n))
    (as : List (VerticalAmplitude (n := n))) :
    composeList (a :: as) = (composeList as).after a := rfl


-- @@ L554-554 verbatim
end VerticalAmplitude


-- @@ L556-556 verbatim
/-! ## The ambient map is a genuine diffeomorphism in the small regime -/


-- @@ L558-563 verbatim
/-- A quantitatively small amplitude.  The Lipschitz constant below one gives a
global inverse by Banach's fixed-point theorem, not merely a local inverse. -/
structure SmallVerticalAmplitude extends VerticalAmplitude (n := n) where
  K : NNReal
  K_lt_one : K < 1
  lipschitz : LipschitzWith K toFun


-- @@ L565-565 verbatim
namespace SmallVerticalAmplitude


-- @@ L567-568 verbatim
instance : CoeFun (SmallVerticalAmplitude (n := n)) fun _ => E' → ℝ :=
  ⟨fun a => a.toFun⟩


-- @@ L570-572 verbatim
/-- The contraction whose fixed point is the inverse image of `y`. -/
def inverseIteration (a : SmallVerticalAmplitude (n := n)) (y x : E') : E' :=
  y - a x • timeVec


-- @@ L574-589 verbatim
theorem lipschitz_inverseIteration (a : SmallVerticalAmplitude (n := n)) (y : E') :
    LipschitzWith a.K (a.inverseIteration y) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x z
  have ha := a.lipschitz.dist_le_mul x z
  have hdist : dist (a.inverseIteration y x) (a.inverseIteration y z) =
      dist (a x) (a z) := by
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (y - a x • timeVec) - (y - a z • timeVec) =
        -((a x - a z) • timeVec) := by
      rw [sub_smul]
      abel
    rw [inverseIteration, inverseIteration, hsub, norm_neg, norm_smul,
      norm_timeVec, mul_one, Real.norm_eq_abs]
  rw [hdist]
  exact ha


-- @@ L591-593 verbatim
theorem contracting_inverseIteration (a : SmallVerticalAmplitude (n := n)) (y : E') :
    ContractingWith a.K (a.inverseIteration y) :=
  ⟨a.K_lt_one, a.lipschitz_inverseIteration y⟩


-- @@ L595-608 verbatim
/-- Every point has a preimage, constructed as the Banach fixed point. -/
theorem surjective_verticalShift (a : SmallVerticalAmplitude (n := n)) :
    Surjective (verticalShift a) := by
  intro y
  let hcon := a.contracting_inverseIteration y
  let x : E' := hcon.fixedPoint (a.inverseIteration y)
  have hfix : a.inverseIteration y x = x :=
    hcon.fixedPoint_isFixedPt
  refine ⟨x, ?_⟩
  calc
    verticalShift a x = x + a x • timeVec := rfl
    _ = (y - a x • timeVec) + a x • timeVec :=
      congrArg (fun z => z + a x • timeVec) hfix.symm
    _ = y := sub_add_cancel _ _


-- @@ L610-632 verbatim
/-- The same smallness estimate gives global injectivity. -/
theorem injective_verticalShift (a : SmallVerticalAmplitude (n := n)) :
    Injective (verticalShift a) := by
  intro x z hxz
  have hzero : (verticalShift a x) - (verticalShift a z) = 0 := by
    rw [hxz, sub_self]
  have hsub : x - z = -((a x - a z) • timeVec) := by
    calc
      x - z = ((verticalShift a x) - (verticalShift a z)) -
          ((a x - a z) • timeVec) := by
            simp only [verticalShift]
            rw [sub_smul]
            abel
      _ = -((a x - a z) • timeVec) := by rw [hzero, zero_sub]
  have hnorm : ‖x - z‖ = |a x - a z| := by
    rw [hsub, norm_neg, norm_smul, norm_timeVec, mul_one, Real.norm_eq_abs]
  have hlip := a.lipschitz.dist_le_mul x z
  rw [Real.dist_eq, dist_eq_norm, ← hnorm] at hlip
  have hK : (a.K : ℝ) < 1 := by exact_mod_cast a.K_lt_one
  have hnorm0 : ‖x - z‖ = 0 := by
    have hn := norm_nonneg (x - z)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)


-- @@ L634-636 verbatim
theorem bijective_verticalShift (a : SmallVerticalAmplitude (n := n)) :
    Bijective (verticalShift a) :=
  ⟨a.injective_verticalShift, a.surjective_verticalShift⟩


-- @@ L638-640 verbatim
/-- The global equivalence underlying the ambient diffeomorphism. -/
def equiv (a : SmallVerticalAmplitude (n := n)) : E' ≃ E' :=
  Equiv.ofBijective (verticalShift a) a.bijective_verticalShift


-- @@ L642-643 verbatim
@[simp] theorem equiv_apply (a : SmallVerticalAmplitude (n := n)) (v : E') :
    a.equiv v = verticalShift a v := rfl


-- @@ L645-687 verbatim
/-- Compact support supplies a global Lipschitz bound; an explicit positive scale
then turns any smooth middle-slab jet into a small vertical amplitude. -/
theorem exists_scaled (raw : E' → ℝ) (hraw : ContDiff ℝ ∞ raw)
    (hsupp : HasCompactSupport raw)
    (hcollar : ∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw v = 0) :
    ∃ ε > 0, ∃ a : SmallVerticalAmplitude (n := n),
      a.toFun = fun v => ε * raw v := by
  obtain ⟨K, hK⟩ := hraw.lipschitzWith_of_hasCompactSupport hsupp (by simp)
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hK0 : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  have hεK : ε * (K : ℝ) < 1 := by
    change (1 / (2 * ((K : ℝ) + 1))) * (K : ℝ) < 1
    rw [one_div, inv_mul_eq_div]
    exact (div_lt_one hden).2 (by linarith)
  let κ : NNReal := ⟨ε * (K : ℝ), mul_nonneg hε.le hK0⟩
  have hκ : κ < 1 := by exact_mod_cast hεK
  let scaled : E' → ℝ := fun v => ε * raw v
  have hscaled : ContDiff ℝ ∞ scaled := contDiff_const.mul hraw
  have hscaledLip : LipschitzWith κ scaled := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x z
    have h := hK.dist_le_mul x z
    have h' := mul_le_mul_of_nonneg_left h hε.le
    dsimp [scaled, κ]
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hε]
    change ε * |raw x - raw z| ≤ (ε * (K : ℝ)) * dist x z
    exact h'.trans_eq (by ring)
  have hfd (v : E') : fderiv ℝ scaled v = ε • fderiv ℝ raw v := by
    exact ((hraw.differentiable (by simp) v).hasFDerivAt.const_mul ε).fderiv
  have hsmall (v : E') : ‖fderiv ℝ scaled v‖ < 1 := by
    rw [hfd, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hderiv : ‖fderiv ℝ raw v‖ ≤ (K : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hK
    exact (mul_le_mul_of_nonneg_left hderiv hε.le).trans_lt hεK
  let base := VerticalAmplitude.ofNormFDerivLtOne scaled hscaled
    (fun v hv => by simp [scaled, hcollar v hv]) hsmall
  refine ⟨ε, hε, {
    toVerticalAmplitude := base
    K := κ
    K_lt_one := hκ
    lipschitz := hscaledLip }, rfl⟩


-- @@ L689-726 verbatim
/-- The inverse supplied by the global equivalence is smooth.  Locally it agrees
with the inverse-function-theorem inverse; global injectivity identifies the two
branches. -/
theorem contDiff_equiv_symm (a : SmallVerticalAmplitude (n := n)) :
    ContDiff ℝ ∞ a.equiv.symm := by
  rw [contDiff_iff_contDiffAt]
  intro y
  let x : E' := a.equiv.symm y
  have hxy : verticalShift a x = y := by
    change a.equiv x = y
    exact a.equiv.apply_symm_apply y
  have hsurj : Surjective (fderiv ℝ (verticalShift a) x) :=
    a.toVerticalAmplitude.surjective_fderiv_verticalShift x
  have hinj : Injective (fderiv ℝ (verticalShift a) x) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  let L : E' ≃L[ℝ] E' := ContinuousLinearEquiv.ofBijective
    (fderiv ℝ (verticalShift a) x) (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj)
  have hLcoe : (L : E' →L[ℝ] E') = fderiv ℝ (verticalShift a) x := rfl
  have hderiv : HasFDerivAt (verticalShift a) (L : E' →L[ℝ] E') x := by
    rw [hLcoe]
    exact ((contDiff_verticalShift a.smooth).differentiable (by simp) x).hasFDerivAt
  have hcd : ContDiffAt ℝ ∞ (verticalShift a) x :=
    (contDiff_verticalShift a.smooth).contDiffAt
  have hlocal : ContDiffAt ℝ ∞ (hcd.localInverse hderiv (by simp))
      (verticalShift a x) := hcd.to_localInverse hderiv (by simp)
  have hleft : ∀ᶠ z in 𝓝 x,
      a.equiv.symm (verticalShift a z) = z := by
    filter_upwards [] with z
    change a.equiv.symm (a.equiv z) = z
    exact a.equiv.symm_apply_apply z
  have hstrict := hcd.hasStrictFDerivAt' hderiv (by simp)
  have heq : a.equiv.symm =ᶠ[𝓝 (verticalShift a x)]
      hcd.localInverse hderiv (by simp) :=
    hstrict.localInverse_unique hleft
  have hinvAt : ContDiffAt ℝ ∞ a.equiv.symm (verticalShift a x) :=
    hlocal.congr_of_eventuallyEq heq
  rwa [hxy] at hinvAt


-- @@ L728-736 verbatim
/-- The vertical map as an actual global `C^∞` ambient diffeomorphism. -/
def diffeomorph (a : SmallVerticalAmplitude (n := n)) : E' ≃ₘ[ℝ] E' where
  toEquiv := a.equiv
  contMDiff_toFun := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_verticalShift a.smooth
  contMDiff_invFun := by
    rw [contMDiff_iff_contDiff]
    exact a.contDiff_equiv_symm


-- @@ L738-739 verbatim
@[simp] theorem diffeomorph_apply (a : SmallVerticalAmplitude (n := n)) (v : E') :
    a.diffeomorph v = verticalShift a v := rfl


-- @@ L741-768 verbatim
/-- Strong form of the local affine replacement theorem: the map used to pull
back the cobordism is the global ambient diffeomorphism `a.diffeomorph`. -/
theorem exists_diffeomorphic_pullback_affine_at
    (C : FramedLevelCobordism n) (center : E') {r : ℝ} (hr : 0 < r)
    (hleft : r < tcoord center - 1 / 4)
    (hright : r < 3 / 4 - tcoord center)
    (A : E' →L[ℝ] ℝ) (c : ℝ) :
    ∃ ε > 0, ∃ a : SmallVerticalAmplitude (n := n),
      (a.toVerticalAmplitude.pullback C).X₀ = C.X₀ ∧
      (a.toVerticalAmplitude.pullback C).X₁ = C.X₁ ∧
      (∀ v ∈ closedBall center (r / 2),
        a v = ε * (A (v - center) + c) ∧
        tcoord (a.diffeomorph v) =
          tcoord v + ε * (A (v - center) + c)) := by
  let χ := (SmoothCutoff.exists_ball center hr).some
  let raw := χ.localize (SmoothCutoff.affineJet A center c)
  have hU := SmoothCutoff.ball_subset_middleSlab center hleft hright
  obtain ⟨ε, hε, a, ha⟩ := SmallVerticalAmplitude.exists_scaled raw
    (χ.contDiff_localize (SmoothCutoff.contDiff_affineJet A center c))
    (χ.hasCompactSupport_localize _)
    (χ.localize_collar_zero hU _)
  refine ⟨ε, hε, a, rfl, rfl, ?_⟩
  intro v hv
  have hraw : raw v = A (v - center) + c := by
    exact χ.localize_affineJet_eq A center c hv
  have hav : a v = ε * (A (v - center) + c) := by
    rw [show a.toFun v = ε * raw v by rw [ha], hraw]
  exact ⟨hav, by rw [diffeomorph_apply, tcoord_verticalShift, hav]⟩


-- @@ L770-770 verbatim
end SmallVerticalAmplitude


-- @@ L772-772 verbatim
/-! ## Downstream Morse package -/


-- @@ L774-778 verbatim
/-- The output of the perturbation stage: a concrete vertical replacement and a
verified Morse atlas on the resulting cobordism. -/
structure MorsePerturbation (C : FramedLevelCobordism n) where
  amplitude : VerticalAmplitude (n := n)
  atlas : MorseAtlas (amplitude.pullback C)


-- @@ L780-780 verbatim
namespace MorsePerturbation


-- @@ L782-785 verbatim
/-- The perturbed cobordism. -/
def cobordism {C : FramedLevelCobordism n} (P : MorsePerturbation C) :
    FramedLevelCobordism n :=
  P.amplitude.pullback C


-- @@ L787-788 verbatim
@[simp] theorem cobordism_X₀ {C : FramedLevelCobordism n} (P : MorsePerturbation C) :
    P.cobordism.X₀ = C.X₀ := rfl


-- @@ L790-791 verbatim
@[simp] theorem cobordism_X₁ {C : FramedLevelCobordism n} (P : MorsePerturbation C) :
    P.cobordism.X₁ = C.X₁ := rfl


-- @@ L793-796 verbatim
/-- The finite event schedule supplied to M2c. -/
def position {C : FramedLevelCobordism n} (P : MorsePerturbation C) :
    MorsePosition P.cobordism :=
  P.atlas.toMorsePosition


-- @@ L798-803 verbatim
/-- Pulling back a side label produces the north-only event schedule without any
additional nonvanishing argument. -/
def labeledPosition {C : FramedLevelCobordism n} (P : MorsePerturbation C)
    (L : FiberSide C) : LabeledMorsePosition P.cobordism where
  position := P.position
  sideLabel := P.amplitude.pullbackSide L


-- @@ L805-805 verbatim
end MorsePerturbation


-- @@ L807-807 verbatim
/-! ## Signed input and the north-only schedule -/


-- @@ L809-815 verbatim
/-- Perturbation output specialized to the signed bridge cobordisms produced by
`exists_signedBridgeCobordism`. -/
structure SignedMorsePerturbation {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁) where
  amplitude : VerticalAmplitude (n := n)
  atlas : MorseAtlas (amplitude.pullback C.cobordism)


-- @@ L817-817 verbatim
namespace SignedMorsePerturbation


-- @@ L819-822 verbatim
def signedCobordism {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀}
    {S₁ : FiberSign X₁} {C : SignedFramedLevelCobordism S₀ S₁}
    (P : SignedMorsePerturbation C) : SignedFramedLevelCobordism S₀ S₁ :=
  P.amplitude.pullbackSigned C


-- @@ L824-828 verbatim
@[simp] theorem signedCobordism_source_eq {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁} (P : SignedMorsePerturbation C) :
    P.signedCobordism.cobordism.X₀ = X₀ :=
  P.signedCobordism.source_eq


-- @@ L830-834 verbatim
@[simp] theorem signedCobordism_target_eq {X₀ X₁ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁} (P : SignedMorsePerturbation C) :
    P.signedCobordism.cobordism.X₁ = X₁ :=
  P.signedCobordism.target_eq


-- @@ L836-842 verbatim
/-- The schedule consumed by the positive-fiber M2 event argument. -/
def labeledPosition {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀}
    {S₁ : FiberSign X₁} {C : SignedFramedLevelCobordism S₀ S₁}
    (P : SignedMorsePerturbation C) :
    LabeledMorsePosition P.signedCobordism.cobordism where
  position := P.atlas.toMorsePosition
  sideLabel := VerticalAmplitude.signedFiberSide P.signedCobordism


-- @@ L844-844 verbatim
end SignedMorsePerturbation


-- @@ L846-846 verbatim
namespace MorseAtlas


-- @@ L848-858 verbatim
/-- An empty critical locus carries the unique vacuous Morse atlas. -/
theorem of_coreCriticalPoints_eq_empty (C : FramedLevelCobordism n)
    (hcrit : coreCriticalPoints C = ∅) : MorseAtlas C where
  localModel := by
    intro v hv
    rw [hcrit] at hv
    exact (by simpa using hv : False).elim
  distinct_times := by
    intro v hv
    rw [hcrit] at hv
    exact (by simpa using hv : False).elim


-- @@ L860-860 verbatim
end MorseAtlas


-- @@ L862-862 verbatim
end Submission
