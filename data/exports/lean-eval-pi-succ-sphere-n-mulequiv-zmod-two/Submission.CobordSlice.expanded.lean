import Mathlib
import Submission.LevelSet


-- @@ L4-40 verbatim
/-!
# Level-set cobordisms: slice theory (pointwise/local)

We study smooth maps `G : ℝ^{n+2} → ℝⁿ` thought of as level-set cobordisms:
the last coordinate of `ℝ^{n+2}` is the *time* coordinate (`tcoord`), and for each
time `t` the *slice map* `sliceMap G t : ℝ^{n+1} → ℝⁿ` is obtained by freezing the
time coordinate at `t`.

**Index conventions** (used throughout `CobordSlice` and `CobordFlow`):

* `E' := EuclideanSpace ℝ (Fin (n+2))` is space-time, `E₁ := EuclideanSpace ℝ (Fin (n+1))`
  is space, `F := EuclideanSpace ℝ (Fin n)` is the target.
* The time coordinate is the **last** coordinate: `tcoord v = v (Fin.last (n+1))`.
* Space is included via `Fin.snoc` / extracted via `Fin.init`:
  `spaceTime x t` has spatial part `x` and time `t`; `spacePart v = Fin.init v`;
  spatial index `i : Fin (n+1)` sits inside `Fin (n+2)` as `Fin.castSucc i`.

Main definitions and results:

* `Submission.kerProj G v` — the orthogonal projection of `E'` onto
  `ker (fderiv ℝ G v)`, via the explicit formula `I - D†(DD†)⁻¹D`
  (`D := fderiv ℝ G v`, inverses via `Ring.inverse`, junk values off the regular set);
  `fderiv_kerProj`, `kerProj_of_fderiv_eq_zero`, `kerProj_idem`, `inner_kerProj_left`
  (self-adjointness), `contDiffAt_kerProj` (smooth dependence on `v`).
* `Submission.timeField G v` — the unique vector in `ker (fderiv ℝ G v)` of unit time
  speed which is orthogonal to the slice direction: `fderiv_timeField`,
  `tcoord_timeField`, `isOpen_slabRegularSet`, `contDiffAt_timeField`.
* `Submission.kerProj_timeVec_eq_zero_iff` — **critical point characterization**:
  at a point with surjective full derivative, the kernel projection of the time
  direction vanishes iff the spatial derivative `spatialDeriv G v` is not surjective.
* `Submission.criticalTimes`, `Submission.sliceRegular`, `Submission.sliceFLS` —
  slices at regular times as framed level sets (`FramedLevelSet n`).
* `Submission.LevelCobordismData` — the minimal packaging of a level-set cobordism
  (smooth `G`, spatially bounded fiber, `0` regular on the fiber).  Only spatial
  boundedness is required because collar cobordisms are necessarily unbounded in
  the time direction; their intersection with every finite time slab is compact.
-/


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
namespace Submission


-- @@ L46-46 verbatim
open Set Function Metric Module Submodule

-- @@ L47-47 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L49-49 verbatim
variable {n : ℕ}


-- @@ L51-51 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L52-52 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L53-53 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L55-55 verbatim
/-! ## The time coordinate and the space/time splitting -/


-- @@ L57-58 verbatim
/-- The time coordinate: the last coordinate of `ℝ^{n+2}`. -/
def tcoord (v : E') : ℝ := v (Fin.last (n + 1))


-- @@ L60-61 verbatim
/-- The unit vector in the time direction. -/
def timeVec : E' := EuclideanSpace.single (Fin.last (n + 1)) 1


-- @@ L63-67 verbatim
/-- The point of space-time with spatial part `x` and time `t`.

The `cob` prefix keeps this slice-theory coordinate map disjoint from the
definition used by the forward PT bridge. -/
def cobSpaceTime (x : E₁) (t : ℝ) : E' := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)


-- @@ L69-69 verbatim
local notation "spaceTime" => cobSpaceTime


-- @@ L71-72 verbatim
/-- The spatial part of a space-time point. -/
def spacePart (v : E') : E₁ := WithLp.toLp 2 (Fin.init (WithLp.ofLp v))


-- @@ L74-75 verbatim
@[simp] lemma tcoord_spaceTime (x : E₁) (t : ℝ) : tcoord (spaceTime x t) = t := by
  simp [tcoord, cobSpaceTime, Fin.snoc_last]


-- @@ L77-79 verbatim
@[simp] lemma spaceTime_apply_castSucc (x : E₁) (t : ℝ) (i : Fin (n + 1)) :
    spaceTime x t (Fin.castSucc i) = x i := by
  simp [cobSpaceTime, Fin.snoc_castSucc]


-- @@ L81-83 verbatim
@[simp] lemma spaceTime_apply_last (x : E₁) (t : ℝ) :
    spaceTime x t (Fin.last (n + 1)) = t := by
  simp [cobSpaceTime, Fin.snoc_last]


-- @@ L85-86 verbatim
@[simp] lemma spacePart_apply (v : E') (i : Fin (n + 1)) :
    spacePart v i = v (Fin.castSucc i) := rfl


-- @@ L88-91 verbatim
@[simp] lemma spacePart_spaceTime (x : E₁) (t : ℝ) : spacePart (spaceTime x t) = x := by
  apply (WithLp.equiv 2 _).injective
  funext i
  simp [spacePart, cobSpaceTime, Fin.init_snoc]


-- @@ L93-101 verbatim
lemma spaceTime_spacePart (v : E') : spaceTime (spacePart v) (tcoord v) = v := by
  apply (WithLp.equiv 2 _).injective
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · show spaceTime (spacePart v) (tcoord v) (Fin.castSucc i) = v (Fin.castSucc i)
    rw [spaceTime_apply_castSucc, spacePart_apply]
  · show spaceTime (spacePart v) (tcoord v) (Fin.last (n + 1)) = v (Fin.last (n + 1))
    rw [spaceTime_apply_last]
    rfl


-- @@ L103-103 verbatim
@[simp] lemma tcoord_add (a b : E') : tcoord (a + b) = tcoord a + tcoord b := rfl


-- @@ L105-105 verbatim
@[simp] lemma tcoord_sub (a b : E') : tcoord (a - b) = tcoord a - tcoord b := rfl


-- @@ L107-107 verbatim
@[simp] lemma tcoord_smul (c : ℝ) (a : E') : tcoord (c • a) = c * tcoord a := rfl


-- @@ L109-110 verbatim
@[simp] lemma tcoord_timeVec : tcoord (timeVec (n := n)) = 1 := by
  simp [tcoord, timeVec]


-- @@ L112-113 verbatim
@[simp] lemma norm_timeVec : ‖timeVec (n := n)‖ = 1 := by
  simp [timeVec]


-- @@ L115-117 verbatim
lemma timeVec_apply (j : Fin (n + 2)) :
    timeVec (n := n) j = if j = Fin.last (n + 1) then 1 else 0 :=
  PiLp.single_apply 2 ℝ (Fin.last (n + 1)) (1 : ℝ) j


-- @@ L119-122 verbatim
/-- Pairing with the time vector computes the time coordinate. -/
lemma inner_timeVec (w : E') : ⟪timeVec, w⟫ = tcoord w := by
  rw [timeVec, EuclideanSpace.inner_single_left]
  simp [tcoord]


-- @@ L124-125 verbatim
lemma continuous_tcoord : Continuous (tcoord (n := n)) :=
  (EuclideanSpace.proj (Fin.last (n + 1)) (𝕜 := ℝ)).continuous


-- @@ L127-146 verbatim
/-- Space inclusion at time `0`, as a linear map. -/
def spaceInclLM : E₁ →ₗ[ℝ] E' where
  toFun x := spaceTime x 0
  map_add' x y := by
    apply (WithLp.equiv 2 _).injective
    funext j
    show spaceTime (x + y) 0 j = (spaceTime x 0 + spaceTime y 0) j
    rw [PiLp.add_apply]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [spaceTime_apply_castSucc, spaceTime_apply_castSucc, spaceTime_apply_castSucc,
        PiLp.add_apply]
    · rw [spaceTime_apply_last, spaceTime_apply_last, spaceTime_apply_last, add_zero]
  map_smul' c x := by
    apply (WithLp.equiv 2 _).injective
    funext j
    show spaceTime (c • x) 0 j = (c • spaceTime x 0) j
    rw [PiLp.smul_apply]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [spaceTime_apply_castSucc, spaceTime_apply_castSucc, PiLp.smul_apply]
    · rw [spaceTime_apply_last, spaceTime_apply_last, smul_zero]


-- @@ L148-149 verbatim
/-- Space inclusion at time `0`, as a continuous linear map. -/
def spaceInclL : E₁ →L[ℝ] E' := LinearMap.toContinuousLinearMap spaceInclLM


-- @@ L151-151 verbatim
@[simp] lemma spaceInclL_apply (x : E₁) : spaceInclL x = spaceTime x 0 := rfl


-- @@ L153-154 verbatim
@[simp] lemma tcoord_spaceInclL (x : E₁) : tcoord (spaceInclL x) = 0 := by
  rw [spaceInclL_apply, tcoord_spaceTime]


-- @@ L156-165 verbatim
/-- The affine decomposition of `spaceTime`. -/
lemma spaceTime_eq (x : E₁) (t : ℝ) : spaceTime x t = spaceInclL x + t • timeVec := by
  apply (WithLp.equiv 2 _).injective
  funext j
  show spaceTime x t j = ((spaceInclL x + t • timeVec : E')) j
  rw [PiLp.add_apply, PiLp.smul_apply, spaceInclL_apply, timeVec_apply, smul_eq_mul]
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [spaceTime_apply_castSucc, spaceTime_apply_castSucc,
      if_neg (Fin.castSucc_lt_last i).ne, mul_zero, add_zero]
  · rw [spaceTime_apply_last, spaceTime_apply_last, if_pos rfl, mul_one, zero_add]


-- @@ L167-169 verbatim
/-- A point with vanishing time coordinate is purely spatial. -/
lemma spaceInclL_spacePart {v : E'} (h : tcoord v = 0) : spaceInclL (spacePart v) = v := by
  rw [spaceInclL_apply, ← h, spaceTime_spacePart]


-- @@ L171-180 verbatim
lemma norm_spacePart_le (v : E') : ‖spacePart v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have h : ∑ j : Fin (n + 2), ‖v j‖ ^ 2
      = (∑ i : Fin (n + 1), ‖v (Fin.castSucc i)‖ ^ 2) + ‖v (Fin.last (n + 1))‖ ^ 2 :=
    Fin.sum_univ_castSucc (f := fun j => ‖v j‖ ^ 2)
  rw [h]
  have h2 : ∀ i : Fin (n + 1), ‖spacePart v i‖ ^ 2 = ‖v (Fin.castSucc i)‖ ^ 2 := fun i => rfl
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  exact le_add_of_nonneg_right (by positivity)


-- @@ L182-187 verbatim
/-- Inclusion of the spatial coordinates at time zero preserves the Euclidean norm. -/
lemma norm_spaceInclL (x : E₁) : ‖spaceInclL (n := n) x‖ = ‖x‖ := by
  rw [spaceInclL_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [spaceTime_apply_castSucc, spaceTime_apply_last]


-- @@ L189-194 verbatim
lemma hasFDerivAt_cobSpaceTime (t : ℝ) (x : E₁) :
    HasFDerivAt (fun y : E₁ => spaceTime y t) (spaceInclL (n := n)) x := by
  have heq : (fun y : E₁ => spaceTime y t) = fun y => spaceInclL y + t • timeVec :=
    funext fun y => spaceTime_eq y t
  rw [heq]
  exact (spaceInclL (n := n)).hasFDerivAt.add_const _


-- @@ L196-207 verbatim
/-- `spaceTime` is smooth jointly in `(t, x)`. -/
lemma contDiff_spaceTime_pair :
    ContDiff ℝ ∞ (fun p : ℝ × E₁ => spaceTime p.2 p.1) := by
  have heq : (fun p : ℝ × E₁ => spaceTime p.2 p.1)
      = fun p : ℝ × E₁ => spaceInclL p.2 + p.1 • timeVec :=
    funext fun p => spaceTime_eq p.2 p.1
  rw [heq]
  apply ContDiff.add
  · have h2 : ContDiff ℝ ∞ (Prod.snd : ℝ × E₁ → E₁) := contDiff_snd
    have h := (spaceInclL (n := n)).contDiff.comp h2
    exact h
  · exact contDiff_fst.smul contDiff_const


-- @@ L209-209 verbatim
/-! ## The Gram operator -/


-- @@ L211-214 verbatim
/-- The Gram operator `D D†` of the derivative `D := fderiv ℝ G v`. It is invertible
exactly when `D` is surjective. -/
def gramCLM (G : E' → F) (v : E') : F →L[ℝ] F :=
  (fderiv ℝ G v).comp (ContinuousLinearMap.adjoint (fderiv ℝ G v))


-- @@ L216-224 verbatim
lemma inner_gramCLM_self (G : E' → F) (v : E') (x : F) :
    ⟪x, gramCLM G v x⟫ = ‖ContinuousLinearMap.adjoint (fderiv ℝ G v) x‖ ^ 2 := by
  have h := ContinuousLinearMap.adjoint_inner_left (fderiv ℝ G v)
    (ContinuousLinearMap.adjoint (fderiv ℝ G v) x) x
  calc ⟪x, gramCLM G v x⟫
      = ⟪ContinuousLinearMap.adjoint (fderiv ℝ G v) x,
          ContinuousLinearMap.adjoint (fderiv ℝ G v) x⟫ := h.symm
    _ = ‖ContinuousLinearMap.adjoint (fderiv ℝ G v) x‖ ^ 2 :=
        real_inner_self_eq_norm_sq _


-- @@ L226-240 verbatim
/-- The Gram operator is symmetric. -/
lemma inner_gramCLM_left (G : E' → F) (v : E') (x y : F) :
    ⟪gramCLM G v x, y⟫ = ⟪x, gramCLM G v y⟫ := by
  have h1 := ContinuousLinearMap.adjoint_inner_left (fderiv ℝ G v)
    (ContinuousLinearMap.adjoint (fderiv ℝ G v) x) y
  have h2 := ContinuousLinearMap.adjoint_inner_left (fderiv ℝ G v)
    (ContinuousLinearMap.adjoint (fderiv ℝ G v) y) x
  calc ⟪gramCLM G v x, y⟫
      = ⟪y, fderiv ℝ G v (ContinuousLinearMap.adjoint (fderiv ℝ G v) x)⟫ :=
        real_inner_comm _ _
    _ = ⟪ContinuousLinearMap.adjoint (fderiv ℝ G v) y,
          ContinuousLinearMap.adjoint (fderiv ℝ G v) x⟫ := h1.symm
    _ = ⟪ContinuousLinearMap.adjoint (fderiv ℝ G v) x,
          ContinuousLinearMap.adjoint (fderiv ℝ G v) y⟫ := real_inner_comm _ _
    _ = ⟪x, gramCLM G v y⟫ := h2


-- @@ L242-253 verbatim
/-- The adjoint of a surjective map is injective. -/
lemma adjoint_fderiv_injective {G : E' → F} {v : E'}
    (hv : Surjective (fderiv ℝ G v)) :
    Injective (ContinuousLinearMap.adjoint (fderiv ℝ G v)) := by
  intro x y hxy
  have hz : ContinuousLinearMap.adjoint (fderiv ℝ G v) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨w, hw⟩ := hv (x - y)
  have h0 : ⟪x - y, x - y⟫ = 0 := by
    nth_rewrite 2 [← hw]
    rw [← ContinuousLinearMap.adjoint_inner_left, hz, inner_zero_left]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)


-- @@ L255-273 verbatim
/-- Surjectivity of the derivative makes the Gram operator invertible. -/
lemma isUnit_gramCLM {G : E' → F} {v : E'} (hv : Surjective (fderiv ℝ G v)) :
    IsUnit (gramCLM G v) := by
  have hinj : Injective (gramCLM G v) := by
    intro x y hxy
    have h0 : gramCLM G v (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : ⟪x - y, gramCLM G v (x - y)⟫ = 0 := by rw [h0, inner_zero_right]
    rw [inner_gramCLM_self] at h1
    have h2 : ContinuousLinearMap.adjoint (fderiv ℝ G v) (x - y) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
    have h3 : ContinuousLinearMap.adjoint (fderiv ℝ G v) (x - y)
        = ContinuousLinearMap.adjoint (fderiv ℝ G v) 0 := by rw [h2, map_zero]
    exact sub_eq_zero.mp (adjoint_fderiv_injective hv h3)
  have hsurj : Surjective (gramCLM G v) := by
    have h := LinearMap.injective_iff_surjective
      (f := ((gramCLM G v : F →L[ℝ] F) : F →ₗ[ℝ] F))
    exact h.mp hinj
  exact ⟨(LinearEquiv.ofBijective ((gramCLM G v : F →L[ℝ] F) : F →ₗ[ℝ] F)
    ⟨hinj, hsurj⟩).toContinuousLinearEquiv.toUnit, ContinuousLinearMap.ext fun x => rfl⟩


-- @@ L275-286 verbatim
/-- Conversely, invertibility of the Gram operator gives surjectivity. -/
lemma surjective_of_isUnit_gramCLM {G : E' → F} {v : E'}
    (hu : IsUnit (gramCLM G v)) : Surjective (fderiv ℝ G v) := by
  intro y
  refine ⟨ContinuousLinearMap.adjoint (fderiv ℝ G v)
    (Ring.inverse (gramCLM G v) y), ?_⟩
  have h := Ring.mul_inverse_cancel _ hu
  calc fderiv ℝ G v (ContinuousLinearMap.adjoint (fderiv ℝ G v)
        (Ring.inverse (gramCLM G v) y))
      = (gramCLM G v * Ring.inverse (gramCLM G v)) y := rfl
    _ = (1 : F →L[ℝ] F) y := by rw [h]
    _ = y := rfl


-- @@ L288-290 verbatim
lemma surjective_iff_isUnit_gramCLM (G : E' → F) (v : E') :
    Surjective (fderiv ℝ G v) ↔ IsUnit (gramCLM G v) :=
  ⟨isUnit_gramCLM, surjective_of_isUnit_gramCLM⟩


-- @@ L292-300 verbatim
/-- The Gram operator inverts on the nose (`Ring.inverse` version, left form). -/
lemma gramCLM_ringInverse_apply {G : E' → F} {v : E'}
    (hu : IsUnit (gramCLM G v)) (y : F) :
    gramCLM G v (Ring.inverse (gramCLM G v) y) = y := by
  have h := Ring.mul_inverse_cancel _ hu
  calc gramCLM G v (Ring.inverse (gramCLM G v) y)
      = (gramCLM G v * Ring.inverse (gramCLM G v)) y := rfl
    _ = (1 : F →L[ℝ] F) y := by rw [h]
    _ = y := rfl


-- @@ L302-310 verbatim
/-- The inverse Gram operator is symmetric. -/
lemma inner_ringInverse_gramCLM {G : E' → F} {v : E'}
    (hu : IsUnit (gramCLM G v)) (x y : F) :
    ⟪Ring.inverse (gramCLM G v) x, y⟫ = ⟪x, Ring.inverse (gramCLM G v) y⟫ := by
  have h1 : ⟪Ring.inverse (gramCLM G v) x, gramCLM G v (Ring.inverse (gramCLM G v) y)⟫
      = ⟪gramCLM G v (Ring.inverse (gramCLM G v) x), Ring.inverse (gramCLM G v) y⟫ :=
    (inner_gramCLM_left G v _ _).symm
  rw [gramCLM_ringInverse_apply hu x, gramCLM_ringInverse_apply hu y] at h1
  exact h1


-- @@ L312-312 verbatim
/-! ## The kernel projection -/


-- @@ L314-319 verbatim
/-- Orthogonal projection onto `ker (fderiv ℝ G v)`, by the explicit formula
`I - D† (D D†)⁻¹ D`. Off the regular set it takes junk values. -/
def kerProj (G : E' → F) (v : E') : E' →L[ℝ] E' :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 2))) -
    (ContinuousLinearMap.adjoint (fderiv ℝ G v)).comp
      ((Ring.inverse (gramCLM G v)).comp (fderiv ℝ G v))


-- @@ L321-323 verbatim
lemma kerProj_apply (G : E' → F) (v w : E') :
    kerProj G v w = w - ContinuousLinearMap.adjoint (fderiv ℝ G v)
      (Ring.inverse (gramCLM G v) (fderiv ℝ G v w)) := rfl


-- @@ L325-333 verbatim
/-- The projection lands in the kernel of the derivative. -/
lemma fderiv_kerProj {G : E' → F} {v : E'} (hv : Surjective (fderiv ℝ G v)) (w : E') :
    fderiv ℝ G v (kerProj G v w) = 0 := by
  have hu := isUnit_gramCLM hv
  rw [kerProj_apply, map_sub]
  have hg : fderiv ℝ G v (ContinuousLinearMap.adjoint (fderiv ℝ G v)
      (Ring.inverse (gramCLM G v) (fderiv ℝ G v w)))
      = gramCLM G v (Ring.inverse (gramCLM G v) (fderiv ℝ G v w)) := rfl
  rw [hg, gramCLM_ringInverse_apply hu, sub_self]


-- @@ L335-338 verbatim
/-- Kernel vectors are fixed by the projection (no regularity needed). -/
lemma kerProj_of_fderiv_eq_zero {G : E' → F} {v w : E'}
    (hw : fderiv ℝ G v w = 0) : kerProj G v w = w := by
  rw [kerProj_apply, hw, map_zero, map_zero, sub_zero]


-- @@ L340-342 verbatim
lemma kerProj_idem {G : E' → F} {v : E'} (hv : Surjective (fderiv ℝ G v)) (w : E') :
    kerProj G v (kerProj G v w) = kerProj G v w :=
  kerProj_of_fderiv_eq_zero (fderiv_kerProj hv w)


-- @@ L344-351 verbatim
/-- The kernel projection is self-adjoint. -/
lemma inner_kerProj_left {G : E' → F} {v : E'} (hv : Surjective (fderiv ℝ G v))
    (u w : E') : ⟪kerProj G v u, w⟫ = ⟪u, kerProj G v w⟫ := by
  have hu := isUnit_gramCLM hv
  rw [kerProj_apply, kerProj_apply, inner_sub_left, inner_sub_right]
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left, inner_ringInverse_gramCLM hu,
    ContinuousLinearMap.adjoint_inner_right]


-- @@ L353-358 verbatim
/-- The characterizing identity `⟪e_t, P e_t⟫ = ‖P e_t‖²`. -/
lemma inner_timeVec_kerProj_timeVec {G : E' → F} {v : E'}
    (hv : Surjective (fderiv ℝ G v)) :
    ⟪timeVec, kerProj G v timeVec⟫ = ‖kerProj G v timeVec‖ ^ 2 := by
  conv_lhs => rw [← kerProj_idem hv (timeVec (n := n)), ← inner_kerProj_left hv]
  exact real_inner_self_eq_norm_sq _


-- @@ L360-367 verbatim
/-- Membership in the kernel is equivalent to being fixed by `kerProj`. -/
lemma kerProj_eq_self_iff {G : E' → F} {v : E'} (hv : Surjective (fderiv ℝ G v))
    (w : E') : kerProj G v w = w ↔ fderiv ℝ G v w = 0 := by
  constructor
  · intro h
    have := fderiv_kerProj hv w
    rwa [h] at this
  · exact kerProj_of_fderiv_eq_zero


-- @@ L369-369 verbatim
/-! ## Smooth dependence on the base point -/


-- @@ L371-379 verbatim
/-- Taking adjoints of operators `E' →L F`, as a continuous linear map (finite
dimensions; over `ℝ` the adjoint is genuinely linear). -/
def adjointCLM : (EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 2))) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
      map_smul' := fun c A => by
        rw [RingHom.id_apply, map_smulₛₗ, starRingEnd_apply, star_trivial] }


-- @@ L381-382 verbatim
@[simp] lemma adjointCLM_apply (A : E' →L[ℝ] F) :
    adjointCLM A = ContinuousLinearMap.adjoint A := rfl


-- @@ L384-386 verbatim
lemma contDiff_fderivCLM {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fderiv ℝ G) :=
  hG.fderiv_right (by simp)


-- @@ L388-391 verbatim
lemma contDiff_adjointFderiv {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun w => ContinuousLinearMap.adjoint (fderiv ℝ G w)) := by
  have h := (adjointCLM (n := n)).contDiff.comp (contDiff_fderivCLM hG)
  exact h


-- @@ L393-396 verbatim
lemma contDiff_gramCLM {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (gramCLM G) := by
  have h := ContDiff.clm_comp (contDiff_fderivCLM hG) (contDiff_adjointFderiv hG)
  exact h


-- @@ L398-414 verbatim
/-- The kernel projection depends smoothly on the base point, near any regular
point. -/
lemma contDiffAt_kerProj {G : E' → F} {v : E'} (hG : ContDiff ℝ ∞ G)
    (hv : Surjective (fderiv ℝ G v)) : ContDiffAt ℝ ∞ (kerProj G) v := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ G) v := (contDiff_fderivCLM hG).contDiffAt
  have hAdj : ContDiffAt ℝ ∞ (fun w => ContinuousLinearMap.adjoint (fderiv ℝ G w)) v :=
    (contDiff_adjointFderiv hG).contDiffAt
  have hginv : ContDiffAt ℝ ∞ (fun w => Ring.inverse (gramCLM G w)) v := by
    have hu := isUnit_gramCLM hv
    have h1 : ContDiffAt ℝ ∞ (Ring.inverse (M₀ := F →L[ℝ] F)) (gramCLM G v) := by
      have := contDiffAt_ringInverse ℝ (n := (∞ : WithTop ℕ∞)) hu.unit
      rwa [hu.unit_spec] at this
    exact h1.comp v (contDiff_gramCLM hG).contDiffAt
  have h := ContDiffAt.sub
    (contDiffAt_const (c := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 2)))))
    (hAdj.clm_comp (hginv.clm_comp hD))
  exact h


-- @@ L416-419 verbatim
lemma contDiffAt_kerProj_timeVec {G : E' → F} {v : E'} (hG : ContDiff ℝ ∞ G)
    (hv : Surjective (fderiv ℝ G v)) :
    ContDiffAt ℝ ∞ (fun w => kerProj G w timeVec) v :=
  (contDiffAt_kerProj hG hv).clm_apply contDiffAt_const


-- @@ L421-421 verbatim
/-! ## The time-flow field -/


-- @@ L423-426 verbatim
/-- The time-flow field: the kernel projection of the time direction, normalized to
unit time speed. Junk values where the normalization fails. -/
def timeField (G : E' → F) (v : E') : E' :=
  (⟪timeVec, kerProj G v timeVec⟫)⁻¹ • kerProj G v timeVec


-- @@ L428-431 verbatim
/-- The set on which the time-flow field is defined: the derivative is surjective and
the time direction is not orthogonal to the kernel. -/
def slabRegularSet (G : E' → F) : Set E' :=
  {v | Surjective (fderiv ℝ G v) ∧ kerProj G v timeVec ≠ 0}


-- @@ L433-434 verbatim
lemma slabRegularSet_subset_regular (G : E' → F) :
    slabRegularSet G ⊆ {v | Surjective (fderiv ℝ G v)} := fun _ hv => hv.1


-- @@ L436-441 verbatim
/-- On the slab-regular set, the normalizing inner product is positive. -/
lemma inner_timeVec_kerProj_pos {G : E' → F} {v : E'} (hv : v ∈ slabRegularSet G) :
    0 < ⟪timeVec, kerProj G v timeVec⟫ := by
  rw [inner_timeVec_kerProj_timeVec hv.1]
  have h : 0 < ‖kerProj G v timeVec‖ := norm_pos_iff.mpr hv.2
  positivity


-- @@ L443-446 verbatim
/-- The time field lies in the kernel of the derivative. -/
lemma fderiv_timeField {G : E' → F} {v : E'} (hv : Surjective (fderiv ℝ G v)) :
    fderiv ℝ G v (timeField G v) = 0 := by
  rw [timeField, map_smul, fderiv_kerProj hv, smul_zero]


-- @@ L448-452 verbatim
/-- Unit time speed: the time component of the time field is `1`. -/
lemma inner_timeVec_timeField {G : E' → F} {v : E'} (hv : v ∈ slabRegularSet G) :
    ⟪timeVec, timeField G v⟫ = 1 := by
  rw [timeField, real_inner_smul_right]
  exact inv_mul_cancel₀ (ne_of_gt (inner_timeVec_kerProj_pos hv))


-- @@ L454-457 verbatim
lemma tcoord_timeField {G : E' → F} {v : E'} (hv : v ∈ slabRegularSet G) :
    tcoord (timeField G v) = 1 := by
  rw [← inner_timeVec]
  exact inner_timeVec_timeField hv


-- @@ L459-475 verbatim
/-- The slab-regular set is open. -/
lemma isOpen_slabRegularSet {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    IsOpen (slabRegularSet G) := by
  rw [isOpen_iff_mem_nhds]
  rintro v ⟨hsurj, hne⟩
  have h1 : {w : E' | IsUnit (gramCLM G w)} ∈ 𝓝 v := by
    have hopen : IsOpen {w : E' | IsUnit (gramCLM G w)} :=
      Units.isOpen.preimage (contDiff_gramCLM hG).continuous
    exact hopen.mem_nhds (isUnit_gramCLM hsurj)
  have h2 : {w : E' | kerProj G w timeVec ≠ 0} ∈ 𝓝 v := by
    have hc : ContinuousAt (fun w => kerProj G w timeVec) v :=
      (contDiffAt_kerProj_timeVec hG hsurj).continuousAt
    have hmem : ({0}ᶜ : Set E') ∈ 𝓝 (kerProj G v timeVec) :=
      isOpen_compl_singleton.mem_nhds hne
    exact hc.preimage_mem_nhds hmem
  filter_upwards [h1, h2] with w hw1 hw2
  exact ⟨surjective_of_isUnit_gramCLM hw1, hw2⟩


-- @@ L477-486 verbatim
/-- The time field is smooth at slab-regular points. -/
lemma contDiffAt_timeField {G : E' → F} {v : E'} (hG : ContDiff ℝ ∞ G)
    (hv : v ∈ slabRegularSet G) : ContDiffAt ℝ ∞ (timeField G) v := by
  have hP : ContDiffAt ℝ ∞ (fun w => kerProj G w timeVec) v :=
    contDiffAt_kerProj_timeVec hG hv.1
  have hinner : ContDiffAt ℝ ∞ (fun w => ⟪(timeVec : E'), kerProj G w timeVec⟫) v :=
    ContDiffAt.inner ℝ contDiffAt_const hP
  have hval : ⟪(timeVec : E'), kerProj G v timeVec⟫ ≠ 0 :=
    ne_of_gt (inner_timeVec_kerProj_pos hv)
  exact (hinner.inv hval).smul hP


-- @@ L488-488 verbatim
/-! ## The critical point characterization -/


-- @@ L490-493 verbatim
/-- The spatial derivative: the restriction of the full derivative to the spatial
hyperplane. -/
def spatialDeriv (G : E' → F) (v : E') : E₁ →L[ℝ] F :=
  (fderiv ℝ G v).comp spaceInclL


-- @@ L495-496 verbatim
lemma spatialDeriv_apply (G : E' → F) (v : E') (x : E₁) :
    spatialDeriv G v x = fderiv ℝ G v (spaceInclL x) := rfl


-- @@ L498-540 verbatim
/-- **Critical point characterization.** At a point with surjective full derivative,
the kernel projection of the time direction vanishes iff the spatial derivative is
not surjective (i.e. the point is a critical point of time restricted to the fiber). -/
theorem kerProj_timeVec_eq_zero_iff {G : E' → F} {v : E'}
    (hv : Surjective (fderiv ℝ G v)) :
    kerProj G v timeVec = 0 ↔ ¬ Surjective (spatialDeriv G v) := by
  constructor
  · -- if the projection vanishes, a spatial preimage of `D e_t` would give a kernel
    -- vector with unit time coordinate, contradicting `e_t ⊥ ker D`.
    intro h0 hs
    obtain ⟨x, hx⟩ := hs (fderiv ℝ G v timeVec)
    set u : E' := timeVec - spaceInclL x with hu
    have hDu : fderiv ℝ G v u = 0 := by
      rw [hu, map_sub, ← spatialDeriv_apply, hx, sub_self]
    have hPu : kerProj G v u = u := kerProj_of_fderiv_eq_zero hDu
    have htu : ⟪timeVec, u⟫ = 1 := by
      rw [inner_timeVec, hu, tcoord_sub, tcoord_timeVec, tcoord_spaceInclL, sub_zero]
    have hcontra : (1 : ℝ) = 0 := by
      calc (1 : ℝ) = ⟪timeVec, u⟫ := htu.symm
        _ = ⟪timeVec, kerProj G v u⟫ := by rw [hPu]
        _ = ⟪kerProj G v timeVec, u⟫ := (inner_kerProj_left hv _ _).symm
        _ = 0 := by rw [h0, inner_zero_left]
    norm_num at hcontra
  · -- contrapositive: a nonzero projection is a kernel vector with nonzero time
    -- coordinate, which corrects arbitrary preimages into spatial ones.
    intro hns
    by_contra hne
    apply hns
    intro y
    obtain ⟨w, hw⟩ := hv y
    set u : E' := kerProj G v timeVec with hudef
    have hDu : fderiv ℝ G v u = 0 := fderiv_kerProj hv timeVec
    have htu : tcoord u ≠ 0 := by
      rw [← inner_timeVec, hudef, inner_timeVec_kerProj_timeVec hv]
      have h : 0 < ‖kerProj G v timeVec‖ := norm_pos_iff.mpr hne
      positivity
    set w' : E' := w - (tcoord w / tcoord u) • u with hw'def
    have hDw' : fderiv ℝ G v w' = y := by
      rw [hw'def, map_sub, map_smul, hDu, smul_zero, sub_zero, hw]
    have htw' : tcoord w' = 0 := by
      rw [hw'def, tcoord_sub, tcoord_smul, div_mul_cancel₀ _ htu, sub_self]
    refine ⟨spacePart w', ?_⟩
    rw [spatialDeriv_apply, spaceInclL_spacePart htw', hDw']


-- @@ L542-549 verbatim
/-- Bridge into the slab-regular set: a fiber-regular point over a regular slice time
is slab-regular. -/
lemma mem_slabRegularSet_of_spatial_surjective {G : E' → F} {v : E'}
    (hv : Surjective (fderiv ℝ G v)) (hs : Surjective (spatialDeriv G v)) :
    v ∈ slabRegularSet G := by
  refine ⟨hv, ?_⟩
  intro h0
  exact (kerProj_timeVec_eq_zero_iff hv).mp h0 hs


-- @@ L551-551 verbatim
/-! ## Critical times, regular slices -/


-- @@ L553-555 verbatim
/-- Fiber points that are critical for the time function on the fiber. -/
def timeCritical (G : E' → F) : Set E' :=
  {v | G v = 0 ∧ ¬ Surjective (spatialDeriv G v)}


-- @@ L557-558 verbatim
/-- The set of critical times: images of critical fiber points. -/
def criticalTimes (G : E' → F) : Set ℝ := tcoord '' timeCritical G


-- @@ L560-563 verbatim
/-- `t` is a regular slice time if every fiber point at time `t` has surjective
spatial derivative. -/
def sliceRegular (G : E' → F) (t : ℝ) : Prop :=
  ∀ v : E', G v = 0 → tcoord v = t → Surjective (spatialDeriv G v)


-- @@ L565-572 verbatim
lemma sliceRegular_iff_notMem_criticalTimes (G : E' → F) (t : ℝ) :
    sliceRegular G t ↔ t ∉ criticalTimes G := by
  constructor
  · rintro h ⟨v, ⟨hf, hns⟩, rfl⟩
    exact hns (h v hf rfl)
  · intro h v hf ht
    by_contra hns
    exact h ⟨v, ⟨hf, hns⟩, ht⟩


-- @@ L574-576 verbatim
/-- `[a, b]` is a regular slab if it contains no critical time. -/
def regularSlab (G : E' → F) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, t ∉ criticalTimes G


-- @@ L578-580 verbatim
lemma regularSlab.sliceRegular {G : E' → F} {a b : ℝ} (h : regularSlab G a b)
    {t : ℝ} (ht : t ∈ Icc a b) : sliceRegular G t :=
  (sliceRegular_iff_notMem_criticalTimes G t).mpr (h t ht)


-- @@ L582-582 verbatim
/-! ## Slices as framed level sets -/


-- @@ L584-585 verbatim
/-- The slice map at time `t`. -/
def sliceMap (G : E' → F) (t : ℝ) : E₁ → F := fun x => G (spaceTime x t)


-- @@ L587-596 verbatim
lemma contDiff_sliceMap {G : E' → F} (hG : ContDiff ℝ ∞ G) (t : ℝ) :
    ContDiff ℝ ∞ (sliceMap G t) := by
  have h1 : ContDiff ℝ ∞ (fun x : E₁ => spaceTime x t) := by
    have heq : (fun x : E₁ => spaceTime x t) = fun x => spaceInclL x + t • timeVec :=
      funext fun x => spaceTime_eq x t
    rw [heq]
    apply ContDiff.add
    · exact (spaceInclL (n := n)).contDiff
    · exact contDiff_const
  exact hG.comp h1


-- @@ L598-608 verbatim
/-- The derivative of a slice map is the spatial derivative at the corresponding
space-time point. -/
lemma fderiv_sliceMap {G : E' → F} (hG : ContDiff ℝ ∞ G) (t : ℝ) (x : E₁) :
    fderiv ℝ (sliceMap G t) x = spatialDeriv G (spaceTime x t) := by
  have hf : DifferentiableAt ℝ (fun y : E₁ => spaceTime y t) x :=
    (hasFDerivAt_cobSpaceTime t x).differentiableAt
  have hg : DifferentiableAt ℝ G (spaceTime x t) :=
    (hG.differentiable (by simp)).differentiableAt
  have h := fderiv_comp x hg hf
  rw [(hasFDerivAt_cobSpaceTime t x).fderiv] at h
  exact h


-- @@ L610-618 verbatim
/-- A spatial bound on the cobordism fiber bounds every time slice. -/
lemma isBounded_sliceFiber {G : E' → F}
    (hb : ∃ R, ∀ v, G v = 0 → ‖spacePart v‖ ≤ R) (t : ℝ) :
    Bornology.IsBounded {x : E₁ | sliceMap G t x = 0} := by
  obtain ⟨C, hC⟩ := hb
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, fun x hx => ?_⟩
  have hmem : spaceTime x t ∈ {v | G v = 0} := hx
  simpa using hC (spaceTime x t) hmem


-- @@ L620-630 verbatim
/-- The slice at a regular time, as a framed level set. -/
def sliceFLS (G : E' → F) (hG : ContDiff ℝ ∞ G)
    (hb : ∃ R, ∀ v, G v = 0 → ‖spacePart v‖ ≤ R)
    (t : ℝ) (ht : sliceRegular G t) :
    FramedLevelSet n where
  g := sliceMap G t
  smooth := contDiff_sliceMap hG t
  fiber_bounded := isBounded_sliceFiber hb t
  regular := fun x hx => by
    rw [fderiv_sliceMap hG]
    exact ht (spaceTime x t) hx (tcoord_spaceTime x t)


-- @@ L632-635 verbatim
@[simp] lemma sliceFLS_g (G : E' → F) (hG : ContDiff ℝ ∞ G)
    (hb : ∃ R, ∀ v, G v = 0 → ‖spacePart v‖ ≤ R)
    (t : ℝ) (ht : sliceRegular G t) :
    (sliceFLS G hG hb t ht).g = sliceMap G t := rfl


-- @@ L637-641 verbatim
lemma mem_sliceFLS_fiber {G : E' → F} {hG : ContDiff ℝ ∞ G}
    {hb : ∃ R, ∀ v, G v = 0 → ‖spacePart v‖ ≤ R}
    {t : ℝ} {ht : sliceRegular G t}
    (x : E₁) : x ∈ (sliceFLS G hG hb t ht).fiber ↔ G (spaceTime x t) = 0 :=
  Iff.rfl


-- @@ L643-643 verbatim
/-! ## Joint smoothness of the slice data -/


-- @@ L645-669 verbatim
/-- The slice gradients depend smoothly on the pair (time, space point). -/
lemma contDiff_sliceGrad {G : E' → F} (hG : ContDiff ℝ ∞ G) (i : Fin n) :
    ContDiff ℝ ∞ (fun p : ℝ × E₁ => gradVec (sliceMap G p.1) i p.2) := by
  have heq : (fun p : ℝ × E₁ => gradVec (sliceMap G p.1) i p.2)
      = fun p : ℝ × E₁ => (InnerProductSpace.toDual ℝ
          (EuclideanSpace ℝ (Fin (n + 1)))).symm
          ((EuclideanSpace.proj i).comp (spatialDeriv G (spaceTime p.2 p.1))) := by
    funext p
    rw [gradVec, fderiv_sliceMap hG]
  rw [heq]
  apply (InnerProductSpace.toDual ℝ
    (EuclideanSpace ℝ (Fin (n + 1)))).symm.contDiff.comp
  have hst : ContDiff ℝ ∞ (fun p : ℝ × E₁ => fderiv ℝ G (spaceTime p.2 p.1)) := by
    have h := (contDiff_fderivCLM hG).comp contDiff_spaceTime_pair
    exact h
  have hsd : ContDiff ℝ ∞ (fun p : ℝ × E₁ => spatialDeriv G (spaceTime p.2 p.1)) := by
    have h := hst.clm_comp (contDiff_const (c := spaceInclL (n := n)))
    exact h
  have h2 : (fun p : ℝ × E₁ =>
      (EuclideanSpace.proj i (𝕜 := ℝ)).comp (spatialDeriv G (spaceTime p.2 p.1)))
      = fun p : ℝ × E₁ => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (n + 1)))
          (EuclideanSpace ℝ (Fin n)) ℝ (EuclideanSpace.proj i))
          (spatialDeriv G (spaceTime p.2 p.1)) := rfl
  rw [h2]
  exact (ContinuousLinearMap.contDiff _).comp hsd


-- @@ L671-674 verbatim
/-- The unnormalized slice kernel field depends smoothly on (time, space point). -/
lemma contDiff_sliceKerCross {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun p : ℝ × E₁ => kerCross (sliceMap G p.1) p.2) :=
  contDiff_crossVec_comp fun i => contDiff_sliceGrad hG i


-- @@ L676-688 verbatim
/-- The slice unit kernel field is continuous in (time, space point) at regular
pairs. -/
lemma continuousAt_sliceTau {G : E' → F} (hG : ContDiff ℝ ∞ G) {p : ℝ × E₁}
    (hp : p.2 ∈ regularSet (sliceMap G p.1)) :
    ContinuousAt (fun q : ℝ × E₁ => tauField (sliceMap G q.1) q.2) p := by
  have hne : kerCross (sliceMap G p.1) p.2 ≠ 0 :=
    (kerCross_ne_zero_iff _ _).mpr hp
  have hker : ContinuousAt (fun q : ℝ × E₁ => kerCross (sliceMap G q.1) q.2) p :=
    (contDiff_sliceKerCross hG).continuous.continuousAt
  have hnorm : ContinuousAt
      (fun q : ℝ × E₁ => ‖kerCross (sliceMap G q.1) q.2‖⁻¹) p :=
    (hker.norm).inv₀ (norm_ne_zero_iff.mpr hne)
  exact hnorm.smul hker


-- @@ L690-690 verbatim
/-! ## Packaging -/


-- @@ L692-704 verbatim
/-- A level-set cobordism presentation: a smooth map `G : ℝ^{n+2} → ℝⁿ` whose zero
fiber is bounded in the spatial directions, with `0` a regular value.  The weaker
spatial condition is deliberate: time collars make the full zero fiber unbounded,
whereas every finite time slab remains compact. -/
structure LevelCobordismData (n : ℕ) where
  /-- The defining map. -/
  G : EuclideanSpace ℝ (Fin (n + 2)) → EuclideanSpace ℝ (Fin n)
  /-- Smoothness. -/
  smooth : ContDiff ℝ ∞ G
  /-- The spatial parts of points in the zero fiber have a uniform norm bound. -/
  spatial_bounded : ∃ R, ∀ v, G v = 0 → ‖spacePart v‖ ≤ R
  /-- `0` is a regular value. -/
  regular : ∀ v, G v = 0 → Function.Surjective (fderiv ℝ G v)


-- @@ L706-706 verbatim
namespace LevelCobordismData


-- @@ L708-708 verbatim
variable (C : LevelCobordismData n)


-- @@ L710-711 verbatim
/-- The zero fiber of the presentation. -/
def fiber : Set (EuclideanSpace ℝ (Fin (n + 2))) := {v | C.G v = 0}


-- @@ L713-714 verbatim
lemma isClosed_fiber : IsClosed C.fiber :=
  isClosed_singleton.preimage C.smooth.continuous


-- @@ L716-720 verbatim
/-- Fiber points over regular slice times are slab-regular. -/
lemma mem_slabRegularSet {v : EuclideanSpace ℝ (Fin (n + 2))}
    (hv : v ∈ C.fiber) (ht : sliceRegular C.G (tcoord v)) :
    v ∈ slabRegularSet C.G :=
  mem_slabRegularSet_of_spatial_surjective (C.regular v hv) (ht v hv rfl)


-- @@ L722-722 verbatim
end LevelCobordismData


-- @@ L724-724 verbatim
end Submission
