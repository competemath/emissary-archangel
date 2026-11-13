import Mathlib
import Submission.FramedMorseDefiniteFrameClass
import Submission.StandardBirthFrameClass


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Function Matrix InnerProductSpace Filter

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace unitInterval Topology ContDiff


-- @@ L10-10 verbatim
namespace Submission


-- @@ L12-12 verbatim
set_option maxHeartbeats 800000


-- @@ L14-20 verbatim
@[simp] theorem matrixRows_rowsMatrix_eq {m : ℕ}
    (v : Fin m → EuclideanSpace ℝ (Fin m)) :
    matrixRows (rowsMatrix v) = v := by
  funext i
  apply WithLp.ofLp_injective
  funext j
  rfl


-- @@ L22-22 verbatim
/-! ## Straight positive-matrix homotopies -/


-- @@ L24-28 verbatim
/-- Pointwise convex interpolation between two square matrices. -/
def matrixSegment {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) (s : I) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 - (s : ℝ)) • A + (s : ℝ) • B


-- @@ L30-33 verbatim
@[simp] theorem matrixSegment_zero {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    matrixSegment A B 0 = A := by
  simp [matrixSegment]


-- @@ L35-38 verbatim
@[simp] theorem matrixSegment_one {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    matrixSegment A B 1 = B := by
  simp [matrixSegment]


-- @@ L40-50 verbatim
/-- The straight segment between two continuous matrix families. -/
def matrixSegmentHomotopy
    {P : Type*} [TopologicalSpace P] {m : ℕ}
    (A B : C(P, Matrix (Fin m) (Fin m) ℝ)) :
    ContinuousMap.Homotopy A B where
  toFun q := matrixSegment (A q.2) (B q.2) q.1
  continuous_toFun := by
    unfold matrixSegment
    fun_prop
  map_zero_left p := by simp
  map_one_left p := by simp


-- @@ L52-58 verbatim
theorem matrixSegmentHomotopy_closed
    {m : ℕ} (A B : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hA : A 0 = A 1) (hB : B 0 = B 1) (s : I) :
    matrixSegmentHomotopy A B (s, 0) =
      matrixSegmentHomotopy A B (s, 1) := by
  change matrixSegment (A 0) (B 0) s = matrixSegment (A 1) (B 1) s
  rw [hA, hB]


-- @@ L60-74 verbatim
/-- Positivity of determinant is uniformly stable over a compact parameter
set for a jointly continuous matrix family. -/
theorem eventually_uniform_det_pos
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {m : ℕ} {K : Set X} (hK : IsCompact K)
    (A : P → X → Matrix (Fin m) (Fin m) ℝ)
    (hA : Continuous fun q : P × X => A q.1 q.2)
    {p₀ : P} (hpos : ∀ x ∈ K, 0 < (A p₀ x).det) :
    ∀ᶠ p in nhds p₀, ∀ x ∈ K, 0 < (A p x).det := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hdet : Continuous fun q : P × X => (A q.1 q.2).det := by
    fun_prop
  exact hdet.continuousAt
    ((isOpen_lt continuous_const continuous_id).mem_nhds (hpos x hx))


-- @@ L76-82 verbatim
/-- Restrict a jointly continuous radius/loop family to one radius. -/
def matrixFamilyRadiusSlice {m : ℕ}
    (A : C(ℝ × I, Matrix (Fin m) (Fin m) ℝ)) (r : ℝ) :
    C(I, Matrix (Fin m) (Fin m) ℝ) where
  toFun u := A (r, u)
  continuous_toFun := A.continuous.comp
    (continuous_const.prodMk continuous_id)


-- @@ L84-112 verbatim
/-- If a jointly continuous radial frame family extends at radius zero to a
positive loop, then every straight segment back to that limiting loop has
positive determinant for all sufficiently small radii. -/
theorem eventually_matrixSegment_det_pos_of_zero_eq
    {m : ℕ}
    (A : C(ℝ × I, Matrix (Fin m) (Fin m) ℝ))
    (S : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hzero : ∀ u, A (0, u) = S u)
    (hSpos : ∀ u, 0 < (S u).det) :
    ∀ᶠ r in nhds (0 : ℝ), ∀ q : I × I,
      0 < (matrixSegment (A (r, q.2)) (S q.2) q.1).det := by
  let L : ℝ → I × I → Matrix (Fin m) (Fin m) ℝ :=
    fun r q => matrixSegment (A (r, q.2)) (S q.2) q.1
  have hL : Continuous fun z : ℝ × (I × I) => L z.1 z.2 := by
    dsimp only [L]
    unfold matrixSegment
    fun_prop
  have hpos : ∀ q ∈ (Set.univ : Set (I × I)),
      0 < (L 0 q).det := by
    intro q _
    dsimp only [L]
    rw [hzero q.2]
    have heq : matrixSegment (S q.2) (S q.2) q.1 = S q.2 := by
      unfold matrixSegment
      module
    rw [heq]
    exact hSpos q.2
  simpa only [Set.mem_univ, forall_const] using
    (eventually_uniform_det_pos isCompact_univ L hL hpos)


-- @@ L114-136 verbatim
/-- Quantitative-radius form of the preceding eventual statement. -/
theorem exists_pos_radius_matrixSegment_det_pos_of_zero_eq
    {m : ℕ}
    (A : C(ℝ × I, Matrix (Fin m) (Fin m) ℝ))
    (S : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hzero : ∀ u, A (0, u) = S u)
    (hSpos : ∀ u, 0 < (S u).det)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ r, 0 < r ∧ r < rho ∧ ∀ q : I × I,
      0 < (matrixSegment (A (r, q.2)) (S q.2) q.1).det := by
  have hevent := eventually_matrixSegment_det_pos_of_zero_eq
    A S hzero hSpos
  obtain ⟨eps, heps, heps_sub⟩ := Metric.mem_nhds_iff.mp hevent
  let r := min (rho / 2) (eps / 2)
  have hr : 0 < r := lt_min (half_pos hrho) (half_pos heps)
  have hrrho : r < rho :=
    (min_le_left (rho / 2) (eps / 2)).trans_lt (half_lt_self hrho)
  have hreps : r < eps :=
    (min_le_right (rho / 2) (eps / 2)).trans_lt (half_lt_self heps)
  refine ⟨r, hr, hrrho, ?_⟩
  apply heps_sub
  simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr]
    using hreps


-- @@ L138-138 verbatim
/-! ## Raw matrices underlying canonical regular-zero frames -/


-- @@ L140-140 verbatim
section RawFrame


-- @@ L142-142 verbatim
variable {n : ℕ}


-- @@ L144-144 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L145-145 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L146-146 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L148-154 verbatim
/-- The unnormalized slice-frame matrix before Gram--Schmidt. -/
def regularZeroRawFrameMatrix
    {P : Type*} [TopologicalSpace P]
    (G : E' → F) (z : C(P, E')) (q : P) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  rowsMatrix (SlabTamedField.sliceFrameAt G
    (tcoord (z q)) (spacePart (z q)))


-- @@ L156-186 verbatim
theorem continuous_regularZeroRawFrameMatrix
    {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) :
    Continuous (regularZeroRawFrameMatrix G z) := by
  let τ : P → ℝ := fun q => tcoord (z q)
  let x : P → E₁ := fun q => spacePart (z q)
  let A : P → Fin (n + 1) → E₁ := fun q =>
    SlabTamedField.sliceFrameAt G (τ q) (x q)
  have hτ : Continuous τ := continuous_tcoord.comp z.continuous
  have hx : Continuous x := continuous_spacePart.comp z.continuous
  have hA : ∀ i, Continuous fun q => A q i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · change Continuous fun q => tauField (sliceMap G (τ q)) (x q)
      rw [continuous_iff_continuousAt]
      intro q
      have hxreg : x q ∈ regularSet (sliceMap G (τ q)) :=
        spacePart_mem_regularSet_of_spatialDeriv_surjective hG (hz q)
      simpa [τ, x, Function.comp_def] using
        (continuousAt_sliceTau hG hxreg).comp
          (hτ.continuousAt.prodMk hx.continuousAt)
    · change Continuous fun q => gradVec (sliceMap G (τ q)) k (x q)
      convert (contDiff_sliceGrad hG k).continuous.comp (hτ.prodMk hx) using 1
      · apply TopologicalSpace.ext
        rfl
      · rfl
  apply continuous_matrix
  intro i j
  change Continuous fun q => WithLp.ofLp (A q i) j
  exact (EuclideanSpace.proj j).continuous.comp (hA i)


-- @@ L188-195 verbatim
/-- The unnormalized regular-zero frame as a continuous matrix family. -/
def regularZeroRawFrame
    {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) :
    C(P, Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) where
  toFun := regularZeroRawFrameMatrix G z
  continuous_toFun := continuous_regularZeroRawFrameMatrix hG z hz


-- @@ L197-204 verbatim
theorem regularZeroRawFrame_det_pos
    {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) (q : P) :
    0 < (regularZeroRawFrame hG z hz q).det := by
  exact PositiveSheetSlabTamedField.det_rowsMatrix_sliceFrameAt_pos
    G (tcoord (z q)) (spacePart (z q))
    (spacePart_mem_regularSet_of_spatialDeriv_surjective hG (hz q))


-- @@ L206-214 verbatim
theorem regularZeroRawFrame_closed
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(I, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q)))
    (hclosed : z 0 = z 1) :
    regularZeroRawFrame hG z hz 0 = regularZeroRawFrame hG z hz 1 := by
  change regularZeroRawFrameMatrix G z 0 =
    regularZeroRawFrameMatrix G z 1
  unfold regularZeroRawFrameMatrix
  rw [hclosed]


-- @@ L216-234 verbatim
/-- The canonical regular-zero frame is exactly positive Gram--Schmidt of its
unnormalized slice-frame matrix. -/
theorem regularZeroFrame_eq_positiveMatrixSOMap_raw
    {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) :
    regularZeroFrame hG z hz =
      positiveMatrixSOMap (regularZeroRawFrame hG z hz)
        (regularZeroRawFrame_det_pos hG z hz) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change rowsMatrix (gramSchmidtNormed ℝ
      (SlabTamedField.sliceFrameAt G
        (tcoord (z q)) (spacePart (z q)))) =
    rowsMatrix (gramSchmidtNormed ℝ
      (matrixRows (rowsMatrix (SlabTamedField.sliceFrameAt G
        (tcoord (z q)) (spacePart (z q))))))
  rw [matrixRows_rowsMatrix_eq]


-- @@ L236-236 verbatim
end RawFrame


-- @@ L238-238 verbatim
namespace StandardBirth


-- @@ L240-245 verbatim
/-- The standard signed birth-plane rotation, viewed only as its underlying
positive-determinant matrix loop. -/
def birthPlaneMatrixLoop (a : ℕ) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun u := (birthPlaneLoop a u : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  continuous_toFun := continuous_SOGroup_val.comp (birthPlaneLoop a).continuous


-- @@ L247-249 verbatim
theorem birthPlaneMatrixLoop_det_pos (a : ℕ) (u : I) :
    0 < (birthPlaneMatrixLoop a u).det :=
  SOGroup_det_pos (birthPlaneLoop a u)


-- @@ L251-253 verbatim
theorem birthPlaneMatrixLoop_closed (a : ℕ) :
    birthPlaneMatrixLoop a 0 = birthPlaneMatrixLoop a 1 := by
  exact congrArg Subtype.val (birthPlaneLoop_closed a)


-- @@ L255-258 verbatim
theorem positiveMatrixSOMap_birthPlaneMatrixLoop (a : ℕ) :
    positiveMatrixSOMap (birthPlaneMatrixLoop a)
        (birthPlaneMatrixLoop_det_pos a) = birthPlaneLoop a := by
  exact positiveMatrixSOMap_SOGroupMatrixMap (birthPlaneLoop a)


-- @@ L260-273 verbatim
theorem loopClassZ2_positiveMatrixSOMap_birthPlaneMatrixLoop (a : ℕ) :
    loopClassZ2
        (positiveMatrixSOMap (birthPlaneMatrixLoop a)
          (birthPlaneMatrixLoop_det_pos a))
        (positiveMatrixSOMap_closed (birthPlaneMatrixLoop a)
          (birthPlaneMatrixLoop_det_pos a)
          (birthPlaneMatrixLoop_closed a)) = 1 := by
  exact (loopClassZ2_congr_fun
    (positiveMatrixSOMap_closed (birthPlaneMatrixLoop a)
      (birthPlaneMatrixLoop_det_pos a)
      (birthPlaneMatrixLoop_closed a))
    (birthPlaneLoop_closed a)
    (positiveMatrixSOMap_birthPlaneMatrixLoop a)).trans
      (loopClassZ2_birthPlaneLoop a)


-- @@ L275-275 verbatim
end StandardBirth


-- @@ L277-296 verbatim
/-- A positive straight segment from one raw frame loop to any class-one raw
frame loop proves that the first loop also has class one. -/
theorem loopClassZ2_positiveMatrixSOMap_eq_one_of_segment_pos
    {m : ℕ}
    (M S : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hMpos : ∀ u, 0 < (M u).det)
    (hSpos : ∀ u, 0 < (S u).det)
    (hMclosed : M 0 = M 1)
    (hSclosed : S 0 = S 1)
    (hSclass : loopClassZ2 (positiveMatrixSOMap S hSpos)
      (positiveMatrixSOMap_closed S hSpos hSclosed) = 1)
    (hsegment : ∀ q : I × I,
      0 < (matrixSegment (M q.2) (S q.2) q.1).det) :
    loopClassZ2 (positiveMatrixSOMap M hMpos)
        (positiveMatrixSOMap_closed M hMpos hMclosed) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (matrixSegmentHomotopy M S) hMpos hSpos hsegment
    hMclosed hSclosed
    (matrixSegmentHomotopy_closed M S hMclosed hSclosed)
  exact hclass.trans hSclass


-- @@ L298-332 verbatim
/-- A continuous radial extension to any positive class-one raw loop supplies
a small positive radius whose projected frame loop has class one. -/
theorem exists_pos_radius_loopClassZ2_eq_one_of_zero_eq
    {m : ℕ}
    (A : C(ℝ × I, Matrix (Fin m) (Fin m) ℝ))
    (S : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hzero : ∀ u, A (0, u) = S u)
    (hclosed : ∀ r, A (r, 0) = A (r, 1))
    (hSpos : ∀ u, 0 < (S u).det)
    (hSclosed : S 0 = S 1)
    (hSclass : loopClassZ2 (positiveMatrixSOMap S hSpos)
      (positiveMatrixSOMap_closed S hSpos hSclosed) = 1)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ r, 0 < r ∧ r < rho ∧
      ∃ hMpos : ∀ u, 0 < (matrixFamilyRadiusSlice A r u).det,
        loopClassZ2
            (positiveMatrixSOMap (matrixFamilyRadiusSlice A r) hMpos)
            (positiveMatrixSOMap_closed (matrixFamilyRadiusSlice A r)
              hMpos (hclosed r)) = 1 := by
  obtain ⟨r, hr, hrrho, hsegment⟩ :=
    exists_pos_radius_matrixSegment_det_pos_of_zero_eq A
      S hzero hSpos hrho
  let M := matrixFamilyRadiusSlice A r
  have hMpos : ∀ u, 0 < (M u).det := by
    intro u
    have h := hsegment (0, u)
    simpa [M, matrixFamilyRadiusSlice] using h
  have hMclosed : M 0 = M 1 := by
    exact hclosed r
  have hMsegment : ∀ q : I × I,
      0 < (matrixSegment (M q.2) (S q.2) q.1).det := by
    simpa [M, matrixFamilyRadiusSlice] using hsegment
  refine ⟨r, hr, hrrho, hMpos, ?_⟩
  exact loopClassZ2_positiveMatrixSOMap_eq_one_of_segment_pos
    M S hMpos hSpos hMclosed hSclosed hSclass hMsegment


-- @@ L334-352 verbatim
/-- Standard-birth specialization of the generic radial-extension bridge. -/
theorem exists_pos_radius_loopClassZ2_eq_one_of_zero_eq_standardBirth
    (a : ℕ)
    (A : C(ℝ × I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ))
    (hzero : ∀ u, A (0, u) = StandardBirth.birthPlaneMatrixLoop a u)
    (hclosed : ∀ r, A (r, 0) = A (r, 1))
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ r, 0 < r ∧ r < rho ∧
      ∃ hMpos : ∀ u, 0 < (matrixFamilyRadiusSlice A r u).det,
        loopClassZ2
            (positiveMatrixSOMap (matrixFamilyRadiusSlice A r) hMpos)
            (positiveMatrixSOMap_closed (matrixFamilyRadiusSlice A r)
              hMpos (hclosed r)) = 1 := by
  exact exists_pos_radius_loopClassZ2_eq_one_of_zero_eq A
    (StandardBirth.birthPlaneMatrixLoop a) hzero hclosed
    (StandardBirth.birthPlaneMatrixLoop_det_pos a)
    (StandardBirth.birthPlaneMatrixLoop_closed a)
    (StandardBirth.loopClassZ2_positiveMatrixSOMap_birthPlaneMatrixLoop a)
    hrho


-- @@ L354-354 verbatim
end Submission
