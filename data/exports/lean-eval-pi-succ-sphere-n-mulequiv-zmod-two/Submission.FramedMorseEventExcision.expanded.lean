import Mathlib
import Submission.MorseCriticalModelAssembly
import Submission.ExactMorsePositionAssembly
import Submission.PositiveMorseLedgerSplice
import Submission.PositiveSheetFrameTransport


-- @@ L7-24 verbatim
/-!
# Differential compatibility of an installed Morse event

The installed finite Morse construction gives an exact equality between
ambient time on its local zero-surface parameter and a two-dimensional Morse
quadratic.  Here we differentiate that equality on the production shrink.

The resulting theorem is genuinely ambient: a tangent vector to a standard
Morse level is carried by the installed surface parameter to a vector with
zero time component in the kernel of the actual defining-map differential.
Equivalently, its spatial part lies in the kernel of the actual slice's
`spatialDeriv`.

This is the differential statement available without adding geometric data to
`LocalMorseNormalForm`.  Identifying the resulting ordered normal frame with a
literal birth or Cassini frame requires further information; see the final
section.
-/


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
open Set Function Metric Filter

-- @@ L31-31 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L33-33 verbatim
variable {n : ℕ}


-- @@ L35-35 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L36-36 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L37-37 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L38-38 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L40-44 verbatim
/-- Insert an ordinary coordinate pair into the standard two-dimensional
Euclidean Morse chart. -/
def pairToMorseParam (q : ℝ × ℝ) : E₂ :=
  q.1 • EuclideanSpace.single 0 1 +
    q.2 • EuclideanSpace.single 1 1


-- @@ L46-48 verbatim
@[simp] theorem pairToMorseParam_apply_zero (q : ℝ × ℝ) :
    pairToMorseParam q 0 = q.1 := by
  simp [pairToMorseParam]


-- @@ L50-52 verbatim
@[simp] theorem pairToMorseParam_apply_one (q : ℝ × ℝ) :
    pairToMorseParam q 1 = q.2 := by
  simp [pairToMorseParam]


-- @@ L54-59 verbatim
/-- Squared Euclidean radius of the inserted Morse parameter. -/
theorem norm_pairToMorseParam_sq (q : ℝ × ℝ) :
    ‖pairToMorseParam q‖ ^ 2 = q.1 ^ 2 + q.2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp [Fin.sum_univ_two, sq_abs]
  · positivity


-- @@ L61-70 verbatim
/-- Both branches of a positive saddle level have the same radial formula. -/
theorem norm_pairToMorseParam_saddlePositiveArc_sq
    (b : SaddleBranch) (a s : ℝ) :
    ‖pairToMorseParam (saddlePositiveArc b a s)‖ ^ 2 =
      a ^ 2 + 2 * s ^ 2 := by
  rw [norm_pairToMorseParam_sq]
  have hsqrt : (Real.sqrt (a ^ 2 + s ^ 2)) ^ 2 = a ^ 2 + s ^ 2 :=
    Real.sq_sqrt (by positivity)
  simp [saddlePositiveArc, signedBranch_sq, hsqrt]
  ring


-- @@ L72-81 verbatim
/-- Both branches of a negative saddle level have the same radial formula. -/
theorem norm_pairToMorseParam_saddleNegativeArc_sq
    (b : SaddleBranch) (a s : ℝ) :
    ‖pairToMorseParam (saddleNegativeArc b a s)‖ ^ 2 =
      a ^ 2 + 2 * s ^ 2 := by
  rw [norm_pairToMorseParam_sq]
  have hsqrt : (Real.sqrt (a ^ 2 + s ^ 2)) ^ 2 = a ^ 2 + s ^ 2 :=
    Real.sq_sqrt (by positivity)
  simp [saddleNegativeArc, signedBranch_sq, hsqrt]
  ring


-- @@ L83-86 verbatim
/-- Parameter magnitude at which a saddle level of height `±a²` meets the
parameter circle of radius `ρ`. -/
def saddleBoundaryParameter (ρ a : ℝ) : ℝ :=
  Real.sqrt ((ρ ^ 2 - a ^ 2) / 2)


-- @@ L88-93 verbatim
theorem saddleBoundaryParameter_sq {ρ a : ℝ} (ha : a ^ 2 ≤ ρ ^ 2) :
    saddleBoundaryParameter ρ a ^ 2 = (ρ ^ 2 - a ^ 2) / 2 := by
  exact Real.sq_sqrt (by
    apply div_nonneg
    · linarith
    · norm_num)


-- @@ L95-100 verbatim
/-- One of the four positive-side ends on a fixed parameter circle.  `b`
labels the hyperbola component and `e` labels its two ends. -/
def saddlePositiveBoundaryEndParam
    (b e : SaddleBranch) (ρ a : ℝ) : E₂ :=
  pairToMorseParam (saddlePositiveArc b a
    (signedBranch e (saddleBoundaryParameter ρ a)))


-- @@ L102-106 verbatim
/-- One of the four negative-side ends on a fixed parameter circle. -/
def saddleNegativeBoundaryEndParam
    (b e : SaddleBranch) (ρ a : ℝ) : E₂ :=
  pairToMorseParam (saddleNegativeArc b a
    (signedBranch e (saddleBoundaryParameter ρ a)))


-- @@ L108-120 verbatim
/-- Every positive-side boundary end lies on the requested parameter circle. -/
theorem norm_saddlePositiveBoundaryEndParam
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) :
    ‖saddlePositiveBoundaryEndParam b e ρ a‖ = ρ := by
  have hs := saddleBoundaryParameter_sq (le_of_lt ha)
  have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b a
    (signedBranch e (saddleBoundaryParameter ρ a))
  rw [signedBranch_sq, hs] at hsq
  have hnorm : 0 ≤ ‖saddlePositiveBoundaryEndParam b e ρ a‖ := norm_nonneg _
  change ‖saddlePositiveBoundaryEndParam b e ρ a‖ ^ 2 =
    a ^ 2 + 2 * ((ρ ^ 2 - a ^ 2) / 2) at hsq
  nlinarith


-- @@ L122-134 verbatim
/-- Every negative-side boundary end lies on the same parameter circle. -/
theorem norm_saddleNegativeBoundaryEndParam
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) :
    ‖saddleNegativeBoundaryEndParam b e ρ a‖ = ρ := by
  have hs := saddleBoundaryParameter_sq (le_of_lt ha)
  have hsq := norm_pairToMorseParam_saddleNegativeArc_sq b a
    (signedBranch e (saddleBoundaryParameter ρ a))
  rw [signedBranch_sq, hs] at hsq
  have hnorm : 0 ≤ ‖saddleNegativeBoundaryEndParam b e ρ a‖ := norm_nonneg _
  change ‖saddleNegativeBoundaryEndParam b e ρ a‖ ^ 2 =
    a ^ 2 + 2 * ((ρ ^ 2 - a ^ 2) / 2) at hsq
  nlinarith


-- @@ L136-150 verbatim
/-- At the critical level, the positive-side component/end labels become the
negative-side end/component labels.  This is the exact four-end pairing switch
underlying the saddle splice. -/
theorem saddle_boundary_pairing_switch (b e : SaddleBranch) (ρ : ℝ) :
    saddlePositiveBoundaryEndParam b e ρ 0 =
      saddleNegativeBoundaryEndParam e b ρ 0 := by
  have hσ : 0 ≤ saddleBoundaryParameter ρ 0 := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt ((saddleBoundaryParameter ρ 0) ^ 2) =
      saddleBoundaryParameter ρ 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hσ]
  ext i
  fin_cases i <;>
    simp [saddlePositiveBoundaryEndParam,
      saddleNegativeBoundaryEndParam, saddlePositiveArc,
      saddleNegativeArc, hsqrt]


-- @@ L152-157 verbatim
private theorem euclidean_fin_two_ext {u v : E₂}
    (h₀ : u 0 = v 0) (h₁ : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · simpa using h₀
  · simpa using h₁


-- @@ L159-186 verbatim
/-- Every point of a positive saddle level with a prescribed first-coordinate
sign is exactly on the corresponding explicit positive arc. -/
theorem eq_pairToMorseParam_saddlePositiveArc_of_signedBranch
    (b : SaddleBranch) (a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0)) :
    u = pairToMorseParam (saddlePositiveArc b a (u 1)) := by
  have hsquare : u 0 ^ 2 = a ^ 2 + u 1 ^ 2 := by
    simp only [morseQuadratic] at hquad
    linarith
  have hsqrt : Real.sqrt (a ^ 2 + u 1 ^ 2) = |u 0| := by
    rw [← hsquare, Real.sqrt_sq_eq_abs]
  apply euclidean_fin_two_ext
  · cases b with
    | positive =>
        rw [pairToMorseParam_apply_zero]
        change u 0 = Real.sqrt (a ^ 2 + u 1 ^ 2)
        simp only [signedBranch] at hsign
        rw [hsqrt, abs_of_pos hsign]
    | negative =>
        rw [pairToMorseParam_apply_zero]
        change u 0 = -Real.sqrt (a ^ 2 + u 1 ^ 2)
        simp only [signedBranch] at hsign
        have hx : u 0 < 0 := by linarith
        rw [hsqrt, abs_of_neg hx]
        ring
  · rw [pairToMorseParam_apply_one]
    rfl


-- @@ L188-215 verbatim
/-- Every point of a negative saddle level with a prescribed second-coordinate
sign is exactly on the corresponding explicit negative arc. -/
theorem eq_pairToMorseParam_saddleNegativeArc_of_signedBranch
    (b : SaddleBranch) (a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1)) :
    u = pairToMorseParam (saddleNegativeArc b a (u 0)) := by
  have hsquare : u 1 ^ 2 = a ^ 2 + u 0 ^ 2 := by
    simp only [morseQuadratic] at hquad
    linarith
  have hsqrt : Real.sqrt (a ^ 2 + u 0 ^ 2) = |u 1| := by
    rw [← hsquare, Real.sqrt_sq_eq_abs]
  apply euclidean_fin_two_ext
  · rw [pairToMorseParam_apply_zero]
    rfl
  · cases b with
    | positive =>
        rw [pairToMorseParam_apply_one]
        change u 1 = Real.sqrt (a ^ 2 + u 0 ^ 2)
        simp only [signedBranch] at hsign
        rw [hsqrt, abs_of_pos hsign]
    | negative =>
        rw [pairToMorseParam_apply_one]
        change u 1 = -Real.sqrt (a ^ 2 + u 0 ^ 2)
        simp only [signedBranch] at hsign
        have hy : u 1 < 0 := by linarith
        rw [hsqrt, abs_of_neg hy]
        ring


-- @@ L217-217 verbatim
/-! ## Affine paths from local saddle points to installed boundary ends -/


-- @@ L219-222 verbatim
/-- The ordinary affine coordinate joining two parameters on one explicit
hyperbola branch. -/
def saddleAffineCoordinate (s₀ s₁ : ℝ) (q : I) : ℝ :=
  (1 - (q : ℝ)) * s₀ + (q : ℝ) * s₁


-- @@ L224-226 verbatim
@[simp] theorem saddleAffineCoordinate_zero (s₀ s₁ : ℝ) :
    saddleAffineCoordinate s₀ s₁ 0 = s₀ := by
  simp [saddleAffineCoordinate]


-- @@ L228-230 verbatim
@[simp] theorem saddleAffineCoordinate_one (s₀ s₁ : ℝ) :
    saddleAffineCoordinate s₀ s₁ 1 = s₁ := by
  simp [saddleAffineCoordinate]


-- @@ L232-244 verbatim
/-- Squared affine interpolation is bounded by the corresponding convex
combination of endpoint squares. -/
theorem saddleAffineCoordinate_sq_le (s₀ s₁ : ℝ) (q : I) :
    saddleAffineCoordinate s₀ s₁ q ^ 2 ≤
      (1 - (q : ℝ)) * s₀ ^ 2 + (q : ℝ) * s₁ ^ 2 := by
  have hq0 : 0 ≤ (q : ℝ) := q.property.1
  have hq1 : (q : ℝ) ≤ 1 := q.property.2
  have hprod : 0 ≤ (q : ℝ) * (1 - (q : ℝ)) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hmul : 0 ≤ (q : ℝ) * (1 - (q : ℝ)) * (s₀ - s₁) ^ 2 :=
    mul_nonneg hprod (sq_nonneg _)
  simp only [saddleAffineCoordinate]
  nlinarith


-- @@ L246-257 verbatim
/-- The positive-level arc from an arbitrary point of a signed component to
a chosen end on the installed parameter circle. -/
def saddlePositiveArcToBoundaryParam
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂) : C(I, E₂) where
  toFun q := pairToMorseParam (saddlePositiveArc b a
    (saddleAffineCoordinate (u 1)
      (signedBranch e (saddleBoundaryParameter ρ a)) q))
  continuous_toFun := by
    cases b <;> cases e <;>
      simp only [pairToMorseParam, saddlePositiveArc, signedBranch,
        saddleAffineCoordinate, saddleBoundaryParameter] <;>
      fun_prop


-- @@ L259-269 verbatim
/-- The negative-level analogue of `saddlePositiveArcToBoundaryParam`. -/
def saddleNegativeArcToBoundaryParam
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂) : C(I, E₂) where
  toFun q := pairToMorseParam (saddleNegativeArc b a
    (saddleAffineCoordinate (u 0)
      (signedBranch e (saddleBoundaryParameter ρ a)) q))
  continuous_toFun := by
    cases b <;> cases e <;>
      simp only [pairToMorseParam, saddleNegativeArc, signedBranch,
        saddleAffineCoordinate, saddleBoundaryParameter] <;>
      fun_prop


-- @@ L271-329 verbatim
/-- If both endpoints of a positive-level branch arc lie in a radius, then
the whole affine branch arc lies strictly in that radius. -/
theorem norm_saddlePositiveArcToBoundaryParam_lt
    (b e : SaddleBranch) {ρ a R : ℝ} (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < R) (hρR : ρ < R) (q : I) :
    ‖saddlePositiveArcToBoundaryParam b e ρ a u q‖ < R := by
  let s₁ := signedBranch e (saddleBoundaryParameter ρ a)
  have hclass :=
    eq_pairToMorseParam_saddlePositiveArc_of_signedBranch b a u hquad hsign
  have hstart : ‖u‖ ^ 2 = a ^ 2 + 2 * (u 1) ^ 2 := by
    calc
      ‖u‖ ^ 2 = ‖pairToMorseParam (saddlePositiveArc b a (u 1))‖ ^ 2 :=
        congrArg (fun z : E₂ => ‖z‖ ^ 2) hclass
      _ = a ^ 2 + 2 * (u 1) ^ 2 :=
        norm_pairToMorseParam_saddlePositiveArc_sq b a (u 1)
  have hend : a ^ 2 + 2 * s₁ ^ 2 = ρ ^ 2 := by
    dsimp [s₁]
    rw [signedBranch_sq, saddleBoundaryParameter_sq (le_of_lt ha)]
    ring
  have hcoord := saddleAffineCoordinate_sq_le (u 1) s₁ q
  have hcurve := norm_pairToMorseParam_saddlePositiveArc_sq b a
    (saddleAffineCoordinate (u 1) s₁ q)
  have hcurveSq :
      ‖saddlePositiveArcToBoundaryParam b e ρ a u q‖ ^ 2 ≤
        (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 := by
    change ‖pairToMorseParam (saddlePositiveArc b a
      (saddleAffineCoordinate (u 1) s₁ q))‖ ^ 2 ≤ _
    calc
      ‖pairToMorseParam (saddlePositiveArc b a
          (saddleAffineCoordinate (u 1) s₁ q))‖ ^ 2 =
          a ^ 2 + 2 * saddleAffineCoordinate (u 1) s₁ q ^ 2 := hcurve
      _ ≤ a ^ 2 + 2 *
          ((1 - (q : ℝ)) * (u 1) ^ 2 + (q : ℝ) * s₁ ^ 2) := by
        gcongr
      _ = (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 := by
        rw [hstart, ← hend]
        ring
  have hR : 0 < R := (norm_nonneg u).trans_lt hu
  have huSq : ‖u‖ ^ 2 < R ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg u) hR.le).2 hu
  have hρSq : ρ ^ 2 < R ^ 2 :=
    (sq_lt_sq₀ hρ.le hR.le).2 hρR
  have hweighted :
      (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 < R ^ 2 := by
    have hq0 : 0 ≤ (q : ℝ) := q.property.1
    have hq1 : (q : ℝ) ≤ 1 := q.property.2
    have hleft : ‖u‖ ^ 2 ≤ max (‖u‖ ^ 2) (ρ ^ 2) := le_max_left _ _
    have hright : ρ ^ 2 ≤ max (‖u‖ ^ 2) (ρ ^ 2) := le_max_right _ _
    calc
      (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 ≤
          (1 - (q : ℝ)) * max (‖u‖ ^ 2) (ρ ^ 2) +
            (q : ℝ) * max (‖u‖ ^ 2) (ρ ^ 2) := by
        gcongr
      _ = max (‖u‖ ^ 2) (ρ ^ 2) := by ring
      _ < R ^ 2 := max_lt huSq hρSq
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).1 (hcurveSq.trans_lt hweighted)


-- @@ L331-388 verbatim
/-- The corresponding radius control on a negative-level branch arc. -/
theorem norm_saddleNegativeArcToBoundaryParam_lt
    (b e : SaddleBranch) {ρ a R : ℝ} (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < R) (hρR : ρ < R) (q : I) :
    ‖saddleNegativeArcToBoundaryParam b e ρ a u q‖ < R := by
  let s₁ := signedBranch e (saddleBoundaryParameter ρ a)
  have hclass :=
    eq_pairToMorseParam_saddleNegativeArc_of_signedBranch b a u hquad hsign
  have hstart : ‖u‖ ^ 2 = a ^ 2 + 2 * (u 0) ^ 2 := by
    calc
      ‖u‖ ^ 2 = ‖pairToMorseParam (saddleNegativeArc b a (u 0))‖ ^ 2 :=
        congrArg (fun z : E₂ => ‖z‖ ^ 2) hclass
      _ = a ^ 2 + 2 * (u 0) ^ 2 :=
        norm_pairToMorseParam_saddleNegativeArc_sq b a (u 0)
  have hend : a ^ 2 + 2 * s₁ ^ 2 = ρ ^ 2 := by
    dsimp [s₁]
    rw [signedBranch_sq, saddleBoundaryParameter_sq (le_of_lt ha)]
    ring
  have hcoord := saddleAffineCoordinate_sq_le (u 0) s₁ q
  have hcurve := norm_pairToMorseParam_saddleNegativeArc_sq b a
    (saddleAffineCoordinate (u 0) s₁ q)
  have hcurveSq :
      ‖saddleNegativeArcToBoundaryParam b e ρ a u q‖ ^ 2 ≤
        (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 := by
    change ‖pairToMorseParam (saddleNegativeArc b a
      (saddleAffineCoordinate (u 0) s₁ q))‖ ^ 2 ≤ _
    calc
      ‖pairToMorseParam (saddleNegativeArc b a
          (saddleAffineCoordinate (u 0) s₁ q))‖ ^ 2 =
          a ^ 2 + 2 * saddleAffineCoordinate (u 0) s₁ q ^ 2 := hcurve
      _ ≤ a ^ 2 + 2 *
          ((1 - (q : ℝ)) * (u 0) ^ 2 + (q : ℝ) * s₁ ^ 2) := by
        gcongr
      _ = (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 := by
        rw [hstart, ← hend]
        ring
  have hR : 0 < R := (norm_nonneg u).trans_lt hu
  have huSq : ‖u‖ ^ 2 < R ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg u) hR.le).2 hu
  have hρSq : ρ ^ 2 < R ^ 2 :=
    (sq_lt_sq₀ hρ.le hR.le).2 hρR
  have hweighted :
      (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 < R ^ 2 := by
    have hq0 : 0 ≤ (q : ℝ) := q.property.1
    have hq1 : (q : ℝ) ≤ 1 := q.property.2
    have hleft : ‖u‖ ^ 2 ≤ max (‖u‖ ^ 2) (ρ ^ 2) := le_max_left _ _
    have hright : ρ ^ 2 ≤ max (‖u‖ ^ 2) (ρ ^ 2) := le_max_right _ _
    calc
      (1 - (q : ℝ)) * ‖u‖ ^ 2 + (q : ℝ) * ρ ^ 2 ≤
          (1 - (q : ℝ)) * max (‖u‖ ^ 2) (ρ ^ 2) +
            (q : ℝ) * max (‖u‖ ^ 2) (ρ ^ 2) := by
        gcongr
      _ = max (‖u‖ ^ 2) (ρ ^ 2) := by ring
      _ < R ^ 2 := max_lt huSq hρSq
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).1 (hcurveSq.trans_lt hweighted)


-- @@ L390-390 verbatim
/-! ## The canonical tangent of a two-dimensional Morse level -/


-- @@ L392-401 verbatim
/-- A non-normalized tangent vector to the level curves of each standard
two-dimensional Morse quadratic. -/
def morseLevelTangent (e : MorseIndexTwo) (u : E₂) : E₂ :=
  match e with
  | .minimum =>
      EuclideanSpace.single 0 (-u 1) + EuclideanSpace.single 1 (u 0)
  | .saddle =>
      EuclideanSpace.single 0 (u 1) + EuclideanSpace.single 1 (u 0)
  | .maximum =>
      EuclideanSpace.single 0 (u 1) + EuclideanSpace.single 1 (-u 0)


-- @@ L403-450 verbatim
/-- The canonical model tangent is killed by the differential of the Morse
quadratic at its base point. -/
theorem fderiv_morseQuadratic_morseLevelTangent
    (e : MorseIndexTwo) (c : ℝ) (u : E₂) :
    fderiv ℝ (fun z : E₂ => c + morseQuadratic e (z 0, z 1)) u
      (morseLevelTangent e u) = 0 := by
  let p0 : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hp0 : HasFDerivAt (fun z : E₂ => z 0) p0 u := by
    simpa [p0] using (p0.hasFDerivAt : HasFDerivAt p0 p0 u)
  have hp1 : HasFDerivAt (fun z : E₂ => z 1) p1 u := by
    simpa [p1] using (p1.hasFDerivAt : HasFDerivAt p1 p1 u)
  have hc : HasFDerivAt (fun _ : E₂ => c) (0 : E₂ →L[ℝ] ℝ) u :=
    hasFDerivAt_const c u
  cases e with
  | minimum =>
      simp only [morseQuadratic, pow_two]
      have hmodel := hc.add ((hp0.mul hp0).add (hp1.mul hp1))
      change HasFDerivAt (fun z : E₂ => c +
        (z 0 * z 0 + z 1 * z 1)) _ u at hmodel
      change (fderiv ℝ (fun z : E₂ => c +
        (z 0 * z 0 + z 1 * z 1)) u)
          (morseLevelTangent .minimum u) = 0
      rw [hmodel.fderiv]
      simp [morseLevelTangent, p0, p1]
      ring
  | saddle =>
      simp only [morseQuadratic, pow_two]
      have hmodel := hc.add ((hp0.mul hp0).sub (hp1.mul hp1))
      change HasFDerivAt (fun z : E₂ => c +
        (z 0 * z 0 - z 1 * z 1)) _ u at hmodel
      change (fderiv ℝ (fun z : E₂ => c +
        (z 0 * z 0 - z 1 * z 1)) u)
          (morseLevelTangent .saddle u) = 0
      rw [hmodel.fderiv]
      simp [morseLevelTangent, p0, p1]
      ring
  | maximum =>
      simp only [morseQuadratic, pow_two]
      have hmodel := hc.add ((hp0.mul hp0).neg.sub (hp1.mul hp1))
      change HasFDerivAt (fun z : E₂ => c +
        (-(z 0 * z 0) - z 1 * z 1)) _ u at hmodel
      change (fderiv ℝ (fun z : E₂ => c +
        (-(z 0 * z 0) - z 1 * z 1)) u)
          (morseLevelTangent .maximum u) = 0
      rw [hmodel.fderiv]
      simp [morseLevelTangent, p0, p1]
      ring


-- @@ L452-460 verbatim
/-- Away from the critical point, the canonical model tangent is nonzero. -/
theorem morseLevelTangent_ne_zero (e : MorseIndexTwo) {u : E₂} (hu : u ≠ 0) :
    morseLevelTangent e u ≠ 0 := by
  cases e <;> intro hzero <;> apply hu <;> ext i <;> fin_cases i
  all_goals
    have h0 := congrArg (fun z : E₂ => z 0) hzero
    have h1 := congrArg (fun z : E₂ => z 1) hzero
    simp [morseLevelTangent] at h0 h1 ⊢
    assumption


-- @@ L462-470 verbatim
/-- A point on a nonzero Morse level has a nonzero canonical tangent. -/
theorem morseLevelTangent_ne_zero_of_morseQuadratic_ne_zero
    (e : MorseIndexTwo) (u : E₂)
    (hquad : morseQuadratic e (u 0, u 1) ≠ 0) :
    morseLevelTangent e u ≠ 0 := by
  apply morseLevelTangent_ne_zero e
  intro hu
  subst u
  cases e <;> simp [morseQuadratic] at hquad


-- @@ L472-472 verbatim
/-! ## Local injectivity of the production parameters -/


-- @@ L474-474 verbatim
namespace LocalMorseNormalForm


-- @@ L476-513 verbatim
/-- An invertible derivative at the origin makes the Morse parameter injective
on a sufficiently small ball.  This recovers the local embedding property of
the inverse-function construction from the compact normal-form interface. -/
theorem exists_param_injOn_ball_of_fderiv_injective
    {f : E₂ → ℝ} (M : LocalMorseNormalForm f)
    (hJinj : Injective (fderiv ℝ M.param 0))
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r > 0, r ≤ r₀ ∧ Set.InjOn M.param (ball (0 : E₂) r) := by
  let J : E₂ →L[ℝ] E₂ := fderiv ℝ M.param 0
  have hJsurj : Surjective J :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hJinj
  let e : E₂ ≃L[ℝ] E₂ := ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hJinj) (LinearMap.range_eq_top.mpr hJsurj)
  have he : (e : E₂ →L[ℝ] E₂) = J := rfl
  have hfd : HasFDerivAt M.param (e : E₂ →L[ℝ] E₂) 0 := by
    rw [he]
    exact (M.param_contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hs : HasStrictFDerivAt M.param (e : E₂ →L[ℝ] E₂) 0 :=
    M.param_contDiffAt.hasStrictFDerivAt' hfd (by simp)
  let inv : E₂ → E₂ := hs.localInverse M.param e 0
  let L : Set E₂ := {u | inv (M.param u) = u}
  have hL : L ∈ nhds (0 : E₂) := by
    exact hs.eventually_left_inverse
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hL
  let r := min δ r₀
  have hr : 0 < r := lt_min hδ hr₀
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro u hu v hv huv
  have huδ : u ∈ ball (0 : E₂) δ :=
    Metric.ball_subset_ball (min_le_left δ r₀) hu
  have hvδ : v ∈ ball (0 : E₂) δ :=
    Metric.ball_subset_ball (min_le_left δ r₀) hv
  have huL : inv (M.param u) = u := hball huδ
  have hvL : inv (M.param v) = v := hball hvδ
  calc
    u = inv (M.param u) := huL.symm
    _ = inv (M.param v) := congrArg inv huv
    _ = v := hvL


-- @@ L515-515 verbatim
end LocalMorseNormalForm


-- @@ L517-517 verbatim
namespace IFTSurfaceChart


-- @@ L519-528 verbatim
/-- The stored recovery coordinates make every production IFT surface chart
injective on its genuine domain. -/
theorem param_injOn_domain {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) : Set.InjOn P.param P.domain := by
  intro u hu v hv huv
  calc
    u = P.recoveryCoordinates (P.param u - P.center) :=
      (P.recoveryCoordinates_param_sub_center hu).symm
    _ = P.recoveryCoordinates (P.param v - P.center) := by rw [huv]
    _ = v := P.recoveryCoordinates_param_sub_center hv


-- @@ L530-530 verbatim
end IFTSurfaceChart


-- @@ L532-549 verbatim
/-- Taking the spatial coordinates of an ambient space-time point is
continuous. -/
theorem continuous_spacePart : Continuous (spacePart (n := n)) := by
  let L : E' →ₗ[ℝ] E₁ :=
    { toFun := spacePart
      map_add' := by
        intro x y
        ext i
        rfl
      map_smul' := by
        intro c x
        ext i
        rfl }
  let Lc : E' →L[ℝ] E₁ := L.mkContinuous 1 (by
    intro x
    simpa [L] using norm_spacePart_le (n := n) x)
  change Continuous (Lc : E' → E₁)
  exact Lc.continuous


-- @@ L551-551 verbatim
namespace TamedField


-- @@ L553-565 verbatim
/-- A continuous interval-valued curve in a regular fiber cannot jump between
intrinsic flow-orbit components. -/
theorem continuousMap_mem_orbit {X : FramedLevelSet n} (V : TamedField X)
    (γ : C(I, E₁)) (hγfiber : ∀ u, γ u ∈ X.fiber)
    (u : I) : γ u ∈ V.orbit (γ 0) := by
  let γreal : ℝ → E₁ :=
    fun t => γ (Set.projIcc (0 : ℝ) 1 zero_le_one t)
  have hγreal : Continuous γreal :=
    γ.continuous.comp continuous_projIcc
  have hγrealFiber : ∀ t, γreal t ∈ X.fiber :=
    fun t => hγfiber (Set.projIcc (0 : ℝ) 1 zero_le_one t)
  have h := V.continuousCurve_mem_orbit γreal hγreal hγrealFiber (u : ℝ)
  simpa [γreal, Set.projIcc_val] using h


-- @@ L567-567 verbatim
end TamedField


-- @@ L569-569 verbatim
/-! ## Truncated local saddle segments -/


-- @@ L571-574 verbatim
/-- Affine coordinate running from the negative to the positive end of a
truncated hyperbola branch. -/
def saddleSegmentCoordinate (ρ a : ℝ) (u : I) : ℝ :=
  (2 * (u : ℝ) - 1) * saddleBoundaryParameter ρ a


-- @@ L576-579 verbatim
@[simp] theorem saddleSegmentCoordinate_zero (ρ a : ℝ) :
    saddleSegmentCoordinate ρ a 0 =
      signedBranch .negative (saddleBoundaryParameter ρ a) := by
  simp [saddleSegmentCoordinate, signedBranch]


-- @@ L581-585 verbatim
@[simp] theorem saddleSegmentCoordinate_one (ρ a : ℝ) :
    saddleSegmentCoordinate ρ a 1 =
      signedBranch .positive (saddleBoundaryParameter ρ a) := by
  simp [saddleSegmentCoordinate, signedBranch]
  ring


-- @@ L587-598 verbatim
theorem saddleSegmentCoordinate_sq_le (ρ a : ℝ) (u : I) :
    saddleSegmentCoordinate ρ a u ^ 2 ≤
      saddleBoundaryParameter ρ a ^ 2 := by
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hu1 : (u : ℝ) ≤ 1 := u.property.2
  have hc : (2 * (u : ℝ) - 1) ^ 2 ≤ 1 := by nlinarith
  rw [saddleSegmentCoordinate, mul_pow]
  calc
    (2 * (u : ℝ) - 1) ^ 2 * saddleBoundaryParameter ρ a ^ 2 ≤
        1 * saddleBoundaryParameter ρ a ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = saddleBoundaryParameter ρ a ^ 2 := one_mul _


-- @@ L600-609 verbatim
/-- One complete truncated positive-side hyperbola branch. -/
def saddlePositiveSegmentParam
    (b : SaddleBranch) (ρ a : ℝ) : C(I, E₂) where
  toFun u := pairToMorseParam
    (saddlePositiveArc b a (saddleSegmentCoordinate ρ a u))
  continuous_toFun := by
    cases b <;>
      simp only [pairToMorseParam, saddlePositiveArc, signedBranch,
        saddleSegmentCoordinate, saddleBoundaryParameter] <;>
      fun_prop


-- @@ L611-620 verbatim
/-- One complete truncated negative-side hyperbola branch. -/
def saddleNegativeSegmentParam
    (b : SaddleBranch) (ρ a : ℝ) : C(I, E₂) where
  toFun u := pairToMorseParam
    (saddleNegativeArc b a (saddleSegmentCoordinate ρ a u))
  continuous_toFun := by
    cases b <;>
      simp only [pairToMorseParam, saddleNegativeArc, signedBranch,
        saddleSegmentCoordinate, saddleBoundaryParameter] <;>
      fun_prop


-- @@ L622-644 verbatim
/-- A truncated positive saddle branch stays inside its boundary circle. -/
theorem norm_saddlePositiveSegmentParam_le
    (b : SaddleBranch) {ρ a : ℝ} (hρ : 0 < ρ)
    (ha : a ^ 2 < ρ ^ 2) (u : I) :
    ‖saddlePositiveSegmentParam b ρ a u‖ ≤ ρ := by
  have hcoord := saddleSegmentCoordinate_sq_le ρ a u
  have hboundary := saddleBoundaryParameter_sq (le_of_lt ha)
  have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b a
    (saddleSegmentCoordinate ρ a u)
  have hsqle : ‖saddlePositiveSegmentParam b ρ a u‖ ^ 2 ≤ ρ ^ 2 := by
    change ‖pairToMorseParam
      (saddlePositiveArc b a (saddleSegmentCoordinate ρ a u))‖ ^ 2 ≤ ρ ^ 2
    rw [hsq]
    rw [hboundary] at hcoord
    nlinarith
  by_contra hnot
  have hgt : ρ < ‖saddlePositiveSegmentParam b ρ a u‖ := lt_of_not_ge hnot
  have hprod : 0 <
      (‖saddlePositiveSegmentParam b ρ a u‖ - ρ) *
        (‖saddlePositiveSegmentParam b ρ a u‖ + ρ) :=
    mul_pos (sub_pos.mpr hgt)
      (add_pos_of_nonneg_of_pos (norm_nonneg _) hρ)
  nlinarith


-- @@ L646-668 verbatim
/-- A truncated negative saddle branch stays inside the same boundary circle. -/
theorem norm_saddleNegativeSegmentParam_le
    (b : SaddleBranch) {ρ a : ℝ} (hρ : 0 < ρ)
    (ha : a ^ 2 < ρ ^ 2) (u : I) :
    ‖saddleNegativeSegmentParam b ρ a u‖ ≤ ρ := by
  have hcoord := saddleSegmentCoordinate_sq_le ρ a u
  have hboundary := saddleBoundaryParameter_sq (le_of_lt ha)
  have hsq := norm_pairToMorseParam_saddleNegativeArc_sq b a
    (saddleSegmentCoordinate ρ a u)
  have hsqle : ‖saddleNegativeSegmentParam b ρ a u‖ ^ 2 ≤ ρ ^ 2 := by
    change ‖pairToMorseParam
      (saddleNegativeArc b a (saddleSegmentCoordinate ρ a u))‖ ^ 2 ≤ ρ ^ 2
    rw [hsq]
    rw [hboundary] at hcoord
    nlinarith
  by_contra hnot
  have hgt : ρ < ‖saddleNegativeSegmentParam b ρ a u‖ := lt_of_not_ge hnot
  have hprod : 0 <
      (‖saddleNegativeSegmentParam b ρ a u‖ - ρ) *
        (‖saddleNegativeSegmentParam b ρ a u‖ + ρ) :=
    mul_pos (sub_pos.mpr hgt)
      (add_pos_of_nonneg_of_pos (norm_nonneg _) hρ)
  nlinarith


-- @@ L670-673 verbatim
/-- The amplitude along a boundary track, from the critical level to a chosen
regular level. -/
def saddleBoundaryTrackAmplitude (A : ℝ) (u : I) : ℝ :=
  (u : ℝ) * A


-- @@ L675-677 verbatim
@[simp] theorem saddleBoundaryTrackAmplitude_zero (A : ℝ) :
    saddleBoundaryTrackAmplitude A 0 = 0 := by
  simp [saddleBoundaryTrackAmplitude]


-- @@ L679-681 verbatim
@[simp] theorem saddleBoundaryTrackAmplitude_one (A : ℝ) :
    saddleBoundaryTrackAmplitude A 1 = A := by
  simp [saddleBoundaryTrackAmplitude]


-- @@ L683-693 verbatim
theorem saddleBoundaryTrackAmplitude_sq_lt {ρ A : ℝ}
    (hA : A ^ 2 < ρ ^ 2) (u : I) :
    saddleBoundaryTrackAmplitude A u ^ 2 < ρ ^ 2 := by
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hu1 : (u : ℝ) ≤ 1 := u.property.2
  have huSq : (u : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hmul : (u : ℝ) ^ 2 * A ^ 2 ≤ A ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right huSq (sq_nonneg A)
  rw [saddleBoundaryTrackAmplitude, mul_pow]
  exact hmul.trans_lt hA


-- @@ L695-701 verbatim
/-- A path contained in the regular part of the zero-surface of `G`.  Recording
the range condition makes reversal and concatenation preserve the geometric
constraint without any new assumptions. -/
structure SpatiallyRegularZeroPath (G : E' → F) (x y : E') where
  toPath : Path x y
  range_subset : Set.range toPath ⊆
    {z | G z = 0 ∧ Surjective (spatialDeriv G z)}


-- @@ L703-703 verbatim
namespace SpatiallyRegularZeroPath


-- @@ L705-705 verbatim
variable {n : ℕ}

-- @@ L706-706 verbatim
variable {G : EuclideanSpace ℝ (Fin (n + 2)) → EuclideanSpace ℝ (Fin n)}

-- @@ L707-707 verbatim
variable {x y z : EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L709-711 verbatim
theorem fiber (γ : SpatiallyRegularZeroPath G x y) (u : I) :
    G (γ.toPath u) = 0 :=
  (γ.range_subset ⟨u, rfl⟩).1


-- @@ L713-715 verbatim
theorem regular (γ : SpatiallyRegularZeroPath G x y) (u : I) :
    Surjective (spatialDeriv G (γ.toPath u)) :=
  (γ.range_subset ⟨u, rfl⟩).2


-- @@ L717-723 verbatim
/-- Reverse a path while preserving its regular-zero range. -/
def symm (γ : SpatiallyRegularZeroPath G x y) :
    SpatiallyRegularZeroPath G y x where
  toPath := γ.toPath.symm
  range_subset := by
    rw [Path.symm_range]
    exact γ.range_subset


-- @@ L725-732 verbatim
/-- Concatenate two paths whose ranges lie in the same regular zero-surface. -/
def trans (γ₁ : SpatiallyRegularZeroPath G x y)
    (γ₂ : SpatiallyRegularZeroPath G y z) :
    SpatiallyRegularZeroPath G x z where
  toPath := γ₁.toPath.trans γ₂.toPath
  range_subset := by
    rw [Path.trans_range]
    exact Set.union_subset γ₁.range_subset γ₂.range_subset


-- @@ L734-734 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L735-735 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L737-745 verbatim
/-- A regular-zero path in a signed cobordism cannot change label sign. -/
theorem pos_iff (C : SignedFramedLevelCobordism S₀ S₁)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : SpatiallyRegularZeroPath C.cobordism.G x y) :
    0 < C x ↔ 0 < C y := by
  have h := C.pos_iff_of_zeroFiber_path γ.toPath.toContinuousMap γ.fiber
  change 0 < C (γ.toPath 0) ↔ 0 < C (γ.toPath 1) at h
  rw [γ.toPath.source, γ.toPath.target] at h
  exact h


-- @@ L747-747 verbatim
end SpatiallyRegularZeroPath


-- @@ L749-749 verbatim
/-! ## Canonical moving frames on the spatially regular zero-surface -/


-- @@ L751-760 verbatim
/-- Spatial regularity of an ambient point is exactly regularity of its
spatial coordinate in the corresponding time slice. -/
theorem spacePart_mem_regularSet_of_spatialDeriv_surjective
    {G : E' → F} (hG : ContDiff ℝ ∞ G) {z : E'}
    (hz : Surjective (spatialDeriv G z)) :
    spacePart z ∈ regularSet (sliceMap G (tcoord z)) := by
  change Surjective
    (fderiv ℝ (sliceMap G (tcoord z)) (spacePart z))
  rw [fderiv_sliceMap hG]
  simpa only [spaceTime_spacePart] using hz


-- @@ L762-768 verbatim
/-- The orthonormal slice-frame matrix along an arbitrary continuous family
of ambient points. -/
def regularZeroFrameMatrix {P : Type*} [TopologicalSpace P]
    (G : E' → F) (z : C(P, E')) (q : P) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  rowsMatrix (InnerProductSpace.gramSchmidtNormed ℝ
    (SlabTamedField.sliceFrameAt G (tcoord (z q)) (spacePart (z q))))


-- @@ L770-805 verbatim
theorem continuous_regularZeroFrameMatrix
    {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) :
    Continuous (regularZeroFrameMatrix G z) := by
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
  have hInd : ∀ q, LinearIndependent ℝ (A q) := by
    intro q
    exact PositiveSheetSlabTamedField.linearIndependent_sliceFrameAt_of_regular
      G (τ q) (x q)
      (spacePart_mem_regularSet_of_spatialDeriv_surjective hG (hz q))
  apply continuous_matrix
  intro i j
  have hgs := continuous_gramSchmidtNormed_family' hA hInd i
  exact (EuclideanSpace.proj j).continuous.comp hgs


-- @@ L807-815 verbatim
theorem regularZeroFrameMatrix_mem_SO
    {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) (q : P) :
    regularZeroFrameMatrix G z q ∈ SOGroup (n + 1) := by
  simpa [regularZeroFrameMatrix] using
    PositiveSheetSlabTamedField.sliceFrameMatrix_mem_SO_of_regular
      G (tcoord (z q)) (spacePart (z q))
      (spacePart_mem_regularSet_of_spatialDeriv_surjective hG (hz q))


-- @@ L817-826 verbatim
/-- Canonical `SO(n+1)` slice frame along any continuous spatially regular
ambient family. -/
def regularZeroFrame {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(P, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q))) :
    C(P, SOGroup (n + 1)) where
  toFun q := ⟨regularZeroFrameMatrix G z q,
    regularZeroFrameMatrix_mem_SO hG z hz q⟩
  continuous_toFun :=
    (continuous_regularZeroFrameMatrix hG z hz).subtype_mk _


-- @@ L828-836 verbatim
theorem regularZeroFrame_closed
    {G : E' → F} (hG : ContDiff ℝ ∞ G) (z : C(I, E'))
    (hz : ∀ q, Surjective (spatialDeriv G (z q)))
    (hclosed : z 0 = z 1) :
    regularZeroFrame hG z hz 0 = regularZeroFrame hG z hz 1 := by
  apply Subtype.ext
  change regularZeroFrameMatrix G z 0 = regularZeroFrameMatrix G z 1
  unfold regularZeroFrameMatrix
  rw [hclosed]


-- @@ L838-857 verbatim
/-- A continuous ambient homotopy through spatially regular points canonically
induces a homotopy of the associated slice frames. -/
def regularZeroFrameHomotopy {P : Type*} [TopologicalSpace P]
    {G : E' → F} (hG : ContDiff ℝ ∞ G) {z₀ z₁ : C(P, E')}
    (H : ContinuousMap.Homotopy z₀ z₁)
    (hreg : ∀ q, Surjective (spatialDeriv G (H q))) :
    ContinuousMap.Homotopy
      (regularZeroFrame hG z₀ (fun q => by
        rw [← H.map_zero_left q]
        exact hreg (0, q)))
      (regularZeroFrame hG z₁ (fun q => by
        rw [← H.map_one_left q]
        exact hreg (1, q))) where
  toContinuousMap := regularZeroFrame hG H.toContinuousMap hreg
  map_zero_left q := by
    apply Subtype.ext
    simp [regularZeroFrame, regularZeroFrameMatrix]
  map_one_left q := by
    apply Subtype.ext
    simp [regularZeroFrame, regularZeroFrameMatrix]


-- @@ L859-874 verbatim
/-- Closed ambient tracks induce a closed frame homotopy, exactly the condition
needed by free-homotopy invariance of `loopClassZ2`. -/
theorem regularZeroFrameHomotopy_closed
    {G : E' → F} (hG : ContDiff ℝ ∞ G) {z₀ z₁ : C(I, E')}
    (H : ContinuousMap.Homotopy z₀ z₁)
    (hreg : ∀ q, Surjective (spatialDeriv G (H q)))
    (hclosed : ∀ s : I, H (s, 0) = H (s, 1)) (s : I) :
    regularZeroFrameHomotopy hG H hreg (s, 0) =
      regularZeroFrameHomotopy hG H hreg (s, 1) := by
  apply Subtype.ext
  change regularZeroFrameMatrix G H.toContinuousMap (s, 0) =
    regularZeroFrameMatrix G H.toContinuousMap (s, 1)
  unfold regularZeroFrameMatrix
  have hc := hclosed s
  change H.toContinuousMap (s, 0) = H.toContinuousMap (s, 1) at hc
  rw [hc]


-- @@ L876-899 verbatim
/-- Ambient closed free homotopy through spatially regular points already
implies equality of the resulting stable frame-loop classes. -/
theorem loopClassZ2_regularZeroFrame_congr
    {G : E' → F} (hG : ContDiff ℝ ∞ G) {z₀ z₁ : C(I, E')}
    (H : ContinuousMap.Homotopy z₀ z₁)
    (hreg : ∀ q, Surjective (spatialDeriv G (H q)))
    (hz₀closed : z₀ 0 = z₀ 1) (hz₁closed : z₁ 0 = z₁ 1)
    (hHclosed : ∀ s : I, H (s, 0) = H (s, 1)) :
    let hz₀ : ∀ q, Surjective (spatialDeriv G (z₀ q)) := fun q => by
      rw [← H.map_zero_left q]
      exact hreg (0, q)
    let hz₁ : ∀ q, Surjective (spatialDeriv G (z₁ q)) := fun q => by
      rw [← H.map_one_left q]
      exact hreg (1, q)
    loopClassZ2 (regularZeroFrame hG z₀ hz₀)
        (regularZeroFrame_closed hG z₀ hz₀ hz₀closed) =
      loopClassZ2 (regularZeroFrame hG z₁ hz₁)
        (regularZeroFrame_closed hG z₁ hz₁ hz₁closed) := by
  dsimp only
  exact loopClassZ2_congr
    (regularZeroFrame_closed hG z₀ _ hz₀closed)
    (regularZeroFrame_closed hG z₁ _ hz₁closed)
    (regularZeroFrameHomotopy hG H hreg)
    (regularZeroFrameHomotopy_closed hG H hreg hHclosed)


-- @@ L901-901 verbatim
namespace SpatiallyRegularZeroPath


-- @@ L903-903 verbatim
variable {n : ℕ}

-- @@ L904-904 verbatim
variable {G : EuclideanSpace ℝ (Fin (n + 2)) → EuclideanSpace ℝ (Fin n)}

-- @@ L905-905 verbatim
variable {x y : EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L907-910 verbatim
/-- The canonical moving slice frame along a regular-zero path. -/
def frame (γ : SpatiallyRegularZeroPath G x y)
    (hG : ContDiff ℝ ∞ G) : C(I, SOGroup (n + 1)) :=
  regularZeroFrame hG γ.toPath.toContinuousMap γ.regular


-- @@ L912-918 verbatim
/-- The preceding continuous frame, with its endpoints recorded as a path in
the special orthogonal group. -/
def framePath (γ : SpatiallyRegularZeroPath G x y)
    (hG : ContDiff ℝ ∞ G) : Path (γ.frame hG 0) (γ.frame hG 1) where
  toContinuousMap := γ.frame hG
  source' := rfl
  target' := rfl


-- @@ L920-920 verbatim
end SpatiallyRegularZeroPath


-- @@ L922-922 verbatim
/-! ## Regular exterior cylinders across an isolated event -/


-- @@ L924-933 verbatim
/-- A globally integrable time field tamed only near a prescribed compact
regular core.  The inherited empty-slab field exposes the existing global
flow API without claiming regularity of the whole event slab. -/
structure CompactTimeTamedField (C : LevelCobordismData n) (K : Set E') where
  base : SlabTamedField C 1 0
  delta : ℝ
  delta_pos : 0 < delta
  eq_time : ∀ x ∈ Metric.cthickening delta K,
    base.w x = timeField C.G x
  subset_regular : Metric.cthickening delta K ⊆ slabRegularSet C.G


-- @@ L935-1069 verbatim
/-- Any compact subset of the slab-regular locus admits a bounded, globally
Lipschitz time field which agrees with the canonical time field on a uniform
collar of that subset. -/
theorem exists_compactTimeTamedField (C : LevelCobordismData n)
    {K : Set E'} (hK : IsCompact K)
    (hKreg : K ⊆ slabRegularSet C.G) :
    Nonempty (CompactTimeTamedField C K) := by
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    hK.exists_cthickening_subset_open
      (isOpen_slabRegularSet C.smooth) hKreg
  set δ := δ₂ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have h2δ : 2 * δ = δ₂ := by rw [hδdef]; ring
  have hsub : Metric.cthickening (2 * δ) K ⊆ slabRegularSet C.G := by
    rw [h2δ]
    exact hδ₂sub
  have hs : IsClosed (Metric.thickening (2 * δ) K)ᶜ :=
    Metric.isOpen_thickening.isClosed_compl
  have ht : IsClosed (Metric.cthickening δ K) :=
    Metric.isClosed_cthickening
  have hd : Disjoint (Metric.thickening (2 * δ) K)ᶜ
      (Metric.cthickening δ K) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.cthickening_subset_thickening'
      (by positivity) (by linarith) _ hx')
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin (n + 2))))
      (n := (⊤ : ℕ∞)) hs ht hd
  have hχ : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  have hsmooth : ContDiff ℝ ∞ fun x => f x • timeField C.G x := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ slabRegularSet C.G
    · exact hχ.contDiffAt.smul (contDiffAt_timeField C.smooth hx)
    · have hxC : x ∈ (Metric.cthickening (2 * δ) K)ᶜ :=
        fun hmem => hx (hsub hmem)
      have hU : IsOpen (Metric.cthickening (2 * δ) K)ᶜ :=
        Metric.isClosed_cthickening.isOpen_compl
      have hzero : ∀ y ∈ (Metric.cthickening (2 * δ) K)ᶜ,
          f y • timeField C.G y = 0 := by
        intro y hy
        have hy' : y ∈ (Metric.thickening (2 * δ) K)ᶜ :=
          fun hmem => hy (Metric.thickening_subset_cthickening _ _ hmem)
        have hfy : f y = 0 := hf0 hy'
        rw [hfy, zero_smul]
      have hev : (fun y => f y • timeField C.G y) =ᶠ[nhds x]
          (fun _ => (0 : E')) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hxC) hzero
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq hev
  have hsupp : HasCompactSupport fun x => f x • timeField C.G x := by
    have h1 : support (fun x => f x • timeField C.G x) ⊆
        Metric.thickening (2 * δ) K := by
      intro x hx
      by_contra hmem
      have hfx : f x = 0 := hf0 hmem
      apply hx
      show f x • timeField C.G x = 0
      rw [hfx, zero_smul]
    have h2 : tsupport (fun x => f x • timeField C.G x) ⊆
        Metric.cthickening (2 * δ) K :=
      closure_minimal
        (h1.trans (Metric.thickening_subset_cthickening _ _))
        Metric.isClosed_cthickening
    exact IsCompact.of_isClosed_subset (hK.cthickening)
      isClosed_closure h2
  have hcont : ContinuousOn (timeField C.G)
      (Metric.cthickening (2 * δ) K) := fun x hx =>
    (contDiffAt_timeField C.smooth (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn hcont
  let w : E' → E' := fun x => f x • timeField C.G x
  have hnorm : ∀ x, ‖w x‖ ≤ (Real.toNNReal M : ℝ) := by
    intro x
    by_cases hx : x ∈ Metric.cthickening (2 * δ) K
    · have h1 : ‖f x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hf01 x).1], (hf01 x).2⟩
      calc
        ‖w x‖ = ‖f x‖ * ‖timeField C.G x‖ := norm_smul _ _
        _ ≤ 1 * M := by
          apply mul_le_mul h1 (hM x hx) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
        _ ≤ Real.toNNReal M := Real.le_coe_toNNReal M
    · have hy' : x ∈ (Metric.thickening (2 * δ) K)ᶜ :=
        fun hmem => hx (Metric.thickening_subset_cthickening _ _ hmem)
      have hfx : f x = 0 := hf0 hy'
      rw [show w x = 0 by simp [w, hfx], norm_zero]
      exact (Real.toNNReal M).coe_nonneg
  have heq : ∀ x ∈ Metric.cthickening δ K,
      w x = timeField C.G x := by
    intro x hx
    have hfx : f x = 1 := hf1 hx
    simp [w, hfx]
  have hfderiv : ∀ x, fderiv ℝ C.G x (w x) = 0 := by
    intro x
    by_cases hx : x ∈ Metric.cthickening (2 * δ) K
    · have hxr : x ∈ slabRegularSet C.G := hsub hx
      rw [show w x = f x • timeField C.G x by rfl,
        map_smul, fderiv_timeField hxr.1, smul_zero]
    · have hy' : x ∈ (Metric.thickening (2 * δ) K)ᶜ :=
        fun hmem => hx (Metric.thickening_subset_cthickening _ _ hmem)
      have hfx : f x = 0 := hf0 hy'
      rw [show w x = 0 by simp [w, hfx], map_zero]
  have hlip : ∃ L : NNReal, LipschitzWith L w :=
    hsmooth.lipschitzWith_of_hasCompactSupport hsupp (by simp)
  let W : SlabTamedField C 1 0 := {
    w := w
    delta := δ
    delta_pos := hδpos
    smooth := hsmooth
    bound := Real.toNNReal M
    norm_le := hnorm
    eq_time := by
      intro x hx
      exfalso
      simpa [slabFiber] using hx
    subset_slabRegular := by
      intro x hx
      exfalso
      simpa [slabFiber] using hx
    fderiv_zero := hfderiv
    lipschitz := hlip
  }
  exact ⟨{
    base := W
    delta := δ
    delta_pos := hδpos
    eq_time := heq
    subset_regular := fun x hx =>
      hsub (Metric.cthickening_mono (by linarith) K hx)
  }⟩


-- @@ L1071-1075 verbatim
/-- The compact part of a critical slice outside a closed metric ball around
the isolated critical point. -/
def criticalSliceExteriorCore (C : LevelCobordismData n)
    (center : E') (t r : ℝ) : Set E' :=
  slabFiber C t t ∩ {v | r ≤ dist v center}


-- @@ L1077-1082 verbatim
@[simp] theorem mem_criticalSliceExteriorCore
    (C : LevelCobordismData n) (center v : E') (t r : ℝ) :
    v ∈ criticalSliceExteriorCore C center t r ↔
      C.G v = 0 ∧ tcoord v = t ∧ r ≤ dist v center := by
  simp [criticalSliceExteriorCore, slabFiber,
    LevelCobordismData.fiber, and_assoc]


-- @@ L1084-1088 verbatim
theorem isCompact_criticalSliceExteriorCore
    (C : LevelCobordismData n) (center : E') (t r : ℝ) :
    IsCompact (criticalSliceExteriorCore C center t r) := by
  apply (isCompact_slabFiber C t t).inter_right
  exact isClosed_le continuous_const (continuous_id.dist continuous_const)


-- @@ L1090-1106 verbatim
/-- If `center` is the only time-critical point on its critical slice, the
whole compact exterior of any positive-radius ball is slab-regular. -/
theorem criticalSliceExteriorCore_subset_slabRegularSet
    (C : LevelCobordismData n) (center : E') (t r : ℝ)
    (hr : 0 < r)
    (hisol : ∀ v, v ∈ timeCritical C.G → tcoord v = t → v = center) :
    criticalSliceExteriorCore C center t r ⊆ slabRegularSet C.G := by
  intro v hv
  rw [mem_criticalSliceExteriorCore] at hv
  have hspatial : Surjective (spatialDeriv C.G v) := by
    by_contra hnot
    have hcritical : v ∈ timeCritical C.G := ⟨hv.1, hnot⟩
    have hvc : v = center := hisol v hcritical hv.2.1
    rw [hvc, dist_self] at hv
    linarith
  exact mem_slabRegularSet_of_spatial_surjective
    (C.regular v hv.1) hspatial


-- @@ L1108-1117 verbatim
/-- An isolated critical slice has a canonical compact-exterior time field. -/
theorem exists_criticalSliceExteriorTimeField
    (C : LevelCobordismData n) (center : E') (t r : ℝ)
    (hr : 0 < r)
    (hisol : ∀ v, v ∈ timeCritical C.G → tcoord v = t → v = center) :
    Nonempty (CompactTimeTamedField C
      (criticalSliceExteriorCore C center t r)) :=
  exists_compactTimeTamedField C
    (isCompact_criticalSliceExteriorCore C center t r)
    (criticalSliceExteriorCore_subset_slabRegularSet C center t r hr hisol)


-- @@ L1119-1119 verbatim
namespace CompactTimeTamedField


-- @@ L1121-1121 verbatim
variable {n : ℕ}

-- @@ L1122-1122 verbatim
variable {C : LevelCobordismData n}

-- @@ L1123-1123 verbatim
variable {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}


-- @@ L1125-1128 verbatim
/-- A uniform time radius on which the bounded flow cannot leave the regular
core collar. -/
def safeTime (R : CompactTimeTamedField C K) : ℝ :=
  R.delta / (2 * ((R.base.bound : ℝ) + 1))


-- @@ L1130-1134 verbatim
theorem safeTime_pos (R : CompactTimeTamedField C K) :
    0 < R.safeTime := by
  unfold safeTime
  exact div_pos R.delta_pos
    (mul_pos (by norm_num) (by positivity))


-- @@ L1136-1164 verbatim
/-- Every sufficiently short flow line starting on the core remains inside
the collar where the field is the canonical unit-time field. -/
theorem flow_mem_coreCollar (R : CompactTimeTamedField C K)
    {p : EuclideanSpace ℝ (Fin (n + 2))} (hp : p ∈ K) {s : ℝ}
    (hs : |s| < 2 * R.safeTime) :
    R.base.flow p s ∈ Metric.cthickening R.delta K := by
  apply Metric.mem_cthickening_of_dist_le (R.base.flow p s) p R.delta K hp
  have hbound : 0 ≤ (R.base.bound : ℝ) := R.base.bound.coe_nonneg
  have hden : 0 < (R.base.bound : ℝ) + 1 := by linarith
  have hq : 0 < R.delta / ((R.base.bound : ℝ) + 1) :=
    div_pos R.delta_pos hden
  have heq : R.delta / ((R.base.bound : ℝ) + 1) *
      ((R.base.bound : ℝ) + 1) = R.delta :=
    div_mul_cancel₀ R.delta (ne_of_gt hden)
  have hmul : (R.base.bound : ℝ) *
      (R.delta / ((R.base.bound : ℝ) + 1)) < R.delta := by
    nlinarith
  have htwo : 2 * R.safeTime =
      R.delta / ((R.base.bound : ℝ) + 1) := by
    unfold safeTime
    field_simp
  calc
    dist (R.base.flow p s) p =
        dist (R.base.flow p s) (R.base.flow p 0) := by simp
    _ ≤ (R.base.bound : ℝ) * |s| := by
      simpa using R.base.dist_flow_self_le p s 0
    _ ≤ (R.base.bound : ℝ) * (2 * R.safeTime) :=
      mul_le_mul_of_nonneg_left (le_of_lt hs) hbound
    _ ≤ R.delta := le_of_lt (by rw [htwo]; exact hmul)


-- @@ L1166-1170 verbatim
theorem flow_mem_fiber (R : CompactTimeTamedField C K)
    {p : EuclideanSpace ℝ (Fin (n + 2))}
    (hp : p ∈ C.fiber) (s : ℝ) :
    R.base.flow p s ∈ C.fiber :=
  R.base.flow_mem_fiber hp s


-- @@ L1172-1180 verbatim
theorem flow_spatialDeriv_surjective
    (R : CompactTimeTamedField C K)
    {p : EuclideanSpace ℝ (Fin (n + 2))} (hp : p ∈ K)
    {s : ℝ} (hs : |s| < 2 * R.safeTime) :
    Surjective (spatialDeriv C.G (R.base.flow p s)) := by
  have hcollar := R.flow_mem_coreCollar hp hs
  have hreg := R.subset_regular hcollar
  by_contra hnot
  exact hreg.2 ((kerProj_timeVec_eq_zero_iff hreg.1).2 hnot)


-- @@ L1182-1224 verbatim
/-- On the safe interval, the compact-core flow changes ambient time at unit
speed even though the full event slab contains a critical point. -/
theorem tcoord_flow (R : CompactTimeTamedField C K)
    {p : EuclideanSpace ℝ (Fin (n + 2))} (hp : p ∈ K) {s : ℝ}
    (hs : |s| ≤ R.safeTime) :
    tcoord (R.base.flow p s) = tcoord p + s := by
  let T := R.safeTime
  let S : Set ℝ := Ioo (-(2 * T)) (2 * T)
  let f : ℝ → ℝ := fun u => tcoord (R.base.flow p u)
  let g : ℝ → ℝ := fun u => tcoord p + u
  have hT : 0 < T := R.safeTime_pos
  have hderiv : ∀ u ∈ S, HasDerivAt f 1 u := by
    intro u hu
    have huabs : |u| < 2 * R.safeTime := by
      exact abs_lt.mpr ⟨by simpa [S, T] using hu.1,
        by simpa [S, T] using hu.2⟩
    have hflow := R.base.hasDerivAt_flow p u
    have hproj :=
      (EuclideanSpace.proj (Fin.last (n + 1)) (𝕜 := ℝ)).hasFDerivAt.comp
        u hflow.hasFDerivAt
    have ht : HasDerivAt f (tcoord (R.base.w (R.base.flow p u))) u := by
      simpa [f, tcoord, Function.comp_def] using hproj.hasDerivAt
    have hcollar := R.flow_mem_coreCollar hp huabs
    have hspeed : tcoord (R.base.w (R.base.flow p u)) = 1 := by
      rw [R.eq_time _ hcollar]
      exact tcoord_timeField (R.subset_regular hcollar)
    rwa [hspeed] at ht
  have hfg : Set.EqOn f g S := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
    · intro u hu
      exact (hderiv u hu).differentiableAt.differentiableWithinAt
    · exact ((differentiable_const (tcoord p)).add
        differentiable_id).differentiableOn
    · intro u hu
      rw [(hderiv u hu).deriv]
      simpa [g] using ((hasDerivAt_id u).const_add (tcoord p)).deriv
    · change -(2 * T) < 0 ∧ 0 < 2 * T
      constructor <;> linarith
    · simp [f, g]
  apply hfg
  change -(2 * T) < s ∧ s < 2 * T
  have habs : -T ≤ s ∧ s ≤ T := abs_le.mp hs
  constructor <;> linarith


-- @@ L1226-1235 verbatim
/-- Every fixed-time map of the global flow is injective, with inverse given
by the opposite flow time. -/
theorem flow_apply_injective
    (R : CompactTimeTamedField C K) (s : ℝ) :
    Function.Injective (fun p => R.base.flow p s) := by
  intro p q hpq
  have hback := congrArg (fun x => R.base.flow x (-s)) hpq
  rw [congrFun (R.base.flow_shift p s) (-s),
    congrFun (R.base.flow_shift q s) (-s)] at hback
  simpa using hback


-- @@ L1237-1244 verbatim
/-- Flow a compact-core family for a continuously varying signed time. -/
def flowFamily {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (a : C(P, ℝ)) : C(P, EuclideanSpace ℝ (Fin (n + 2))) where
  toFun q := R.base.flow (z q) (a q)
  continuous_toFun := R.base.continuous_flow_uncurry.comp
    (z.continuous.prodMk a.continuous)


-- @@ L1246-1256 verbatim
/-- The regular two-dimensional cylinder swept out by a compact-core family
between flow times `-ε` and `+ε`. -/
def cylinder {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (ε : ℝ) : C(I × P, EuclideanSpace ℝ (Fin (n + 2))) where
  toFun q := R.base.flow (z q.2) ((2 * (q.1 : ℝ) - 1) * ε)
  continuous_toFun := R.base.continuous_flow_uncurry.comp
    ((z.continuous.comp continuous_snd).prodMk
      (((continuous_subtype_val.comp continuous_fst).const_mul 2 |>.sub
        continuous_const).mul continuous_const))


-- @@ L1258-1263 verbatim
/-- One flow-time slice of a compact-core family. -/
def flowSlice {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (a : ℝ) : C(P, EuclideanSpace ℝ (Fin (n + 2))) :=
  R.flowFamily z (ContinuousMap.const P a)


-- @@ L1265-1270 verbatim
@[simp] theorem cylinder_zero {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (ε : ℝ) (q : P) :
    R.cylinder z ε (0, q) = R.flowSlice z (-ε) q := by
  simp [cylinder, flowSlice, flowFamily]


-- @@ L1272-1280 verbatim
@[simp] theorem cylinder_one {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (ε : ℝ) (q : P) :
    R.cylinder z ε (1, q) = R.flowSlice z ε q := by
  change R.base.flow (z q) ((2 * (1 : ℝ) - 1) * ε) =
    R.base.flow (z q) ε
  congr 2
  norm_num


-- @@ L1282-1291 verbatim
/-- The constructed cylinder, packaged as an actual homotopy between its two
flowed boundary families. -/
def cylinderHomotopy {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (ε : ℝ) : ContinuousMap.Homotopy
      (R.flowSlice z (-ε)) (R.flowSlice z ε) where
  toContinuousMap := R.cylinder z ε
  map_zero_left := R.cylinder_zero z ε
  map_one_left := R.cylinder_one z ε


-- @@ L1293-1298 verbatim
theorem cylinder_fiber {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (hzfiber : ∀ q, z q ∈ C.fiber) (ε : ℝ) (q : I × P) :
    C.G (R.cylinder z ε q) = 0 := by
  exact R.flow_mem_fiber (hzfiber q.2) _


-- @@ L1300-1318 verbatim
theorem cylinder_regular {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (hzK : ∀ q, z q ∈ K) {ε : ℝ}
    (hε : |ε| ≤ R.safeTime) (q : I × P) :
    Surjective (spatialDeriv C.G (R.cylinder z ε q)) := by
  apply R.flow_spatialDeriv_surjective (hzK q.2)
  have hq₀ : 0 ≤ (q.1 : ℝ) := q.1.property.1
  have hq₁ : (q.1 : ℝ) ≤ 1 := q.1.property.2
  have hcoef : |2 * (q.1 : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul]
  calc
    |2 * (q.1 : ℝ) - 1| * |ε| ≤ 1 * R.safeTime :=
      mul_le_mul hcoef hε (abs_nonneg _) zero_le_one
    _ < 2 * R.safeTime := by
      rw [one_mul]
      linarith [R.safeTime_pos]


-- @@ L1320-1339 verbatim
/-- Ambient time along the exterior cylinder is the critical-slice time plus
the signed flow parameter. -/
theorem cylinder_time {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (hzK : ∀ q, z q ∈ K) {ε : ℝ}
    (hε : |ε| ≤ R.safeTime) (q : I × P) :
    tcoord (R.cylinder z ε q) =
      tcoord (z q.2) + (2 * (q.1 : ℝ) - 1) * ε := by
  apply R.tcoord_flow (hzK q.2)
  rw [abs_mul]
  have hq₀ : 0 ≤ (q.1 : ℝ) := q.1.property.1
  have hq₁ : (q.1 : ℝ) ≤ 1 := q.1.property.2
  have hcoef : |2 * (q.1 : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |2 * (q.1 : ℝ) - 1| * |ε| ≤ 1 * R.safeTime :=
      mul_le_mul hcoef hε (abs_nonneg _) zero_le_one
    _ = R.safeTime := one_mul _


-- @@ L1341-1347 verbatim
theorem flowSlice_time {P : Type*} [TopologicalSpace P]
    (R : CompactTimeTamedField C K)
    (z : C(P, EuclideanSpace ℝ (Fin (n + 2))))
    (hzK : ∀ q, z q ∈ K) {a : ℝ}
    (ha : |a| ≤ R.safeTime) (q : P) :
    tcoord (R.flowSlice z a q) = tcoord (z q) + a := by
  exact R.tcoord_flow (hzK q) ha


-- @@ L1349-1362 verbatim
/-- A fixed-time flow image of an ambient path, with its flowed endpoints
recorded definitionally. -/
def flowSlicePath
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : Path x y) (a : ℝ) :
    Path (R.base.flow x a) (R.base.flow y a) where
  toContinuousMap := R.flowSlice γ.toContinuousMap a
  source' := by
    change R.base.flow (γ 0) a = R.base.flow x a
    rw [γ.source]
  target' := by
    change R.base.flow (γ 1) a = R.base.flow y a
    rw [γ.target]


-- @@ L1364-1373 verbatim
/-- A fixed-time flow preserves embeddedness of an arc. -/
theorem flowSlicePath_injective
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : Path x y) (hγ : Function.Injective γ) (a : ℝ) :
    Function.Injective (R.flowSlicePath γ a) := by
  intro q₁ q₂ hq
  apply hγ
  apply R.flow_apply_injective a
  exact hq


-- @@ L1375-1388 verbatim
/-- A path in one core slice flows into the slice translated by the signed
flow time. -/
theorem flowSlicePath_time
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : Path x y) (hγK : ∀ q, γ q ∈ K)
    {t a : ℝ} (hγt : ∀ q, tcoord (γ q) = t)
    (ha : |a| ≤ R.safeTime) (q : I) :
    tcoord (R.flowSlicePath γ a q) = t + a := by
  change tcoord (R.flowSlice γ.toContinuousMap a q) = t + a
  rw [R.flowSlice_time γ.toContinuousMap hγK ha q]
  have ht : tcoord (γ.toContinuousMap q) = t := by
    simpa using hγt q
  rw [ht]


-- @@ L1390-1407 verbatim
/-- Flowing a regular-zero path in the compact core for a safe time again
gives a regular-zero path. -/
def flowSliceRegularZeroPath
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : SpatiallyRegularZeroPath C.G x y)
    (hγK : ∀ q, γ.toPath q ∈ K) {a : ℝ}
    (ha : |a| ≤ R.safeTime) :
    SpatiallyRegularZeroPath C.G
      (R.base.flow x a) (R.base.flow y a) where
  toPath := R.flowSlicePath γ.toPath a
  range_subset := by
    rintro z ⟨q, rfl⟩
    change C.G (R.base.flow (γ.toPath q) a) = 0 ∧
      Surjective (spatialDeriv C.G (R.base.flow (γ.toPath q) a))
    refine ⟨R.flow_mem_fiber (γ.fiber q) a,
      R.flow_spatialDeriv_surjective (hγK q) ?_⟩
    exact ha.trans_lt (by linarith [R.safeTime_pos])


-- @@ L1409-1417 verbatim
/-- Spatial projection of a fixed flow-time image of an ambient path. -/
def flowSliceSpatialPath
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : Path x y) (a : ℝ) :
    C(I, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun q := spacePart (R.flowSlicePath γ a q)
  continuous_toFun := continuous_spacePart.comp
    (R.flowSlicePath γ a).continuous


-- @@ L1419-1435 verbatim
/-- If the original path lies in one zero-fiber time slice, its safe fixed
flow-time image lies in the translated regular slice. -/
theorem flowSliceSpatialPath_mem_fiber
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : Path x y) (hγK : ∀ q, γ q ∈ K)
    {t a : ℝ} (hγt : ∀ q, tcoord (γ q) = t)
    (hγfiber : ∀ q, C.G (γ q) = 0)
    (ha : |a| ≤ R.safeTime)
    (hreg : sliceRegular C.G (t + a)) (q : I) :
    R.flowSliceSpatialPath γ a q ∈
      (SlabTamedField.sliceFLSAt C (t + a) hreg).fiber := by
  rw [SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (R.flowSlicePath γ a q)) (t + a)) = 0
  rw [← R.flowSlicePath_time γ hγK hγt ha q, spaceTime_spacePart]
  exact R.flow_mem_fiber (hγfiber q) a


-- @@ L1437-1456 verbatim
/-- The two endpoints of a critical-slice path flow into one actual orbit
component of every regular translated slice. -/
theorem flowSlicePath_endpoints_mem_same_orbit
    (R : CompactTimeTamedField C K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (γ : Path x y) (hγK : ∀ q, γ q ∈ K)
    {t a : ℝ} (hγt : ∀ q, tcoord (γ q) = t)
    (hγfiber : ∀ q, C.G (γ q) = 0)
    (ha : |a| ≤ R.safeTime)
    (hreg : sliceRegular C.G (t + a))
    (V : TamedField (SlabTamedField.sliceFLSAt C (t + a) hreg)) :
    spacePart (R.base.flow y a) ∈
      V.orbit (spacePart (R.base.flow x a)) := by
  let δ := R.flowSliceSpatialPath γ a
  have hδfiber : ∀ q, δ q ∈
      (SlabTamedField.sliceFLSAt C (t + a) hreg).fiber := by
    intro q
    exact R.flowSliceSpatialPath_mem_fiber γ hγK hγt hγfiber ha hreg q
  have h := V.continuousMap_mem_orbit δ hδfiber 1
  simpa [δ, flowSliceSpatialPath] using h


-- @@ L1458-1476 verbatim
/-- The negative half of the flow track from time `-ε` back to its critical
slice base point. -/
def negativeFlowTrack
    (R : CompactTimeTamedField C K)
    (p : EuclideanSpace ℝ (Fin (n + 2))) (ε : ℝ) :
    Path (R.base.flow p (-ε)) p where
  toContinuousMap := R.flowFamily (ContinuousMap.const _ p) {
    toFun := fun u : I => ((u : ℝ) - 1) * ε
    continuous_toFun :=
      ((continuous_subtype_val.sub continuous_const).mul continuous_const)
  }
  source' := by
    change R.base.flow p ((((0 : I) : ℝ) - 1) * ε) =
      R.base.flow p (-ε)
    congr 2
    norm_num
  target' := by
    change R.base.flow p ((((1 : I) : ℝ) - 1) * ε) = p
    simp


-- @@ L1478-1494 verbatim
/-- The positive half of the flow track from a critical-slice base point to
time `+ε`. -/
def positiveFlowTrack
    (R : CompactTimeTamedField C K)
    (p : EuclideanSpace ℝ (Fin (n + 2))) (ε : ℝ) :
    Path p (R.base.flow p ε) where
  toContinuousMap := R.flowFamily (ContinuousMap.const _ p) {
    toFun := fun u : I => (u : ℝ) * ε
    continuous_toFun := continuous_subtype_val.mul continuous_const
  }
  source' := by
    change R.base.flow p (((0 : I) : ℝ) * ε) = p
    simp
  target' := by
    change R.base.flow p (((1 : I) : ℝ) * ε) = R.base.flow p ε
    congr 2
    norm_num


-- @@ L1496-1523 verbatim
/-- The negative half-track stays in the regular zero-surface whenever its
base point lies in the compact core. -/
def negativeFlowTrackRegularZeroPath
    (R : CompactTimeTamedField C K)
    {p : EuclideanSpace ℝ (Fin (n + 2))}
    (hpK : p ∈ K) (hpfiber : p ∈ C.fiber) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ R.safeTime) :
    SpatiallyRegularZeroPath C.G (R.base.flow p (-ε)) p where
  toPath := R.negativeFlowTrack p ε
  range_subset := by
    rintro z ⟨q, rfl⟩
    change C.G (R.base.flow p ((((q : I) : ℝ) - 1) * ε)) = 0 ∧
      Surjective (spatialDeriv C.G
        (R.base.flow p ((((q : I) : ℝ) - 1) * ε)))
    refine ⟨R.flow_mem_fiber hpfiber _,
      R.flow_spatialDeriv_surjective hpK ?_⟩
    have hq0 : 0 ≤ (q : ℝ) := q.property.1
    have hq1 : (q : ℝ) ≤ 1 := q.property.2
    rw [abs_mul, abs_of_nonpos (by linarith : (q : ℝ) - 1 ≤ 0),
      abs_of_nonneg hε0]
    have hcoef : 1 - (q : ℝ) ≤ 1 := by linarith
    calc
      -((q : ℝ) - 1) * ε = (1 - (q : ℝ)) * ε := by ring
      _ ≤ 1 * R.safeTime :=
        mul_le_mul hcoef hε hε0 (by norm_num)
      _ < 2 * R.safeTime := by
        rw [one_mul]
        linarith [R.safeTime_pos]


-- @@ L1525-1548 verbatim
/-- The positive half-track stays in the regular zero-surface whenever its
base point lies in the compact core. -/
def positiveFlowTrackRegularZeroPath
    (R : CompactTimeTamedField C K)
    {p : EuclideanSpace ℝ (Fin (n + 2))}
    (hpK : p ∈ K) (hpfiber : p ∈ C.fiber) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ R.safeTime) :
    SpatiallyRegularZeroPath C.G p (R.base.flow p ε) where
  toPath := R.positiveFlowTrack p ε
  range_subset := by
    rintro z ⟨q, rfl⟩
    change C.G (R.base.flow p ((q : ℝ) * ε)) = 0 ∧
      Surjective (spatialDeriv C.G (R.base.flow p ((q : ℝ) * ε)))
    refine ⟨R.flow_mem_fiber hpfiber _,
      R.flow_spatialDeriv_surjective hpK ?_⟩
    have hq0 : 0 ≤ (q : ℝ) := q.property.1
    have hq1 : (q : ℝ) ≤ 1 := q.property.2
    rw [abs_mul, abs_of_nonneg hq0, abs_of_nonneg hε0]
    calc
      (q : ℝ) * ε ≤ 1 * R.safeTime :=
        mul_le_mul hq1 hε hε0 (by norm_num)
      _ < 2 * R.safeTime := by
        rw [one_mul]
        linarith [R.safeTime_pos]


-- @@ L1550-1557 verbatim
theorem cylinder_closed
    (R : CompactTimeTamedField C K)
    (z : C(I, EuclideanSpace ℝ (Fin (n + 2))))
    (hzclosed : z 0 = z 1) (ε : ℝ) (s : I) :
    R.cylinder z ε (s, 0) = R.cylinder z ε (s, 1) := by
  change R.base.flow (z 0) ((2 * (s : ℝ) - 1) * ε) =
    R.base.flow (z 1) ((2 * (s : ℝ) - 1) * ε)
  rw [hzclosed]


-- @@ L1559-1597 verbatim
/-- The cylinder is a closed free homotopy through the spatially regular zero
surface, hence its two boundary frame loops have the same stable class. -/
theorem loopClassZ2_flowSlice_congr
    (R : CompactTimeTamedField C K)
    (z : C(I, EuclideanSpace ℝ (Fin (n + 2))))
    (hzK : ∀ q, z q ∈ K)
    (hzfiber : ∀ q, z q ∈ C.fiber)
    (hzclosed : z 0 = z 1) {ε : ℝ}
    (hε : |ε| ≤ R.safeTime) :
    let zneg := R.flowSlice z (-ε)
    let zpos := R.flowSlice z ε
    let hneg : ∀ q, Surjective (spatialDeriv C.G (zneg q)) := fun q => by
      rw [← R.cylinder_zero z ε q]
      exact R.cylinder_regular z hzK hε (0, q)
    let hpos : ∀ q, Surjective (spatialDeriv C.G (zpos q)) := fun q => by
      rw [← R.cylinder_one z ε q]
      exact R.cylinder_regular z hzK hε (1, q)
    loopClassZ2 (regularZeroFrame C.smooth zneg hneg)
        (regularZeroFrame_closed C.smooth zneg hneg (by
          change R.base.flow (z 0) (-ε) = R.base.flow (z 1) (-ε)
          rw [hzclosed])) =
      loopClassZ2 (regularZeroFrame C.smooth zpos hpos)
        (regularZeroFrame_closed C.smooth zpos hpos (by
          change R.base.flow (z 0) ε = R.base.flow (z 1) ε
          rw [hzclosed])) := by
  dsimp only
  have hzeroRegular : ∀ q,
      C.G (R.cylinder z ε q) = 0 ∧
        Surjective (spatialDeriv C.G (R.cylinder z ε q)) := fun q =>
    ⟨R.cylinder_fiber z hzfiber ε q,
      R.cylinder_regular z hzK hε q⟩
  apply loopClassZ2_regularZeroFrame_congr C.smooth
    (R.cylinderHomotopy z ε)
  · exact fun q => (hzeroRegular q).2
  · change R.base.flow (z 0) (-ε) = R.base.flow (z 1) (-ε)
    rw [hzclosed]
  · change R.base.flow (z 0) ε = R.base.flow (z 1) ε
    rw [hzclosed]
  · exact R.cylinder_closed z hzclosed ε


-- @@ L1599-1599 verbatim
end CompactTimeTamedField


-- @@ L1601-1601 verbatim
namespace MorsePosition


-- @@ L1603-1603 verbatim
variable {n : ℕ}

-- @@ L1604-1604 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L1606-1631 verbatim
/-- Every scheduled event has a compact-exterior time field on its critical
slice, with no regularity assumption across the critical point itself. -/
theorem exists_eventCriticalSliceExteriorTimeField
    (P : MorsePosition C) (t : ℝ)
    (ht : t ∈ P.eventTimes) (r : ℝ) (hr : 0 < r) :
    Nonempty (CompactTimeTamedField C.toLevelCobordismData
      (criticalSliceExteriorCore C.toLevelCobordismData
        (P.eventCenter t ht) t r)) := by
  apply exists_criticalSliceExteriorTimeField
    C.toLevelCobordismData (P.eventCenter t ht) t r hr
  intro v hv hvt
  apply (P.eventBracket t ht).isolates v hv
  have htcenter : tcoord (P.eventCenter t ht) = t :=
    P.eventCenter_time t ht
  constructor
  · calc
      (P.eventBracket t ht).before ≤
          tcoord (P.eventCenter t ht) :=
        le_of_lt (P.eventBracket t ht).before_lt
      _ = t := htcenter
      _ = tcoord v := hvt.symm
  · calc
      tcoord v = t := hvt
      _ = tcoord (P.eventCenter t ht) := htcenter.symm
      _ ≤ (P.eventBracket t ht).after :=
        le_of_lt (P.eventBracket t ht).lt_after


-- @@ L1633-1633 verbatim
end MorsePosition


-- @@ L1635-1635 verbatim
namespace TamedField


-- @@ L1637-1654 verbatim
/-- The actual space-time loop traced by a regular slice orbit.  This is the
ambient geometric representative whose canonical regular-zero frame is the
intrinsic `orbitFrameLoop`. -/
def ambientOrbitLoop (C : LevelCobordismData n) (t : ℝ)
    (ht : sliceRegular C.G t)
    (V : TamedField (SlabTamedField.sliceFLSAt C t ht))
    (O : V.OrbitIndex) : C(I, E') where
  toFun u := cobSpaceTime
    (V.flow (V.orbitPoint O)
      ((u : ℝ) * V.orbitPeriod O)) t
  continuous_toFun := by
    have hcob : Continuous (fun x : E₁ => cobSpaceTime x t) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (hasFDerivAt_cobSpaceTime t x).continuousAt
    exact hcob.comp <|
      (V.continuous_flow (V.orbitPoint O)).comp
        (continuous_subtype_val.mul continuous_const)


-- @@ L1656-1663 verbatim
theorem ambientOrbitLoop_fiber (C : LevelCobordismData n) (t : ℝ)
    (ht : sliceRegular C.G t)
    (V : TamedField (SlabTamedField.sliceFLSAt C t ht))
    (O : V.OrbitIndex) (u : I) :
    C.G (V.ambientOrbitLoop C t ht O u) = 0 := by
  change C.G (cobSpaceTime
    (V.flow (V.orbitPoint O) ((u : ℝ) * V.orbitPeriod O)) t) = 0
  exact V.flow_mem_fiber (V.orbitPoint_mem_fiber O) _


-- @@ L1665-1672 verbatim
theorem ambientOrbitLoop_regular (C : LevelCobordismData n) (t : ℝ)
    (ht : sliceRegular C.G t)
    (V : TamedField (SlabTamedField.sliceFLSAt C t ht))
    (O : V.OrbitIndex) (u : I) :
    Surjective (spatialDeriv C.G (V.ambientOrbitLoop C t ht O u)) := by
  apply ht (V.ambientOrbitLoop C t ht O u)
  · exact V.ambientOrbitLoop_fiber C t ht O u
  · simp [ambientOrbitLoop]


-- @@ L1674-1685 verbatim
theorem ambientOrbitLoop_closed (C : LevelCobordismData n) (t : ℝ)
    (ht : sliceRegular C.G t)
    (V : TamedField (SlabTamedField.sliceFLSAt C t ht))
    (O : V.OrbitIndex) :
    V.ambientOrbitLoop C t ht O 0 = V.ambientOrbitLoop C t ht O 1 := by
  change cobSpaceTime
      (V.flow (V.orbitPoint O) ((0 : ℝ) * V.orbitPeriod O)) t =
    cobSpaceTime
      (V.flow (V.orbitPoint O) ((1 : ℝ) * V.orbitPeriod O)) t
  congr 1
  simpa [orbitPeriod] using
    (V.flow_periodic_orbitPeriod O 0).symm


-- @@ L1687-1703 verbatim
/-- The canonical ambient regular-zero frame of an actual orbit is exactly
the orbit's intrinsic frame loop. -/
theorem regularZeroFrame_ambientOrbitLoop (C : LevelCobordismData n) (t : ℝ)
    (ht : sliceRegular C.G t)
    (V : TamedField (SlabTamedField.sliceFLSAt C t ht))
    (O : V.OrbitIndex) :
    regularZeroFrame C.smooth (V.ambientOrbitLoop C t ht O)
        (V.ambientOrbitLoop_regular C t ht O) =
      V.orbitFrameLoop O := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change regularZeroFrameMatrix C.G
      (V.ambientOrbitLoop C t ht O) u = V.orbitFrameLoop O u
  unfold regularZeroFrameMatrix ambientOrbitLoop TamedField.orbitFrameLoop
    TamedField.fundamentalFrameLoop frameLoop SlabTamedField.sliceFrameAt
  simp [frameAt, SlabTamedField.sliceFLSAt, sliceFLS, orbitPeriod]


-- @@ L1705-1726 verbatim
/-- A closed free homotopy of the actual space-time orbit loops inside the
spatially regular zero-surface identifies their intrinsic frame classes. -/
theorem orbitFrameClass_eq_of_ambientRegularZeroHomotopy
    (C : LevelCobordismData n)
    (t₀ t₁ : ℝ) (ht₀ : sliceRegular C.G t₀)
    (ht₁ : sliceRegular C.G t₁)
    (V₀ : TamedField (SlabTamedField.sliceFLSAt C t₀ ht₀))
    (V₁ : TamedField (SlabTamedField.sliceFLSAt C t₁ ht₁))
    (O₀ : V₀.OrbitIndex) (O₁ : V₁.OrbitIndex)
    (H : ContinuousMap.Homotopy
      (V₀.ambientOrbitLoop C t₀ ht₀ O₀)
      (V₁.ambientOrbitLoop C t₁ ht₁ O₁))
    (hzeroRegular : ∀ q, C.G (H q) = 0 ∧
      Surjective (spatialDeriv C.G (H q)))
    (hclosed : ∀ s : I, H (s, 0) = H (s, 1)) :
    V₀.orbitFrameClass O₀ = V₁.orbitFrameClass O₁ := by
  have hclass := loopClassZ2_regularZeroFrame_congr C.smooth H
    (fun q => (hzeroRegular q).2)
    (V₀.ambientOrbitLoop_closed C t₀ ht₀ O₀)
    (V₁.ambientOrbitLoop_closed C t₁ ht₁ O₁) hclosed
  simpa only [TamedField.orbitFrameClass,
    TamedField.regularZeroFrame_ambientOrbitLoop] using hclass


-- @@ L1728-1728 verbatim
end TamedField


-- @@ L1730-1730 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L1732-1734 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L1736-1742 verbatim
/-- The actual local zero-surface parameter after the finite vertical
installation and the chosen Morse shrink. -/
def criticalSurfaceParam (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (u : E₂) : E' :=
  R.amplitude.diffeomorph.symm
    ((B.chart p.1).param
      (p.2 + (G.localMorseNormalForm p hp).param u))


-- @@ L1744-1818 verbatim
/-- The installed critical parameter covers the pulled-back zero fiber near
its center with arbitrarily small Morse-coordinate radius.  This strengthens
the fixed production-radius cover precisely enough to choose the cover inside
an injective chart shrink. -/
theorem covers_fiber_within_criticalSurfaceParam_radius
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ v : E',
      dist v (R.criticalCenter p) < ε →
      (R.amplitude.toVerticalAmplitude.pullback C).G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ R.criticalSurfaceParam p hp u = v := by
  let P := B.chart p.1
  let M := G.localMorseNormalForm p hp
  let x : E' := P.param p.2
  let c : E' := R.amplitude.diffeomorph.symm x
  have hsmooth : ContDiff ℝ ∞ (G.localSeparatedTime p) := by
    change ContDiff ℝ ∞
      (fun u => (G.tilt p.1).tilted u + G.valueShift p)
    rw [(G.tilt p.1).tilted_eq]
    exact (contDiff_chartLinearTilt
      (B.chart p.1).contDiff_time (G.tilt p.1).q).add contDiff_const
  have hf : ContDiffAt ℝ 2
      (recenter (G.localSeparatedTime p) p.2) 0 :=
    contDiffAt_infty.mp (contDiff_recenter hsmooth p.2).contDiffAt 2
  have hcrit : fderiv ℝ (recenter (G.localSeparatedTime p) p.2) 0 = 0 :=
    fderiv_eq_zero_of_chartGradient_eq_zero
      (nondegenerateCriticalAt_recenter hsmooth
        (G.localSeparatedTime_nondegenerate p hp)).1
  obtain ⟨δ, hδ, hM⟩ := M.exists_preimage_norm_lt hf hcrit hr
  have hpcore : p.2 ∈ B.core p.1 :=
    ((G.criticalPoints_spec p).mp hp).2
  have hpdom : p.2 ∈ P.domain := B.core_subset_domain p.1 hpcore
  obtain ⟨ε₀, hε₀, hP⟩ :=
    P.exists_param_of_fiber_near (B.domain_open p.1) hpdom
      (ball_mem_nhds p.2 hδ)
  have hforward : Tendsto (fun v : E' => R.amplitude.diffeomorph v)
      (nhds c) (nhds x) := by
    have hcx : R.amplitude.diffeomorph c = x := by
      dsimp [c]
      exact R.amplitude.diffeomorph.apply_symm_apply x
    rw [← hcx]
    exact R.amplitude.diffeomorph.continuous.continuousAt
  have hnear : (fun v : E' => R.amplitude.diffeomorph v) ⁻¹'
      ball x ε₀ ∈ nhds c :=
    hforward (ball_mem_nhds x hε₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro v hv hzero
  have hvball : v ∈ ball c ε := by
    simpa [mem_ball, c, criticalCenter] using hv
  have hforwardBall : R.amplitude.diffeomorph v ∈ ball x ε₀ :=
    hball hvball
  have hforwardDist :
      dist (R.amplitude.diffeomorph v) (P.param p.2) < ε₀ := by
    simpa [mem_ball, x] using hforwardBall
  have hforwardZero : C.G (R.amplitude.diffeomorph v) = 0 := by
    simpa [VerticalAmplitude.pullback_G,
      SmallVerticalAmplitude.diffeomorph_apply] using hzero
  obtain ⟨z, hzball, _hzdom, hzparam⟩ :=
    hP (R.amplitude.diffeomorph v) hforwardDist hforwardZero
  have hy : ‖z - p.2‖ < δ := by
    simpa [mem_ball, dist_eq_norm] using hzball
  obtain ⟨u, hu, hMu⟩ := hM (z - p.2) hy
  refine ⟨u, hu, ?_⟩
  change R.amplitude.diffeomorph.symm
      (P.param (p.2 + M.param u)) = v
  calc
    R.amplitude.diffeomorph.symm (P.param (p.2 + M.param u)) =
        R.amplitude.diffeomorph.symm (P.param z) := by
          congr 2
          rw [hMu, add_sub_cancel]
    _ = R.amplitude.diffeomorph.symm
        (R.amplitude.diffeomorph v) := by rw [hzparam]
    _ = v := R.amplitude.diffeomorph.symm_apply_apply v


-- @@ L1820-1830 verbatim
/-- On the production ball, ambient time along the actual surface parameter is
the literal Morse quadratic. -/
theorem criticalSurfaceParam_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalSurfaceParam p hp u) =
      G.localSeparatedTime p p.2 +
        morseQuadratic (G.localMorseNormalForm p hp).index (u 0, u 1) := by
  exact R.time_model_of_criticalModelShrink p hp
    (R.criticalModelShrink p hp) u hu


-- @@ L1832-1850 verbatim
/-- The actual parameter remains in the zero fiber of the installed defining
map throughout the production ball. -/
theorem criticalSurfaceParam_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSurfaceParam p hp u) = 0 := by
  rw [VerticalAmplitude.pullback_G]
  change C.G (verticalShift R.amplitude
    (R.amplitude.diffeomorph.symm
      ((B.chart p.1).param
        (p.2 + (G.localMorseNormalForm p hp).param u)))) = 0
  rw [← R.amplitude.diffeomorph_apply,
    R.amplitude.diffeomorph.apply_symm_apply]
  exact (B.chart p.1).param_fiber _
    (LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := G.localMorseNormalForm p hp)
      (R.criticalModelShrink p hp) u hu)


-- @@ L1852-1870 verbatim
/-- Every noncentral point of the installed critical chart is spatially
regular.  This follows from the already-proved uniqueness of the ambient time
critical point, together with the actual zero-fiber equation. -/
theorem criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hu0 : u ≠ 0) :
    Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u)) := by
  have hnot : R.criticalSurfaceParam p hp u ∉
      timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G := by
    intro hcrit
    apply hu0
    apply (R.critical_model p hp u hu).mp
    simpa [criticalSurfaceParam] using hcrit
  by_contra hns
  exact hnot ⟨R.criticalSurfaceParam_fiber p hp u hu, hns⟩


-- @@ L1872-1872 verbatim
/-! ## Explicit actual saddle branches -/


-- @@ L1874-1880 verbatim
/-- The positive-side standard saddle branch transported into the actual
installed critical surface. -/
def criticalSaddlePositiveBranch (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (a s : ℝ) : E' :=
  R.criticalSurfaceParam p hp
    (pairToMorseParam (saddlePositiveArc b a s))


-- @@ L1882-1888 verbatim
/-- The negative-side standard saddle branch transported into the actual
installed critical surface. -/
def criticalSaddleNegativeBranch (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (a s : ℝ) : E' :=
  R.criticalSurfaceParam p hp
    (pairToMorseParam (saddleNegativeArc b a s))


-- @@ L1890-1899 verbatim
/-- Every installed positive saddle branch remains in the actual zero fiber. -/
theorem criticalSaddlePositiveBranch_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (saddlePositiveArc b a s)‖ <
      (R.criticalModelShrink p hp).radius) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBranch p hp b a s) = 0 := by
  exact R.criticalSurfaceParam_fiber p hp _ hu


-- @@ L1901-1910 verbatim
/-- Every installed negative saddle branch remains in the actual zero fiber. -/
theorem criticalSaddleNegativeBranch_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (saddleNegativeArc b a s)‖ <
      (R.criticalModelShrink p hp).radius) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBranch p hp b a s) = 0 := by
  exact R.criticalSurfaceParam_fiber p hp _ hu


-- @@ L1912-1925 verbatim
/-- On the positive side of an installed saddle, the actual ambient time is
the critical time plus `a²`. -/
theorem criticalSaddlePositiveBranch_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (saddlePositiveArc b a s)‖ <
      (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalSaddlePositiveBranch p hp b a s) =
      G.localSeparatedTime p p.2 + a ^ 2 := by
  rw [criticalSaddlePositiveBranch,
    R.criticalSurfaceParam_time p hp _ hu, hindex]
  simp


-- @@ L1927-1941 verbatim
/-- On the negative side of an installed saddle, the actual ambient time is
the critical time minus `a²`. -/
theorem criticalSaddleNegativeBranch_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (a s : ℝ)
    (hu : ‖pairToMorseParam (saddleNegativeArc b a s)‖ <
      (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalSaddleNegativeBranch p hp b a s) =
      G.localSeparatedTime p p.2 - a ^ 2 := by
  rw [criticalSaddleNegativeBranch,
    R.criticalSurfaceParam_time p hp _ hu, hindex]
  simp
  ring


-- @@ L1943-1943 verbatim
/-! ## The four actual ends on an installed Morse-chart boundary -/


-- @@ L1945-1953 verbatim
/-- A positive-side saddle end on the boundary circle of an installed Morse
chart.  The first branch label records the local component and the second its
chosen end. -/
def criticalSaddlePositiveBoundaryEnd
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) : E' :=
  R.criticalSurfaceParam p hp
    (saddlePositiveBoundaryEndParam b e ρ a)


-- @@ L1955-1961 verbatim
/-- A negative-side saddle end on the same installed chart boundary. -/
def criticalSaddleNegativeBoundaryEnd
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) : E' :=
  R.criticalSurfaceParam p hp
    (saddleNegativeBoundaryEndParam b e ρ a)


-- @@ L1963-1977 verbatim
/-- Every positive-side installed boundary end belongs to the actual zero
fiber. -/
theorem criticalSaddlePositiveBoundaryEnd_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a) = 0 := by
  have hu : ‖saddlePositiveBoundaryEndParam b e ρ a‖ <
      (R.criticalModelShrink p hp).radius := by
    rw [norm_saddlePositiveBoundaryEndParam b e hρ ha]
    exact hρrad
  exact R.criticalSurfaceParam_fiber p hp _ hu


-- @@ L1979-1993 verbatim
/-- Every negative-side installed boundary end belongs to the same actual zero
fiber. -/
theorem criticalSaddleNegativeBoundaryEnd_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a) = 0 := by
  have hu : ‖saddleNegativeBoundaryEndParam b e ρ a‖ <
      (R.criticalModelShrink p hp).radius := by
    rw [norm_saddleNegativeBoundaryEndParam b e hρ ha]
    exact hρrad
  exact R.criticalSurfaceParam_fiber p hp _ hu


-- @@ L1995-2015 verbatim
/-- All four positive-side boundary ends lie at the positive regular time
`criticalTime + a²`. -/
theorem criticalSaddlePositiveBoundaryEnd_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a) =
      G.localSeparatedTime p p.2 + a ^ 2 := by
  have hu : ‖pairToMorseParam (saddlePositiveArc b a
      (signedBranch e (saddleBoundaryParameter ρ a)))‖ <
      (R.criticalModelShrink p hp).radius := by
    change ‖saddlePositiveBoundaryEndParam b e ρ a‖ < _
    rw [norm_saddlePositiveBoundaryEndParam b e hρ ha]
    exact hρrad
  simpa [criticalSaddlePositiveBoundaryEnd,
    saddlePositiveBoundaryEndParam, criticalSaddlePositiveBranch] using
    R.criticalSaddlePositiveBranch_time p hp hindex b a
      (signedBranch e (saddleBoundaryParameter ρ a)) hu


-- @@ L2017-2037 verbatim
/-- All four negative-side boundary ends lie at the negative regular time
`criticalTime - a²`. -/
theorem criticalSaddleNegativeBoundaryEnd_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a) =
      G.localSeparatedTime p p.2 - a ^ 2 := by
  have hu : ‖pairToMorseParam (saddleNegativeArc b a
      (signedBranch e (saddleBoundaryParameter ρ a)))‖ <
      (R.criticalModelShrink p hp).radius := by
    change ‖saddleNegativeBoundaryEndParam b e ρ a‖ < _
    rw [norm_saddleNegativeBoundaryEndParam b e hρ ha]
    exact hρrad
  simpa [criticalSaddleNegativeBoundaryEnd,
    saddleNegativeBoundaryEndParam, criticalSaddleNegativeBranch] using
    R.criticalSaddleNegativeBranch_time p hp hindex b a
      (signedBranch e (saddleBoundaryParameter ρ a)) hu


-- @@ L2039-2059 verbatim
/-- Positive-side installed boundary ends are spatially regular. -/
theorem criticalSaddlePositiveBoundaryEnd_spatialDeriv_surjective
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a)) := by
  have hnorm := norm_saddlePositiveBoundaryEndParam b e hρ ha
  have hu : ‖saddlePositiveBoundaryEndParam b e ρ a‖ <
      (R.criticalModelShrink p hp).radius := by
    rw [hnorm]
    exact hρrad
  have hu0 : saddlePositiveBoundaryEndParam b e ρ a ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  exact R.criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero
    p hp _ hu hu0


-- @@ L2061-2081 verbatim
/-- Negative-side installed boundary ends are spatially regular. -/
theorem criticalSaddleNegativeBoundaryEnd_spatialDeriv_surjective
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a)) := by
  have hnorm := norm_saddleNegativeBoundaryEndParam b e hρ ha
  have hu : ‖saddleNegativeBoundaryEndParam b e ρ a‖ <
      (R.criticalModelShrink p hp).radius := by
    rw [hnorm]
    exact hρrad
  have hu0 : saddleNegativeBoundaryEndParam b e ρ a ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  exact R.criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero
    p hp _ hu hu0


-- @@ L2083-2092 verbatim
/-- The exact four-end switch survives transportation into the installed
Morse chart. -/
theorem criticalSaddle_boundary_pairing_switch
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ : ℝ) :
    R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0 =
      R.criticalSaddleNegativeBoundaryEnd p hp e b ρ 0 := by
  exact congrArg (R.criticalSurfaceParam p hp)
    (saddle_boundary_pairing_switch b e ρ)


-- @@ L2094-2112 verbatim
/-- The installed surface parameter is differentiable at every point of its
production ball. -/
theorem criticalSurfaceParam_differentiableAt
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    DifferentiableAt ℝ (R.criticalSurfaceParam p hp) u := by
  have hM : DifferentiableAt ℝ (G.localMorseNormalForm p hp).param u :=
    LocalMorseNormalForm.SimultaneousShrink.param_differentiableAt_of_contDiffOn_one
      (G.localMorseNormalForm p hp) (R.criticalModelShrink p hp)
      (R.criticalModelShrink_contDiffOn p hp) u hu
  have hshift : DifferentiableAt ℝ
      (fun z : E₂ => p.2 + (G.localMorseNormalForm p hp).param z) u :=
    differentiableAt_const (c := p.2).add hM
  have hchart : DifferentiableAt ℝ
      (fun z : E₂ => (B.chart p.1).param
        (p.2 + (G.localMorseNormalForm p hp).param z)) u :=
    ((B.chart p.1).param_smooth.differentiable (by simp) _).comp u hshift
  exact (R.amplitude.contDiff_equiv_symm.differentiable (by simp) _).comp u hchart


-- @@ L2114-2149 verbatim
/-- Injectivity of the Morse-coordinate differential propagates through the
production IFT chart and the inverse vertical diffeomorphism to the actual
installed surface parameter. -/
theorem fderiv_criticalSurfaceParam_injective_of_param
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hM : Injective
      (fderiv ℝ (G.localMorseNormalForm p hp).param u)) :
    Injective (fderiv ℝ (R.criticalSurfaceParam p hp) u) := by
  let M := G.localMorseNormalForm p hp
  let P := B.chart p.1
  let q : E₂ := p.2 + M.param u
  let J : E₂ →L[ℝ] E₂ := fderiv ℝ M.param u
  have hMdiff : DifferentiableAt ℝ M.param u :=
    LocalMorseNormalForm.SimultaneousShrink.param_differentiableAt_of_contDiffOn_one
      M (R.criticalModelShrink p hp)
      (R.criticalModelShrink_contDiffOn p hp) u hu
  have hshift : HasFDerivAt (fun z : E₂ => p.2 + M.param z) J u := by
    simpa [J] using hMdiff.hasFDerivAt.const_add p.2
  have hqdom : q ∈ P.domain := by
    exact LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := M) (R.criticalModelShrink p hp) u hu
  have hP : Injective (fderiv ℝ P.param q) := by
    exact P.fderiv_param_injective ((B.domain_open p.1).mem_nhds hqdom)
  have hchart : HasFDerivAt (fun z : E₂ => P.param (p.2 + M.param z))
      ((fderiv ℝ P.param q).comp J) u := by
    exact ((P.param_smooth.differentiable (by simp) q).hasFDerivAt.comp u hshift)
  have hamp : HasFDerivAt (R.criticalSurfaceParam p hp)
      ((fderiv ℝ R.amplitude.diffeomorph.symm (P.param q)).comp
        ((fderiv ℝ P.param q).comp J)) u := by
    exact ((R.amplitude.contDiff_equiv_symm.differentiable (by simp)
      (P.param q)).hasFDerivAt.comp u hchart)
  rw [hamp.fderiv]
  exact (R.amplitude.fderiv_equiv_symm_injective (P.param q)).comp
    (hP.comp hM)


-- @@ L2151-2166 verbatim
/-- After one derived positive-radius shrink, the actual installed surface
parameter has injective differential at every point of the ball.  This
discharges the conditional chart-injectivity premise used below without
adding a field to the event data. -/
theorem exists_criticalSurfaceParam_injective_radius
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ u : E₂, ‖u‖ < r →
        Injective (fderiv ℝ (R.criticalSurfaceParam p hp) u) := by
  obtain ⟨r, hr, hrle, hM⟩ :=
    R.exists_criticalModelShrink_fderiv_param_injective_radius p hp
  refine ⟨r, hr, hrle, ?_⟩
  intro u hu
  exact R.fderiv_criticalSurfaceParam_injective_of_param p hp u
    (hu.trans_le hrle) (hM u hu)


-- @@ L2168-2208 verbatim
/-- After a further derived shrink, the actual installed surface parameter is
itself injective on the whole ball, not merely immersive pointwise. -/
theorem exists_criticalSurfaceParam_injOn_radius
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      Set.InjOn (R.criticalSurfaceParam p hp) (ball (0 : E₂) r) := by
  let M := G.localMorseNormalForm p hp
  let S := R.criticalModelShrink p hp
  let P := B.chart p.1
  obtain ⟨r₀, hr₀, hr₀S, hderiv⟩ :=
    R.exists_criticalModelShrink_fderiv_param_injective_radius p hp
  have hJinj : Injective (fderiv ℝ M.param 0) := by
    apply hderiv 0
    simpa using hr₀
  obtain ⟨r, hr, hrr₀, hMinj⟩ :=
    M.exists_param_injOn_ball_of_fderiv_injective hJinj hr₀
  refine ⟨r, hr, hrr₀.trans hr₀S, ?_⟩
  intro u hu v hv huv
  apply hMinj hu hv
  have huS : ‖u‖ < S.radius := by
    have hur : ‖u‖ < r := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact hur.trans_le (hrr₀.trans hr₀S)
  have hvS : ‖v‖ < S.radius := by
    have hvr : ‖v‖ < r := by
      simpa [Metric.mem_ball, dist_zero_right] using hv
    exact hvr.trans_le (hrr₀.trans hr₀S)
  have huDom : p.2 + M.param u ∈ P.domain :=
    LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := M) S u huS
  have hvDom : p.2 + M.param v ∈ P.domain :=
    LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := M) S v hvS
  have hparam : P.param (p.2 + M.param u) =
      P.param (p.2 + M.param v) := by
    have h := congrArg R.amplitude.diffeomorph huv
    simpa [criticalSurfaceParam, M, P] using h
  have hshift : p.2 + M.param u = p.2 + M.param v :=
    P.param_injOn_domain huDom hvDom hparam
  exact add_left_cancel hshift


-- @@ L2210-2275 verbatim
/-- On an injective compact chart shrink, an ambient neighborhood of one
parameter point cannot meet the image of the opposite signed branch.  This is
the local branch-preservation input for a short exterior time flow. -/
theorem exists_criticalSurfaceParam_signedBranch_neighborhood
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (i : Fin 2) (u₀ : E₂)
    {r rInj : ℝ} (_hr : 0 < r) (hrrInj : r < rInj)
    (hrInjShrink : rInj ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp)
      (ball (0 : E₂) rInj))
    (hu₀ : ‖u₀‖ < rInj)
    (hu₀sign : 0 < signedBranch b (u₀ i)) :
    ∃ ε > 0, ∀ u : E₂, ‖u‖ < r →
      dist (R.criticalSurfaceParam p hp u)
        (R.criticalSurfaceParam p hp u₀) < ε →
      0 < signedBranch b (u i) := by
  let Φ := R.criticalSurfaceParam p hp
  let bad : Set E₂ :=
    closedBall (0 : E₂) r ∩ {u | signedBranch b (u i) ≤ 0}
  have hcoord : Continuous (fun u : E₂ => signedBranch b (u i)) := by
    cases b <;> simp only [signedBranch] <;> fun_prop
  have hbadCompact : IsCompact bad := by
    apply (isCompact_closedBall (0 : E₂) r).inter_right
    exact isClosed_le hcoord continuous_const
  have hbadSub : bad ⊆ ball (0 : E₂)
      (R.criticalModelShrink p hp).radius := by
    intro u hu
    rw [mem_ball, dist_zero_right]
    have hur : ‖u‖ ≤ r := by
      simpa [bad, mem_closedBall, dist_zero_right] using hu.1
    exact (hur.trans_lt hrrInj).trans_le hrInjShrink
  have hΦcont : ContinuousOn Φ bad := by
    intro u hu
    exact (R.criticalSurfaceParam_differentiableAt p hp u
      (by simpa [Φ, mem_ball, dist_zero_right] using
        hbadSub hu)).continuousAt.continuousWithinAt
  have himageCompact : IsCompact (Φ '' bad) :=
    hbadCompact.image_of_continuousOn hΦcont
  have hu₀Ball : u₀ ∈ ball (0 : E₂) rInj := by
    simpa [mem_ball, dist_zero_right] using hu₀
  have hnotmem : Φ u₀ ∉ Φ '' bad := by
    rintro ⟨u, huBad, hu⟩
    have huBall : u ∈ ball (0 : E₂) rInj := by
      rw [mem_ball, dist_zero_right]
      have hur : ‖u‖ ≤ r := by
        simpa [bad, mem_closedBall, dist_zero_right] using huBad.1
      exact hur.trans_lt hrrInj
    have heq : u = u₀ := hinj huBall hu₀Ball hu
    have hbadSign : signedBranch b (u i) ≤ 0 := huBad.2
    rw [heq] at hbadSign
    exact (not_lt_of_ge hbadSign) hu₀sign
  have hnhds : (Φ '' bad)ᶜ ∈ nhds (Φ u₀) :=
    himageCompact.isClosed.isOpen_compl.mem_nhds hnotmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ε, hε, ?_⟩
  intro u hu hdist
  by_contra hnotpos
  have huBad : u ∈ bad := by
    constructor
    · simpa [mem_closedBall, dist_zero_right] using le_of_lt hu
    · exact le_of_not_gt hnotpos
  have himage : Φ u ∈ Φ '' bad := ⟨u, huBad, rfl⟩
  have hballmem : Φ u ∈ ball (Φ u₀) ε := by
    simpa [mem_ball] using hdist
  exact (hball hballmem) himage


-- @@ L2277-2277 verbatim
variable {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}


-- @@ L2279-2356 verbatim
/-- A sufficiently short positive flow from a critical-level chart point has
a small Morse-coordinate preimage on the same signed branch and on the
positive saddle level. -/
theorem exists_positiveFlowEndpoint_morseParam
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (i : Fin 2) (u₀ : E₂)
    (hu₀Shrink : ‖u₀‖ < (R.criticalModelShrink p hp).radius)
    (hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0)
    (hu₀K : R.criticalSurfaceParam p hp u₀ ∈ K)
    {r εcover εbranch A : ℝ}
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hcover : ∀ v : E', dist v (R.criticalCenter p) < εcover →
      (R.amplitude.toVerticalAmplitude.pullback C).G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ R.criticalSurfaceParam p hp u = v)
    (hbranch : ∀ u : E₂, ‖u‖ < r →
      dist (R.criticalSurfaceParam p hp u)
        (R.criticalSurfaceParam p hp u₀) < εbranch →
      0 < signedBranch b (u i))
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hcenterClose : dist (R.criticalSurfaceParam p hp u₀)
        (R.criticalCenter p) + (T.base.bound : ℝ) * A ^ 2 < εcover)
    (hbranchClose : (T.base.bound : ℝ) * A ^ 2 < εbranch) :
    ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSurfaceParam p hp u₀) (A ^ 2) ∧
      0 < signedBranch b (u i) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2 := by
  let Φ := R.criticalSurfaceParam p hp
  let v := T.base.flow (Φ u₀) (A ^ 2)
  have hu₀fiber : (R.amplitude.toVerticalAmplitude.pullback C).G (Φ u₀) = 0 :=
    R.criticalSurfaceParam_fiber p hp u₀ hu₀Shrink
  have hvfiber : (R.amplitude.toVerticalAmplitude.pullback C).G v = 0 :=
    T.flow_mem_fiber hu₀fiber (A ^ 2)
  have hdist : dist v (Φ u₀) ≤ (T.base.bound : ℝ) * A ^ 2 := by
    calc
      dist v (Φ u₀) =
          dist (T.base.flow (Φ u₀) (A ^ 2))
            (T.base.flow (Φ u₀) 0) := by simp [v]
      _ ≤ (T.base.bound : ℝ) * |A ^ 2 - 0| :=
        T.base.dist_flow_self_le (Φ u₀) (A ^ 2) 0
      _ = (T.base.bound : ℝ) * A ^ 2 := by
        rw [sub_zero, abs_of_nonneg (sq_nonneg A)]
  have hvcenter : dist v (R.criticalCenter p) < εcover := by
    calc
      dist v (R.criticalCenter p) ≤
          dist v (Φ u₀) + dist (Φ u₀) (R.criticalCenter p) :=
        dist_triangle _ _ _
      _ ≤ (T.base.bound : ℝ) * A ^ 2 +
          dist (Φ u₀) (R.criticalCenter p) := by
        linarith
      _ < εcover := by linarith
  obtain ⟨u, hu, huΦ⟩ := hcover v hvcenter hvfiber
  change Φ u = v at huΦ
  have hparamDist : dist (Φ u) (Φ u₀) < εbranch := by
    rw [huΦ]
    exact hdist.trans_lt hbranchClose
  have husign : 0 < signedBranch b (u i) :=
    hbranch u hu hparamDist
  have huShrink : ‖u‖ < (R.criticalModelShrink p hp).radius :=
    hu.trans_le hrShrink
  have htflow : tcoord v = tcoord (Φ u₀) + A ^ 2 := by
    apply T.tcoord_flow hu₀K
    rw [abs_of_nonneg (sq_nonneg A)]
    exact hAsafe
  have htimeEq : tcoord (Φ u) = tcoord (Φ u₀) + A ^ 2 := by
    rw [huΦ]
    exact htflow
  have htu := R.criticalSurfaceParam_time p hp u huShrink
  have htu₀ := R.criticalSurfaceParam_time p hp u₀ hu₀Shrink
  rw [hindex] at htu htu₀
  have huquad : morseQuadratic .saddle (u 0, u 1) = A ^ 2 := by
    rw [htu, htu₀, hquad₀] at htimeEq
    linarith
  exact ⟨u, hu, huΦ, husign, huquad⟩


-- @@ L2358-2435 verbatim
/-- Negative-time counterpart of
`exists_positiveFlowEndpoint_morseParam`. -/
theorem exists_negativeFlowEndpoint_morseParam
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (i : Fin 2) (u₀ : E₂)
    (hu₀Shrink : ‖u₀‖ < (R.criticalModelShrink p hp).radius)
    (hquad₀ : morseQuadratic .saddle (u₀ 0, u₀ 1) = 0)
    (hu₀K : R.criticalSurfaceParam p hp u₀ ∈ K)
    {r εcover εbranch A : ℝ}
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hcover : ∀ v : E', dist v (R.criticalCenter p) < εcover →
      (R.amplitude.toVerticalAmplitude.pullback C).G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ R.criticalSurfaceParam p hp u = v)
    (hbranch : ∀ u : E₂, ‖u‖ < r →
      dist (R.criticalSurfaceParam p hp u)
        (R.criticalSurfaceParam p hp u₀) < εbranch →
      0 < signedBranch b (u i))
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hcenterClose : dist (R.criticalSurfaceParam p hp u₀)
        (R.criticalCenter p) + (T.base.bound : ℝ) * A ^ 2 < εcover)
    (hbranchClose : (T.base.bound : ℝ) * A ^ 2 < εbranch) :
    ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSurfaceParam p hp u₀) (-(A ^ 2)) ∧
      0 < signedBranch b (u i) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2) := by
  let Φ := R.criticalSurfaceParam p hp
  let v := T.base.flow (Φ u₀) (-(A ^ 2))
  have hu₀fiber : (R.amplitude.toVerticalAmplitude.pullback C).G (Φ u₀) = 0 :=
    R.criticalSurfaceParam_fiber p hp u₀ hu₀Shrink
  have hvfiber : (R.amplitude.toVerticalAmplitude.pullback C).G v = 0 :=
    T.flow_mem_fiber hu₀fiber (-(A ^ 2))
  have hdist : dist v (Φ u₀) ≤ (T.base.bound : ℝ) * A ^ 2 := by
    calc
      dist v (Φ u₀) =
          dist (T.base.flow (Φ u₀) (-(A ^ 2)))
            (T.base.flow (Φ u₀) 0) := by simp [v]
      _ ≤ (T.base.bound : ℝ) * |-(A ^ 2) - 0| :=
        T.base.dist_flow_self_le (Φ u₀) (-(A ^ 2)) 0
      _ = (T.base.bound : ℝ) * A ^ 2 := by
        rw [sub_zero, abs_neg, abs_of_nonneg (sq_nonneg A)]
  have hvcenter : dist v (R.criticalCenter p) < εcover := by
    calc
      dist v (R.criticalCenter p) ≤
          dist v (Φ u₀) + dist (Φ u₀) (R.criticalCenter p) :=
        dist_triangle _ _ _
      _ ≤ (T.base.bound : ℝ) * A ^ 2 +
          dist (Φ u₀) (R.criticalCenter p) := by
        linarith
      _ < εcover := by linarith
  obtain ⟨u, hu, huΦ⟩ := hcover v hvcenter hvfiber
  change Φ u = v at huΦ
  have hparamDist : dist (Φ u) (Φ u₀) < εbranch := by
    rw [huΦ]
    exact hdist.trans_lt hbranchClose
  have husign : 0 < signedBranch b (u i) :=
    hbranch u hu hparamDist
  have huShrink : ‖u‖ < (R.criticalModelShrink p hp).radius :=
    hu.trans_le hrShrink
  have htflow : tcoord v = tcoord (Φ u₀) - A ^ 2 := by
    have ht := T.tcoord_flow hu₀K (s := -(A ^ 2)) (by
      rw [abs_neg, abs_of_nonneg (sq_nonneg A)]
      exact hAsafe)
    linarith
  have htimeEq : tcoord (Φ u) = tcoord (Φ u₀) - A ^ 2 := by
    rw [huΦ]
    exact htflow
  have htu := R.criticalSurfaceParam_time p hp u huShrink
  have htu₀ := R.criticalSurfaceParam_time p hp u₀ hu₀Shrink
  rw [hindex] at htu htu₀
  have huquad : morseQuadratic .saddle (u 0, u 1) = -(A ^ 2) := by
    rw [htu, htu₀, hquad₀] at htimeEq
    linarith
  exact ⟨u, hu, huΦ, husign, huquad⟩


-- @@ L2437-2456 verbatim
/-- Differentiating the installed time identity gives equality with the
standard Morse differential at every point of the shrink. -/
theorem fderiv_criticalSurfaceParam_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    fderiv ℝ (fun z : E₂ => tcoord (R.criticalSurfaceParam p hp z)) u =
      fderiv ℝ (fun z : E₂ =>
        G.localSeparatedTime p p.2 +
          morseQuadratic (G.localMorseNormalForm p hp).index (z 0, z 1)) u := by
  have huball : u ∈ ball (0 : E₂) (R.criticalModelShrink p hp).radius := by
    simpa [mem_ball, dist_zero_right] using hu
  have heq :
      (fun z : E₂ => tcoord (R.criticalSurfaceParam p hp z)) =ᶠ[nhds u]
        (fun z : E₂ => G.localSeparatedTime p p.2 +
          morseQuadratic (G.localMorseNormalForm p hp).index (z 0, z 1)) := by
    filter_upwards [isOpen_ball.mem_nhds huball] with z hz
    apply R.criticalSurfaceParam_time p hp z
    simpa [mem_ball, dist_zero_right] using hz
  exact heq.fderiv_eq


-- @@ L2458-2491 verbatim
/-- The differential of the actual ambient parameter is killed by the full
defining-map differential.  This is the differentiated zero-fiber equation. -/
theorem fderiv_criticalSurfaceParam_mem_ker
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (w : E₂) :
    fderiv ℝ (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u)
        (fderiv ℝ (R.criticalSurfaceParam p hp) u w) = 0 := by
  let C' := R.amplitude.toVerticalAmplitude.pullback C
  let Φ := R.criticalSurfaceParam p hp
  have huball : u ∈ ball (0 : E₂) (R.criticalModelShrink p hp).radius := by
    simpa [mem_ball, dist_zero_right] using hu
  have hzeroEventually : (fun z : E₂ => C'.G (Φ z)) =ᶠ[nhds u]
      (fun _ : E₂ => (0 : EuclideanSpace ℝ (Fin n))) := by
    filter_upwards [isOpen_ball.mem_nhds huball] with z hz
    exact R.criticalSurfaceParam_fiber p hp z
      (by simpa [mem_ball, dist_zero_right] using hz)
  have hzero : fderiv ℝ (fun z : E₂ => C'.G (Φ z)) u = 0 := by
    rw [hzeroEventually.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ)
      (0 : EuclideanSpace ℝ (Fin n)) u).fderiv
  have hchain : fderiv ℝ (fun z : E₂ => C'.G (Φ z)) u =
      (fderiv ℝ C'.G (Φ u)).comp (fderiv ℝ Φ u) := by
    exact ((C'.smooth.differentiable (by simp) (Φ u)).hasFDerivAt.comp u
      (R.criticalSurfaceParam_differentiableAt p hp u hu).hasFDerivAt).fderiv
  have hcomp :
      (fderiv ℝ C'.G (Φ u)).comp (fderiv ℝ Φ u) = 0 := by
    rw [← hchain]
    exact hzero
  have happ := congrArg
    (fun L : E₂ →L[ℝ] EuclideanSpace ℝ (Fin n) => L w) hcomp
  simpa [C', Φ] using happ


-- @@ L2493-2511 verbatim
/-- Local chain rule for the time coordinate of the installed parameter. -/
theorem fderiv_criticalSurfaceParam_time_apply
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (w : E₂) :
    fderiv ℝ (fun z : E₂ => tcoord (R.criticalSurfaceParam p hp z)) u w =
      tcoord (fderiv ℝ (R.criticalSurfaceParam p hp) u w) := by
  let proj : E' →L[ℝ] ℝ :=
    EuclideanSpace.proj (Fin.last (n + 1)) (𝕜 := ℝ)
  have h := proj.hasFDerivAt.comp u
    (R.criticalSurfaceParam_differentiableAt p hp u hu).hasFDerivAt
  have hfd := h.fderiv
  change fderiv ℝ (proj ∘ R.criticalSurfaceParam p hp) u =
      proj.comp (fderiv ℝ (R.criticalSurfaceParam p hp) u) at hfd
  change (fderiv ℝ (proj ∘ R.criticalSurfaceParam p hp) u) w =
    proj (fderiv ℝ (R.criticalSurfaceParam p hp) u w)
  rw [hfd]
  rfl


-- @@ L2513-2536 verbatim
/-- **Ambient spatial differential compatibility.**  Any tangent vector of
the standard Morse level is sent to the kernel of the actual spatial
derivative on the installed slice. -/
theorem spatialDeriv_criticalSurfaceParam_eq_zero_of_model_tangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (w : E₂)
    (hw : fderiv ℝ (fun z : E₂ =>
      G.localSeparatedTime p p.2 +
        morseQuadratic (G.localMorseNormalForm p hp).index (z 0, z 1)) u w = 0) :
    spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u)
        (spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u w)) = 0 := by
  have htimeModel := congrArg
    (fun L : E₂ →L[ℝ] ℝ => L w)
    (R.fderiv_criticalSurfaceParam_time p hp u hu)
  have htime : tcoord
      (fderiv ℝ (R.criticalSurfaceParam p hp) u w) = 0 := by
    rw [← R.fderiv_criticalSurfaceParam_time_apply p hp u hu w,
      htimeModel, hw]
  rw [spatialDeriv_apply,
    spaceInclL_spacePart htime]
  exact R.fderiv_criticalSurfaceParam_mem_ker p hp u hu w


-- @@ L2538-2551 verbatim
/-- The canonical tangent of the standard Morse level therefore maps directly
to the kernel of the actual installed slice's spatial derivative. -/
theorem spatialDeriv_criticalSurfaceParam_morseLevelTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u)
        (spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u
          (morseLevelTangent (G.localMorseNormalForm p hp).index u))) = 0 := by
  apply R.spatialDeriv_criticalSurfaceParam_eq_zero_of_model_tangent
    p hp u hu
  exact fderiv_morseQuadratic_morseLevelTangent
    (G.localMorseNormalForm p hp).index (G.localSeparatedTime p p.2) u


-- @@ L2553-2569 verbatim
/-- Once injectivity of the local chart differential is available, the
transported tangent is genuinely nonzero on every noncritical Morse level. -/
theorem fderiv_criticalSurfaceParam_morseLevelTangent_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂)
    (hinj : Function.Injective
      (fderiv ℝ (R.criticalSurfaceParam p hp) u))
    (hquad : morseQuadratic (G.localMorseNormalForm p hp).index
      (u 0, u 1) ≠ 0) :
    fderiv ℝ (R.criticalSurfaceParam p hp) u
      (morseLevelTangent (G.localMorseNormalForm p hp).index u) ≠ 0 := by
  intro hzero
  apply morseLevelTangent_ne_zero_of_morseQuadratic_ne_zero
    (G.localMorseNormalForm p hp).index u hquad
  apply hinj
  simpa using hzero


-- @@ L2571-2606 verbatim
/-- Under the same chart-injectivity hypothesis, the transported tangent has
a nonzero spatial part.  Together with
`spatialDeriv_criticalSurfaceParam_morseLevelTangent`, this produces an actual
nonzero vector in the installed slice kernel. -/
theorem spacePart_fderiv_criticalSurfaceParam_morseLevelTangent_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hinj : Function.Injective
      (fderiv ℝ (R.criticalSurfaceParam p hp) u))
    (hquad : morseQuadratic (G.localMorseNormalForm p hp).index
      (u 0, u 1) ≠ 0) :
    spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u
      (morseLevelTangent (G.localMorseNormalForm p hp).index u)) ≠ 0 := by
  let w := morseLevelTangent (G.localMorseNormalForm p hp).index u
  let v := fderiv ℝ (R.criticalSurfaceParam p hp) u w
  have hv : v ≠ 0 := by
    exact R.fderiv_criticalSurfaceParam_morseLevelTangent_ne_zero
      p hp u hinj hquad
  have htimeModel := congrArg
    (fun L : E₂ →L[ℝ] ℝ => L w)
    (R.fderiv_criticalSurfaceParam_time p hp u hu)
  have htime : tcoord v = 0 := by
    rw [← R.fderiv_criticalSurfaceParam_time_apply p hp u hu w,
      htimeModel]
    exact fderiv_morseQuadratic_morseLevelTangent
      (G.localMorseNormalForm p hp).index
      (G.localSeparatedTime p p.2) u
  intro hspace
  change spacePart v = 0 at hspace
  apply hv
  calc
    v = spaceInclL (spacePart v) :=
      (spaceInclL_spacePart htime).symm
    _ = spaceInclL 0 := by rw [hspace]
    _ = 0 := map_zero spaceInclL


-- @@ L2608-2635 verbatim
/-- At a spatially regular installed point, the transported model tangent lies
in the line generated by the actual oriented slice tangent `tauField`. -/
theorem spacePart_fderiv_criticalSurfaceParam_morseLevelTangent_mem_span_tauField
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hreg : Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u))) :
    spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u
      (morseLevelTangent (G.localMorseNormalForm p hp).index u)) ∈
      Submodule.span ℝ {
        tauField
          (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
            (tcoord (R.criticalSurfaceParam p hp u)))
          (spacePart (R.criticalSurfaceParam p hp u))} := by
  let C' := R.amplitude.toVerticalAmplitude.pullback C
  let v := R.criticalSurfaceParam p hp u
  let z := spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u
    (morseLevelTangent (G.localMorseNormalForm p hp).index u))
  have hx : spacePart v ∈ regularSet (sliceMap C'.G (tcoord v)) := by
    change Surjective
      (fderiv ℝ (sliceMap C'.G (tcoord v)) (spacePart v))
    rw [fderiv_sliceMap C'.smooth, spaceTime_spacePart]
    exact hreg
  apply (fderiv_eq_zero_iff_mem_span_tauField hx z).mp
  rw [fderiv_sliceMap C'.smooth, spaceTime_spacePart]
  exact R.spatialDeriv_criticalSurfaceParam_morseLevelTangent p hp u hu


-- @@ L2637-2667 verbatim
/-- Combining spatial regularity with injectivity of the chart differential,
the transported model tangent is a *nonzero* scalar multiple of the actual
oriented slice tangent.  Determining the sign of this scalar is exactly the
remaining orientation-comparison step for the local frame homotopy. -/
theorem exists_ne_zero_scalar_smul_tauField_eq_spacePart_fderiv_morseLevelTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hreg : Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u)))
    (hinj : Function.Injective
      (fderiv ℝ (R.criticalSurfaceParam p hp) u))
    (hquad : morseQuadratic (G.localMorseNormalForm p hp).index
      (u 0, u 1) ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      c • tauField
          (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
            (tcoord (R.criticalSurfaceParam p hp u)))
          (spacePart (R.criticalSurfaceParam p hp u)) =
        spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u
          (morseLevelTangent (G.localMorseNormalForm p hp).index u)) := by
  have hmem :=
    R.spacePart_fderiv_criticalSurfaceParam_morseLevelTangent_mem_span_tauField
      p hp u hu hreg
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_, hc⟩
  intro hzero
  rw [hzero, zero_smul] at hc
  exact (R.spacePart_fderiv_criticalSurfaceParam_morseLevelTangent_ne_zero
    p hp u hu hinj hquad) hc.symm


-- @@ L2669-2702 verbatim
/-- On one derived event radius, all regular Morse levels carry the complete
actual tangent comparison: the transported model tangent is a nonzero scalar
multiple of the canonical oriented slice tangent.  Spatial regularity and
chart-differential injectivity are derived, not supplied as hypotheses. -/
theorem exists_radius_for_actual_morse_tangent_comparison
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ u : E₂, ‖u‖ < r →
        morseQuadratic (G.localMorseNormalForm p hp).index
          (u 0, u 1) ≠ 0 →
        ∃ c : ℝ, c ≠ 0 ∧
          c • tauField
              (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
                (tcoord (R.criticalSurfaceParam p hp u)))
              (spacePart (R.criticalSurfaceParam p hp u)) =
            spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u
              (morseLevelTangent
                (G.localMorseNormalForm p hp).index u)) := by
  obtain ⟨r, hr, hrle, hinj⟩ :=
    R.exists_criticalSurfaceParam_injective_radius p hp
  refine ⟨r, hr, hrle, ?_⟩
  intro u hu hquad
  have huProd : ‖u‖ < (R.criticalModelShrink p hp).radius := hu.trans_le hrle
  have hu0 : u ≠ 0 := by
    intro hzero
    subst u
    cases hi : (G.localMorseNormalForm p hp).index <;>
      simp [morseQuadratic, hi] at hquad
  exact R.exists_ne_zero_scalar_smul_tauField_eq_spacePart_fderiv_morseLevelTangent
    p hp u huProd
    (R.criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero
      p hp u huProd hu0)
    (hinj u hu) hquad


-- @@ L2704-2752 verbatim
/-- For an installed saddle, the same derived radius simultaneously compares
the actual oriented tangent with the transported model tangent on all four
explicit hyperbola branches on both sides of the event. -/
theorem exists_radius_for_actual_saddle_branch_tangent_comparison
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      (∀ (b : SaddleBranch) (a s : ℝ),
        ‖pairToMorseParam (saddlePositiveArc b a s)‖ < r → a ≠ 0 →
          ∃ c : ℝ, c ≠ 0 ∧
            c • tauField
                (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
                  (tcoord (R.criticalSaddlePositiveBranch p hp b a s)))
                (spacePart (R.criticalSaddlePositiveBranch p hp b a s)) =
              spacePart (fderiv ℝ (R.criticalSurfaceParam p hp)
                (pairToMorseParam (saddlePositiveArc b a s))
                (morseLevelTangent (G.localMorseNormalForm p hp).index
                  (pairToMorseParam (saddlePositiveArc b a s))))) ∧
      (∀ (b : SaddleBranch) (a s : ℝ),
        ‖pairToMorseParam (saddleNegativeArc b a s)‖ < r → a ≠ 0 →
          ∃ c : ℝ, c ≠ 0 ∧
            c • tauField
                (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
                  (tcoord (R.criticalSaddleNegativeBranch p hp b a s)))
                (spacePart (R.criticalSaddleNegativeBranch p hp b a s)) =
              spacePart (fderiv ℝ (R.criticalSurfaceParam p hp)
                (pairToMorseParam (saddleNegativeArc b a s))
                (morseLevelTangent (G.localMorseNormalForm p hp).index
                  (pairToMorseParam (saddleNegativeArc b a s))))) := by
  obtain ⟨r, hr, hrle, hcompare⟩ :=
    R.exists_radius_for_actual_morse_tangent_comparison p hp
  refine ⟨r, hr, hrle, ?_, ?_⟩
  · intro b a s hu ha
    have hquad : morseQuadratic (G.localMorseNormalForm p hp).index
        ((pairToMorseParam (saddlePositiveArc b a s)) 0,
          (pairToMorseParam (saddlePositiveArc b a s)) 1) ≠ 0 := by
      rw [hindex]
      simp [ha]
    simpa [criticalSaddlePositiveBranch] using
      hcompare (pairToMorseParam (saddlePositiveArc b a s)) hu hquad
  · intro b a s hu ha
    have hquad : morseQuadratic (G.localMorseNormalForm p hp).index
        ((pairToMorseParam (saddleNegativeArc b a s)) 0,
          (pairToMorseParam (saddleNegativeArc b a s)) 1) ≠ 0 := by
      rw [hindex]
      simp [ha]
    simpa [criticalSaddleNegativeBranch] using
      hcompare (pairToMorseParam (saddleNegativeArc b a s)) hu hquad


-- @@ L2754-2769 verbatim
/-- The installed image of one complete truncated positive-side hyperbola
branch. -/
def criticalSaddlePositiveSegment
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun u := R.criticalSurfaceParam p hp
    (saddlePositiveSegmentParam b ρ a u)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      (saddlePositiveSegmentParam b ρ a).continuous.continuousAt
    exact (norm_saddlePositiveSegmentParam_le b hρ ha u).trans_lt hρrad


-- @@ L2771-2786 verbatim
/-- The installed image of one complete truncated negative-side hyperbola
branch. -/
def criticalSaddleNegativeSegment
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun u := R.criticalSurfaceParam p hp
    (saddleNegativeSegmentParam b ρ a u)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      (saddleNegativeSegmentParam b ρ a).continuous.continuousAt
    exact (norm_saddleNegativeSegmentParam_le b hρ ha u).trans_lt hρrad


-- @@ L2788-2798 verbatim
/-- The spatial projection of an installed positive saddle segment. -/
def criticalSaddlePositiveSpatialSegment
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E₁) where
  toFun u := spacePart
    (R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad u)
  continuous_toFun := continuous_spacePart.comp
    (R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad).continuous


-- @@ L2800-2810 verbatim
/-- The spatial projection of an installed negative saddle segment. -/
def criticalSaddleNegativeSpatialSegment
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E₁) where
  toFun u := spacePart
    (R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad u)
  continuous_toFun := continuous_spacePart.comp
    (R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad).continuous


-- @@ L2812-2821 verbatim
@[simp] theorem criticalSaddlePositiveSegment_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad 0 =
      R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a := by
  simp [criticalSaddlePositiveSegment, saddlePositiveSegmentParam,
    criticalSaddlePositiveBoundaryEnd, saddlePositiveBoundaryEndParam]


-- @@ L2823-2832 verbatim
@[simp] theorem criticalSaddlePositiveSegment_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad 1 =
      R.criticalSaddlePositiveBoundaryEnd p hp b .positive ρ a := by
  simp [criticalSaddlePositiveSegment, saddlePositiveSegmentParam,
    criticalSaddlePositiveBoundaryEnd, saddlePositiveBoundaryEndParam]


-- @@ L2834-2843 verbatim
@[simp] theorem criticalSaddleNegativeSegment_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad 0 =
      R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a := by
  simp [criticalSaddleNegativeSegment, saddleNegativeSegmentParam,
    criticalSaddleNegativeBoundaryEnd, saddleNegativeBoundaryEndParam]


-- @@ L2845-2854 verbatim
@[simp] theorem criticalSaddleNegativeSegment_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad 1 =
      R.criticalSaddleNegativeBoundaryEnd p hp b .positive ρ a := by
  simp [criticalSaddleNegativeSegment, saddleNegativeSegmentParam,
    criticalSaddleNegativeBoundaryEnd, saddleNegativeBoundaryEndParam]


-- @@ L2856-2866 verbatim
theorem criticalSaddlePositiveSegment_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (u : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad u) = 0 := by
  exact R.criticalSurfaceParam_fiber p hp _
    ((norm_saddlePositiveSegmentParam_le b hρ ha u).trans_lt hρrad)


-- @@ L2868-2878 verbatim
theorem criticalSaddleNegativeSegment_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (u : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad u) = 0 := by
  exact R.criticalSurfaceParam_fiber p hp _
    ((norm_saddleNegativeSegmentParam_le b hρ ha u).trans_lt hρrad)


-- @@ L2880-2894 verbatim
theorem criticalSaddlePositiveSegment_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (u : I) :
    tcoord (R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad u) =
      G.localSeparatedTime p p.2 + a ^ 2 := by
  simpa [criticalSaddlePositiveSegment, saddlePositiveSegmentParam,
    criticalSaddlePositiveBranch] using
    R.criticalSaddlePositiveBranch_time p hp hindex b a
      (saddleSegmentCoordinate ρ a u)
      ((norm_saddlePositiveSegmentParam_le b hρ ha u).trans_lt hρrad)


-- @@ L2896-2910 verbatim
theorem criticalSaddleNegativeSegment_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (u : I) :
    tcoord (R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad u) =
      G.localSeparatedTime p p.2 - a ^ 2 := by
  simpa [criticalSaddleNegativeSegment, saddleNegativeSegmentParam,
    criticalSaddleNegativeBranch] using
    R.criticalSaddleNegativeBranch_time p hp hindex b a
      (saddleSegmentCoordinate ρ a u)
      ((norm_saddleNegativeSegmentParam_le b hρ ha u).trans_lt hρrad)


-- @@ L2912-2921 verbatim
/-- The actual regular slice just above an installed saddle. -/
def criticalSaddlePositiveSlice
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (_hp : p ∈ G.criticalPoints) (a : ℝ)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt
    (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData
    (G.localSeparatedTime p p.2 + a ^ 2) hreg


-- @@ L2923-2932 verbatim
/-- The actual regular slice just below an installed saddle. -/
def criticalSaddleNegativeSlice
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (_hp : p ∈ G.criticalPoints) (a : ℝ)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt
    (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData
    (G.localSeparatedTime p p.2 - a ^ 2) hreg


-- @@ L2934-2955 verbatim
theorem criticalSaddlePositiveSpatialSegment_mem_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (u : I) :
    R.criticalSaddlePositiveSpatialSegment p hp b ρ a hρ ha hρrad u ∈
      (R.criticalSaddlePositiveSlice p hp a hreg).fiber := by
  rw [criticalSaddlePositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalSaddlePositiveSegment p hp b ρ a
        hρ ha hρrad u))
      (G.localSeparatedTime p p.2 + a ^ 2)) = 0
  rw [← R.criticalSaddlePositiveSegment_time p hp hindex b ρ a
    hρ ha hρrad u, spaceTime_spacePart]
  exact R.criticalSaddlePositiveSegment_fiber p hp b ρ a hρ ha hρrad u


-- @@ L2957-2978 verbatim
theorem criticalSaddleNegativeSpatialSegment_mem_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (u : I) :
    R.criticalSaddleNegativeSpatialSegment p hp b ρ a hρ ha hρrad u ∈
      (R.criticalSaddleNegativeSlice p hp a hreg).fiber := by
  rw [criticalSaddleNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalSaddleNegativeSegment p hp b ρ a
        hρ ha hρrad u))
      (G.localSeparatedTime p p.2 - a ^ 2)) = 0
  rw [← R.criticalSaddleNegativeSegment_time p hp hindex b ρ a
    hρ ha hρrad u, spaceTime_spacePart]
  exact R.criticalSaddleNegativeSegment_fiber p hp b ρ a hρ ha hρrad u


-- @@ L2980-3003 verbatim
/-- The two ends of each positive-side local hyperbola branch belong to one
actual flow-orbit component of the regular slice. -/
theorem criticalSaddlePositiveBoundaryEnds_mem_same_orbit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp a hreg)) :
    spacePart (R.criticalSaddlePositiveBoundaryEnd p hp b .positive ρ a) ∈
      V.orbit
        (spacePart (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a)) := by
  let γ := R.criticalSaddlePositiveSpatialSegment p hp b ρ a hρ ha hρrad
  have hγfiber : ∀ u, γ u ∈
      (R.criticalSaddlePositiveSlice p hp a hreg).fiber := by
    intro u
    exact R.criticalSaddlePositiveSpatialSegment_mem_fiber p hp hindex b ρ a
      hρ ha hρrad hreg u
  have h := V.continuousMap_mem_orbit γ hγfiber 1
  simpa [γ, criticalSaddlePositiveSpatialSegment] using h


-- @@ L3005-3028 verbatim
/-- The two ends of each negative-side local hyperbola branch likewise belong
to one actual flow-orbit component. -/
theorem criticalSaddleNegativeBoundaryEnds_mem_same_orbit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp a hreg)) :
    spacePart (R.criticalSaddleNegativeBoundaryEnd p hp b .positive ρ a) ∈
      V.orbit
        (spacePart (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a)) := by
  let γ := R.criticalSaddleNegativeSpatialSegment p hp b ρ a hρ ha hρrad
  have hγfiber : ∀ u, γ u ∈
      (R.criticalSaddleNegativeSlice p hp a hreg).fiber := by
    intro u
    exact R.criticalSaddleNegativeSpatialSegment_mem_fiber p hp hindex b ρ a
      hρ ha hρrad hreg u
  have h := V.continuousMap_mem_orbit γ hγfiber 1
  simpa [γ, criticalSaddleNegativeSpatialSegment] using h


-- @@ L3030-3030 verbatim
/-! ## Fixed-slice transport from dynamic flow endpoints to local ends -/


-- @@ L3032-3051 verbatim
/-- Transport a positive-level Morse parameter along its actual installed
hyperbola component to any chosen boundary end of that component. -/
def criticalSaddlePositiveArcToBoundary
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun q := R.criticalSurfaceParam p hp
    (saddlePositiveArcToBoundaryParam b e ρ a u q)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro q
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      (saddlePositiveArcToBoundaryParam b e ρ a u).continuous.continuousAt
    exact norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q


-- @@ L3053-3072 verbatim
/-- Negative-level counterpart of
`criticalSaddlePositiveArcToBoundary`. -/
def criticalSaddleNegativeArcToBoundary
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun q := R.criticalSurfaceParam p hp
    (saddleNegativeArcToBoundaryParam b e ρ a u q)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro q
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      (saddleNegativeArcToBoundaryParam b e ρ a u).continuous.continuousAt
    exact norm_saddleNegativeArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q


-- @@ L3074-3089 verbatim
@[simp] theorem criticalSaddlePositiveArcToBoundary_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad 0 = R.criticalSurfaceParam p hp u := by
  rw [criticalSaddlePositiveArcToBoundary]
  simp only [saddlePositiveArcToBoundaryParam,
    saddleAffineCoordinate_zero, ContinuousMap.coe_mk]
  rw [← eq_pairToMorseParam_saddlePositiveArc_of_signedBranch
    b a u hquad hsign]


-- @@ L3091-3105 verbatim
@[simp] theorem criticalSaddlePositiveArcToBoundary_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad 1 =
      R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a := by
  simp [criticalSaddlePositiveArcToBoundary,
    saddlePositiveArcToBoundaryParam,
    criticalSaddlePositiveBoundaryEnd, saddlePositiveBoundaryEndParam]


-- @@ L3107-3122 verbatim
@[simp] theorem criticalSaddleNegativeArcToBoundary_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad 0 = R.criticalSurfaceParam p hp u := by
  rw [criticalSaddleNegativeArcToBoundary]
  simp only [saddleNegativeArcToBoundaryParam,
    saddleAffineCoordinate_zero, ContinuousMap.coe_mk]
  rw [← eq_pairToMorseParam_saddleNegativeArc_of_signedBranch
    b a u hquad hsign]


-- @@ L3124-3138 verbatim
@[simp] theorem criticalSaddleNegativeArcToBoundary_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad 1 =
      R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a := by
  simp [criticalSaddleNegativeArcToBoundary,
    saddleNegativeArcToBoundaryParam,
    criticalSaddleNegativeBoundaryEnd, saddleNegativeBoundaryEndParam]


-- @@ L3140-3154 verbatim
theorem criticalSaddlePositiveArcToBoundary_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (q : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
        hquad hsign hρ ha hu hρrad q) = 0 := by
  exact R.criticalSurfaceParam_fiber p hp _
    (norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q)


-- @@ L3156-3170 verbatim
theorem criticalSaddleNegativeArcToBoundary_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (q : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
        hquad hsign hρ ha hu hρrad q) = 0 := by
  exact R.criticalSurfaceParam_fiber p hp _
    (norm_saddleNegativeArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q)


-- @@ L3172-3190 verbatim
theorem criticalSaddlePositiveArcToBoundary_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (q : I) :
    tcoord (R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad q) =
      G.localSeparatedTime p p.2 + a ^ 2 := by
  change tcoord (R.criticalSurfaceParam p hp
    (saddlePositiveArcToBoundaryParam b e ρ a u q)) = _
  rw [R.criticalSurfaceParam_time p hp _
    (norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q), hindex]
  simp [saddlePositiveArcToBoundaryParam]


-- @@ L3192-3211 verbatim
theorem criticalSaddleNegativeArcToBoundary_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (q : I) :
    tcoord (R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad q) =
      G.localSeparatedTime p p.2 - a ^ 2 := by
  change tcoord (R.criticalSurfaceParam p hp
    (saddleNegativeArcToBoundaryParam b e ρ a u q)) = _
  rw [R.criticalSurfaceParam_time p hp _
    (norm_saddleNegativeArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q), hindex]
  simp [saddleNegativeArcToBoundaryParam]
  ring


-- @@ L3213-3228 verbatim
/-- Spatial projection of the actual positive fixed-level branch arc. -/
def criticalSaddlePositiveSpatialArcToBoundary
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E₁) where
  toFun q := spacePart
    (R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad q)
  continuous_toFun := continuous_spacePart.comp
    (R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad).continuous


-- @@ L3230-3245 verbatim
/-- Spatial projection of the actual negative fixed-level branch arc. -/
def criticalSaddleNegativeSpatialArcToBoundary
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E₁) where
  toFun q := spacePart
    (R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad q)
  continuous_toFun := continuous_spacePart.comp
    (R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad).continuous


-- @@ L3247-3272 verbatim
theorem criticalSaddlePositiveSpatialArcToBoundary_mem_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2)) (q : I) :
    R.criticalSaddlePositiveSpatialArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad q ∈
      (R.criticalSaddlePositiveSlice p hp a hreg).fiber := by
  rw [criticalSaddlePositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalSaddlePositiveArcToBoundary p hp b e ρ a u
        hquad hsign hρ ha hu hρrad q))
      (G.localSeparatedTime p p.2 + a ^ 2)) = 0
  rw [← R.criticalSaddlePositiveArcToBoundary_time p hp hindex
    b e ρ a u hquad hsign hρ ha hu hρrad q, spaceTime_spacePart]
  exact R.criticalSaddlePositiveArcToBoundary_fiber p hp b e ρ a u
    hquad hsign hρ ha hu hρrad q


-- @@ L3274-3299 verbatim
theorem criticalSaddleNegativeSpatialArcToBoundary_mem_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2)) (q : I) :
    R.criticalSaddleNegativeSpatialArcToBoundary p hp b e ρ a u
      hquad hsign hρ ha hu hρrad q ∈
      (R.criticalSaddleNegativeSlice p hp a hreg).fiber := by
  rw [criticalSaddleNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalSaddleNegativeArcToBoundary p hp b e ρ a u
        hquad hsign hρ ha hu hρrad q))
      (G.localSeparatedTime p p.2 - a ^ 2)) = 0
  rw [← R.criticalSaddleNegativeArcToBoundary_time p hp hindex
    b e ρ a u hquad hsign hρ ha hu hρrad q, spaceTime_spacePart]
  exact R.criticalSaddleNegativeArcToBoundary_fiber p hp b e ρ a u
    hquad hsign hρ ha hu hρrad q


-- @@ L3301-3332 verbatim
/-- Any sufficiently local positive-level point on a signed saddle component
belongs to the actual flow orbit through either chosen installed end of that
component. -/
theorem criticalSaddlePositiveParam_mem_boundary_orbit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp a hreg)) :
    spacePart (R.criticalSurfaceParam p hp u) ∈
      V.orbit (spacePart
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a)) := by
  let γ := R.criticalSaddlePositiveSpatialArcToBoundary p hp b e ρ a u
    hquad hsign hρ ha hu hρrad
  have hγfiber : ∀ q, γ q ∈
      (R.criticalSaddlePositiveSlice p hp a hreg).fiber := by
    intro q
    exact R.criticalSaddlePositiveSpatialArcToBoundary_mem_fiber p hp
      hindex b e ρ a u hquad hsign hρ ha hu hρrad hreg q
  have hend := V.continuousMap_mem_orbit γ hγfiber 1
  have hresult : γ 0 ∈ V.orbit (γ 1) := by
    rw [V.orbit_eq_of_mem hend]
    exact V.mem_orbit_self _
  simpa [γ, criticalSaddlePositiveSpatialArcToBoundary] using hresult


-- @@ L3334-3364 verbatim
/-- Negative-level counterpart of
`criticalSaddlePositiveParam_mem_boundary_orbit`. -/
theorem criticalSaddleNegativeParam_mem_boundary_orbit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp a hreg)) :
    spacePart (R.criticalSurfaceParam p hp u) ∈
      V.orbit (spacePart
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a)) := by
  let γ := R.criticalSaddleNegativeSpatialArcToBoundary p hp b e ρ a u
    hquad hsign hρ ha hu hρrad
  have hγfiber : ∀ q, γ q ∈
      (R.criticalSaddleNegativeSlice p hp a hreg).fiber := by
    intro q
    exact R.criticalSaddleNegativeSpatialArcToBoundary_mem_fiber p hp
      hindex b e ρ a u hquad hsign hρ ha hu hρrad hreg q
  have hend := V.continuousMap_mem_orbit γ hγfiber 1
  have hresult : γ 0 ∈ V.orbit (γ 1) := by
    rw [V.orbit_eq_of_mem hend]
    exact V.mem_orbit_self _
  simpa [γ, criticalSaddleNegativeSpatialArcToBoundary] using hresult


-- @@ L3366-3398 verbatim
/-- Package a positive exterior-flow endpoint represented by a small Morse
parameter into membership in the actual orbit through any chosen installed
end of the corresponding positive saddle component.  The required endpoint
witness is supplied directly by `exists_positiveFlowEndpoint_morseParam`. -/
theorem positiveFlowEndpoint_mem_boundary_orbit_of_morseParam
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (u₀ : E₂) {r ρ A : ℝ}
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSurfaceParam p hp u₀) (A ^ 2) ∧
      0 < signedBranch b (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp A hreg)) :
    spacePart (T.base.flow (R.criticalSurfaceParam p hp u₀) (A ^ 2)) ∈
      V.orbit (spacePart
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A)) := by
  obtain ⟨u, hu, hflow, hsign, hquad⟩ := hendpoint
  have huShrink : ‖u‖ < (R.criticalModelShrink p hp).radius :=
    hu.trans_le hrShrink
  have horbit := R.criticalSaddlePositiveParam_mem_boundary_orbit p hp
    hindex b e ρ A u hquad hsign hρ hA huShrink hρrad hreg V
  rw [hflow] at horbit
  exact horbit


-- @@ L3400-3430 verbatim
/-- Negative-time counterpart of
`positiveFlowEndpoint_mem_boundary_orbit_of_morseParam`. -/
theorem negativeFlowEndpoint_mem_boundary_orbit_of_morseParam
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (u₀ : E₂) {r ρ A : ℝ}
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSurfaceParam p hp u₀) (-(A ^ 2)) ∧
      0 < signedBranch b (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp A hreg)) :
    spacePart (T.base.flow (R.criticalSurfaceParam p hp u₀) (-(A ^ 2))) ∈
      V.orbit (spacePart
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ A)) := by
  obtain ⟨u, hu, hflow, hsign, hquad⟩ := hendpoint
  have huShrink : ‖u‖ < (R.criticalModelShrink p hp).radius :=
    hu.trans_le hrShrink
  have horbit := R.criticalSaddleNegativeParam_mem_boundary_orbit p hp
    hindex b e ρ A u hquad hsign hρ hA huShrink hρrad hreg V
  rw [hflow] at horbit
  exact horbit


-- @@ L3432-3432 verbatim
/-! ## Actual orbit indices of the two local saddle branches -/


-- @@ L3434-3453 verbatim
theorem criticalSaddlePositiveBoundaryEnd_mem_slice_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2)) :
    spacePart (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a) ∈
      (R.criticalSaddlePositiveSlice p hp a hreg).fiber := by
  rw [criticalSaddlePositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a))
      (G.localSeparatedTime p p.2 + a ^ 2)) = 0
  rw [← R.criticalSaddlePositiveBoundaryEnd_time p hp hindex b e
    hρ ha hρrad, spaceTime_spacePart]
  exact R.criticalSaddlePositiveBoundaryEnd_fiber p hp b e hρ ha hρrad


-- @@ L3455-3474 verbatim
theorem criticalSaddleNegativeBoundaryEnd_mem_slice_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2)) :
    spacePart (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a) ∈
      (R.criticalSaddleNegativeSlice p hp a hreg).fiber := by
  rw [criticalSaddleNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a))
      (G.localSeparatedTime p p.2 - a ^ 2)) = 0
  rw [← R.criticalSaddleNegativeBoundaryEnd_time p hp hindex b e
    hρ ha hρrad, spaceTime_spacePart]
  exact R.criticalSaddleNegativeBoundaryEnd_fiber p hp b e hρ ha hρrad


-- @@ L3476-3496 verbatim
/-- The actual positive-slice orbit component containing one local hyperbola
branch.  The negative end is used only as a canonical base point; the next
theorem proves independence of that choice. -/
def criticalSaddlePositiveBranchOrbitIndex
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp a hreg)) :
    V.OrbitIndex :=
  ⟨V.orbit (spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a)),
    V.mem_orbitFinset.mpr ⟨_,
      R.criticalSaddlePositiveBoundaryEnd_mem_slice_fiber p hp hindex
        b .negative ρ a hρ ha hρrad hreg,
      rfl⟩⟩


-- @@ L3498-3516 verbatim
/-- The corresponding actual negative-slice branch component. -/
def criticalSaddleNegativeBranchOrbitIndex
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp a hreg)) :
    V.OrbitIndex :=
  ⟨V.orbit (spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a)),
    V.mem_orbitFinset.mpr ⟨_,
      R.criticalSaddleNegativeBoundaryEnd_mem_slice_fiber p hp hindex
        b .negative ρ a hρ ha hρrad hreg,
      rfl⟩⟩


-- @@ L3518-3532 verbatim
@[simp] theorem criticalSaddlePositiveBranchOrbitIndex_coe
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp a hreg)) :
    ((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b ρ a
      hρ ha hρrad hreg V : V.OrbitIndex) : Set E₁) =
      V.orbit (spacePart
        (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a)) := rfl


-- @@ L3534-3548 verbatim
@[simp] theorem criticalSaddleNegativeBranchOrbitIndex_coe
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp a hreg)) :
    ((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b ρ a
      hρ ha hρrad hreg V : V.OrbitIndex) : Set E₁) =
      V.orbit (spacePart
        (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a)) := rfl


-- @@ L3550-3575 verbatim
/-- Either boundary end of a positive local branch generates its canonical
actual branch orbit index. -/
theorem criticalSaddlePositiveBoundaryEnd_orbit_eq_branchOrbitIndex
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp a hreg)) :
    V.orbit (spacePart
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a)) =
      (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b ρ a
        hρ ha hρrad hreg V : Set E₁) := by
  change V.orbit (spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ a)) =
    V.orbit (spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a))
  have h := R.criticalSaddlePositiveBoundaryEnds_mem_same_orbit p hp hindex
    b ρ a hρ ha hρrad hreg V
  cases e
  · exact V.orbit_eq_of_mem h
  · rfl


-- @@ L3577-3602 verbatim
/-- Either boundary end of a negative local branch generates its canonical
actual branch orbit index. -/
theorem criticalSaddleNegativeBoundaryEnd_orbit_eq_branchOrbitIndex
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp a hreg)) :
    V.orbit (spacePart
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a)) =
      (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b ρ a
        hρ ha hρrad hreg V : Set E₁) := by
  change V.orbit (spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ a)) =
    V.orbit (spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a))
  have h := R.criticalSaddleNegativeBoundaryEnds_mem_same_orbit p hp hindex
    b ρ a hρ ha hρrad hreg V
  cases e
  · exact V.orbit_eq_of_mem h
  · rfl


-- @@ L3604-3625 verbatim
/-- Every sufficiently local positive-level Morse point is classified by the
actual orbit index of its signed local branch. -/
theorem criticalSaddlePositiveParam_orbit_eq_branchOrbitIndex
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp a hreg)) :
    V.orbit (spacePart (R.criticalSurfaceParam p hp u)) =
      (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b ρ a
        hρ ha hρrad hreg V : Set E₁) := by
  exact V.orbit_eq_of_mem
    (R.criticalSaddlePositiveParam_mem_boundary_orbit p hp hindex
      b .negative ρ a u hquad hsign hρ ha hu hρrad hreg V)


-- @@ L3627-3648 verbatim
/-- Negative-level counterpart of
`criticalSaddlePositiveParam_orbit_eq_branchOrbitIndex`. -/
theorem criticalSaddleNegativeParam_orbit_eq_branchOrbitIndex
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp a hreg)) :
    V.orbit (spacePart (R.criticalSurfaceParam p hp u)) =
      (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b ρ a
        hρ ha hρrad hreg V : Set E₁) := by
  exact V.orbit_eq_of_mem
    (R.criticalSaddleNegativeParam_mem_boundary_orbit p hp hindex
      b .negative ρ a u hquad hsign hρ ha hu hρrad hreg V)


-- @@ L3650-3650 verbatim
/-! ## Exterior connectors as equalities of actual branch orbit indices -/


-- @@ L3652-3705 verbatim
/-- Orbit chaining turns two positive local endpoint memberships and one
flowed exterior connector into equality of the corresponding actual branch
indices. -/
theorem criticalSaddlePositiveBranchOrbitIndex_eq_of_flow_orbits
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (r ρ A : ℝ)
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint₁ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ 0)
          (A ^ 2) ∧
      0 < signedBranch b₁ (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hendpoint₂ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ 0)
          (A ^ 2) ∧
      0 < signedBranch b₂ (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp A hreg))
    (hflow : spacePart (T.base.flow
        (R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ 0) (A ^ 2)) ∈
      V.orbit (spacePart (T.base.flow
        (R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ 0) (A ^ 2)))) :
    R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b₁ ρ A
        hρ hA hρrad hreg V =
      R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b₂ ρ A
        hρ hA hρrad hreg V := by
  have hmem₁ := R.positiveFlowEndpoint_mem_boundary_orbit_of_morseParam
    T p hp hindex b₁ e₁
    (saddlePositiveBoundaryEndParam b₁ e₁ ρ 0)
    hrShrink hendpoint₁ hρ hA hρrad hreg V
  have hmem₂ := R.positiveFlowEndpoint_mem_boundary_orbit_of_morseParam
    T p hp hindex b₂ e₂
    (saddlePositiveBoundaryEndParam b₂ e₂ ρ 0)
    hrShrink hendpoint₂ hρ hA hρrad hreg V
  have heq₁ := V.orbit_eq_of_mem hmem₁
  have heq₂ := V.orbit_eq_of_mem hmem₂
  have heqflow := V.orbit_eq_of_mem hflow
  apply Subtype.ext
  rw [← R.criticalSaddlePositiveBoundaryEnd_orbit_eq_branchOrbitIndex
      p hp hindex b₁ e₁ ρ A hρ hA hρrad hreg V,
    ← R.criticalSaddlePositiveBoundaryEnd_orbit_eq_branchOrbitIndex
      p hp hindex b₂ e₂ ρ A hρ hA hρrad hreg V]
  exact heq₁.symm.trans (heqflow.symm.trans heq₂)


-- @@ L3707-3755 verbatim
/-- A critical-slice exterior connector identifies exactly the two positive
branch orbit indices selected by its transposed endpoint labels. -/
theorem criticalSaddlePositiveBranchOrbitIndex_eq_of_criticalExteriorPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (r ρ A : ℝ)
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint₁ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ 0)
          (A ^ 2) ∧
      0 < signedBranch b₁ (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hendpoint₂ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ 0)
          (A ^ 2) ∧
      0 < signedBranch b₂ (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp A hreg))
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K)
    (hηtime : ∀ q, tcoord (η.toPath q) = G.localSeparatedTime p p.2) :
    R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b₁ ρ A
        hρ hA hρrad hreg V =
      R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b₂ ρ A
        hρ hA hρrad hreg V := by
  have hposSafe : |A ^ 2| ≤ T.safeTime := by
    rw [abs_of_nonneg (sq_nonneg A)]
    exact hAsafe
  have hflow := T.flowSlicePath_endpoints_mem_same_orbit
    η.toPath hηK hηtime η.fiber hposSafe hreg V
  rw [← R.criticalSaddle_boundary_pairing_switch p hp b₁ e₁ ρ,
    ← R.criticalSaddle_boundary_pairing_switch p hp b₂ e₂ ρ] at hflow
  exact R.criticalSaddlePositiveBranchOrbitIndex_eq_of_flow_orbits
    T p hp hindex b₁ e₁ b₂ e₂ r ρ A hrShrink hendpoint₁ hendpoint₂
      hρ hA hρrad hreg V hflow


-- @@ L3757-3808 verbatim
/-- Orbit chaining counterpart for negative local branch endpoints. -/
theorem criticalSaddleNegativeBranchOrbitIndex_eq_of_flow_orbits
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (r ρ A : ℝ)
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint₁ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddleNegativeBoundaryEnd p hp b₁ e₁ ρ 0)
          (-(A ^ 2)) ∧
      0 < signedBranch b₁ (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hendpoint₂ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddleNegativeBoundaryEnd p hp b₂ e₂ ρ 0)
          (-(A ^ 2)) ∧
      0 < signedBranch b₂ (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp A hreg))
    (hflow : spacePart (T.base.flow
        (R.criticalSaddleNegativeBoundaryEnd p hp b₂ e₂ ρ 0) (-(A ^ 2))) ∈
      V.orbit (spacePart (T.base.flow
        (R.criticalSaddleNegativeBoundaryEnd p hp b₁ e₁ ρ 0) (-(A ^ 2))))) :
    R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b₁ ρ A
        hρ hA hρrad hreg V =
      R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b₂ ρ A
        hρ hA hρrad hreg V := by
  have hmem₁ := R.negativeFlowEndpoint_mem_boundary_orbit_of_morseParam
    T p hp hindex b₁ e₁
    (saddleNegativeBoundaryEndParam b₁ e₁ ρ 0)
    hrShrink hendpoint₁ hρ hA hρrad hreg V
  have hmem₂ := R.negativeFlowEndpoint_mem_boundary_orbit_of_morseParam
    T p hp hindex b₂ e₂
    (saddleNegativeBoundaryEndParam b₂ e₂ ρ 0)
    hrShrink hendpoint₂ hρ hA hρrad hreg V
  have heq₁ := V.orbit_eq_of_mem hmem₁
  have heq₂ := V.orbit_eq_of_mem hmem₂
  have heqflow := V.orbit_eq_of_mem hflow
  apply Subtype.ext
  rw [← R.criticalSaddleNegativeBoundaryEnd_orbit_eq_branchOrbitIndex
      p hp hindex b₁ e₁ ρ A hρ hA hρrad hreg V,
    ← R.criticalSaddleNegativeBoundaryEnd_orbit_eq_branchOrbitIndex
      p hp hindex b₂ e₂ ρ A hρ hA hρrad hreg V]
  exact heq₁.symm.trans (heqflow.symm.trans heq₂)


-- @@ L3810-3861 verbatim
/-- The same critical exterior connector identifies the two transposed
negative branch orbit indices after a short safe negative flow. -/
theorem criticalSaddleNegativeBranchOrbitIndex_eq_of_criticalExteriorPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (r ρ A : ℝ)
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint₁ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0)
          (-(A ^ 2)) ∧
      0 < signedBranch e₁ (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hendpoint₂ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0)
          (-(A ^ 2)) ∧
      0 < signedBranch e₂ (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp A hreg))
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K)
    (hηtime : ∀ q, tcoord (η.toPath q) = G.localSeparatedTime p p.2) :
    R.criticalSaddleNegativeBranchOrbitIndex p hp hindex e₁ ρ A
        hρ hA hρrad hreg V =
      R.criticalSaddleNegativeBranchOrbitIndex p hp hindex e₂ ρ A
        hρ hA hρrad hreg V := by
  have hnegSafe : |-(A ^ 2)| ≤ T.safeTime := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg A)]
    exact hAsafe
  have hflow := T.flowSlicePath_endpoints_mem_same_orbit
    η.toPath hηK hηtime η.fiber hnegSafe (a := -(A ^ 2))
      (by
        change sliceRegular
          (R.amplitude.toVerticalAmplitude.pullback C).G
          (G.localSeparatedTime p p.2 + -(A ^ 2))
        simpa [sub_eq_add_neg] using hreg) V
  exact R.criticalSaddleNegativeBranchOrbitIndex_eq_of_flow_orbits
    T p hp hindex e₁ b₁ e₂ b₂ r ρ A hrShrink hendpoint₁ hendpoint₂
      hρ hA hρrad hreg V hflow


-- @@ L3863-3863 verbatim
/-! ## Regular boundary tracks through an installed saddle event -/


-- @@ L3865-3890 verbatim
/-- One installed positive-side boundary end followed continuously from the
critical level to a chosen nearby regular level. -/
def criticalSaddlePositiveBoundaryTrack
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun u := R.criticalSaddlePositiveBoundaryEnd p hp b e ρ
    (saddleBoundaryTrackAmplitude A u)
  continuous_toFun := by
    change Continuous (fun u : I => R.criticalSurfaceParam p hp
      (saddlePositiveBoundaryEndParam b e ρ
        (saddleBoundaryTrackAmplitude A u)))
    rw [continuous_iff_continuousAt]
    intro u
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      ?_
    · rw [norm_saddlePositiveBoundaryEndParam b e hρ
        (saddleBoundaryTrackAmplitude_sq_lt hA u)]
      exact hρrad
    · cases b <;> cases e <;>
        simp only [saddlePositiveBoundaryEndParam, pairToMorseParam,
          saddlePositiveArc, signedBranch, saddleBoundaryParameter,
          saddleBoundaryTrackAmplitude] <;>
        fun_prop


-- @@ L3892-3917 verbatim
/-- One installed negative-side boundary end followed continuously from the
critical level to a chosen nearby regular level. -/
def criticalSaddleNegativeBoundaryTrack
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun u := R.criticalSaddleNegativeBoundaryEnd p hp b e ρ
    (saddleBoundaryTrackAmplitude A u)
  continuous_toFun := by
    change Continuous (fun u : I => R.criticalSurfaceParam p hp
      (saddleNegativeBoundaryEndParam b e ρ
        (saddleBoundaryTrackAmplitude A u)))
    rw [continuous_iff_continuousAt]
    intro u
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      ?_
    · rw [norm_saddleNegativeBoundaryEndParam b e hρ
        (saddleBoundaryTrackAmplitude_sq_lt hA u)]
      exact hρrad
    · cases b <;> cases e <;>
        simp only [saddleNegativeBoundaryEndParam, pairToMorseParam,
          saddleNegativeArc, signedBranch, saddleBoundaryParameter,
          saddleBoundaryTrackAmplitude] <;>
        fun_prop


-- @@ L3919-3927 verbatim
@[simp] theorem criticalSaddlePositiveBoundaryTrack_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddlePositiveBoundaryTrack p hp b e ρ A hρ hA hρrad 0 =
      R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0 := by
  simp [criticalSaddlePositiveBoundaryTrack]


-- @@ L3929-3937 verbatim
@[simp] theorem criticalSaddlePositiveBoundaryTrack_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddlePositiveBoundaryTrack p hp b e ρ A hρ hA hρrad 1 =
      R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A := by
  simp [criticalSaddlePositiveBoundaryTrack]


-- @@ L3939-3947 verbatim
@[simp] theorem criticalSaddleNegativeBoundaryTrack_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddleNegativeBoundaryTrack p hp b e ρ A hρ hA hρrad 0 =
      R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0 := by
  simp [criticalSaddleNegativeBoundaryTrack]


-- @@ L3949-3957 verbatim
@[simp] theorem criticalSaddleNegativeBoundaryTrack_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    R.criticalSaddleNegativeBoundaryTrack p hp b e ρ A hρ hA hρrad 1 =
      R.criticalSaddleNegativeBoundaryEnd p hp b e ρ A := by
  simp [criticalSaddleNegativeBoundaryTrack]


-- @@ L3959-3969 verbatim
theorem criticalSaddlePositiveBoundaryTrack_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (u : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryTrack p hp b e ρ A
        hρ hA hρrad u) = 0 := by
  exact R.criticalSaddlePositiveBoundaryEnd_fiber p hp b e hρ
    (saddleBoundaryTrackAmplitude_sq_lt hA u) hρrad


-- @@ L3971-3981 verbatim
theorem criticalSaddleNegativeBoundaryTrack_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (u : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryTrack p hp b e ρ A
        hρ hA hρrad u) = 0 := by
  exact R.criticalSaddleNegativeBoundaryEnd_fiber p hp b e hρ
    (saddleBoundaryTrackAmplitude_sq_lt hA u) hρrad


-- @@ L3983-3994 verbatim
theorem criticalSaddlePositiveBoundaryTrack_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (u : I) :
    tcoord (R.criticalSaddlePositiveBoundaryTrack p hp b e ρ A
      hρ hA hρrad u) =
      G.localSeparatedTime p p.2 + saddleBoundaryTrackAmplitude A u ^ 2 := by
  exact R.criticalSaddlePositiveBoundaryEnd_time p hp hindex b e hρ
    (saddleBoundaryTrackAmplitude_sq_lt hA u) hρrad


-- @@ L3996-4007 verbatim
theorem criticalSaddleNegativeBoundaryTrack_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (u : I) :
    tcoord (R.criticalSaddleNegativeBoundaryTrack p hp b e ρ A
      hρ hA hρrad u) =
      G.localSeparatedTime p p.2 - saddleBoundaryTrackAmplitude A u ^ 2 := by
  exact R.criticalSaddleNegativeBoundaryEnd_time p hp hindex b e hρ
    (saddleBoundaryTrackAmplitude_sq_lt hA u) hρrad


-- @@ L4009-4020 verbatim
theorem criticalSaddlePositiveBoundaryTrack_regular
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (u : I) :
    Surjective (spatialDeriv
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryTrack p hp b e ρ A
        hρ hA hρrad u)) := by
  exact R.criticalSaddlePositiveBoundaryEnd_spatialDeriv_surjective
    p hp b e hρ (saddleBoundaryTrackAmplitude_sq_lt hA u) hρrad


-- @@ L4022-4033 verbatim
theorem criticalSaddleNegativeBoundaryTrack_regular
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) (u : I) :
    Surjective (spatialDeriv
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryTrack p hp b e ρ A
        hρ hA hρrad u)) := by
  exact R.criticalSaddleNegativeBoundaryEnd_spatialDeriv_surjective
    p hp b e hρ (saddleBoundaryTrackAmplitude_sq_lt hA u) hρrad


-- @@ L4035-4047 verbatim
/-- The positive boundary track regarded as a path with explicit endpoints. -/
def criticalSaddlePositiveBoundaryPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Path (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0)
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A) where
  toContinuousMap :=
    R.criticalSaddlePositiveBoundaryTrack p hp b e ρ A hρ hA hρrad
  source' := by simp
  target' := by simp


-- @@ L4049-4061 verbatim
/-- The negative boundary track regarded as a path with explicit endpoints. -/
def criticalSaddleNegativeBoundaryPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Path (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ A) where
  toContinuousMap :=
    R.criticalSaddleNegativeBoundaryTrack p hp b e ρ A hρ hA hρrad
  source' := by simp
  target' := by simp


-- @@ L4063-4082 verbatim
/-- The positive boundary track, including the proof that it stays in the
spatially regular part of the installed zero-surface. -/
def criticalSaddlePositiveBoundaryRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0)
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A) where
  toPath :=
    R.criticalSaddlePositiveBoundaryPath p hp b e ρ A hρ hA hρrad
  range_subset := by
    rintro z ⟨u, rfl⟩
    exact ⟨R.criticalSaddlePositiveBoundaryTrack_fiber p hp b e ρ A
        hρ hA hρrad u,
      R.criticalSaddlePositiveBoundaryTrack_regular p hp b e ρ A
        hρ hA hρrad u⟩


-- @@ L4084-4103 verbatim
/-- The negative boundary track, including the proof that it stays in the
spatially regular part of the installed zero-surface. -/
def criticalSaddleNegativeBoundaryRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ A) where
  toPath :=
    R.criticalSaddleNegativeBoundaryPath p hp b e ρ A hρ hA hρrad
  range_subset := by
    rintro z ⟨u, rfl⟩
    exact ⟨R.criticalSaddleNegativeBoundaryTrack_fiber p hp b e ρ A
        hρ hA hρrad u,
      R.criticalSaddleNegativeBoundaryTrack_regular p hp b e ρ A
        hρ hA hρrad u⟩


-- @@ L4105-4105 verbatim
variable {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}


-- @@ L4107-4130 verbatim
/-- The dynamically flowed negative end and the installed fixed-radius
negative end are joined through their common critical-slice boundary point. -/
def criticalSaddleNegativeFlowAlignmentRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hendK : R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0 ∈ K)
    (hAsafe : A ^ 2 ≤ T.safeTime) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (T.base.flow
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0) (-(A ^ 2)))
      (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ A) := by
  exact (T.negativeFlowTrackRegularZeroPath hendK
    (R.criticalSaddleNegativeBoundaryEnd_fiber p hp b e hρ
      (by simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        sq_pos_of_pos hρ) hρrad)
    (sq_nonneg A) hAsafe).trans
    (R.criticalSaddleNegativeBoundaryRegularZeroPath p hp b e ρ A
      hρ hA hρrad)


-- @@ L4132-4155 verbatim
/-- The dynamically flowed positive end and the installed fixed-radius
positive end are joined through their common critical-slice boundary point. -/
def criticalSaddlePositiveFlowAlignmentRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hendK : R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0 ∈ K)
    (hAsafe : A ^ 2 ≤ T.safeTime) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (T.base.flow
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0) (A ^ 2))
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A) := by
  exact (T.positiveFlowTrackRegularZeroPath hendK
    (R.criticalSaddlePositiveBoundaryEnd_fiber p hp b e hρ
      (by simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        sq_pos_of_pos hρ) hρrad)
    (sq_nonneg A) hAsafe).symm.trans
    (R.criticalSaddlePositiveBoundaryRegularZeroPath p hp b e ρ A
      hρ hA hρrad)


-- @@ L4157-4193 verbatim
/-- Flow an arbitrary critical-slice exterior arc to the negative regular
slice and attach its two dynamically moved endpoints to the installed local
saddle ends. -/
def criticalSaddleNegativeFlowedExteriorRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ A)
      (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ A) := by
  have hend₁K :
      R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0 ∈ K := by
    rw [← η.toPath.source]
    exact hηK 0
  have hend₂K :
      R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0 ∈ K := by
    rw [← η.toPath.target]
    exact hηK 1
  have hnegSafe : |-(A ^ 2)| ≤ T.safeTime := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg A)]
    exact hAsafe
  let ηneg := T.flowSliceRegularZeroPath η hηK hnegSafe
  exact ((R.criticalSaddleNegativeFlowAlignmentRegularZeroPath T p hp
      e₁ b₁ ρ A hρ hA hρrad hend₁K hAsafe).symm.trans ηneg).trans
    (R.criticalSaddleNegativeFlowAlignmentRegularZeroPath T p hp
      e₂ b₂ ρ A hρ hA hρrad hend₂K hAsafe)


-- @@ L4195-4248 verbatim
/-- The same critical exterior arc flows to the positive regular slice; the
critical four-end switch changes the negative `(end, branch)` labels into the
positive `(branch, end)` labels before the endpoint attachments are made. -/
def criticalSaddlePositiveFlowedExteriorRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ A)
      (R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ A) := by
  have hneg₁K :
      R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ 0 ∈ K := by
    rw [← η.toPath.source]
    exact hηK 0
  have hneg₂K :
      R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ 0 ∈ K := by
    rw [← η.toPath.target]
    exact hηK 1
  have hend₁K :
      R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ 0 ∈ K := by
    rw [R.criticalSaddle_boundary_pairing_switch p hp b₁ e₁ ρ]
    exact hneg₁K
  have hend₂K :
      R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ 0 ∈ K := by
    rw [R.criticalSaddle_boundary_pairing_switch p hp b₂ e₂ ρ]
    exact hneg₂K
  have hposSafe : |A ^ 2| ≤ T.safeTime := by
    rw [abs_of_nonneg (sq_nonneg A)]
    exact hAsafe
  let ηflowNeg := T.flowSliceRegularZeroPath η hηK hposSafe
  have ηflow : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (T.base.flow
        (R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ 0) (A ^ 2))
      (T.base.flow
        (R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ 0) (A ^ 2)) := by
    rw [R.criticalSaddle_boundary_pairing_switch p hp b₁ e₁ ρ,
      R.criticalSaddle_boundary_pairing_switch p hp b₂ e₂ ρ]
    exact ηflowNeg
  exact ((R.criticalSaddlePositiveFlowAlignmentRegularZeroPath T p hp
      b₁ e₁ ρ A hρ hA hρrad hend₁K hAsafe).symm.trans ηflow).trans
    (R.criticalSaddlePositiveFlowAlignmentRegularZeroPath T p hp
      b₂ e₂ ρ A hρ hA hρrad hend₂K hAsafe)


-- @@ L4250-4274 verbatim
/-- The transposed negative and positive ends are connected through the
regular zero-surface outside the critical point. -/
def criticalSaddleBoundaryCrossingRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e b ρ A)
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A) := by
  let γneg :=
    (R.criticalSaddleNegativeBoundaryRegularZeroPath p hp e b ρ A
      hρ hA hρrad).symm
  let γpos :=
    R.criticalSaddlePositiveBoundaryRegularZeroPath p hp b e ρ A
      hρ hA hρrad
  have γpos' : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e b ρ 0)
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A) := by
    rw [← R.criticalSaddle_boundary_pairing_switch p hp b e ρ]
    exact γpos
  exact γneg.trans γpos'


-- @@ L4276-4286 verbatim
/-- The underlying ordinary path of the regular-zero boundary crossing. -/
def criticalSaddleBoundaryCrossingPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Path (R.criticalSaddleNegativeBoundaryEnd p hp e b ρ A)
      (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ A) :=
  (R.criticalSaddleBoundaryCrossingRegularZeroPath p hp b e ρ A
    hρ hA hρrad).toPath


-- @@ L4288-4288 verbatim
/-! ## Arbitrary exterior-path transport through the four saddle ends -/


-- @@ L4290-4301 verbatim
/-- A positive local saddle segment as a path with its two boundary ends. -/
def criticalSaddlePositiveSegmentPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Path (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a)
      (R.criticalSaddlePositiveBoundaryEnd p hp b .positive ρ a) where
  toContinuousMap := R.criticalSaddlePositiveSegment p hp b ρ a hρ ha hρrad
  source' := by simp
  target' := by simp


-- @@ L4303-4314 verbatim
/-- A negative local saddle segment as a path with its two boundary ends. -/
def criticalSaddleNegativeSegmentPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    Path (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a)
      (R.criticalSaddleNegativeBoundaryEnd p hp b .positive ρ a) where
  toContinuousMap := R.criticalSaddleNegativeSegment p hp b ρ a hρ ha hρrad
  source' := by simp
  target' := by simp


-- @@ L4316-4327 verbatim
theorem saddlePositiveSegmentParam_ne_zero
    (b : SaddleBranch) (ρ a : ℝ) (ha0 : a ≠ 0) (u : I) :
    saddlePositiveSegmentParam b ρ a u ≠ 0 := by
  intro hzero
  have hquad : morseQuadratic .saddle
      ((saddlePositiveSegmentParam b ρ a u) 0,
        (saddlePositiveSegmentParam b ρ a u) 1) = a ^ 2 := by
    simp [saddlePositiveSegmentParam]
  rw [hzero] at hquad
  have hsquare : a ^ 2 = 0 := by
    simpa [morseQuadratic] using hquad.symm
  exact ha0 (sq_eq_zero_iff.mp hsquare)


-- @@ L4329-4342 verbatim
theorem saddleNegativeSegmentParam_ne_zero
    (b : SaddleBranch) (ρ a : ℝ) (ha0 : a ≠ 0) (u : I) :
    saddleNegativeSegmentParam b ρ a u ≠ 0 := by
  intro hzero
  have hquad : morseQuadratic .saddle
      ((saddleNegativeSegmentParam b ρ a u) 0,
        (saddleNegativeSegmentParam b ρ a u) 1) = -(a ^ 2) := by
    simp [saddleNegativeSegmentParam]
  rw [hzero] at hquad
  have hsquare : a ^ 2 = 0 := by
    have h : (0 : ℝ) = -(a ^ 2) := by
      simpa [morseQuadratic] using hquad
    linarith
  exact ha0 (sq_eq_zero_iff.mp hsquare)


-- @@ L4344-4363 verbatim
/-- A noncritical installed positive saddle segment lies in the spatially
regular zero-surface. -/
def criticalSaddlePositiveSegmentRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (ha0 : a ≠ 0)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ a)
      (R.criticalSaddlePositiveBoundaryEnd p hp b .positive ρ a) where
  toPath := R.criticalSaddlePositiveSegmentPath p hp b ρ a hρ ha hρrad
  range_subset := by
    rintro z ⟨u, rfl⟩
    refine ⟨R.criticalSaddlePositiveSegment_fiber p hp b ρ a
      hρ ha hρrad u, ?_⟩
    exact R.criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero p hp _
      ((norm_saddlePositiveSegmentParam_le b hρ ha u).trans_lt hρrad)
      (saddlePositiveSegmentParam_ne_zero b ρ a ha0 u)


-- @@ L4365-4384 verbatim
/-- A noncritical installed negative saddle segment lies in the spatially
regular zero-surface. -/
def criticalSaddleNegativeSegmentRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (ha0 : a ≠ 0)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ a)
      (R.criticalSaddleNegativeBoundaryEnd p hp b .positive ρ a) where
  toPath := R.criticalSaddleNegativeSegmentPath p hp b ρ a hρ ha hρrad
  range_subset := by
    rintro z ⟨u, rfl⟩
    refine ⟨R.criticalSaddleNegativeSegment_fiber p hp b ρ a
      hρ ha hρrad u, ?_⟩
    exact R.criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero p hp _
      ((norm_saddleNegativeSegmentParam_le b hρ ha u).trans_lt hρrad)
      (saddleNegativeSegmentParam_ne_zero b ρ a ha0 u)


-- @@ L4386-4406 verbatim
/-- Transport an arbitrary exterior regular-zero connector through the
installed saddle boundary.  The exterior path itself is retained unchanged;
only the two canonical boundary tracks are attached. -/
def criticalSaddleTransportExteriorRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b₁ e₁ b₂ e₂ : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp e₁ b₁ ρ A)
      (R.criticalSaddleNegativeBoundaryEnd p hp e₂ b₂ ρ A)) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryEnd p hp b₁ e₁ ρ A)
      (R.criticalSaddlePositiveBoundaryEnd p hp b₂ e₂ ρ A) :=
  ((R.criticalSaddleBoundaryCrossingRegularZeroPath p hp b₁ e₁ ρ A
      hρ hA hρrad).symm.trans η).trans
    (R.criticalSaddleBoundaryCrossingRegularZeroPath p hp b₂ e₂ ρ A
      hρ hA hρrad)


-- @@ L4408-4424 verbatim
/-- Each negative-side local branch gives, after attaching its two boundary
tracks, a regular-zero connector between the two positive-side branch labels.
This is the actual pair-of-pants transposition, with no fixed exterior circle. -/
def criticalSaddlePositiveBranchesRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (e : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2) (hA0 : A ≠ 0)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddlePositiveBoundaryEnd p hp .negative e ρ A)
      (R.criticalSaddlePositiveBoundaryEnd p hp .positive e ρ A) :=
  R.criticalSaddleTransportExteriorRegularZeroPath p hp
    .negative e .positive e ρ A hρ hA hρrad
    (R.criticalSaddleNegativeSegmentRegularZeroPath p hp e ρ A
      hρ hA hA0 hρrad)


-- @@ L4426-4443 verbatim
/-- Dually, each positive-side local branch connects the two transposed
negative-side branch labels through the regular zero-surface. -/
def criticalSaddleNegativeBranchesRegularZeroPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (b : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2) (hA0 : A ≠ 0)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius) :
    SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp .negative b ρ A)
      (R.criticalSaddleNegativeBoundaryEnd p hp .positive b ρ A) :=
  ((R.criticalSaddleBoundaryCrossingRegularZeroPath p hp b .negative ρ A
      hρ hA hρrad).trans
    (R.criticalSaddlePositiveSegmentRegularZeroPath p hp b ρ A
      hρ hA hA0 hρrad)).trans
    (R.criticalSaddleBoundaryCrossingRegularZeroPath p hp b .positive ρ A
      hρ hA hρrad).symm


-- @@ L4445-4445 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L4447-4453 verbatim
/-! ## Exterior-relative saddle splice

The correct global comparison does not identify each complete actual circle
with a fixed Cassini circle.  Each complete loop retains an arbitrary exterior
factor; only the three local factors satisfy the standard saddle correction.
The following theorem cancels those exterior factors at the level of stable
frame classes. -/


-- @@ L4455-4455 verbatim
open scoped unitInterval


-- @@ L4457-4515 verbatim
/-- **Exterior-relative saddle splice.**  Suppose the two incoming complete
frame loops split, through closed free homotopies, into their individual
exterior factors and local factors.  Suppose the outgoing loop uses the
product of the two exterior factors and a local outgoing factor.  Then the
local `+1` relation implies the same splice relation for the complete actual
loops. -/
theorem loopClassZ2_relative_saddle_splice {m : ℕ}
    (γ₁ γ₂ γhat exterior₁ exterior₂ local₁ local₂ localhat :
      C(I, SOGroup m))
    (hγ₁ : γ₁ 0 = γ₁ 1) (hγ₂ : γ₂ 0 = γ₂ 1)
    (hγhat : γhat 0 = γhat 1)
    (hext₁ : exterior₁ 0 = exterior₁ 1)
    (hext₂ : exterior₂ 0 = exterior₂ 1)
    (hloc₁ : local₁ 0 = local₁ 1)
    (hloc₂ : local₂ 0 = local₂ 1)
    (hlochat : localhat 0 = localhat 1)
    (H₁ : ContinuousMap.Homotopy γ₁ (exterior₁ * local₁))
    (H₂ : ContinuousMap.Homotopy γ₂ (exterior₂ * local₂))
    (Hhat : ContinuousMap.Homotopy γhat
      ((exterior₁ * exterior₂) * localhat))
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1))
    (hlocal : loopClassZ2 localhat hlochat =
      loopClassZ2 local₁ hloc₁ + loopClassZ2 local₂ hloc₂ + 1) :
    loopClassZ2 γhat hγhat =
      loopClassZ2 γ₁ hγ₁ + loopClassZ2 γ₂ hγ₂ + 1 := by
  have hextprod : (exterior₁ * exterior₂) 0 =
      (exterior₁ * exterior₂) 1 := by
    change exterior₁ 0 * exterior₂ 0 = exterior₁ 1 * exterior₂ 1
    rw [hext₁, hext₂]
  have hprod₁ : (exterior₁ * local₁) 0 = (exterior₁ * local₁) 1 := by
    change exterior₁ 0 * local₁ 0 = exterior₁ 1 * local₁ 1
    rw [hext₁, hloc₁]
  have hprod₂ : (exterior₂ * local₂) 0 = (exterior₂ * local₂) 1 := by
    change exterior₂ 0 * local₂ 0 = exterior₂ 1 * local₂ 1
    rw [hext₂, hloc₂]
  have hprodhat : ((exterior₁ * exterior₂) * localhat) 0 =
      ((exterior₁ * exterior₂) * localhat) 1 := by
    change (exterior₁ 0 * exterior₂ 0) * localhat 0 =
      (exterior₁ 1 * exterior₂ 1) * localhat 1
    rw [hext₁, hext₂, hlochat]
  have hc₁ : loopClassZ2 γ₁ hγ₁ =
      loopClassZ2 exterior₁ hext₁ + loopClassZ2 local₁ hloc₁ := by
    rw [loopClassZ2_congr hγ₁ hprod₁ H₁ H₁_closed]
    exact loopClassZ2_mul exterior₁ local₁ hext₁ hloc₁ hprod₁
  have hc₂ : loopClassZ2 γ₂ hγ₂ =
      loopClassZ2 exterior₂ hext₂ + loopClassZ2 local₂ hloc₂ := by
    rw [loopClassZ2_congr hγ₂ hprod₂ H₂ H₂_closed]
    exact loopClassZ2_mul exterior₂ local₂ hext₂ hloc₂ hprod₂
  have hchat : loopClassZ2 γhat hγhat =
      (loopClassZ2 exterior₁ hext₁ + loopClassZ2 exterior₂ hext₂) +
        loopClassZ2 localhat hlochat := by
    rw [loopClassZ2_congr hγhat hprodhat Hhat Hhat_closed]
    rw [loopClassZ2_mul (exterior₁ * exterior₂) localhat
      hextprod hlochat hprodhat]
    rw [loopClassZ2_mul exterior₁ exterior₂ hext₁ hext₂ hextprod]
  rw [hc₁, hc₂, hchat, hlocal]
  abel


-- @@ L4517-4543 verbatim
/-- A `SaddleModelContract` supplies exactly the local relation needed by the
exterior-relative splice theorem. -/
theorem loopClassZ2_relative_saddle_splice_of_contract {m : ℕ} (hm : 3 ≤ m)
    (γ₁ γ₂ γhat exterior₁ exterior₂ : C(I, SOGroup m))
    (hγ₁ : γ₁ 0 = γ₁ 1) (hγ₂ : γ₂ 0 = γ₂ 1)
    (hγhat : γhat 0 = γhat 1)
    (hext₁ : exterior₁ 0 = exterior₁ 1)
    (hext₂ : exterior₂ 0 = exterior₂ 1)
    (S : SaddleModelContract)
    (H₁ : ContinuousMap.Homotopy γ₁
      (exterior₁ * S.incoming₁.frame m))
    (H₂ : ContinuousMap.Homotopy γ₂
      (exterior₂ * S.incoming₂.frame m))
    (Hhat : ContinuousMap.Homotopy γhat
      ((exterior₁ * exterior₂) * S.outgoing.frame m))
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    loopClassZ2 γhat hγhat =
      loopClassZ2 γ₁ hγ₁ + loopClassZ2 γ₂ hγ₂ + 1 := by
  exact loopClassZ2_relative_saddle_splice
    γ₁ γ₂ γhat exterior₁ exterior₂
    (S.incoming₁.frame m) (S.incoming₂.frame m) (S.outgoing.frame m)
    hγ₁ hγ₂ hγhat hext₁ hext₂
    (S.incoming₁.frame_closed m) (S.incoming₂.frame_closed m)
    (S.outgoing.frame_closed m) H₁ H₂ Hhat H₁_closed H₂_closed Hhat_closed
    (S.frame_class_splice hm)


-- @@ L4545-4545 verbatim
namespace TamedField


-- @@ L4547-4574 verbatim
/-- Orbit-level form of the exterior-relative saddle splice.  The actual
incoming and outgoing frame loops remain intact; only their local factors are
compared by the saddle contract. -/
theorem orbitFrameClass_relative_saddle_splice {n : ℕ} (hm : 3 ≤ n + 1)
    {Xbefore Xafter : FramedLevelSet n}
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (O₁ O₂ : Vbefore.OrbitIndex) (Ohat : Vafter.OrbitIndex)
    (exterior₁ exterior₂ : C(I, SOGroup (n + 1)))
    (hext₁ : exterior₁ 0 = exterior₁ 1)
    (hext₂ : exterior₂ 0 = exterior₂ 1)
    (S : SaddleModelContract)
    (H₁ : ContinuousMap.Homotopy (Vbefore.orbitFrameLoop O₁)
      (exterior₁ * S.incoming₁.frame (n + 1)))
    (H₂ : ContinuousMap.Homotopy (Vbefore.orbitFrameLoop O₂)
      (exterior₂ * S.incoming₂.frame (n + 1)))
    (Hhat : ContinuousMap.Homotopy (Vafter.orbitFrameLoop Ohat)
      ((exterior₁ * exterior₂) * S.outgoing.frame (n + 1)))
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    Vafter.orbitFrameClass Ohat =
      Vbefore.orbitFrameClass O₁ + Vbefore.orbitFrameClass O₂ + 1 := by
  exact loopClassZ2_relative_saddle_splice_of_contract hm
    (Vbefore.orbitFrameLoop O₁) (Vbefore.orbitFrameLoop O₂)
    (Vafter.orbitFrameLoop Ohat) exterior₁ exterior₂
    (Vbefore.orbitFrameLoop_closed O₁) (Vbefore.orbitFrameLoop_closed O₂)
    (Vafter.orbitFrameLoop_closed Ohat) hext₁ hext₂ S
    H₁ H₂ Hhat H₁_closed H₂_closed Hhat_closed


-- @@ L4576-4576 verbatim
end TamedField


-- @@ L4578-4578 verbatim
/-! ## Tail-aware decomposition of complete saddle ledgers -/


-- @@ L4580-4580 verbatim
namespace TamedField


-- @@ L4582-4582 verbatim
variable {X Y : FramedLevelSet n}

-- @@ L4583-4583 verbatim
variable (V : TamedField X) (W : TamedField Y)


-- @@ L4585-4585 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L4587-4600 verbatim
private theorem saddleOfFn_perm_of_equiv
    {α : Type*} {p q : ℕ}
    (e : Fin p ≃ Fin q)
    (f : Fin p → α) (g : Fin q → α)
    (hfg : ∀ i, f i = g (e i)) :
    (List.ofFn f).Perm (List.ofFn g) := by
  have hpq : p = q := by
    simpa using Fintype.card_congr e
  subst q
  have hfun : f = g ∘ e := by
    funext i
    exact hfg i
  rw [hfun]
  simpa using Equiv.Perm.ofFn_comp_perm e g


-- @@ L4602-4613 verbatim
private theorem saddleEnumeratedValues_perm_of_equiv
    {α β γ : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → γ) (g : β → γ)
    (hfg : ∀ a, f a = g (e a)) :
    (List.ofFn fun i : Fin (Fintype.card α) =>
      f ((Fintype.equivFin α).symm i)).Perm
    (List.ofFn fun i : Fin (Fintype.card β) =>
      g ((Fintype.equivFin β).symm i)) := by
  apply saddleOfFn_perm_of_equiv
    ((Fintype.equivFin α).symm.trans (e.trans (Fintype.equivFin β)))
  intro i
  simpa using hfg ((Fintype.equivFin α).symm i)


-- @@ L4615-4638 verbatim
private theorem saddleEnumeratedOptionValues_perm_cons
    {α γ : Type*} [Fintype α] (head : γ) (f : α → γ) :
    (List.ofFn fun i : Fin (Fintype.card (Option α)) =>
      (Fintype.equivFin (Option α)).symm i |>.elim head f).Perm
    (head :: List.ofFn fun i : Fin (Fintype.card α) =>
      f ((Fintype.equivFin α).symm i)) := by
  let eα := Fintype.equivFin α
  let eOption := Fintype.equivFin (Option α)
  let sigmaEquiv : Fin (Fintype.card (Option α)) ≃
      Fin (Fintype.card α + 1) :=
    eOption.symm.trans
      ((Equiv.optionCongr eα).trans (finSuccEquiv (Fintype.card α)).symm)
  let g : Fin (Fintype.card α + 1) → γ := fun i =>
    (Equiv.optionCongr eα.symm
      (finSuccEquiv (Fintype.card α) i)).elim head f
  have hperm := saddleOfFn_perm_of_equiv sigmaEquiv
    (fun i : Fin (Fintype.card (Option α)) =>
      (eOption.symm i).elim head f) g (by
        intro i
        cases hO : eOption.symm i <;>
          simp [sigmaEquiv, g, hO, Equiv.optionCongr])
  refine hperm.trans (List.Perm.of_eq ?_)
  rw [List.ofFn_succ]
  congr 1


-- @@ L4640-4674 verbatim
/-- General head-insertion adapter, with an arbitrary distinguished frame
class rather than the class-one special case used by definite births. -/
theorem selectedFrameLedger_perm_cons_of_option_equiv_at
    (A B : Set (Set E)) (β : ZMod 2)
    (e : Option (V.SelectedOrbitIndex A) ≃ W.SelectedOrbitIndex B)
    (hnone : W.orbitFrameClass (e none).1 = β)
    (hsome : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e (some O)).1) :
    (W.selectedFrameLedger B).Perm (β :: V.selectedFrameLedger A) := by
  classical
  let f : Option (V.SelectedOrbitIndex A) → ZMod 2 := fun O =>
    O.elim β (fun P => V.orbitFrameClass P.1)
  let g : W.SelectedOrbitIndex B → ZMod 2 := fun O =>
    W.orbitFrameClass O.1
  have hequiv :
      (List.ofFn fun i : Fin
          (Fintype.card (Option (V.SelectedOrbitIndex A))) =>
        f ((Fintype.equivFin (Option (V.SelectedOrbitIndex A))).symm i)).Perm
      (W.selectedFrameLedger B) := by
    unfold selectedFrameLedger
    apply saddleEnumeratedValues_perm_of_equiv e f g
    intro O
    cases O with
    | none => exact hnone.symm
    | some O => exact hsome O
  have hcons :
      (List.ofFn fun i : Fin
          (Fintype.card (Option (V.SelectedOrbitIndex A))) =>
        f ((Fintype.equivFin (Option (V.SelectedOrbitIndex A))).symm i)).Perm
      (β :: V.selectedFrameLedger A) := by
    unfold selectedFrameLedger
    simpa [f] using saddleEnumeratedOptionValues_perm_cons
      (α := V.SelectedOrbitIndex A) β
      (fun O => V.orbitFrameClass O.1)
  exact hequiv.symm.trans hcons


-- @@ L4676-4697 verbatim
/-- Put one arbitrary distinguished selected orbit at the head of its actual
frame ledger, leaving the literal set-theoretic complement as tail. -/
theorem selectedFrameLedger_perm_cons_of_distinguished_at
    (B : Set (Set E)) (new : V.SelectedOrbitIndex B) :
    (V.selectedFrameLedger B).Perm
      (V.orbitFrameClass new.1 ::
        V.selectedFrameLedger
          (B \ {((new.1 : V.OrbitIndex) : Set E)})) := by
  let e : V.SelectedOrbitIndex
        (B \ {((new.1 : V.OrbitIndex) : Set E)}) ≃
      {O : V.SelectedOrbitIndex B // O ≠ new} :=
    V.selectedOrbitIndexSdiffSingletonEquiv B new
  let eOption : Option (V.SelectedOrbitIndex
        (B \ {((new.1 : V.OrbitIndex) : Set E)})) ≃
      V.SelectedOrbitIndex B :=
    (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe new)
  apply V.selectedFrameLedger_perm_cons_of_option_equiv_at V
    (B \ {((new.1 : V.OrbitIndex) : Set E)}) B
    (V.orbitFrameClass new.1) eOption
  · rfl
  · intro O
    rfl


-- @@ L4699-4699 verbatim
end TamedField


-- @@ L4701-4718 verbatim
/-- Complete saddle component decomposition: two distinguished components on
one side, one on the other, and a framed transport of exactly the remaining
components.  Its exterior ledger is retained verbatim as the common tail. -/
structure SaddleOrbitLedgerDecomposition {n : ℕ}
    {Xbefore Xafter : FramedLevelSet n}
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (before after : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))) where
  incoming₁ : Vbefore.SelectedOrbitIndex before
  incoming₂ : Vbefore.SelectedOrbitIndex before
  incoming_ne : incoming₁ ≠ incoming₂
  outgoing : Vafter.SelectedOrbitIndex after
  exteriorTransport : Vbefore.SelectedDeltaTransport Vafter
    ((before \ {((incoming₁.1 : Vbefore.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))}) \
      {((incoming₂.1 : Vbefore.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))})
    (after \ {((outgoing.1 : Vafter.OrbitIndex) :
      Set (EuclideanSpace ℝ (Fin (n + 1))))})


-- @@ L4720-4720 verbatim
namespace SaddleOrbitLedgerDecomposition


-- @@ L4722-4722 verbatim
variable {Xbefore Xafter : FramedLevelSet n}

-- @@ L4723-4723 verbatim
variable {Vbefore : TamedField Xbefore} {Vafter : TamedField Xafter}

-- @@ L4724-4724 verbatim
variable {before after : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))}


-- @@ L4726-4738 verbatim
/-- The second distinguished orbit, viewed after removing the first one. -/
def incoming₂Exterior
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter before after) :
    Vbefore.SelectedOrbitIndex
      (before \ {((D.incoming₁.1 : Vbefore.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))}) := by
  refine ⟨D.incoming₂.1, D.incoming₂.2, ?_⟩
  rw [Set.mem_singleton_iff]
  intro hsets
  apply D.incoming_ne
  apply Subtype.ext
  apply Subtype.ext
  exact hsets.symm


-- @@ L4740-4758 verbatim
/-- The complete two-component-side ledger is the two local frame classes
followed by the actual exterior tail, up to its arbitrary enumeration. -/
theorem before_perm
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter before after) :
    (Vbefore.selectedFrameLedger before).Perm
      (Vbefore.orbitFrameClass D.incoming₁.1 ::
        Vbefore.orbitFrameClass D.incoming₂.1 ::
          Vbefore.selectedFrameLedger
            ((before \ {((D.incoming₁.1 : Vbefore.OrbitIndex) :
                Set (EuclideanSpace ℝ (Fin (n + 1))))}) \
              {((D.incoming₂.1 : Vbefore.OrbitIndex) :
                Set (EuclideanSpace ℝ (Fin (n + 1))))})) := by
  have h₁ := Vbefore.selectedFrameLedger_perm_cons_of_distinguished_at
    before D.incoming₁
  have h₂ := Vbefore.selectedFrameLedger_perm_cons_of_distinguished_at
    (before \ {((D.incoming₁.1 : Vbefore.OrbitIndex) :
      Set (EuclideanSpace ℝ (Fin (n + 1))))})
    D.incoming₂Exterior
  exact h₁.trans (h₂.cons _)


-- @@ L4760-4774 verbatim
/-- The complete one-component-side ledger has its local frame class followed
by the same transported exterior tail. -/
theorem after_perm
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter before after) :
    (Vafter.selectedFrameLedger after).Perm
      (Vafter.orbitFrameClass D.outgoing.1 ::
        Vbefore.selectedFrameLedger
          ((before \ {((D.incoming₁.1 : Vbefore.OrbitIndex) :
              Set (EuclideanSpace ℝ (Fin (n + 1))))}) \
            {((D.incoming₂.1 : Vbefore.OrbitIndex) :
              Set (EuclideanSpace ℝ (Fin (n + 1))))})) := by
  have hhead := Vafter.selectedFrameLedger_perm_cons_of_distinguished_at
    after D.outgoing
  have htail := D.exteriorTransport.selectedFrameLedger_perm
  exact hhead.trans (htail.symm.cons _)


-- @@ L4776-4786 verbatim
/-- A geometric two-to-one saddle decomposition plus the already established
actual frame splice produces the required tail-aware merge move. -/
theorem toIndexedMorseLedgerMerge
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter before after)
    (hsplice : Vafter.orbitFrameClass D.outgoing.1 =
      Vbefore.orbitFrameClass D.incoming₁.1 +
        Vbefore.orbitFrameClass D.incoming₂.1 + 1) :
    IndexedMorseLedgerMove .saddle
      (Vbefore.selectedFrameLedger before)
      (Vafter.selectedFrameLedger after) := by
  exact .saddleMerge _ _ _ _ hsplice D.before_perm D.after_perm


-- @@ L4788-4798 verbatim
/-- The identical decomposition read chronologically backwards produces the
tail-aware saddle split move. -/
theorem toIndexedMorseLedgerSplit
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter before after)
    (hsplice : Vafter.orbitFrameClass D.outgoing.1 =
      Vbefore.orbitFrameClass D.incoming₁.1 +
        Vbefore.orbitFrameClass D.incoming₂.1 + 1) :
    IndexedMorseLedgerMove .saddle
      (Vafter.selectedFrameLedger after)
      (Vbefore.selectedFrameLedger before) := by
  exact .saddleSplit _ _ _ _ hsplice D.after_perm D.before_perm


-- @@ L4800-4800 verbatim
end SaddleOrbitLedgerDecomposition


-- @@ L4802-4802 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L4803-4803 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L4805-4805 verbatim
namespace PositiveEventLedgerMoveData


-- @@ L4807-4807 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L4808-4808 verbatim
variable {P : MorsePosition C.cobordism}

-- @@ L4809-4809 verbatim
variable {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L4811-4835 verbatim
/-- Package a two-to-one actual orbit decomposition as the chronological
positive-sheet saddle merge consumed by the global event schedule. -/
def saddleMerge_of_decomposition
    (hindex : (P.eventModel t ht).index = .saddle)
    (Vbefore : TamedField
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).before (P.eventBracket t ht).before_regular))
    (Vafter : TamedField
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).after (P.eventBracket t ht).after_regular))
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter
      ((C.sliceSign (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveOrbitCollection Vbefore)
      ((C.sliceSign (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveOrbitCollection Vafter))
    (hsplice : Vafter.orbitFrameClass D.outgoing.1 =
      Vbefore.orbitFrameClass D.incoming₁.1 +
        Vbefore.orbitFrameClass D.incoming₂.1 + 1) :
    PositiveEventLedgerMoveData C P t ht where
  beforeField := Vbefore
  afterField := Vafter
  move := by
    rw [hindex]
    simpa only [FiberSign.positiveFrameLedger] using
      D.toIndexedMorseLedgerMerge hsplice


-- @@ L4837-4862 verbatim
/-- Package a one-to-two decomposition as the reverse chronological saddle
split.  The decomposition is oriented from its two-component side back to its
one-component side, while the resulting event move is chronological. -/
def saddleSplit_of_decomposition
    (hindex : (P.eventModel t ht).index = .saddle)
    (Vbefore : TamedField
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).before (P.eventBracket t ht).before_regular))
    (Vafter : TamedField
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).after (P.eventBracket t ht).after_regular))
    (D : SaddleOrbitLedgerDecomposition Vafter Vbefore
      ((C.sliceSign (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveOrbitCollection Vafter)
      ((C.sliceSign (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveOrbitCollection Vbefore))
    (hsplice : Vbefore.orbitFrameClass D.outgoing.1 =
      Vafter.orbitFrameClass D.incoming₁.1 +
        Vafter.orbitFrameClass D.incoming₂.1 + 1) :
    PositiveEventLedgerMoveData C P t ht where
  beforeField := Vbefore
  afterField := Vafter
  move := by
    rw [hindex]
    simpa only [FiberSign.positiveFrameLedger] using
      D.toIndexedMorseLedgerSplit hsplice


-- @@ L4864-4864 verbatim
end PositiveEventLedgerMoveData


-- @@ L4866-4866 verbatim
end Submission
