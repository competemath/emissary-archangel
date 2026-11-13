import Submission.CompactSaddleConfiguration
import Submission.ConcreteZeroPairCassiniTwist


-- @@ L4-13 verbatim
/-!
# Twisting the already compact Cassini saddle

This file applies the two-row Cassini twist to `CompactSaddle.eventMap`
itself.  In the positive stable range the two selected rows vanish on the
common background, so this operation preserves the spatially constant tail
literally.  The first checkpoint below records smoothness, time collars, and
that exact background identity; the zero-set comparison is developed in the
next section.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace Submission

-- @@ L20-20 verbatim
namespace ConcreteZeroPairCompactTwist


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L25-25 verbatim
variable (m : ℕ)


-- @@ L27-27 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (m + 4))

-- @@ L28-28 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L29-29 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L31-32 verbatim
abbrev rowZero : Fin (m + 2) :=
  ConcreteZeroPairCassiniTwist.rowZero m


-- @@ L34-35 verbatim
abbrev rowOne : Fin (m + 2) :=
  ConcreteZeroPairCassiniTwist.rowOne m


-- @@ L37-41 verbatim
/-- Squared norm of the two rows of the compact Cassini map that carry the
complex twist. -/
def transverseSq (v : A) : ℝ :=
  CompactSaddle.eventMap m v (rowZero m) ^ 2 +
    CompactSaddle.eventMap m v (rowOne m) ^ 2


-- @@ L43-46 verbatim
/-- The same bounded, second-order desingularizing shift as in the polynomial
model, now measured on the compact base map. -/
def twistShift (v : A) : ℝ :=
  transverseSq m v / (2 * (1 + transverseSq m v))


-- @@ L48-49 verbatim
lemma transverseSq_nonneg (v : A) : 0 ≤ transverseSq m v := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)


-- @@ L51-54 verbatim
lemma twistShift_nonneg (v : A) : 0 ≤ twistShift m v := by
  have hden : 0 ≤ 2 * (1 + transverseSq m v) := by
    nlinarith [transverseSq_nonneg m v]
  exact div_nonneg (transverseSq_nonneg m v) hden


-- @@ L56-60 verbatim
lemma twistShift_lt_half (v : A) : twistShift m v < 1 / 2 := by
  have hr := transverseSq_nonneg m v
  have hden : 0 < 2 * (1 + transverseSq m v) := by positivity
  rw [twistShift, div_lt_iff₀ hden]
  linarith


-- @@ L62-76 verbatim
/-- Direct twist of the already spatially compact Cassini event map. -/
def eventMap (v : A) : F :=
  WithLp.toLp 2 fun i =>
    if i = rowZero m then
      (ConcreteZeroPairCassiniTwist.twistRe m v + twistShift m v) *
          CompactSaddle.eventMap m v (rowZero m) -
        ConcreteZeroPairCassiniTwist.twistIm m v *
          CompactSaddle.eventMap m v (rowOne m)
    else if i = rowOne m then
      ConcreteZeroPairCassiniTwist.twistIm m v *
          CompactSaddle.eventMap m v (rowZero m) +
        (ConcreteZeroPairCassiniTwist.twistRe m v + twistShift m v) *
          CompactSaddle.eventMap m v (rowOne m)
    else
      CompactSaddle.eventMap m v i


-- @@ L78-85 verbatim
@[simp] lemma eventMap_apply_rowZero (v : A) :
    eventMap m v (rowZero m) =
      (ConcreteZeroPairCassiniTwist.twistRe m v + twistShift m v) *
          CompactSaddle.eventMap m v (rowZero m) -
        ConcreteZeroPairCassiniTwist.twistIm m v *
          CompactSaddle.eventMap m v (rowOne m) := by
  simp [eventMap, ConcreteZeroPairCassiniTwist.rowZero,
    ConcreteZeroPairCassiniTwist.rowOne]


-- @@ L87-94 verbatim
@[simp] lemma eventMap_apply_rowOne (v : A) :
    eventMap m v (rowOne m) =
      ConcreteZeroPairCassiniTwist.twistIm m v *
          CompactSaddle.eventMap m v (rowZero m) +
        (ConcreteZeroPairCassiniTwist.twistRe m v + twistShift m v) *
          CompactSaddle.eventMap m v (rowOne m) := by
  simp [eventMap, ConcreteZeroPairCassiniTwist.rowZero,
    ConcreteZeroPairCassiniTwist.rowOne]


-- @@ L96-99 verbatim
lemma eventMap_apply_of_ne {i : Fin (m + 2)}
    (hi₀ : i ≠ rowZero m) (hi₁ : i ≠ rowOne m) (v : A) :
    eventMap m v i = CompactSaddle.eventMap m v i := by
  simp [eventMap, hi₀, hi₁]


-- @@ L101-104 verbatim
lemma contDiff_compactEventMap_coord (i : Fin (m + 2)) :
    ContDiff ℝ ∞ (fun v => CompactSaddle.eventMap m v i) := by
  exact (EuclideanSpace.proj i : F →L[ℝ] ℝ).contDiff.comp
    (CompactSaddle.contDiff_eventMap m)


-- @@ L106-108 verbatim
lemma contDiff_transverseSq : ContDiff ℝ ∞ (transverseSq m) := by
  exact ((contDiff_compactEventMap_coord m (rowZero m)).pow 2).add
    ((contDiff_compactEventMap_coord m (rowOne m)).pow 2)


-- @@ L110-113 verbatim
lemma one_add_transverseSq_ne_zero (v : A) :
    1 + transverseSq m v ≠ 0 := by
  have hr := transverseSq_nonneg m v
  linarith


-- @@ L115-121 verbatim
lemma contDiff_twistShift : ContDiff ℝ ∞ (twistShift m) := by
  have hden : ContDiff ℝ ∞ (fun v : A => 2 * (1 + transverseSq m v)) :=
    contDiff_const.mul (contDiff_const.add (contDiff_transverseSq m))
  have hden0 : ∀ v : A, 2 * (1 + transverseSq m v) ≠ 0 := by
    intro v
    exact mul_ne_zero (by norm_num) (one_add_transverseSq_ne_zero m v)
  exact (contDiff_transverseSq m).div hden hden0


-- @@ L123-143 verbatim
theorem contDiff_eventMap : ContDiff ℝ ∞ (eventMap m) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi₀ : i = rowZero m
  · subst i
    simp only [eventMap_apply_rowZero]
    exact ((ConcreteZeroPairCassiniTwist.contDiff_twistRe m).add
        (contDiff_twistShift m)).mul
          (contDiff_compactEventMap_coord m (rowZero m)) |>.sub
      ((ConcreteZeroPairCassiniTwist.contDiff_twistIm m).mul
        (contDiff_compactEventMap_coord m (rowOne m)))
  · by_cases hi₁ : i = rowOne m
    · subst i
      simp only [eventMap_apply_rowOne]
      exact (ConcreteZeroPairCassiniTwist.contDiff_twistIm m).mul
          (contDiff_compactEventMap_coord m (rowZero m)) |>.add
        (((ConcreteZeroPairCassiniTwist.contDiff_twistRe m).add
          (contDiff_twistShift m)).mul
            (contDiff_compactEventMap_coord m (rowOne m)))
    · simpa only [eventMap_apply_of_ne m hi₀ hi₁] using
        contDiff_compactEventMap_coord m i


-- @@ L145-145 verbatim
/-! ## Exact agreement on the compact saddle core -/


-- @@ L147-173 verbatim
lemma eventMap_eq_polynomial_of_cutoff_eq_zero {v : A}
    (hc : CompactSaddle.cutoff (initCLM (m + 3) v) = 0) :
    eventMap m v = ConcreteZeroPairCassiniTwist.eventMap m v := by
  have hbase : CompactSaddle.eventMap m v =
      StandardSaddle.eventMap m v := by
    simp [CompactSaddle.eventMap, hc]
  have hsq : transverseSq m v =
      ConcreteZeroPairCassiniTwist.transverseSq m v := by
    simp only [transverseSq,
      ConcreteZeroPairCassiniTwist.transverseSq, hbase]
  have hshift : twistShift m v =
      ConcreteZeroPairCassiniTwist.twistShift m v := by
    simp only [twistShift, ConcreteZeroPairCassiniTwist.twistShift, hsq]
  ext i
  by_cases hi₀ : i = rowZero m
  · subst i
    rw [eventMap_apply_rowZero,
      ConcreteZeroPairCassiniTwist.eventMap_apply_rowZero,
      hbase, hshift]
  · by_cases hi₁ : i = rowOne m
    · subst i
      rw [eventMap_apply_rowOne,
        ConcreteZeroPairCassiniTwist.eventMap_apply_rowOne,
        hbase, hshift]
    · rw [eventMap_apply_of_ne m hi₀ hi₁,
        ConcreteZeroPairCassiniTwist.eventMap_apply_of_ne m hi₀ hi₁,
        hbase]


-- @@ L175-179 verbatim
lemma eventMap_eq_polynomial_of_normSq_le_four {v : A}
    (hv : CompactBirth.normSq (initCLM (m + 3) v) ≤ 4) :
    eventMap m v = ConcreteZeroPairCassiniTwist.eventMap m v :=
  eventMap_eq_polynomial_of_cutoff_eq_zero m
    (CompactSaddle.cutoff_eq_zero hv)


-- @@ L181-196 verbatim
/-- At every point of the intended Cassini surface, the compact direct twist
is literally the already-verified polynomial twist on a whole neighborhood.
In particular its complete first jet there is unchanged. -/
lemma eventMap_eventuallyEq_polynomial_of_standard_zero {v : A}
    (hv : StandardSaddle.eventMap m v = 0) :
    eventMap m =ᶠ[nhds v] ConcreteZeroPairCassiniTwist.eventMap m := by
  have hslt : CompactBirth.normSq (initCLM (m + 3) v) < 4 :=
    lt_of_le_of_lt (CompactSaddle.standard_event_normSq_le_three m hv)
      (by norm_num)
  have hopen : IsOpen
      {w : A | CompactBirth.normSq (initCLM (m + 3) w) < 4} :=
    isOpen_lt
      (CompactBirth.contDiff_normSq.continuous.comp
        (initCLM (m + 3)).continuous) continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hslt) fun w hw =>
    eventMap_eq_polynomial_of_normSq_le_four m hw.le


-- @@ L198-201 verbatim
lemma eventMap_eq_zero_of_standard_zero (hm : 0 < m) {v : A}
    (hv : StandardSaddle.eventMap m v = 0) : eventMap m v = 0 := by
  rw [(eventMap_eventuallyEq_polynomial_of_standard_zero m hv).eq_of_nhds]
  exact (ConcreteZeroPairCassiniTwist.eventMap_eq_zero_iff m hm v).mpr hv


-- @@ L203-209 verbatim
lemma eventMap_regular_at_standard_zero (hm : 0 < m) {v : A}
    (hv : StandardSaddle.eventMap m v = 0) :
    Function.Surjective (fderiv ℝ (eventMap m) v) := by
  have htwisted : ConcreteZeroPairCassiniTwist.eventMap m v = 0 :=
    (ConcreteZeroPairCassiniTwist.eventMap_eq_zero_iff m hm v).mpr hv
  rw [(eventMap_eventuallyEq_polynomial_of_standard_zero m hv).fderiv_eq]
  exact ConcreteZeroPairCassiniTwist.eventMap_regular m hm htwisted


-- @@ L211-211 verbatim
/-! ## Exact time collars -/


-- @@ L213-233 verbatim
lemma eventMap_spaceTime_eq_of_compact_eq (x : E) (t s : ℝ)
    (hbase : CompactSaddle.eventMap m (spaceTime x t) =
      CompactSaddle.eventMap m (spaceTime x s)) :
    eventMap m (spaceTime x t) = eventMap m (spaceTime x s) := by
  have hre := ConcreteZeroPairCassiniTwist.twistRe_spaceTime m x t s
  have him := ConcreteZeroPairCassiniTwist.twistIm_spaceTime m x t s
  have hsq : transverseSq m (spaceTime x t) =
      transverseSq m (spaceTime x s) := by
    simp only [transverseSq, hbase]
  have hshift : twistShift m (spaceTime x t) =
      twistShift m (spaceTime x s) := by
    simp only [twistShift, hsq]
  ext i
  by_cases hi₀ : i = rowZero m
  · subst i
    simp only [eventMap_apply_rowZero, hre, him, hshift, hbase]
  · by_cases hi₁ : i = rowOne m
    · subst i
      simp only [eventMap_apply_rowOne, hre, him, hshift, hbase]
    · rw [eventMap_apply_of_ne m hi₀ hi₁,
        eventMap_apply_of_ne m hi₀ hi₁, hbase]


-- @@ L235-240 verbatim
lemma eventMap_collar_zero (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    eventMap m (spaceTime x t) = eventMap m (spaceTime x 0) := by
  apply eventMap_spaceTime_eq_of_compact_eq m x t 0
  rw [CompactSaddle.eventMap_spaceTime, CompactSaddle.eventMap_spaceTime,
    StandardSaddle.height_of_le_quarter ht,
    StandardSaddle.height_of_le_quarter (by norm_num)]


-- @@ L242-247 verbatim
lemma eventMap_collar_one (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    eventMap m (spaceTime x t) = eventMap m (spaceTime x 1) := by
  apply eventMap_spaceTime_eq_of_compact_eq m x t 1
  rw [CompactSaddle.eventMap_spaceTime, CompactSaddle.eventMap_spaceTime,
    StandardSaddle.height_of_threeQuarter_le ht,
    StandardSaddle.height_of_threeQuarter_le (by norm_num)]


-- @@ L249-249 verbatim
/-! ## Literal preservation of the compact background -/


-- @@ L251-254 verbatim
@[simp] lemma background_apply_rowZero :
    CompactSaddle.background m (rowZero m) = 0 := by
  simpa [ConcreteZeroPairCassiniTwist.rowZero] using
    CompactSaddle.background_apply_castSucc m (0 : Fin (m + 1))


-- @@ L256-260 verbatim
@[simp] lemma background_apply_rowOne (hm : 0 < m) :
    CompactSaddle.background m (rowOne m) = 0 := by
  let j : Fin (m + 1) := ⟨1, by omega⟩
  simpa [j, ConcreteZeroPairCassiniTwist.rowOne] using
    CompactSaddle.background_apply_castSucc m j


-- @@ L262-281 verbatim
lemma eventMap_eq_background_of_compact_eq_background
    (hm : 0 < m) {v : A}
    (hv : CompactSaddle.eventMap m v = CompactSaddle.background m) :
    eventMap m v = CompactSaddle.background m := by
  have h₀ : CompactSaddle.eventMap m v (rowZero m) = 0 := by
    rw [hv]
    exact background_apply_rowZero m
  have h₁ : CompactSaddle.eventMap m v (rowOne m) = 0 := by
    rw [hv]
    exact background_apply_rowOne m hm
  ext i
  by_cases hi₀ : i = rowZero m
  · subst i
    rw [eventMap_apply_rowZero, h₀, h₁]
    simpa using (background_apply_rowZero m).symm
  · by_cases hi₁ : i = rowOne m
    · subst i
      rw [eventMap_apply_rowOne, h₀, h₁]
      simpa using (background_apply_rowOne m hm).symm
    · rw [eventMap_apply_of_ne m hi₀ hi₁, hv]


-- @@ L283-294 verbatim
/-- Outside the radius-three spatial ball, the direct twist still equals the
same compact background exactly. -/
theorem eventMap_spatialFlatOutside (hm : 0 < m) {v : A}
    (hv : 3 ≤ ‖initCLM (m + 3) v‖) :
    eventMap m v = CompactSaddle.background m := by
  have hs : 9 ≤ CompactBirth.normSq (initCLM (m + 3) v) := by
    rw [CompactBirth.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (initCLM (m + 3) v)]
  have hc : CompactSaddle.cutoff (initCLM (m + 3) v) = 1 :=
    CompactSaddle.cutoff_eq_one hs
  apply eventMap_eq_background_of_compact_eq_background m hm
  simp [CompactSaddle.eventMap, hc]


-- @@ L296-296 verbatim
end ConcreteZeroPairCompactTwist

-- @@ L297-297 verbatim
end Submission
