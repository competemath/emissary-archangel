import Submission.ProductionMorseChronologicalWindow


-- @@ L3-12 verbatim
/-!
# Local excision for production definite Morse events

The local cover stored by `StandardMorseEventAt` sees the complete zero fiber
in a fixed ambient ball.  On a definite level the exact quadratic time model
then says that the covered fiber is empty on one side of the critical value
and is a single orbit on the other side.  The final section applies these
route-independent statements to the chronological embedded shrink of the
production package.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Metric

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L25-25 verbatim
namespace StandardMorseEventAt


-- @@ L27-27 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L28-28 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L30-36 verbatim
/-- The part of a spatial slice which lies in the event's complete-cover
ball. -/
def coveredSliceFiber
    (M : StandardMorseEventAt (n := n) C center) (s : ℝ) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | dist (cobSpaceTime (n := n) x s) center < M.fiberCoverRadius ∧
    C.G (cobSpaceTime (n := n) x s) = 0}


-- @@ L38-44 verbatim
theorem exists_param_of_mem_coveredSliceFiber
    (M : StandardMorseEventAt (n := n) C center) {s : ℝ}
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ M.coveredSliceFiber s) :
    ∃ u : E₂, ‖u‖ < M.radius ∧
      M.param u = cobSpaceTime (n := n) x s := by
  exact M.covers_fiber.choose_spec.2 _ hx.1 hx.2


-- @@ L46-51 verbatim
/-- Any vector in the two-dimensional Euclidean Morse chart is recovered
from its two coordinates. -/
theorem pairToMorseParam_coordinates (u : E₂) :
    pairToMorseParam (u 0, u 1) = u := by
  ext i
  fin_cases i <;> simp


-- @@ L53-58 verbatim
theorem norm_sq_eq_coordinates (u : E₂) :
    ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
  calc
    ‖u‖ ^ 2 = ‖pairToMorseParam (u 0, u 1)‖ ^ 2 := by
      rw [pairToMorseParam_coordinates]
    _ = (u 0) ^ 2 + (u 1) ^ 2 := norm_pairToMorseParam_sq _


-- @@ L60-94 verbatim
/-- On either definite model, the covered zero fiber at the critical time is
the critical center itself.  This is the local fact which prevents a regular
exterior flow line from entering the cover ball at its midpoint. -/
theorem definite_coveredSliceFiber_at_critical_eq_center
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .minimum ∨ M.index = .maximum)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ M.coveredSliceFiber (tcoord center)) :
    cobSpaceTime (n := n) x (tcoord center) = center := by
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center := by
    rw [huv, tcoord_spaceTime]
  have hq : morseQuadratic M.index (u 0, u 1) = 0 := by
    rw [htime] at hs
    linarith
  have hu0 : u = 0 := by
    rcases hindex with hmin | hmax
    · rw [hmin] at hq
      simp only [morseQuadratic] at hq
      have h0 : u 0 = 0 := by
        nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have h1 : u 1 = 0 := by
        nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      ext i
      fin_cases i <;> simp [h0, h1]
    · rw [hmax] at hq
      simp only [morseQuadratic] at hq
      have h0 : u 0 = 0 := by
        nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have h1 : u 1 = 0 := by
        nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      ext i
      fin_cases i <;> simp [h0, h1]
  rw [← huv, hu0, M.param_zero]


-- @@ L96-98 verbatim
/-- Regard the two Morse coordinates as one complex number. -/
def morseParamComplex (u : E₂) : ℂ :=
  ⟨u 0, u 1⟩


-- @@ L100-101 verbatim
@[simp] theorem morseParamComplex_re (u : E₂) :
    (morseParamComplex u).re = u 0 := rfl


-- @@ L103-104 verbatim
@[simp] theorem morseParamComplex_im (u : E₂) :
    (morseParamComplex u).im = u 1 := rfl


-- @@ L106-111 verbatim
theorem norm_morseParamComplex (u : E₂) :
    ‖morseParamComplex u‖ = ‖u‖ := by
  rw [Complex.norm_def, EuclideanSpace.norm_eq]
  congr 1
  simp [Complex.normSq, morseParamComplex, Fin.sum_univ_two, sq_abs]
  ring


-- @@ L113-125 verbatim
/-- Every point of a positive-radius Morse circle has the literal polar
parameter given by its complex argument. -/
theorem eq_definiteCircleParam_arg {u : E₂} {a : ℝ}
    (hnorm : ‖u‖ = a) :
    u = definiteCircleParam a (Complex.arg (morseParamComplex u)) := by
  let z := morseParamComplex u
  have hre := Complex.norm_mul_cos_arg z
  have him := Complex.norm_mul_sin_arg z
  rw [norm_morseParamComplex, hnorm] at hre him
  ext i
  fin_cases i
  · simpa [z] using hre.symm
  · simpa [z] using him.symm


-- @@ L127-142 verbatim
/-- A minimum has no covered local fiber below its critical value. -/
theorem minimum_coveredSliceFiber_before_eq_empty
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) :
    M.coveredSliceFiber (tcoord center - a ^ 2) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center - a ^ 2 := by
    rw [huv, tcoord_spaceTime]
  rw [hindex] at htime
  simp only [morseQuadratic] at htime
  rw [htime] at hs
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_pos_of_pos ha]


-- @@ L144-159 verbatim
/-- A maximum has no covered local fiber above its critical value. -/
theorem maximum_coveredSliceFiber_after_eq_empty
    (M : StandardMorseEventAt (n := n) C center)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) :
    M.coveredSliceFiber (tcoord center + a ^ 2) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center + a ^ 2 := by
    rw [huv, tcoord_spaceTime]
  rw [hindex] at htime
  simp only [morseQuadratic] at htime
  rw [htime] at hs
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_pos_of_pos ha]


-- @@ L161-161 verbatim
namespace EmbeddedShrink


-- @@ L163-163 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L165-180 verbatim
/-- The spatial definite circle arc from angle zero to an arbitrary real
angle.  This avoids choosing a representative in `[0,2π]`. -/
def definiteSpatialAnglePath (T : M.EmbeddedShrink)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius) (theta : ℝ) :
    C(I, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun u := spacePart
    (M.definiteCircle a (theta * (u : ℝ)))
  continuous_toFun := by
    apply continuous_spacePart.comp
    rw [continuous_iff_continuousAt]
    intro u
    apply (T.param_differentiableAt _ ?_).continuousAt.comp'
    · unfold definiteCircleParam pairToMorseParam
      fun_prop
    · rw [norm_definiteCircleParam ha.le]
      exact har


-- @@ L182-186 verbatim
@[simp] theorem definiteSpatialAnglePath_zero (T : M.EmbeddedShrink)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius) (theta : ℝ) :
    T.definiteSpatialAnglePath a ha har theta 0 =
      spacePart (M.definiteCircle a 0) := by
  simp [definiteSpatialAnglePath]


-- @@ L188-192 verbatim
@[simp] theorem definiteSpatialAnglePath_one (T : M.EmbeddedShrink)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius) (theta : ℝ) :
    T.definiteSpatialAnglePath a ha har theta 1 =
      spacePart (M.definiteCircle a theta) := by
  simp [definiteSpatialAnglePath]


-- @@ L194-207 verbatim
theorem minimumDefiniteSpatialPoint_mem_fiber (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) (theta : ℝ) :
    spacePart (M.definiteCircle a theta) ∈
      (T.minimumPositiveSlice a hreg).fiber := by
  rw [minimumPositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime (n := n)
    (spacePart (M.definiteCircle a theta))
    (tcoord center + a ^ 2)) = 0
  rw [← M.minimumCircle_time hindex ha.le
      (har.trans_le T.radius_le),
    spaceTime_spacePart]
  exact M.definiteCircle_fiber ha.le (har.trans_le T.radius_le)


-- @@ L209-222 verbatim
theorem maximumDefiniteSpatialPoint_mem_fiber (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) (theta : ℝ) :
    spacePart (M.definiteCircle a theta) ∈
      (T.maximumNegativeSlice a hreg).fiber := by
  rw [maximumNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime (n := n)
    (spacePart (M.definiteCircle a theta))
    (tcoord center - a ^ 2)) = 0
  rw [← M.maximumCircle_time hindex ha.le
      (har.trans_le T.radius_le),
    spaceTime_spacePart]
  exact M.definiteCircle_fiber ha.le (har.trans_le T.radius_le)


-- @@ L224-236 verbatim
theorem minimumDefiniteSpatialPoint_mem_same_orbit
    (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.minimumPositiveSlice a hreg)) (theta : ℝ) :
    spacePart (M.definiteCircle a theta) ∈
      V.orbit (spacePart (M.definiteCircle a 0)) := by
  have h := V.continuousMap_mem_orbit
    (T.definiteSpatialAnglePath a ha har theta)
    (fun u => T.minimumDefiniteSpatialPoint_mem_fiber
      hindex a ha har hreg (theta * (u : ℝ))) 1
  simpa using h


-- @@ L238-250 verbatim
theorem maximumDefiniteSpatialPoint_mem_same_orbit
    (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.maximumNegativeSlice a hreg)) (theta : ℝ) :
    spacePart (M.definiteCircle a theta) ∈
      V.orbit (spacePart (M.definiteCircle a 0)) := by
  have h := V.continuousMap_mem_orbit
    (T.definiteSpatialAnglePath a ha har theta)
    (fun u => T.maximumDefiniteSpatialPoint_mem_fiber
      hindex a ha har hreg (theta * (u : ℝ))) 1
  simpa using h


-- @@ L252-286 verbatim
/-- Every covered point on the born side of a minimum belongs to the orbit
of the literal definite circle. -/
theorem minimum_coveredSliceFiber_after_subset_orbit
    (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.minimumPositiveSlice a hreg)) :
    M.coveredSliceFiber (tcoord center + a ^ 2) ⊆
      V.orbit (spacePart (M.definiteCircle a 0)) := by
  intro x hx
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center + a ^ 2 := by
    rw [huv, tcoord_spaceTime]
  rw [hindex] at htime
  simp only [morseQuadratic] at htime
  have hcoord : (u 0) ^ 2 + (u 1) ^ 2 = a ^ 2 := by
    nlinarith [htime, hs]
  have hnormsq := norm_sq_eq_coordinates u
  have hnorm : ‖u‖ = a := by
    nlinarith [norm_nonneg u]
  let theta := Complex.arg (morseParamComplex u)
  have hcircle : u = definiteCircleParam a theta :=
    eq_definiteCircleParam_arg hnorm
  have hspace := congrArg spacePart huv
  have hxEq : x = spacePart (M.definiteCircle a theta) := by
    calc
      x = spacePart (M.param u) := by simpa using hspace.symm
      _ = spacePart (M.definiteCircle a theta) := by
        rw [hcircle]
        rfl
  rw [hxEq]
  exact T.minimumDefiniteSpatialPoint_mem_same_orbit
    hindex a ha har hreg V theta


-- @@ L288-322 verbatim
/-- Every covered point on the pre-death side of a maximum belongs to the
orbit of the literal definite circle. -/
theorem maximum_coveredSliceFiber_before_subset_orbit
    (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.maximumNegativeSlice a hreg)) :
    M.coveredSliceFiber (tcoord center - a ^ 2) ⊆
      V.orbit (spacePart (M.definiteCircle a 0)) := by
  intro x hx
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center - a ^ 2 := by
    rw [huv, tcoord_spaceTime]
  rw [hindex] at htime
  simp only [morseQuadratic] at htime
  have hcoord : (u 0) ^ 2 + (u 1) ^ 2 = a ^ 2 := by
    nlinarith [htime, hs]
  have hnormsq := norm_sq_eq_coordinates u
  have hnorm : ‖u‖ = a := by
    nlinarith [norm_nonneg u]
  let theta := Complex.arg (morseParamComplex u)
  have hcircle : u = definiteCircleParam a theta :=
    eq_definiteCircleParam_arg hnorm
  have hspace := congrArg spacePart huv
  have hxEq : x = spacePart (M.definiteCircle a theta) := by
    calc
      x = spacePart (M.param u) := by simpa using hspace.symm
      _ = spacePart (M.definiteCircle a theta) := by
        rw [hcircle]
        rfl
  rw [hxEq]
  exact T.maximumDefiniteSpatialPoint_mem_same_orbit
    hindex a ha har hreg V theta


-- @@ L324-324 verbatim
end EmbeddedShrink


-- @@ L326-326 verbatim
end StandardMorseEventAt


-- @@ L328-328 verbatim
/-! ## Production chronological specializations -/


-- @@ L330-330 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L331-331 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L332-332 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L334-334 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L336-347 verbatim
/-- The covered portion of the production minimum's chronological before
slice is empty. -/
theorem chronologicalMinimumBeforeCoveredSliceFiber_eq_empty
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalBeforeTime t ht) = ∅ := by
  simpa [chronologicalBeforeTime] using
    (D.position.eventModel t ht).minimum_coveredSliceFiber_before_eq_empty
      hindex (D.chronologicalWindowRadius t ht)
      (D.chronologicalWindowRadius_pos t ht)


-- @@ L349-369 verbatim
/-- Every covered point on the production minimum's chronological after
slice belongs to its born definite-circle orbit. -/
theorem chronologicalMinimumAfterCoveredSliceFiber_subset_orbit
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (V : TamedField (D.chronologicalAfterSlice t ht)) :
    (D.position.eventModel t ht).coveredSliceFiber
        (D.chronologicalAfterTime t ht) ⊆
      V.orbit
        (spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht) 0)) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let a := D.chronologicalWindowRadius t ht
  have ha : 0 < a := D.chronologicalWindowRadius_pos t ht
  have har : a < T.radius :=
    D.chronologicalWindowRadius_lt_embedded t ht
  have h := T.minimum_coveredSliceFiber_after_subset_orbit
    hindex a ha har (D.chronologicalAfterTime_regular t ht) V
  convert h using 1 <;> simp [T, a, chronologicalAfterTime]
  all_goals congr


-- @@ L371-391 verbatim
/-- Every covered point on the production maximum's chronological before
slice belongs to its pre-death definite-circle orbit. -/
theorem chronologicalMaximumBeforeCoveredSliceFiber_subset_orbit
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (V : TamedField (D.chronologicalBeforeSlice t ht)) :
    (D.position.eventModel t ht).coveredSliceFiber
        (D.chronologicalBeforeTime t ht) ⊆
      V.orbit
        (spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht) 0)) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let a := D.chronologicalWindowRadius t ht
  have ha : 0 < a := D.chronologicalWindowRadius_pos t ht
  have har : a < T.radius :=
    D.chronologicalWindowRadius_lt_embedded t ht
  have h := T.maximum_coveredSliceFiber_before_subset_orbit
    hindex a ha har (D.chronologicalBeforeTime_regular t ht) V
  convert h using 1 <;> simp [T, a, chronologicalBeforeTime]
  all_goals congr


-- @@ L393-404 verbatim
/-- The covered portion of the production maximum's chronological after
slice is empty. -/
theorem chronologicalMaximumAfterCoveredSliceFiber_eq_empty
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalAfterTime t ht) = ∅ := by
  simpa [chronologicalAfterTime] using
    (D.position.eventModel t ht).maximum_coveredSliceFiber_after_eq_empty
      hindex (D.chronologicalWindowRadius t ht)
      (D.chronologicalWindowRadius_pos t ht)


-- @@ L406-406 verbatim
end ValueSeparatedSignedMorsePackage

-- @@ L407-407 verbatim
end Submission
