import Mathlib
import Submission.CanonicalRoundOrbitUnknotting
import Submission.SOStableLocalRelativeNormalization


-- @@ L5-16 verbatim
/-!
# Stable local frame gauges at canonical circle slots

`SOStableLocalRelativeNormalization` constructs a supported frame gauge around
the standard unit circle centered at the origin.  Canonical component placement
uses translated copies of that same circle.  This file performs the missing
conjugation by translation and feeds the result into `SOFrameGauge.homotopy`.

Thus a stable-class-zero smooth Cartesian `SO` loop gives an actual
`DefiningMapHomotopy` supported near any prescribed canonical circle, not just
an abstract local-gauge contract.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped unitInterval ContDiff Topology RealInnerProductSpace


-- @@ L25-25 verbatim
namespace Submission

-- @@ L26-26 verbatim
namespace SmoothCartesianSOLoop


-- @@ L28-28 verbatim
variable {m : ℕ}


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L31-31 verbatim
local notation "M" => Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ


-- @@ L33-49 verbatim
/-- The standard-circle parametrization is the same coordinate formula used
by the canonical round targets. -/
theorem circleAt_eq_canonical_plane (theta : ℝ) :
    circleAt (m := m) theta =
      Real.cos theta • CanonicalRoundOrbit.e₀ (n := m + 2) (by omega) +
        Real.sin theta • CanonicalRoundOrbit.e₁ (n := m + 2) (by omega) := by
  ext j
  by_cases h0 : j = 0
  · subst j
    simp [circleAt_apply, CanonicalRoundOrbit.e₀,
      CanonicalRoundOrbit.e₁]
  by_cases h1 : j = 1
  · subst j
    simp [circleAt_apply, CanonicalRoundOrbit.e₀,
      CanonicalRoundOrbit.e₁]
  · simp [circleAt_apply, CanonicalRoundOrbit.e₀,
      CanonicalRoundOrbit.e₁, h0, h1]


-- @@ L51-60 verbatim
/-- Hence a canonical round parametrization is literally a translated copy
of the standard circle. -/
theorem canonical_point_eq_circleAt_add_center
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (O : V.OrbitIndex) (theta : ℝ) :
    CanonicalRoundOrbit.point V (by omega) O theta =
      circleAt (m := m) theta +
        CanonicalRoundOrbit.center V (by omega) O := by
  rw [CanonicalRoundOrbit.point, circleAt_eq_canonical_plane]
  abel


-- @@ L62-85 verbatim
/-- The standard tubular squared-distance is exactly the squared displacement
when the unit circle is shifted in the third coordinate. -/
theorem tubeDistSq_circleAt_add_smul_e₂ (theta d : ℝ) :
    tubeDistSq (circleAt (m := m) theta +
      d • CanonicalRoundOrbit.e₂ (n := m + 2) (by omega)) = d ^ 2 := by
  let e2 : E := CanonicalRoundOrbit.e₂ (n := m + 2) (by omega)
  have hrad : rad (circleAt (m := m) theta + d • e2) = 1 := by
    rw [rad]
    have hrs : radSq (circleAt (m := m) theta + d • e2) = 1 := by
      simp [radSq, e2, CanonicalRoundOrbit.e₂,
        Real.cos_sq_add_sin_sq]
    rw [hrs, Real.sqrt_one]
  have hinner :
      inner ℝ (circleAt (m := m) theta) (d • e2) = 0 := by
    rw [real_inner_smul_right]
    simp [e2, CanonicalRoundOrbit.e₂,
      EuclideanSpace.inner_single_right]
  have he2norm : ‖e2‖ = 1 := by
    simp [e2, CanonicalRoundOrbit.e₂]
  have hnorm := norm_add_sq_real (circleAt (m := m) theta) (d • e2)
  rw [tubeDistSq, hrad, hnorm, hinner, norm_circleAt,
    norm_smul, he2norm]
  simp [Real.norm_eq_abs, sq_abs]
  ring


-- @@ L87-124 verbatim
/-- Distinct canonical circles lie outside one another's translated outer
tubes.  The slot spacing is four, while each outer tube has radius `1/3`. -/
theorem canonical_point_sub_center_not_mem_outerTube
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    {O P : V.OrbitIndex} (hOP : O ≠ P) (theta : ℝ) :
    CanonicalRoundOrbit.point V (by omega) P theta -
        CanonicalRoundOrbit.center V (by omega) O ∉
      tubeRegion (m := m) (1 / 3) := by
  let kO : ℕ := V.orbitSlot O
  let kP : ℕ := V.orbitSlot P
  have hslot : V.orbitSlot O ≠ V.orbitSlot P := by
    intro h
    exact hOP (V.orbitSlot_injective h)
  have hnat : kO ≠ kP := by
    intro h
    apply hslot
    exact Fin.ext h
  have hpoint :
      CanonicalRoundOrbit.point V (by omega) P theta -
          CanonicalRoundOrbit.center V (by omega) O =
        circleAt (m := m) theta +
          (4 * ((kP : ℝ) - (kO : ℝ))) •
            CanonicalRoundOrbit.e₂ (n := m + 2) (by omega) := by
    rw [canonical_point_eq_circleAt_add_center]
    simp only [CanonicalRoundOrbit.center, kO, kP]
    module
  rw [hpoint]
  change ¬ tubeDistSq _ < (1 / 3 : ℝ) ^ 2
  rw [tubeDistSq_circleAt_add_smul_e₂]
  rcases lt_or_gt_of_ne hnat with hlt | hgt
  · have hgap : (kO : ℝ) + 1 ≤ (kP : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    norm_num
    nlinarith
  · have hgap : (kP : ℝ) + 1 ≤ (kO : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hgt)
    norm_num
    nlinarith


-- @@ L126-126 verbatim
namespace NullGaugeData


-- @@ L128-128 verbatim
variable {L : SmoothCartesianSOLoop (m + 2)}


-- @@ L130-133 verbatim
/-- Translate the standard supported gauge to a circle centered at `c`. -/
def centeredSpatialGauge (D : L.NullGaugeData) (c : E)
    (s : ℝ) (x : E) : SOGroup (m + 2) :=
  D.spatialGauge s (x - c)


-- @@ L135-142 verbatim
/-- Translation preserves joint smoothness of every matrix coefficient. -/
theorem centeredSpatialGauge_smooth (D : L.NullGaugeData) (c : E) :
    ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E =>
        ((D.centeredSpatialGauge c p.1 p.2 : SOGroup (m + 2)) : M) i j) := by
  intro i j
  exact (D.spatialGauge_smooth i j).comp
    (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))


-- @@ L144-147 verbatim
/-- Every translated local gauge still starts at the identity. -/
@[simp] theorem centeredSpatialGauge_zero (D : L.NullGaugeData)
    (c x : E) : D.centeredSpatialGauge c 0 x = 1 := by
  simp [centeredSpatialGauge]


-- @@ L149-155 verbatim
/-- At the translated standard circle, the endpoint is the prescribed loop. -/
@[simp] theorem centeredSpatialGauge_one_circleAt (D : L.NullGaugeData)
    (c : E) (theta : ℝ) :
    D.centeredSpatialGauge c 1 (circleAt theta + c) =
      L.cartesian (Real.cos theta, Real.sin theta) := by
  rw [centeredSpatialGauge, add_sub_cancel_right,
    D.spatialGauge_one_circleAt]


-- @@ L157-164 verbatim
/-- The translated gauge is the identity off the correspondingly translated
outer tube. -/
theorem centeredSpatialGauge_eq_one_off_outer (D : L.NullGaugeData)
    (c : E) (s : ℝ) {x : E}
    (hx : x - c ∉ tubeRegion (m := m) (1 / 3)) :
    D.centeredSpatialGauge c s x = 1 := by
  exact SOLocalExtension.extendCircleSOHomotopy_eq_one_off_outer
    D.Q D.zero s hx


-- @@ L166-175 verbatim
/-- The endpoint presentation produced by the translated supported gauge. -/
def centeredEndpointX (D : L.NullGaugeData) (c : E)
    (X : FramedLevelSet (m + 2)) : FramedLevelSet (m + 2) :=
  X.gaugeTransform
    (fun x => SOFrameGauge.toCLM (D.centeredSpatialGauge c 1 x))
    (SOFrameGauge.contDiff_toCLM (fun i j =>
      (D.centeredSpatialGauge_smooth c i j).comp
        (contDiff_const.prodMk contDiff_id)))
    (fun x => SOFrameGauge.toCLM_bijective
      (D.centeredSpatialGauge c 1 x))


-- @@ L177-184 verbatim
/-- A translated null gauge is an actual common-fiber defining-map homotopy
at one arbitrary circle center. -/
def centeredHomotopy (D : L.NullGaugeData) (c : E)
    (X : FramedLevelSet (m + 2)) :
    DefiningMapHomotopy X (D.centeredEndpointX c X) :=
  SOFrameGauge.homotopy X (D.centeredSpatialGauge c)
    (D.centeredSpatialGauge_smooth c)
    (D.centeredSpatialGauge_zero c)


-- @@ L186-195 verbatim
/-- The one-component homotopy realizes the requested endpoint loop on the
translated circle. -/
@[simp] theorem centeredHomotopy_H_one_circleAt (D : L.NullGaugeData)
    (c : E) (X : FramedLevelSet (m + 2)) (theta : ℝ) :
    (D.centeredHomotopy c X).H 1 (circleAt theta + c) =
      SOFrameGauge.toCLM
        (L.cartesian (Real.cos theta, Real.sin theta))
        (X.g (circleAt theta + c)) := by
  rw [centeredHomotopy, SOFrameGauge.homotopy_H,
    centeredSpatialGauge_one_circleAt]


-- @@ L197-209 verbatim
/-- Specialized to a canonical placement slot, the translated homotopy
realizes the prescribed endpoint loop on that exact round component. -/
@[simp] theorem centeredHomotopy_H_one_canonicalPoint
    {X₀ : FramedLevelSet (m + 2)} (V : TamedField X₀)
    (O : V.OrbitIndex) (D : L.NullGaugeData)
    (X : FramedLevelSet (m + 2)) (theta : ℝ) :
    (D.centeredHomotopy (CanonicalRoundOrbit.center V (by omega) O) X).H 1
        (CanonicalRoundOrbit.point V (by omega) O theta) =
      SOFrameGauge.toCLM
        (L.cartesian (Real.cos theta, Real.sin theta))
        (X.g (CanonicalRoundOrbit.point V (by omega) O theta)) := by
  rw [canonical_point_eq_circleAt_add_center]
  exact D.centeredHomotopy_H_one_circleAt _ X theta


-- @@ L211-215 verbatim
/-- The gauge endpoint has exactly the same fiber as the input presentation. -/
theorem centeredEndpointX_fiber (D : L.NullGaugeData) (c : E)
    (X : FramedLevelSet (m + 2)) :
    (D.centeredEndpointX c X).fiber = X.fiber := by
  exact FramedLevelSet.gaugeTransform_fiber _ _ _ _


-- @@ L217-217 verbatim
end NullGaugeData


-- @@ L219-219 verbatim
/-! ## Direct class-zero constructor -/


-- @@ L221-226 verbatim
/-- Choose the fully constructed smooth null gauge supplied by stable
completeness. -/
def nullGaugeDataOfClassZero (L : SmoothCartesianSOLoop (m + 2))
    (h3 : 3 ≤ m + 2)
    (hclass : loopClassZ2 L.loop L.closed = 0) : L.NullGaugeData :=
  Classical.choice (L.nonempty_nullGaugeData h3 hclass)


-- @@ L228-237 verbatim
/-- A stable-class-zero Cartesian loop therefore gives an inhabited, concrete
one-component defining-map homotopy at any translated circle. -/
def centeredHomotopyOfClassZero
    (L : SmoothCartesianSOLoop (m + 2))
    (h3 : 3 ≤ m + 2)
    (hclass : loopClassZ2 L.loop L.closed = 0)
    (c : E) (X : FramedLevelSet (m + 2)) :
    DefiningMapHomotopy X
      ((nullGaugeDataOfClassZero L h3 hclass).centeredEndpointX c X) :=
  (nullGaugeDataOfClassZero L h3 hclass).centeredHomotopy c X


-- @@ L239-239 verbatim
/-! ## Specialization to a canonical placement slot -/


-- @@ L241-241 verbatim
variable {X : FramedLevelSet (m + 2)} (V : TamedField X)


-- @@ L243-256 verbatim
/-- Put the supported gauge at the center assigned to orbit `O` by canonical
component placement. -/
def canonicalOrbitHomotopyOfClassZero
    (L : SmoothCartesianSOLoop (m + 2))
    (h3 : 3 ≤ m + 2)
    (hclass : loopClassZ2 L.loop L.closed = 0)
    (O : V.OrbitIndex) (Y : FramedLevelSet (m + 2)) :
    DefiningMapHomotopy Y
      ((nullGaugeDataOfClassZero L h3 hclass).centeredEndpointX
        (CanonicalRoundOrbit.center V
          (by omega) O) Y) :=
  centeredHomotopyOfClassZero L h3 hclass
    (CanonicalRoundOrbit.center V
      (by omega) O) Y


-- @@ L258-258 verbatim
/-! ## Finite composition over all canonical slots -/


-- @@ L260-260 verbatim
namespace CanonicalFiniteGauge


-- @@ L262-262 verbatim
variable {X₀ : FramedLevelSet (m + 2)} (V₀ : TamedField X₀)

-- @@ L263-263 verbatim
variable (L₀ : V₀.OrbitIndex → SmoothCartesianSOLoop (m + 2))

-- @@ L264-264 verbatim
variable (D₀ : ∀ O : V₀.OrbitIndex, (L₀ O).NullGaugeData)


-- @@ L266-268 verbatim
/-- Canonical slot order, used because matrix multiplication need not commute. -/
def orbitList : List V₀.OrbitIndex :=
  List.ofFn fun i => (Fintype.equivFin V₀.OrbitIndex).symm i


-- @@ L270-272 verbatim
theorem orbitList_nodup : (orbitList V₀).Nodup := by
  rw [orbitList, List.nodup_ofFn]
  exact (Fintype.equivFin V₀.OrbitIndex).symm.injective


-- @@ L274-277 verbatim
theorem mem_orbitList (O : V₀.OrbitIndex) : O ∈ orbitList V₀ := by
  rw [orbitList, List.mem_ofFn]
  exact ⟨Fintype.equivFin V₀.OrbitIndex O,
    (Fintype.equivFin V₀.OrbitIndex).symm_apply_apply O⟩


-- @@ L279-286 verbatim
/-- Ordered pointwise multiplication of the translated supported gauges. -/
def listSpatialGauge :
    List V₀.OrbitIndex → ℝ → E → SOGroup (m + 2)
  | [], _, _ => 1
  | O :: tail, s, x =>
      (D₀ O).centeredSpatialGauge
          (CanonicalRoundOrbit.center V₀ (by omega) O) s x *
        listSpatialGauge tail s x


-- @@ L288-310 verbatim
/-- A finite ordered product of the translated gauges is still jointly smooth. -/
theorem listSpatialGauge_smooth (tail : List V₀.OrbitIndex) :
    ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E =>
        ((listSpatialGauge V₀ L₀ D₀ tail p.1 p.2 :
          SOGroup (m + 2)) : M) i j) := by
  induction tail with
  | nil =>
      intro i j
      exact contDiff_const
  | cons O tail ih =>
      intro i j
      change ContDiff ℝ ∞ (fun p : ℝ × E =>
        ∑ k : Fin (m + 2),
          (((D₀ O).centeredSpatialGauge
            (CanonicalRoundOrbit.center V₀ (by omega) O) p.1 p.2 :
              SOGroup (m + 2)) : M) i k *
            ((listSpatialGauge V₀ L₀ D₀ tail p.1 p.2 :
              SOGroup (m + 2)) : M) k j)
      exact ContDiff.sum fun k _ =>
        ((D₀ O).centeredSpatialGauge_smooth
          (CanonicalRoundOrbit.center V₀ (by omega) O) i k).mul
            (ih k j)


-- @@ L312-319 verbatim
/-- The finite product starts at the identity. -/
@[simp] theorem listSpatialGauge_zero (tail : List V₀.OrbitIndex)
    (x : E) : listSpatialGauge V₀ L₀ D₀ tail 0 x = 1 := by
  induction tail with
  | nil => rfl
  | cons O tail ih =>
      rw [listSpatialGauge, NullGaugeData.centeredSpatialGauge_zero, ih,
        mul_one]


-- @@ L321-335 verbatim
/-- If every slot in a list differs from `P`, all its factors are the identity
on the canonical circle of `P`. -/
theorem listSpatialGauge_eq_one_at_canonicalPoint_of_forall_ne
    (tail : List V₀.OrbitIndex) (P : V₀.OrbitIndex)
    (hne : ∀ O ∈ tail, O ≠ P) (s theta : ℝ) :
    listSpatialGauge V₀ L₀ D₀ tail s
      (CanonicalRoundOrbit.point V₀ (by omega) P theta) = 1 := by
  induction tail with
  | nil => rfl
  | cons O tail ih =>
      rw [listSpatialGauge,
        (D₀ O).centeredSpatialGauge_eq_one_off_outer]
      · rw [ih (fun Q hQ => hne Q (by simp [hQ])), one_mul]
      · exact canonical_point_sub_center_not_mem_outerTube V₀
          (hne O (by simp)) theta


-- @@ L337-370 verbatim
/-- On a noduplicated list containing `P`, the endpoint product restricts on
the circle of `P` to exactly the prescribed `P`-loop; all other factors vanish
by support separation. -/
theorem listSpatialGauge_one_canonicalPoint
    (tail : List V₀.OrbitIndex) (hnodup : tail.Nodup)
    (P : V₀.OrbitIndex) (hmem : P ∈ tail) (theta : ℝ) :
    listSpatialGauge V₀ L₀ D₀ tail 1
      (CanonicalRoundOrbit.point V₀ (by omega) P theta) =
        (L₀ P).cartesian (Real.cos theta, Real.sin theta) := by
  induction tail with
  | nil => simp at hmem
  | cons O tail ih =>
      rw [List.nodup_cons] at hnodup
      rcases hnodup with ⟨hOtail, htail⟩
      by_cases hOP : O = P
      · subst O
        rw [listSpatialGauge]
        rw [show (D₀ P).centeredSpatialGauge
            (CanonicalRoundOrbit.center V₀ (by omega) P) 1
              (CanonicalRoundOrbit.point V₀ (by omega) P theta) =
            (L₀ P).cartesian (Real.cos theta, Real.sin theta) by
          rw [canonical_point_eq_circleAt_add_center,
            (D₀ P).centeredSpatialGauge_one_circleAt]]
        rw [listSpatialGauge_eq_one_at_canonicalPoint_of_forall_ne]
        · rw [mul_one]
        · intro Q hQ hQP
          subst Q
          exact hOtail hQ
      · have hPtail : P ∈ tail := by
          simpa [hOP, Ne.symm hOP] using hmem
        rw [listSpatialGauge,
          (D₀ O).centeredSpatialGauge_eq_one_off_outer]
        · rw [one_mul, ih htail hPtail]
        · exact canonical_point_sub_center_not_mem_outerTube V₀ hOP theta


-- @@ L372-374 verbatim
/-- The product used for the complete canonical configuration. -/
def spatialGauge (s : ℝ) (x : E) : SOGroup (m + 2) :=
  listSpatialGauge V₀ L₀ D₀ (orbitList V₀) s x


-- @@ L376-380 verbatim
theorem spatialGauge_smooth : ∀ i j, ContDiff ℝ ∞
    (fun p : ℝ × E =>
      ((spatialGauge V₀ L₀ D₀ p.1 p.2 :
        SOGroup (m + 2)) : M) i j) :=
  listSpatialGauge_smooth V₀ L₀ D₀ (orbitList V₀)


-- @@ L382-384 verbatim
@[simp] theorem spatialGauge_zero (x : E) :
    spatialGauge V₀ L₀ D₀ 0 x = 1 :=
  listSpatialGauge_zero V₀ L₀ D₀ (orbitList V₀) x


-- @@ L386-394 verbatim
/-- The simultaneous endpoint gauge realizes each component's loop exactly on
its own canonical circle. -/
@[simp] theorem spatialGauge_one_canonicalPoint
    (P : V₀.OrbitIndex) (theta : ℝ) :
    spatialGauge V₀ L₀ D₀ 1
      (CanonicalRoundOrbit.point V₀ (by omega) P theta) =
        (L₀ P).cartesian (Real.cos theta, Real.sin theta) :=
  listSpatialGauge_one_canonicalPoint V₀ L₀ D₀
    (orbitList V₀) (orbitList_nodup V₀) P (mem_orbitList V₀ P) theta


-- @@ L396-401 verbatim
/-- Finite composition now yields one actual defining-map homotopy for all
canonical slots simultaneously. -/
def homotopy (Y : FramedLevelSet (m + 2)) :=
  SOFrameGauge.homotopy Y (spatialGauge V₀ L₀ D₀)
    (spatialGauge_smooth V₀ L₀ D₀)
    (spatialGauge_zero V₀ L₀ D₀)


-- @@ L403-413 verbatim
/-- The actual finite defining-map homotopy has the prescribed endpoint frame
action on every canonical component. -/
@[simp] theorem homotopy_H_one_canonicalPoint
    (Y : FramedLevelSet (m + 2)) (P : V₀.OrbitIndex) (theta : ℝ) :
    (homotopy V₀ L₀ D₀ Y).H 1
        (CanonicalRoundOrbit.point V₀ (by omega) P theta) =
      SOFrameGauge.toCLM
        ((L₀ P).cartesian (Real.cos theta, Real.sin theta))
        (Y.g (CanonicalRoundOrbit.point V₀ (by omega) P theta)) := by
  rw [homotopy, SOFrameGauge.homotopy_H,
    spatialGauge_one_canonicalPoint]


-- @@ L415-420 verbatim
/-- Choose the constructed null gauge independently at every finite orbit. -/
def nullGaugeFamilyOfClassZero (h3 : 3 ≤ m + 2)
    (hclass : ∀ O : V₀.OrbitIndex,
      loopClassZ2 (L₀ O).loop (L₀ O).closed = 0) :
    ∀ O : V₀.OrbitIndex, (L₀ O).NullGaugeData :=
  fun O => nullGaugeDataOfClassZero (L₀ O) h3 (hclass O)


-- @@ L422-429 verbatim
/-- Stable class zero on every prescribed component loop now produces one
actual finite common-fiber defining-map homotopy, with no local gauge witnesses
left as inputs. -/
def homotopyOfClassZero (h3 : 3 ≤ m + 2)
    (hclass : ∀ O : V₀.OrbitIndex,
      loopClassZ2 (L₀ O).loop (L₀ O).closed = 0)
    (Y : FramedLevelSet (m + 2)) :=
  homotopy V₀ L₀ (nullGaugeFamilyOfClassZero V₀ L₀ h3 hclass) Y


-- @@ L431-444 verbatim
/-- The class-zero finite constructor realizes every requested component loop
at its canonical slot. -/
@[simp] theorem homotopyOfClassZero_H_one_canonicalPoint
    (h3 : 3 ≤ m + 2)
    (hclass : ∀ O : V₀.OrbitIndex,
      loopClassZ2 (L₀ O).loop (L₀ O).closed = 0)
    (Y : FramedLevelSet (m + 2)) (P : V₀.OrbitIndex) (theta : ℝ) :
    (homotopyOfClassZero V₀ L₀ h3 hclass Y).H 1
        (CanonicalRoundOrbit.point V₀ (by omega) P theta) =
      SOFrameGauge.toCLM
        ((L₀ P).cartesian (Real.cos theta, Real.sin theta))
        (Y.g (CanonicalRoundOrbit.point V₀ (by omega) P theta)) := by
  exact homotopy_H_one_canonicalPoint V₀ L₀
    (nullGaugeFamilyOfClassZero V₀ L₀ h3 hclass) Y P theta


-- @@ L446-446 verbatim
end CanonicalFiniteGauge


-- @@ L448-448 verbatim
end SmoothCartesianSOLoop

-- @@ L449-449 verbatim
end Submission
