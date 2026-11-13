import Mathlib
import Submission.Sard
import Submission.BridgeCobordism
import Submission.CobordSlice
import Submission.MorseEvents


-- @@ L7-31 verbatim
/-!
# Morse position for framed level cobordisms

This module is the global companion to `Submission.MorseEvents`.  It develops the
parts of the Morse-position argument which do not depend on an unformalized manifold
library:

* the critical locus in the compact middle slab is closed and compact;
* the associated set of critical times is compact;
* the end-collar times are regular, and any interval avoiding the middle critical
  times is a `regularSlab`, ready for `CobordFlow`;
* an exact standard-event chart has a concrete two-dimensional quadratic time model
  and is proved to isolate its critical point;
* a compact cobordism covered by such charts has finitely many critical points;
* after the usual distinct-critical-values condition, these data are packaged as a
  finite, canonically ordered event schedule;
* the Sard step used to make a two-dimensional gradient transverse is implemented:
  arbitrarily small regular values exist, their inverse images are discrete, and
  their intersections with compact sets are finite.

The only remaining input for the full perturbation theorem is the ambient
jet-replacement construction which turns an arbitrary `FramedLevelCobordism` into
one carrying `MorseAtlas`.  No theorem in this file assumes that construction as an
unproved premise.
-/


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Function Metric MeasureTheory

-- @@ L36-36 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L38-38 verbatim
namespace Submission


-- @@ L40-40 verbatim
variable {n : ℕ}


-- @@ L42-42 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L43-43 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L44-44 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)

-- @@ L45-45 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L47-47 verbatim
/-! ## Closedness and compactness of the middle critical locus -/


-- @@ L49-53 verbatim
/-- Write the spatial derivative with target `Fin n → ℝ`, so that the closedness
theorem for nonsurjective continuous linear maps from `SardPrelim` applies directly. -/
def spatialDerivPi (G : E' → F) (v : E') : E₁ →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ : F ≃L[ℝ] (Fin n → ℝ)).toContinuousLinearMap.comp
    (spatialDeriv G v)


-- @@ L55-64 verbatim
theorem spatialDerivPi_surjective_iff (G : E' → F) (v : E') :
    Surjective (spatialDerivPi G v) ↔ Surjective (spatialDeriv G v) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ : F ≃L[ℝ] (Fin n → ℝ))
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e y)
    refine ⟨x, e.injective ?_⟩
    exact hx
  · intro h
    exact e.surjective.comp h


-- @@ L66-70 verbatim
theorem contDiff_spatialDerivPi {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (spatialDerivPi G) := by
  have hsp : ContDiff ℝ ∞ (spatialDeriv G) := by
    exact ContDiff.clm_comp (contDiff_fderivCLM hG) contDiff_const
  exact ContDiff.clm_comp contDiff_const hsp


-- @@ L72-86 verbatim
/-- The fiber-critical set of a smooth space-time map is closed. -/
theorem isClosed_timeCritical {G : E' → F} (hG : ContDiff ℝ ∞ G) :
    IsClosed (timeCritical G) := by
  have hzero : IsClosed {v : E' | G v = 0} :=
    isClosed_singleton.preimage hG.continuous
  have hnonsurj : IsClosed {v : E' | ¬Surjective (spatialDerivPi G v)} :=
    (isClosed_setOf_not_surjective (E := E₁) (q := n)).preimage
      (contDiff_spatialDerivPi hG).continuous
  have heq : timeCritical G =
      {v : E' | G v = 0} ∩ {v : E' | ¬Surjective (spatialDerivPi G v)} := by
    ext v
    simp only [timeCritical, mem_setOf_eq, mem_inter_iff,
      spatialDerivPi_surjective_iff]
  rw [heq]
  exact hzero.inter hnonsurj


-- @@ L88-91 verbatim
/-- The critical points which can participate in Morse events: the critical locus
over the compact middle slab `[1/4, 3/4]`. -/
def coreCriticalPoints (C : FramedLevelCobordism n) : Set E' :=
  timeCritical C.G ∩ tcoord ⁻¹' Icc (1 / 4 : ℝ) (3 / 4 : ℝ)


-- @@ L93-95 verbatim
/-- Critical times occurring in the middle slab. -/
def coreCriticalTimes (C : FramedLevelCobordism n) : Set ℝ :=
  tcoord '' coreCriticalPoints C


-- @@ L97-100 verbatim
theorem isClosed_coreCriticalPoints (C : FramedLevelCobordism n) :
    IsClosed (coreCriticalPoints C) := by
  exact (isClosed_timeCritical C.smooth).inter
    (isClosed_Icc.preimage continuous_tcoord)


-- @@ L102-109 verbatim
theorem coreCriticalPoints_subset_fiber (C : FramedLevelCobordism n) :
    coreCriticalPoints C ⊆ C.fiber := by
  rintro v ⟨⟨hv, -⟩, ht⟩
  refine ⟨hv, ?_, ?_⟩
  · change 0 ≤ tcoord v
    linarith [ht.1]
  · change tcoord v ≤ 1
    linarith [ht.2]


-- @@ L111-116 verbatim
/-- Compactness is the key global input: isolated model critical points are therefore
finite without any compact-manifold infrastructure. -/
theorem isCompact_coreCriticalPoints (C : FramedLevelCobordism n) :
    IsCompact (coreCriticalPoints C) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_coreCriticalPoints C)
  exact C.isBounded_fiber.subset (coreCriticalPoints_subset_fiber C)


-- @@ L118-120 verbatim
theorem isCompact_coreCriticalTimes (C : FramedLevelCobordism n) :
    IsCompact (coreCriticalTimes C) :=
  (isCompact_coreCriticalPoints C).image continuous_tcoord


-- @@ L122-122 verbatim
/-! ## Collar regularity and regular cells between events -/


-- @@ L124-139 verbatim
theorem FramedLevelCobordism.sliceRegular_of_le_quarter
    (C : FramedLevelCobordism n) {t : ℝ} (ht : t ≤ 1 / 4) :
    sliceRegular C.G t := by
  intro v hv htv
  have hvst : cobSpaceTime (spacePart v) t = v := by
    rw [← htv]
    exact spaceTime_spacePart v
  have hslice : sliceMap C.G t = C.X₀.g := by
    funext x
    exact C.collar_zero x t ht
  rw [← hvst, ← fderiv_sliceMap C.smooth, hslice]
  apply C.X₀.regular
  have h0 : sliceMap C.G t (spacePart v) = 0 := by
    rw [sliceMap, hvst]
    exact hv
  rwa [hslice] at h0


-- @@ L141-156 verbatim
theorem FramedLevelCobordism.sliceRegular_of_three_quarter_le
    (C : FramedLevelCobordism n) {t : ℝ} (ht : 3 / 4 ≤ t) :
    sliceRegular C.G t := by
  intro v hv htv
  have hvst : cobSpaceTime (spacePart v) t = v := by
    rw [← htv]
    exact spaceTime_spacePart v
  have hslice : sliceMap C.G t = C.X₁.g := by
    funext x
    exact C.collar_one x t ht
  rw [← hvst, ← fderiv_sliceMap C.smooth, hslice]
  apply C.X₁.regular
  have h0 : sliceMap C.G t (spacePart v) = 0 := by
    rw [sliceMap, hvst]
    exact hv
  rwa [hslice] at h0


-- @@ L158-161 verbatim
theorem FramedLevelCobordism.quarter_notMem_coreCriticalTimes
    (C : FramedLevelCobordism n) : (1 / 4 : ℝ) ∉ coreCriticalTimes C := by
  rintro ⟨v, ⟨hcrit, -⟩, ht⟩
  exact hcrit.2 ((C.sliceRegular_of_le_quarter le_rfl) v hcrit.1 ht)


-- @@ L163-166 verbatim
theorem FramedLevelCobordism.threeQuarter_notMem_coreCriticalTimes
    (C : FramedLevelCobordism n) : (3 / 4 : ℝ) ∉ coreCriticalTimes C := by
  rintro ⟨v, ⟨hcrit, -⟩, ht⟩
  exact hcrit.2 ((C.sliceRegular_of_three_quarter_le le_rfl) v hcrit.1 ht)


-- @@ L168-182 verbatim
/-- Any middle interval which avoids the compact set of critical times is a regular
slab and can immediately be transported by `CobordFlow`. -/
theorem FramedLevelCobordism.regularSlab_of_disjoint_coreCriticalTimes
    (C : FramedLevelCobordism n) {a b : ℝ}
    (ha : 1 / 4 ≤ a) (hb : b ≤ 3 / 4)
    (hdis : Disjoint (Icc a b) (coreCriticalTimes C)) :
    regularSlab C.G a b := by
  intro t ht hcritical
  rcases hcritical with ⟨v, hvcrit, hvt⟩
  have hcore : v ∈ coreCriticalPoints C := by
    refine ⟨hvcrit, ?_⟩
    change tcoord v ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ)
    rw [hvt]
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩
  exact Set.disjoint_left.1 hdis ht ⟨v, hcore, hvt⟩


-- @@ L184-184 verbatim
/-! ## A continuous north/south label on the fiber -/


-- @@ L186-193 verbatim
/-- A continuous real label which never vanishes on the zero fiber.  In the PT
application its positive part is the north fiber and its negative part is the south
fiber.  Keeping this datum separate from `G` makes it stable under pulling back by
the ambient diffeomorphisms used in jet replacement. -/
structure FiberSide (C : FramedLevelCobordism n) where
  side : E' → ℝ
  continuous : Continuous side
  nonzero_on_fiber : ∀ v, C.G v = 0 → side v ≠ 0


-- @@ L195-195 verbatim
namespace FiberSide


-- @@ L197-199 verbatim
/-- The positively labelled (north) part of the zero fiber. -/
def positiveFiber {C : FramedLevelCobordism n} (L : FiberSide C) : Set E' :=
  {v | C.G v = 0 ∧ 0 < L.side v}


-- @@ L201-203 verbatim
/-- The negatively labelled (south) part of the zero fiber. -/
def negativeFiber {C : FramedLevelCobordism n} (L : FiberSide C) : Set E' :=
  {v | C.G v = 0 ∧ L.side v < 0}


-- @@ L205-214 verbatim
theorem fiber_eq_positive_union_negative {C : FramedLevelCobordism n}
    (L : FiberSide C) :
    {v : E' | C.G v = 0} = L.positiveFiber ∪ L.negativeFiber := by
  ext v
  constructor
  · intro hv
    rcases lt_or_gt_of_ne (L.nonzero_on_fiber v hv) with hvneg | hvpos
    · exact Or.inr ⟨hv, hvneg⟩
    · exact Or.inl ⟨hv, hvpos⟩
  · rintro (hv | hv) <;> exact hv.1


-- @@ L216-220 verbatim
theorem disjoint_positive_negative {C : FramedLevelCobordism n}
    (L : FiberSide C) : Disjoint L.positiveFiber L.negativeFiber := by
  rw [Set.disjoint_left]
  intro v hvp hvn
  linarith [hvp.2, hvn.2]


-- @@ L222-227 verbatim
/-- Positivity is relatively open in the fiber. -/
theorem exists_open_positive {C : FramedLevelCobordism n} (L : FiberSide C) :
    ∃ U : Set E', IsOpen U ∧ L.positiveFiber = {v | C.G v = 0} ∩ U := by
  refine ⟨L.side ⁻¹' Ioi 0, isOpen_Ioi.preimage L.continuous, ?_⟩
  ext v
  simp [positiveFiber]


-- @@ L229-234 verbatim
/-- Negativity is relatively open in the fiber. -/
theorem exists_open_negative {C : FramedLevelCobordism n} (L : FiberSide C) :
    ∃ U : Set E', IsOpen U ∧ L.negativeFiber = {v | C.G v = 0} ∩ U := by
  refine ⟨L.side ⁻¹' Iio 0, isOpen_Iio.preimage L.continuous, ?_⟩
  ext v
  simp [negativeFiber]


-- @@ L236-250 verbatim
/-- If one point of a connected fiber component is north, the whole component is
north.  This is the precise restriction principle needed by the orbit-level `δ`. -/
theorem positive_on_preconnected {C : FramedLevelCobordism n} (L : FiberSide C)
    {S : Set E'} (hS : IsPreconnected S) (hsub : S ⊆ {v | C.G v = 0})
    {x : E'} (hx : x ∈ S) (hxpos : 0 < L.side x) :
    S ⊆ L.positiveFiber := by
  intro y hy
  refine ⟨hsub hy, ?_⟩
  by_contra hypos
  have hyne : L.side y ≠ 0 := L.nonzero_on_fiber y (hsub hy)
  have hylt : L.side y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hyne
  have hzrange : (0 : ℝ) ∈ Icc (L.side y) (L.side x) := ⟨hylt.le, hxpos.le⟩
  obtain ⟨z, hzS, hz0⟩ :=
    hS.intermediate_value hy hx L.continuous.continuousOn hzrange
  exact (L.nonzero_on_fiber z (hsub hzS)) hz0


-- @@ L252-265 verbatim
/-- The analogous constancy statement for a south component. -/
theorem negative_on_preconnected {C : FramedLevelCobordism n} (L : FiberSide C)
    {S : Set E'} (hS : IsPreconnected S) (hsub : S ⊆ {v | C.G v = 0})
    {x : E'} (hx : x ∈ S) (hxneg : L.side x < 0) :
    S ⊆ L.negativeFiber := by
  intro y hy
  refine ⟨hsub hy, ?_⟩
  by_contra hyneg
  have hyne : L.side y ≠ 0 := L.nonzero_on_fiber y (hsub hy)
  have hypos : 0 < L.side y := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm hyne)
  have hzrange : (0 : ℝ) ∈ Icc (L.side x) (L.side y) := ⟨hxneg.le, hypos.le⟩
  obtain ⟨z, hzS, hz0⟩ :=
    hS.intermediate_value hx hy L.continuous.continuousOn hzrange
  exact (L.nonzero_on_fiber z (hsub hzS)) hz0


-- @@ L267-276 verbatim
/-- Every nonempty connected subset of the fiber lies entirely on one labelled
side. -/
theorem preconnected_side_dichotomy {C : FramedLevelCobordism n} (L : FiberSide C)
    {S : Set E'} (hS : IsPreconnected S) (hsub : S ⊆ {v | C.G v = 0})
    (hne : S.Nonempty) :
    S ⊆ L.positiveFiber ∨ S ⊆ L.negativeFiber := by
  obtain ⟨x, hx⟩ := hne
  rcases lt_or_gt_of_ne (L.nonzero_on_fiber x (hsub hx)) with hxneg | hxpos
  · exact Or.inr (L.negative_on_preconnected hS hsub hx hxneg)
  · exact Or.inl (L.positive_on_preconnected hS hsub hx hxpos)


-- @@ L278-285 verbatim
/-- At a positive point, continuity supplies a whole neighborhood on which the
label remains positive. -/
theorem exists_positive_neighborhood {C : FramedLevelCobordism n} (L : FiberSide C)
    {v : E'} (hv : 0 < L.side v) :
    ∃ U : Set E', IsOpen U ∧ v ∈ U ∧ ∀ w ∈ U, 0 < L.side w := by
  refine ⟨L.side ⁻¹' Ioi 0, isOpen_Ioi.preimage L.continuous, hv, ?_⟩
  intro w hw
  exact hw


-- @@ L287-292 verbatim
theorem exists_negative_neighborhood {C : FramedLevelCobordism n} (L : FiberSide C)
    {v : E'} (hv : L.side v < 0) :
    ∃ U : Set E', IsOpen U ∧ v ∈ U ∧ ∀ w ∈ U, L.side w < 0 := by
  refine ⟨L.side ⁻¹' Iio 0, isOpen_Iio.preimage L.continuous, hv, ?_⟩
  intro w hw
  exact hw


-- @@ L294-294 verbatim
end FiberSide


-- @@ L296-296 verbatim
/-! ## Exact standard event charts -/


-- @@ L298-316 verbatim
/-- An exact jet-replaced Morse chart centered at `center`.  The fields say that the
chart parametrizes the zero surface, its time coordinate is literally the standard
quadratic model, and the model detects the unique critical point in the chart.
`covers_fiber` is the local-surjectivity statement supplied by the implicit-function
chart. -/
structure StandardMorseEventAt (C : FramedLevelCobordism n) (center : E') where
  index : MorseIndexTwo
  radius : ℝ
  radius_pos : 0 < radius
  param : E₂ → E'
  param_smooth : ContDiffAt ℝ ∞ param 0
  param_zero : param 0 = center
  param_fiber : ∀ u, ‖u‖ < radius → C.G (param u) = 0
  time_model : ∀ u, ‖u‖ < radius →
    tcoord (param u) = tcoord center + morseQuadratic index (u 0, u 1)
  critical_model : ∀ u, ‖u‖ < radius →
    (param u ∈ timeCritical C.G ↔ u = 0)
  covers_fiber : ∃ ε > 0, ∀ v, dist v center < ε → C.G v = 0 →
    ∃ u, ‖u‖ < radius ∧ param u = v


-- @@ L318-318 verbatim
namespace StandardMorseEventAt


-- @@ L320-327 verbatim
theorem center_mem_timeCritical {C : FramedLevelCobordism n} {center : E'}
    (M : StandardMorseEventAt C center) : center ∈ timeCritical C.G := by
  rw [← M.param_zero]
  have hm : M.param 0 ∈ timeCritical C.G ↔ (0 : E₂) = 0 := by
    have hfun : ‖(0 : E₂)‖ < M.radius →
        (M.param 0 ∈ timeCritical C.G ↔ (0 : E₂) = 0) := M.critical_model 0
    exact hfun (by simpa using M.radius_pos)
  exact hm.2 rfl


-- @@ L329-349 verbatim
/-- A standard Morse chart isolates its center in the full critical locus. -/
theorem exists_isolating_open {C : FramedLevelCobordism n} {center : E'}
    (M : StandardMorseEventAt C center) :
    ∃ U : Set E', IsOpen U ∧ U ∩ timeCritical C.G = {center} := by
  obtain ⟨ε, hε, hcover⟩ := M.covers_fiber
  refine ⟨Metric.ball center ε, Metric.isOpen_ball, ?_⟩
  ext v
  constructor
  · rintro ⟨hvball, hvcrit⟩
    obtain ⟨u, hu, huv⟩ := hcover v hvball hvcrit.1
    have hm : M.param u ∈ timeCritical C.G ↔ u = 0 := by
      have hfun : ‖u‖ < M.radius →
          (M.param u ∈ timeCritical C.G ↔ u = 0) := M.critical_model u
      exact hfun hu
    have hu0 : u = 0 := hm.1 (huv ▸ hvcrit)
    rw [← huv, hu0, M.param_zero]
    exact mem_singleton center
  · intro hv
    rw [mem_singleton_iff] at hv
    subst v
    exact ⟨Metric.mem_ball_self hε, M.center_mem_timeCritical⟩


-- @@ L351-365 verbatim
theorem exists_isolating_open_core {C : FramedLevelCobordism n} {center : E'}
    (M : StandardMorseEventAt C center) (hc : center ∈ coreCriticalPoints C) :
    ∃ U : Set E', IsOpen U ∧ U ∩ coreCriticalPoints C = {center} := by
  obtain ⟨U, hU, hUcrit⟩ := M.exists_isolating_open
  refine ⟨U, hU, ?_⟩
  apply Set.Subset.antisymm
  · intro v hv
    exact hUcrit ▸ ⟨hv.1, hv.2.1⟩
  · intro v hv
    rw [mem_singleton_iff] at hv
    subst v
    have hcUcrit : center ∈ U ∩ timeCritical C.G := by
      rw [hUcrit]
      exact mem_singleton center
    exact ⟨hcUcrit.1, hc⟩


-- @@ L367-367 verbatim
end StandardMorseEventAt


-- @@ L369-369 verbatim
/-! ## A finite global Morse atlas and its event schedule -/


-- @@ L371-374 verbatim
/-- Verified Morse-position data before choosing a finite enumeration. -/
structure MorseAtlas (C : FramedLevelCobordism n) where
  localModel : ∀ v, v ∈ coreCriticalPoints C → Nonempty (StandardMorseEventAt C v)
  distinct_times : Set.InjOn tcoord (coreCriticalPoints C)


-- @@ L376-381 verbatim
theorem MorseAtlas.finite_coreCriticalPoints {C : FramedLevelCobordism n}
    (A : MorseAtlas C) : (coreCriticalPoints C).Finite := by
  apply (isCompact_coreCriticalPoints C).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro v hv
  exact (A.localModel v hv).some.exists_isolating_open_core hv


-- @@ L383-389 verbatim
/-- A finite collection of standard events, with distinct time coordinates.  The
linear order on `ℝ` gives a canonical sequence through `orderedCenters`. -/
structure MorsePosition (C : FramedLevelCobordism n) where
  centers : Finset E'
  centers_exact : (centers : Set E') = coreCriticalPoints C
  model : ∀ v, v ∈ centers → StandardMorseEventAt C v
  distinct_times : Set.InjOn tcoord (coreCriticalPoints C)


-- @@ L391-399 verbatim
/-- Compactness plus isolated standard charts produces the finite event package. -/
def MorseAtlas.toMorsePosition {C : FramedLevelCobordism n}
    (A : MorseAtlas C) : MorsePosition C where
  centers := A.finite_coreCriticalPoints.toFinset
  centers_exact := A.finite_coreCriticalPoints.coe_toFinset
  model := fun v hv => (A.localModel v (by
    rw [← A.finite_coreCriticalPoints.coe_toFinset]
    exact hv)).some
  distinct_times := A.distinct_times


-- @@ L401-401 verbatim
namespace MorsePosition


-- @@ L403-405 verbatim
/-- The finite set of event times. -/
def eventTimes {C : FramedLevelCobordism n} (P : MorsePosition C) : Finset ℝ :=
  P.centers.image tcoord


-- @@ L407-419 verbatim
theorem mem_eventTimes_iff {C : FramedLevelCobordism n} (P : MorsePosition C) (t : ℝ) :
    t ∈ P.eventTimes ↔ t ∈ coreCriticalTimes C := by
  constructor
  · intro ht
    obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp ht
    exact ⟨v, P.centers_exact ▸ hv, hvt⟩
  · rintro ⟨v, hv, hvt⟩
    apply Finset.mem_image.mpr
    have hv' : v ∈ P.centers := by
      change v ∈ (P.centers : Set E')
      rw [P.centers_exact]
      exact hv
    exact ⟨v, hv', hvt⟩


-- @@ L421-424 verbatim
theorem coe_eventTimes {C : FramedLevelCobordism n} (P : MorsePosition C) :
    (P.eventTimes : Set ℝ) = coreCriticalTimes C := by
  ext t
  exact P.mem_eventTimes_iff t


-- @@ L426-428 verbatim
/-- Canonical chronological enumeration of the event times. -/
def orderedEventTimes {C : FramedLevelCobordism n} (P : MorsePosition C) : List ℝ :=
  P.eventTimes.sort (· ≤ ·)


-- @@ L430-433 verbatim
@[simp] theorem mem_orderedEventTimes_iff {C : FramedLevelCobordism n}
    (P : MorsePosition C) (t : ℝ) :
    t ∈ P.orderedEventTimes ↔ t ∈ coreCriticalTimes C := by
  rw [orderedEventTimes, Finset.mem_sort, mem_eventTimes_iff]


-- @@ L435-437 verbatim
theorem orderedEventTimes_nodup {C : FramedLevelCobordism n} (P : MorsePosition C) :
    P.orderedEventTimes.Nodup := by
  exact Finset.sort_nodup _ _


-- @@ L439-450 verbatim
/-- Every chronological cell which contains no listed event is a regular slab. -/
theorem regularSlab_of_cell {C : FramedLevelCobordism n} (P : MorsePosition C)
    {a b : ℝ} (ha : 1 / 4 ≤ a) (hb : b ≤ 3 / 4)
    (havoid : ∀ t ∈ P.eventTimes, t ∉ Icc a b) :
    regularSlab C.G a b := by
  apply C.regularSlab_of_disjoint_coreCriticalTimes ha hb
  rw [Set.disjoint_left]
  intro t ht htc
  have ht' : t ∈ P.eventTimes := by
    rw [P.mem_eventTimes_iff]
    exact htc
  exact havoid t ht' ht


-- @@ L452-452 verbatim
end MorsePosition


-- @@ L454-454 verbatim
/-! ## North-labelled event schedule -/


-- @@ L456-461 verbatim
/-- Morse position together with a north/south label on the fiber.  The event
schedule is geometric data, while `sideLabel` records which connected components
are relevant to the north-fiber invariant. -/
structure LabeledMorsePosition (C : FramedLevelCobordism n) where
  position : MorsePosition C
  sideLabel : FiberSide C


-- @@ L463-463 verbatim
namespace LabeledMorsePosition


-- @@ L465-468 verbatim
/-- Critical events whose center lies on the positive (north) part of the fiber. -/
def positiveCenters {C : FramedLevelCobordism n} (P : LabeledMorsePosition C) :
    Finset E' :=
  P.position.centers.filter fun v => 0 < P.sideLabel.side v


-- @@ L470-473 verbatim
/-- The complementary critical events, lying on the negative (south) part. -/
def negativeCenters {C : FramedLevelCobordism n} (P : LabeledMorsePosition C) :
    Finset E' :=
  P.position.centers.filter fun v => P.sideLabel.side v < 0


-- @@ L475-480 verbatim
theorem event_side_ne_zero {C : FramedLevelCobordism n} (P : LabeledMorsePosition C)
    {v : E'} (hv : v ∈ P.position.centers) : P.sideLabel.side v ≠ 0 := by
  have hvcore : v ∈ coreCriticalPoints C := by
    rw [← P.position.centers_exact]
    exact hv
  exact P.sideLabel.nonzero_on_fiber v hvcore.1.1


-- @@ L482-485 verbatim
@[simp] theorem mem_positiveCenters_iff {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) {v : E'} :
    v ∈ P.positiveCenters ↔ v ∈ P.position.centers ∧ 0 < P.sideLabel.side v := by
  simp [positiveCenters]


-- @@ L487-490 verbatim
@[simp] theorem mem_negativeCenters_iff {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) {v : E'} :
    v ∈ P.negativeCenters ↔ v ∈ P.position.centers ∧ P.sideLabel.side v < 0 := by
  simp [negativeCenters]


-- @@ L492-498 verbatim
/-- Every event belongs to exactly one labelled side. -/
theorem event_mem_positive_or_negative {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) {v : E'} (hv : v ∈ P.position.centers) :
    v ∈ P.positiveCenters ∨ v ∈ P.negativeCenters := by
  rcases lt_or_gt_of_ne (P.event_side_ne_zero hv) with hvneg | hvpos
  · exact Or.inr (P.mem_negativeCenters_iff.mpr ⟨hv, hvneg⟩)
  · exact Or.inl (P.mem_positiveCenters_iff.mpr ⟨hv, hvpos⟩)


-- @@ L500-510 verbatim
theorem positiveCenters_union_negativeCenters {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) :
    P.positiveCenters ∪ P.negativeCenters = P.position.centers := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hvp | hvn
    · exact (P.mem_positiveCenters_iff.mp hvp).1
    · exact (P.mem_negativeCenters_iff.mp hvn).1
  · intro hv
    exact Finset.mem_union.mpr (P.event_mem_positive_or_negative hv)


-- @@ L512-519 verbatim
theorem disjoint_positiveCenters_negativeCenters {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) :
    Disjoint P.positiveCenters P.negativeCenters := by
  rw [Finset.disjoint_left]
  intro v hvp hvn
  have hp := (P.mem_positiveCenters_iff.mp hvp).2
  have hn := (P.mem_negativeCenters_iff.mp hvn).2
  linarith


-- @@ L521-524 verbatim
/-- The finite set of event times relevant to the north fiber. -/
def positiveEventTimes {C : FramedLevelCobordism n} (P : LabeledMorsePosition C) :
    Finset ℝ :=
  P.positiveCenters.image tcoord


-- @@ L526-529 verbatim
/-- Canonical chronological order on north-fiber events. -/
def orderedPositiveEventTimes {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) : List ℝ :=
  P.positiveEventTimes.sort (· ≤ ·)


-- @@ L531-547 verbatim
theorem mem_positiveEventTimes_iff {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) (t : ℝ) :
    t ∈ P.positiveEventTimes ↔
      ∃ v ∈ coreCriticalPoints C, 0 < P.sideLabel.side v ∧ tcoord v = t := by
  constructor
  · intro ht
    obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp ht
    have hvp := P.mem_positiveCenters_iff.mp hv
    refine ⟨v, ?_, hvp.2, hvt⟩
    rw [← P.position.centers_exact]
    exact hvp.1
  · rintro ⟨v, hvcore, hvpos, hvt⟩
    apply Finset.mem_image.mpr
    refine ⟨v, P.mem_positiveCenters_iff.mpr ⟨?_, hvpos⟩, hvt⟩
    change v ∈ (P.position.centers : Set E')
    rw [P.position.centers_exact]
    exact hvcore


-- @@ L549-553 verbatim
@[simp] theorem mem_orderedPositiveEventTimes_iff {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) (t : ℝ) :
    t ∈ P.orderedPositiveEventTimes ↔
      ∃ v ∈ coreCriticalPoints C, 0 < P.sideLabel.side v ∧ tcoord v = t := by
  rw [orderedPositiveEventTimes, Finset.mem_sort, mem_positiveEventTimes_iff]


-- @@ L555-557 verbatim
theorem orderedPositiveEventTimes_nodup {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) : P.orderedPositiveEventTimes.Nodup := by
  exact Finset.sort_nodup _ _


-- @@ L559-566 verbatim
/-- A north event has an ambient neighborhood on which the label remains positive.
Thus its standard local model may be fed directly to the north-fiber `δ` theorem. -/
theorem positive_event_neighborhood {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) {v : E'} (hv : v ∈ P.positiveCenters) :
    ∃ U : Set E', IsOpen U ∧ v ∈ U ∧
      ∀ w ∈ U, 0 < P.sideLabel.side w := by
  exact P.sideLabel.exists_positive_neighborhood
    (P.mem_positiveCenters_iff.mp hv).2


-- @@ L568-580 verbatim
/-- A south event has a neighborhood disjoint from the north fiber, so it can be
discarded when composing a north-only event schedule. -/
theorem negative_event_neighborhood_disjoint_positiveFiber
    {C : FramedLevelCobordism n} (P : LabeledMorsePosition C)
    {v : E'} (hv : v ∈ P.negativeCenters) :
    ∃ U : Set E', IsOpen U ∧ v ∈ U ∧ Disjoint U P.sideLabel.positiveFiber := by
  obtain ⟨U, hUopen, hvU, hUneg⟩ :=
    P.sideLabel.exists_negative_neighborhood
      (P.mem_negativeCenters_iff.mp hv).2
  refine ⟨U, hUopen, hvU, ?_⟩
  rw [Set.disjoint_left]
  intro w hwU hwpos
  linarith [hUneg w hwU, hwpos.2]


-- @@ L582-592 verbatim
/-- Every event center comes with a sign-constant neighborhood. -/
theorem event_sign_neighborhood {C : FramedLevelCobordism n}
    (P : LabeledMorsePosition C) {v : E'} (hv : v ∈ P.position.centers) :
    (∃ U : Set E', IsOpen U ∧ v ∈ U ∧
        ∀ w ∈ U, 0 < P.sideLabel.side w) ∨
      (∃ U : Set E', IsOpen U ∧ v ∈ U ∧
        ∀ w ∈ U, P.sideLabel.side w < 0) := by
  rcases P.event_mem_positive_or_negative hv with hvp | hvn
  · exact Or.inl (P.positive_event_neighborhood hvp)
  · exact Or.inr (P.sideLabel.exists_negative_neighborhood
      (P.mem_negativeCenters_iff.mp hvn).2)


-- @@ L594-594 verbatim
end LabeledMorsePosition


-- @@ L596-596 verbatim
/-! ## The actual two-dimensional Sard step -/


-- @@ L598-604 verbatim
/-- Taking the adjoint of a scalar differential, as a continuous linear operation. -/
def scalarAdjointCLM : (E₂ →L[ℝ] ℝ) →L[ℝ] (ℝ →L[ℝ] E₂) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
      map_smul' := fun c A => by
        rw [RingHom.id_apply, map_smulₛₗ, starRingEnd_apply, star_trivial] }


-- @@ L606-608 verbatim
/-- The Euclidean gradient of a smooth chart time function. -/
def chartGradient (f : E₂ → ℝ) (x : E₂) : E₂ :=
  scalarAdjointCLM (fderiv ℝ f x) 1


-- @@ L610-613 verbatim
theorem contDiff_chartGradient {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (chartGradient f) := by
  exact (scalarAdjointCLM.contDiff.comp
    (hf.fderiv_right (by simp))).clm_apply contDiff_const


-- @@ L615-621 verbatim
/-- Sard supplies arbitrarily small gradient values at which the Hessian is
nonsingular at every preimage.  Subtracting the corresponding linear form is the
standard local Morse tilt. -/
theorem exists_small_regular_chartGradient {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ Metric.ball (0 : E₂) ε, IsRegularValue (chartGradient f) q :=
  sard_exists_regular_value_in_ball (contDiff_chartGradient hf) 0 hε


-- @@ L623-656 verbatim
/-- A regular value of a smooth self-map has a discrete inverse image. -/
theorem isDiscrete_preimage_singleton_of_regularValue
    {f : E₂ → E₂} (hf : ContDiff ℝ ∞ f) {q : E₂}
    (hq : IsRegularValue f q) : IsDiscrete (f ⁻¹' ({q} : Set E₂)) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hfx : f x = q := by simpa using hx
  have hsurj : Surjective (fderiv ℝ f x) := hq x hfx
  have hinj : Injective (fderiv ℝ f x) := by
    exact LinearMap.injective_iff_surjective.mpr hsurj
  let e : E₂ ≃L[ℝ] E₂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  have hderiv : HasFDerivAt f (e : E₂ →L[ℝ] E₂) x := by
    have h := (hf.differentiable (by simp) x).hasFDerivAt
    simpa [e, ContinuousLinearEquiv.coe_ofBijective] using h
  let φ := hf.contDiffAt.toOpenPartialHomeomorph f hderiv (by simp)
  refine ⟨φ.source, φ.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hyU, hyq⟩
    rw [mem_preimage, mem_singleton_iff] at hyq
    have hxU : x ∈ φ.source :=
      hf.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)
    have hφ : (φ : E₂ → E₂) = f := by rfl
    have hφyx : φ y = φ x := by
      rw [hφ, hyq, hfx]
    have hxy : y = x := φ.injOn hyU hxU hφyx
    simpa [hxy]
  · intro hy
    rw [mem_singleton_iff] at hy
    subst y
    refine ⟨?_, ?_⟩
    · exact hf.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)
    · simpa [hfx]


-- @@ L658-666 verbatim
/-- Consequently, a regular gradient level has only finitely many points in any
compact chart core. -/
theorem finite_regularValue_preimage_inter_compact
    {f : E₂ → E₂} (hf : ContDiff ℝ ∞ f) {q : E₂}
    (hq : IsRegularValue f q) {K : Set E₂} (hK : IsCompact K) :
    (f ⁻¹' ({q} : Set E₂) ∩ K).Finite := by
  rw [inter_comm]
  apply (hK.inter_right (isClosed_singleton.preimage hf.continuous)).finite
  exact (isDiscrete_preimage_singleton_of_regularValue hf hq).mono inter_subset_right


-- @@ L668-678 verbatim
/-- Scalar regular values can be chosen in every nonempty interval; this is the
critical-value-separation tool used after the finite-point step. -/
theorem exists_scalar_regular_value_between {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, ∀ x, f x = c → fderiv ℝ f x ≠ 0 := by
  have hvol : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.mpr hab
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae (regular_value_ae f hf))


-- @@ L680-680 verbatim
end Submission
