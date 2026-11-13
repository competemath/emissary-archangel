import Submission.MorseAtlasAssembly
import Submission.MorseEventSchedule
import Submission.MorseGlobalValueSeparation


-- @@ L5-20 verbatim
/-!
# A Morse schedule which remembers the installed finite critical index

`MorseAtlas.toMorsePosition` is intentionally choice based: it first turns the
critical locus into a finite set and then chooses one local model at every
center.  For the installed generic atlas this forgets which finite critical
index supplied the model.  The chronological event constructors need precisely
that identification in order to reuse the already proved minimum, saddle, and
maximum geometry.

This file builds the same `MorsePosition` directly from the finite generic
critical set.  Its model field is the installed event itself (transported only
along the equality between its installed center and the selected center).  It
then exposes, at every chronological event time, the original critical index
and the exact model equation.
-/


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L31-31 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L33-33 verbatim
namespace MorseAtlasAssemblyContract


-- @@ L35-36 verbatim
variable {ι : Type*} [Fintype ι] {A : FiniteIFTChartFamily ι}
  {G : GenericFiniteIFTAtlas A}


-- @@ L38-42 verbatim
private theorem eventIndex_transport {C : FramedLevelCobordism n}
    {v w : E'} (h : v = w) (M : StandardMorseEventAt C v) :
    (h ▸ M).index = M.index := by
  subst w
  rfl


-- @@ L44-49 verbatim
/-- The original finite generic critical index which installed a given center. -/
def criticalIndexAtCenter (D : MorseAtlasAssemblyContract (n := n) G)
    {v : E'} (hv : v ∈ G.criticalPoints.image D.center) :
    {p : Σ _ : ι, E₂ // p ∈ G.criticalPoints} :=
  ⟨(Finset.mem_image.mp hv).choose,
    (Finset.mem_image.mp hv).choose_spec.1⟩


-- @@ L51-55 verbatim
theorem center_criticalIndexAtCenter
    (D : MorseAtlasAssemblyContract (n := n) G)
    {v : E'} (hv : v ∈ G.criticalPoints.image D.center) :
    D.center (D.criticalIndexAtCenter hv) = v :=
  (Finset.mem_image.mp hv).choose_spec.2


-- @@ L57-63 verbatim
/-- The installed event at a center, without passing through a `Nonempty.some`. -/
def installedEventAtCenter
    (D : MorseAtlasAssemblyContract (n := n) G)
    {v : E'} (hv : v ∈ G.criticalPoints.image D.center) :
    StandardMorseEventAt D.output v := by
  let p := D.criticalIndexAtCenter hv
  exact D.center_criticalIndexAtCenter hv ▸ D.event p p.property


-- @@ L65-74 verbatim
/-- A finite Morse position whose centers and event models retain their finite
generic critical indices definitionally. -/
def toIndexedMorsePosition
    (D : MorseAtlasAssemblyContract (n := n) G) :
    MorsePosition D.output where
  centers := G.criticalPoints.image D.center
  centers_exact := by
    simpa only [Finset.coe_image] using D.centers_exact
  model := fun _ hv => D.installedEventAtCenter hv
  distinct_times := D.toMorsePosition_distinct_times


-- @@ L76-78 verbatim
@[simp] theorem toIndexedMorsePosition_centers
    (D : MorseAtlasAssemblyContract (n := n) G) :
    D.toIndexedMorsePosition.centers = G.criticalPoints.image D.center := rfl


-- @@ L80-84 verbatim
theorem toIndexedMorsePosition_centers_exact
    (D : MorseAtlasAssemblyContract (n := n) G) :
    (D.toIndexedMorsePosition.centers : Set E') =
      coreCriticalPoints D.output :=
  D.toIndexedMorsePosition.centers_exact


-- @@ L86-92 verbatim
/-- The finite generic critical index underlying a chronological event. -/
def eventCriticalIndex
    (D : MorseAtlasAssemblyContract (n := n) G)
    (t : ℝ) (ht : t ∈ D.toIndexedMorsePosition.eventTimes) :
    {p : Σ _ : ι, E₂ // p ∈ G.criticalPoints} :=
  D.criticalIndexAtCenter
    (D.toIndexedMorsePosition.eventCenter_mem t ht)


-- @@ L94-101 verbatim
/-- The installed center of the recovered finite index is exactly the center
selected by the chronological schedule. -/
theorem center_eventCriticalIndex
    (D : MorseAtlasAssemblyContract (n := n) G)
    (t : ℝ) (ht : t ∈ D.toIndexedMorsePosition.eventTimes) :
    D.center (D.eventCriticalIndex t ht) =
      D.toIndexedMorsePosition.eventCenter t ht :=
  D.center_criticalIndexAtCenter _


-- @@ L103-112 verbatim
/-- The recovered critical index has precisely the chronological event time. -/
theorem eventCriticalIndex_time
    (D : MorseAtlasAssemblyContract (n := n) G)
    (t : ℝ) (ht : t ∈ D.toIndexedMorsePosition.eventTimes) :
    G.localSeparatedTime (D.eventCriticalIndex t ht)
        (D.eventCriticalIndex t ht).1.2 = t := by
  rw [← D.center_time (D.eventCriticalIndex t ht)
    (D.eventCriticalIndex t ht).property,
    D.center_eventCriticalIndex t ht,
    D.toIndexedMorsePosition.eventCenter_time t ht]


-- @@ L114-124 verbatim
/-- Exact chronological model equation: the scheduled chart is the installed
chart at the recovered finite critical index, with only its center equality
transported. -/
theorem eventModel_eq_installedEvent
    (D : MorseAtlasAssemblyContract (n := n) G)
    (t : ℝ) (ht : t ∈ D.toIndexedMorsePosition.eventTimes) :
    D.toIndexedMorsePosition.eventModel t ht =
      D.center_eventCriticalIndex t ht ▸
        D.event (D.eventCriticalIndex t ht)
          (D.eventCriticalIndex t ht).property := by
  rfl


-- @@ L126-135 verbatim
/-- In particular, chronological scheduling preserves the installed Morse
index rather than choosing a potentially unrelated local model. -/
theorem eventModel_index_eq_installed
    (D : MorseAtlasAssemblyContract (n := n) G)
    (t : ℝ) (ht : t ∈ D.toIndexedMorsePosition.eventTimes) :
    (D.toIndexedMorsePosition.eventModel t ht).index =
      (D.event (D.eventCriticalIndex t ht)
        (D.eventCriticalIndex t ht).property).index := by
  rw [D.eventModel_eq_installedEvent t ht]
  exact eventIndex_transport _ _


-- @@ L137-152 verbatim
/-- The finite index above is propositionally canonical: any installed
critical index with the same separated event time is equal to it. -/
theorem subtype_eq_eventCriticalIndex_of_time
    (D : MorseAtlasAssemblyContract (n := n) G)
    (t : ℝ) (ht : t ∈ D.toIndexedMorsePosition.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hpt : G.localSeparatedTime p p.2 = t) :
    (⟨p, hp⟩ : {q : Σ _ : ι, E₂ // q ∈ G.criticalPoints}) =
      D.eventCriticalIndex t ht := by
  apply Subtype.ext
  apply G.localCriticalValues_injective hp
    (D.eventCriticalIndex t ht).property
  change G.localSeparatedTime p p.2 =
    G.localSeparatedTime (D.eventCriticalIndex t ht)
      (D.eventCriticalIndex t ht).1.2
  exact hpt.trans (D.eventCriticalIndex_time t ht).symm


-- @@ L154-154 verbatim
end MorseAtlasAssemblyContract


-- @@ L156-156 verbatim
/-! ## The production shared-cutoff and value-separation route -/


-- @@ L158-158 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData

-- @@ L159-159 verbatim
namespace StableCriticalValueShiftData


-- @@ L161-161 verbatim
variable {C : FramedLevelCobordism n} {I : Type*} [Fintype I]

-- @@ L162-162 verbatim
variable {B : FiniteIFTSurfaceCover C I}

-- @@ L163-164 verbatim
variable {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
  {χ : SmoothCutoff K U}

-- @@ L165-165 verbatim
variable {R : B.SharedCutoffMorseData χ}


-- @@ L167-171 verbatim
private theorem transportedEventIndex {D : FramedLevelCobordism n}
    {v w : E'} (h : v = w) (M : StandardMorseEventAt D v) :
    (h ▸ M).index = M.index := by
  subst w
  rfl


-- @@ L173-180 verbatim
/-- The duplicate-free global critical event which installed a value-separated
center. -/
def globalEventAtCenter (S : StableCriticalValueShiftData R)
    {v : E'}
    (hv : v ∈ Finset.univ.image
      S.toCriticalValueShiftData.shiftedCenter) :
    GlobalCriticalEvent R :=
  (Finset.mem_image.mp hv).choose


-- @@ L182-189 verbatim
theorem shiftedCenter_globalEventAtCenter
    (S : StableCriticalValueShiftData R)
    {v : E'}
    (hv : v ∈ Finset.univ.image
      S.toCriticalValueShiftData.shiftedCenter) :
    S.toCriticalValueShiftData.shiftedCenter
        (S.globalEventAtCenter hv) = v :=
  (Finset.mem_image.mp hv).choose_spec.2


-- @@ L191-201 verbatim
/-- The transported production event at a selected shifted center, without
passing through the choice-based `MorseAtlas.localModel`. -/
def installedEventAtShiftedCenter
    (S : StableCriticalValueShiftData R)
    {v : E'}
    (hv : v ∈ Finset.univ.image
      S.toCriticalValueShiftData.shiftedCenter) :
    StandardMorseEventAt S.toCriticalValueShiftData.output v := by
  let e := S.globalEventAtCenter hv
  exact S.shiftedCenter_globalEventAtCenter hv ▸
    S.toCriticalValueShiftData.transportedStandardMorseEvent e


-- @@ L203-212 verbatim
/-- The production Morse position, enumerated by the actual duplicate-free
global critical events and storing their transported models exactly. -/
def toIndexedMorsePosition (S : StableCriticalValueShiftData R) :
    MorsePosition S.toCriticalValueShiftData.output where
  centers := Finset.univ.image S.toCriticalValueShiftData.shiftedCenter
  centers_exact := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      S.range_shiftedCenter_eq_coreCriticalPoints
  model := fun _ hv => S.installedEventAtShiftedCenter hv
  distinct_times := S.toMorseAtlas.distinct_times


-- @@ L214-217 verbatim
@[simp] theorem toIndexedMorsePosition_centers
    (S : StableCriticalValueShiftData R) :
    S.toIndexedMorsePosition.centers =
      Finset.univ.image S.toCriticalValueShiftData.shiftedCenter := rfl


-- @@ L219-223 verbatim
theorem toIndexedMorsePosition_centers_exact
    (S : StableCriticalValueShiftData R) :
    (S.toIndexedMorsePosition.centers : Set E') =
      coreCriticalPoints S.toCriticalValueShiftData.output :=
  S.toIndexedMorsePosition.centers_exact


-- @@ L225-230 verbatim
/-- The actual duplicate-free global event underlying a chronological time. -/
def chronologicalGlobalEvent
    (S : StableCriticalValueShiftData R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    GlobalCriticalEvent R :=
  S.globalEventAtCenter (S.toIndexedMorsePosition.eventCenter_mem t ht)


-- @@ L232-238 verbatim
theorem shiftedCenter_chronologicalGlobalEvent
    (S : StableCriticalValueShiftData R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    S.toCriticalValueShiftData.shiftedCenter
        (S.chronologicalGlobalEvent t ht) =
      S.toIndexedMorsePosition.eventCenter t ht :=
  S.shiftedCenter_globalEventAtCenter _


-- @@ L240-246 verbatim
theorem chronologicalGlobalEvent_time
    (S : StableCriticalValueShiftData R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    tcoord (S.toCriticalValueShiftData.shiftedCenter
      (S.chronologicalGlobalEvent t ht)) = t := by
  rw [S.shiftedCenter_chronologicalGlobalEvent t ht,
    S.toIndexedMorsePosition.eventCenter_time t ht]


-- @@ L248-256 verbatim
/-- Exact production model equation at a chronological time. -/
theorem eventModel_eq_transportedStandardMorseEvent
    (S : StableCriticalValueShiftData R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    S.toIndexedMorsePosition.eventModel t ht =
      S.shiftedCenter_chronologicalGlobalEvent t ht ▸
        S.toCriticalValueShiftData.transportedStandardMorseEvent
          (S.chronologicalGlobalEvent t ht) := by
  rfl


-- @@ L258-267 verbatim
/-- Hence the chronological model has exactly the Morse index of the original
owner model transported through the value-separation diffeomorphism. -/
theorem eventModel_index_eq_ownerModel
    (S : StableCriticalValueShiftData R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes) :
    (S.toIndexedMorsePosition.eventModel t ht).index =
      (S.toCriticalValueShiftData.ownerModel
        (S.chronologicalGlobalEvent t ht)).index := by
  rw [S.eventModel_eq_transportedStandardMorseEvent t ht]
  exact transportedEventIndex _ _


-- @@ L269-281 verbatim
/-- The chronological global event is canonical, since shifted event times
are injective. -/
theorem eq_chronologicalGlobalEvent_of_time
    (S : StableCriticalValueShiftData R)
    (t : ℝ) (ht : t ∈ S.toIndexedMorsePosition.eventTimes)
    (e : GlobalCriticalEvent R)
    (het : tcoord (S.toCriticalValueShiftData.shiftedCenter e) = t) :
    e = S.chronologicalGlobalEvent t ht := by
  apply S.toCriticalValueShiftData.shiftedCenter_time_injective
  change tcoord (S.toCriticalValueShiftData.shiftedCenter e) =
    tcoord (S.toCriticalValueShiftData.shiftedCenter
      (S.chronologicalGlobalEvent t ht))
  exact het.trans (S.chronologicalGlobalEvent_time t ht).symm


-- @@ L283-283 verbatim
end StableCriticalValueShiftData

-- @@ L284-284 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L286-286 verbatim
end Submission
