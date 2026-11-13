import Mathlib
import Submission.PositiveSheetSlabTransport
import Submission.ExplicitOrbitParam
import Submission.SignedMorseEventTransport


-- @@ L6-18 verbatim
/-!
# Frame transport on the positive sheet across a negative Morse event

The localized field of `PositiveSheetSlabTransport` flows the complete
positive sheet through a bracket containing a critical point on the negative
sheet.  This file upgrades its pointwise bijection to the component and frame
transport consumed by `NegativeEventPositiveExteriorTransportData`.

Only points on the transported positive circles enter the moving-frame
construction.  Their spatial derivatives are surjective by the collar
regularity carried by `PositiveSheetSlabTamedField`; no regularity of the
negative sheet, and hence no `regularSlab` hypothesis, is used.
-/


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
set_option maxHeartbeats 4000000


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
open Set Function Topology Module Submodule InnerProductSpace

-- @@ L27-27 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval BigOperators


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L34-34 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L36-36 verbatim
namespace PositiveSheetSlabTamedField


-- @@ L38-46 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁} {a b t₁ t₂ : ℝ}
  (W : PositiveSheetSlabTamedField C a b)
  (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
  (hreg₁ : sliceRegular C.cobordism.G t₁)
  (hreg₂ : sliceRegular C.cobordism.G t₂)
  (V₁ : TamedField (SlabTamedField.sliceFLSAt
    C.cobordism.toLevelCobordismData t₁ hreg₁))
  (V₂ : TamedField (SlabTamedField.sliceFLSAt
    C.cobordism.toLevelCobordismData t₂ hreg₂))


-- @@ L48-48 verbatim
/-! ## The induced equivalence of positive orbit components -/


-- @@ L50-57 verbatim
/-- A positive source orbit stays in the positive source slice. -/
theorem sourceOrbit_subset_positiveSliceFiber
    (O : V₁.OrbitIndex)
    (hO : (O : Set E₁) ∈
      (C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁) :
    (O : Set E₁) ⊆ positiveSliceFiber C t₁ := by
  rw [positiveSliceFiber_eq_positivePart C t₁ hreg₁]
  exact hO


-- @@ L59-125 verbatim
/-- On a positive source component the localized slice transport lands in the
target flow component containing the transported base point. -/
theorem sliceTransport_mapsTo_positiveOrbit
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    {p : E₁} (hp : p ∈
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        t₁ hreg₁).fiber)
    (hppos : 0 < C (cobSpaceTime p t₁)) :
    MapsTo (W.sliceTransport t₁ t₂) (V₁.orbit p)
      (V₂.orbit (W.sliceTransport t₁ t₂ p)) := by
  let f : E₁ → E₁ := W.sliceTransport t₁ t₂
  let γ : ℝ → E₁ := fun s => f (V₁.flow p s)
  let A : Set ℝ := γ ⁻¹' V₂.orbit (f p)
  have hpPos : p ∈ positiveSliceFiber C t₁ := by
    exact ⟨hp, hppos⟩
  have hqPos : f p ∈ positiveSliceFiber C t₂ :=
    W.sliceTransport_mapsTo ht₁ ht₂ hpPos
  have hq : f p ∈
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        t₂ hreg₂).fiber := hqPos.1
  have hflowPos : ∀ s, V₁.flow p s ∈ positiveSliceFiber C t₁ := by
    intro s
    refine ⟨V₁.flow_mem_fiber hp s, ?_⟩
    let η : C(I, E₂) :=
      ⟨fun u => cobSpaceTime (V₁.flow p ((u : ℝ) * s)) t₁,
        (by
          have hflow : Continuous fun u : I =>
              V₁.flow p ((u : ℝ) * s) :=
            (V₁.continuous_flow p).comp
              (continuous_subtype_val.mul (continuous_const :
                Continuous fun _ : I => s))
          have hcob : Continuous fun x : E₁ => cobSpaceTime x t₁ := by
            rw [continuous_iff_continuousAt]
            exact fun x => (hasFDerivAt_cobSpaceTime t₁ x).continuousAt
          exact hcob.comp hflow)⟩
    have hη : ∀ u, C.cobordism.G (η u) = 0 := by
      intro u
      exact V₁.flow_mem_fiber hp _
    have hs := C.pos_iff_of_zeroFiber_path η hη
    have hzero : 0 < C (η 0) := by simpa [η] using hppos
    simpa [η] using hs.mp hzero
  have hAS : A ⊆ (Set.univ : Set ℝ) := fun _ _ => Set.mem_univ _
  have hAclosed : IsClosed A :=
    (V₂.isCompact_orbit hq).isClosed.preimage
      ((W.continuous_sliceTransport t₁ t₂).comp (V₁.continuous_flow p))
  have hAopen : ∀ s ∈ A, ∃ r > 0,
      (Set.univ : Set ℝ) ∩ Metric.ball s r ⊆ A := by
    intro s hs
    obtain ⟨r, hr, hrsub⟩ := V₂.orbit_isOpen_in_fiber hq hs
    have hopen : IsOpen (γ ⁻¹' Metric.ball (γ s) r) :=
      Metric.isOpen_ball.preimage
        ((W.continuous_sliceTransport t₁ t₂).comp (V₁.continuous_flow p))
    have hsmem : s ∈ γ ⁻¹' Metric.ball (γ s) r := Metric.mem_ball_self hr
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen s hsmem
    refine ⟨ε, hε, ?_⟩
    rintro u ⟨-, hus⟩
    apply hrsub
    exact ⟨(W.sliceTransport_mapsTo ht₁ ht₂ (hflowPos u)).1, hεsub hus⟩
  have hA0 : A.Nonempty := by
    refine ⟨0, ?_⟩
    change f (V₁.flow p 0) ∈ V₂.orbit (f p)
    rw [V₁.flow_zero]
    exact V₂.mem_orbit_self (f p)
  have hAll : (Set.univ : Set ℝ) ⊆ A :=
    subset_of_relOpen_closed isPreconnected_univ hAS hAclosed hAopen hA0
  rintro x ⟨s, rfl⟩
  exact hAll (Set.mem_univ s)


-- @@ L127-152 verbatim
/-- Target orbit containing the transported canonical point of a selected
positive source orbit. -/
def positiveOrbitMap
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    {O // O ∈ V₂.selectedOrbitFinset
      ((C.sliceSign t₂ hreg₂).positiveOrbitCollection V₂)} := by
  let p : E₁ := V₁.orbitPoint O.1
  let y : E₁ := W.sliceTransport t₁ t₂ p
  have hpPos : p ∈ positiveSliceFiber C t₁ :=
    sourceOrbit_subset_positiveSliceFiber (C := C) hreg₁ V₁ O.1
      ((V₁.mem_selectedOrbitFinset O.1).mp O.2)
      (by rw [V₁.orbitPoint_orbit O.1]; exact V₁.mem_orbit_self p)
  have hyPos : y ∈ positiveSliceFiber C t₂ :=
    W.sliceTransport_mapsTo ht₁ ht₂ hpPos
  let Q : V₂.OrbitIndex :=
    ⟨V₂.orbit y, V₂.mem_orbitFinset.mpr ⟨y, hyPos.1, rfl⟩⟩
  refine ⟨Q, (V₂.mem_selectedOrbitFinset Q).mpr ?_⟩
  rw [(C.sliceSign t₂ hreg₂).mem_positiveOrbitCollection_iff]
  have hqmem : V₂.orbitPoint Q ∈ V₂.orbit y := by
    have hself := V₂.mem_orbit_self (V₂.orbitPoint Q)
    rwa [← V₂.orbitPoint_orbit Q] at hself
  have hySign : 0 < (C.sliceSign t₂ hreg₂) y := hyPos.2
  exact ((C.sliceSign t₂ hreg₂).pos_iff_of_mem_orbit V₂ hyPos.1 hqmem).mp
    hySign


-- @@ L154-160 verbatim
@[simp] theorem positiveOrbitMap_val
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    (((W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
        (V₁ := V₁) (V₂ := V₂) ht₁ ht₂ O).1 :
        V₂.OrbitIndex) : Set E₁) =
      V₂.orbit (W.sliceTransport t₁ t₂ (V₁.orbitPoint O.1)) := rfl


-- @@ L162-204 verbatim
/-- Forward and reverse maps on positive components are inverse. -/
theorem positiveOrbitMap_leftInverse
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    W.positiveOrbitMap (hreg₁ := hreg₂) (hreg₂ := hreg₁)
        (V₁ := V₂) (V₂ := V₁) ht₂ ht₁
        (W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
          (V₁ := V₁) (V₂ := V₂) ht₁ ht₂ O) = O := by
  apply Subtype.ext
  apply Subtype.ext
  let p : E₁ := V₁.orbitPoint O.1
  let q : E₁ := W.sliceTransport t₁ t₂ p
  let O₂ := (W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
    (V₁ := V₁) (V₂ := V₂) ht₁ ht₂ O).1
  let r : E₁ := V₂.orbitPoint O₂
  have hpPos : p ∈ positiveSliceFiber C t₁ :=
    sourceOrbit_subset_positiveSliceFiber (C := C) hreg₁ V₁ O.1
      ((V₁.mem_selectedOrbitFinset O.1).mp O.2)
      (by rw [V₁.orbitPoint_orbit O.1]; exact V₁.mem_orbit_self p)
  have hqPos : q ∈ positiveSliceFiber C t₂ :=
    W.sliceTransport_mapsTo ht₁ ht₂ hpPos
  have hrOrbit : r ∈ V₂.orbit q := by
    have hself := V₂.mem_orbit_self r
    have hOr : (O₂ : Set E₁) = V₂.orbit r := V₂.orbitPoint_orbit O₂
    have hOq : (O₂ : Set E₁) = V₂.orbit q := rfl
    rwa [← hOq, hOr]
  have hrPos : r ∈ positiveSliceFiber C t₂ := by
    rw [positiveSliceFiber_eq_positivePart C t₂ hreg₂]
    exact ((V₂.mem_selectedOrbitFinset O₂).mp
      (W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
        (V₁ := V₁) (V₂ := V₂) ht₁ ht₂ O).2) (by
        rw [V₂.orbitPoint_orbit O₂]
        exact V₂.mem_orbit_self r)
  have hback := W.sliceTransport_mapsTo_positiveOrbit
    (hreg₁ := hreg₂) (hreg₂ := hreg₁) (V₁ := V₂) (V₂ := V₁)
    ht₂ ht₁ (p := q) hqPos.1 hqPos.2 hrOrbit
  have hqp : W.sliceTransport t₂ t₁ q = p := by
    exact W.sliceTransport_leftInverse ht₁ ht₂ hpPos
  have hrSource : W.sliceTransport t₂ t₁ r ∈ V₁.orbit p := by
    rwa [hqp] at hback
  change V₁.orbit (W.sliceTransport t₂ t₁ r) = (O.1 : Set E₁)
  exact (V₁.orbit_eq_of_mem hrSource).trans (V₁.orbitPoint_orbit O.1).symm


-- @@ L206-222 verbatim
/-- Actual equivalence of the finite positive component families. -/
def positiveOrbitEquiv
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)} ≃
    {O // O ∈ V₂.selectedOrbitFinset
      ((C.sliceSign t₂ hreg₂).positiveOrbitCollection V₂)} where
  toFun := W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
    (V₁ := V₁) (V₂ := V₂) ht₁ ht₂
  invFun := W.positiveOrbitMap (hreg₁ := hreg₂) (hreg₂ := hreg₁)
    (V₁ := V₂) (V₂ := V₁) ht₂ ht₁
  left_inv := W.positiveOrbitMap_leftInverse
    (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
    ht₁ ht₂
  right_inv := W.positiveOrbitMap_leftInverse
    (hreg₁ := hreg₂) (hreg₂ := hreg₁) (V₁ := V₂) (V₂ := V₁)
    ht₂ ht₁


-- @@ L224-224 verbatim
/-! ## A moving frame using only positive-sheet regularity -/


-- @@ L226-229 verbatim
/-- Linear interpolation of slice times, independent of the auxiliary empty
slab carried by `W.base`. -/
def positiveIntermediateTime (t₁ t₂ : ℝ) (s : I) : ℝ :=
  t₁ + (s : ℝ) * (t₂ - t₁)


-- @@ L231-242 verbatim
theorem positiveIntermediateTime_mem_Icc
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (s : I) :
    positiveIntermediateTime t₁ t₂ s ∈ Icc a b := by
  constructor
  · have hs₀ : 0 ≤ (s : ℝ) := s.2.1
    have hs₁ : (s : ℝ) ≤ 1 := s.2.2
    rcases le_total t₁ t₂ with h | h <;>
      dsimp [positiveIntermediateTime] <;> nlinarith [ht₁.1, ht₂.1]
  · have hs₀ : 0 ≤ (s : ℝ) := s.2.1
    have hs₁ : (s : ℝ) ≤ 1 := s.2.2
    rcases le_total t₁ t₂ with h | h <;>
      dsimp [positiveIntermediateTime] <;> nlinarith [ht₁.2, ht₂.2]


-- @@ L244-246 verbatim
theorem continuous_positiveIntermediateTime (t₁ t₂ : ℝ) :
    Continuous (positiveIntermediateTime t₁ t₂) :=
  continuous_const.add (continuous_subtype_val.mul continuous_const)


-- @@ L248-256 verbatim
/-- The source fundamental circle transported to every intermediate positive
slice. -/
def positiveTransportedOrbitPoint
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)})
    (q : I × I) : E₁ :=
  W.sliceTransport t₁ (positiveIntermediateTime t₁ t₂ q.1)
    (V₁.flow (V₁.orbitPoint O.1)
      ((q.2 : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1)))


-- @@ L258-290 verbatim
theorem continuous_positiveTransportedOrbitPoint
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    Continuous (W.positiveTransportedOrbitPoint
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O) := by
  let p : E₁ := V₁.orbitPoint O.1
  let T : ℝ := V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1)
  have hsource : Continuous fun q : I × I => V₁.flow p ((q.2 : ℝ) * T) :=
    (V₁.continuous_flow p).comp
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const)
  have hinit : Continuous fun q : I × I =>
      cobSpaceTime (V₁.flow p ((q.2 : ℝ) * T)) t₁ := by
    have hcob : Continuous fun z : E₁ => cobSpaceTime z t₁ := by
      rw [continuous_iff_continuousAt]
      exact fun z => (hasFDerivAt_cobSpaceTime t₁ z).continuousAt
    exact hcob.comp hsource
  have htime : Continuous fun q : I × I =>
      positiveIntermediateTime t₁ t₂ q.1 - t₁ :=
    ((continuous_positiveIntermediateTime t₁ t₂).comp continuous_fst).sub
      continuous_const
  have hflow : Continuous fun q : I × I =>
      W.flow (cobSpaceTime (V₁.flow p ((q.2 : ℝ) * T)) t₁)
        (positiveIntermediateTime t₁ t₂ q.1 - t₁) :=
    W.base.continuous_flow_uncurry.comp (hinit.prodMk htime)
  have hspace : Continuous (spacePart (n := n)) := by
    have hsp : LipschitzWith 1 (spacePart (n := n)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      change ‖spacePart (x - y)‖ ≤ ‖x - y‖
      exact norm_spacePart_le (x - y)
    exact hsp.continuous
  exact hspace.comp hflow


-- @@ L292-308 verbatim
theorem positiveTransportedOrbitPoint_mem_positiveSliceFiber
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)})
    (q : I × I) :
    W.positiveTransportedOrbitPoint
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q ∈
      positiveSliceFiber C (positiveIntermediateTime t₁ t₂ q.1) := by
  have hsource : V₁.flow (V₁.orbitPoint O.1)
        ((q.2 : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1)) ∈
      positiveSliceFiber C t₁ := by
    apply sourceOrbit_subset_positiveSliceFiber (C := C) hreg₁ V₁ O.1
      ((V₁.mem_selectedOrbitFinset O.1).mp O.2)
    rw [V₁.orbitPoint_orbit O.1]
    exact V₁.flow_mem_orbit _ _
  exact W.sliceTransport_mapsTo ht₁
    (positiveIntermediateTime_mem_Icc ht₁ ht₂ q.1) hsource


-- @@ L310-339 verbatim
/-- Every moving positive point is spatially regular, although its whole time
slice need not be. -/
theorem positiveTransportedOrbitPoint_regular
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)})
    (q : I × I) :
    W.positiveTransportedOrbitPoint
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q ∈
      regularSet (sliceMap C.cobordism.G
        (positiveIntermediateTime t₁ t₂ q.1)) := by
  let τ := positiveIntermediateTime t₁ t₂ q.1
  let x := W.positiveTransportedOrbitPoint
    (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q
  have hxPos : x ∈ positiveSliceFiber C τ :=
    W.positiveTransportedOrbitPoint_mem_positiveSliceFiber
      (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O q
  have hcore : cobSpaceTime x τ ∈ C.positiveSlabCore a b := by
    refine ⟨hxPos.1, ?_, hxPos.2.le⟩
    simpa [τ] using positiveIntermediateTime_mem_Icc ht₁ ht₂ q.1
  have hcollar : cobSpaceTime x τ ∈
      Metric.cthickening W.delta (C.positiveSlabCore a b) :=
    Metric.self_subset_cthickening (E := C.positiveSlabCore a b) hcore
  have hslab := W.subset_slabRegular hcollar
  have hspatial : Surjective (spatialDeriv C.cobordism.G (cobSpaceTime x τ)) := by
    by_contra hnot
    exact hslab.2 ((kerProj_timeVec_eq_zero_iff hslab.1).mpr hnot)
  change Surjective (fderiv ℝ (sliceMap C.cobordism.G τ) x)
  rw [fderiv_sliceMap C.cobordism.smooth]
  exact hspatial


-- @@ L341-342 verbatim
/-! The next three pointwise lemmas are the local-regularity versions of the
corresponding `FramedLevelSet` lemmas in `LevelFrame`. -/


-- @@ L344-362 verbatim
theorem linearIndependent_sliceFrameAt_of_regular
    (G : E₂ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (x : E₁)
    (hx : x ∈ regularSet (sliceMap G t)) :
    LinearIndependent ℝ (SlabTamedField.sliceFrameAt G t x) := by
  unfold SlabTamedField.sliceFrameAt
  apply linearIndependent_finCons.mpr
  refine ⟨(surjective_fderiv_iff_linearIndependent (sliceMap G t) x).mp hx, ?_⟩
  intro hmem
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun _).mp hmem
  have hzero : ⟪tauField (sliceMap G t) x, tauField (sliceMap G t) x⟫_ℝ = 0 := by
    nth_rewrite 2 [← hc]
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [real_inner_smul_right, tauField_inner_gradVec, mul_zero]
  have hz : tauField (sliceMap G t) x = 0 := inner_self_eq_zero.mp hzero
  have hnorm : ‖tauField (sliceMap G t) x‖ = 1 := norm_tauField hx
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm


-- @@ L364-375 verbatim
theorem det_rowsMatrix_sliceFrameAt_pos
    (G : E₂ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (x : E₁)
    (hx : x ∈ regularSet (sliceMap G t)) :
    0 < (rowsMatrix (SlabTamedField.sliceFrameAt G t x)).det := by
  have hrows : rowsMatrix (SlabTamedField.sliceFrameAt G t x) =
      crossRows (fun i => gradVec (sliceMap G t) i x)
        (tauField (sliceMap G t) x) := by
    ext i j
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;>
      simp [rowsMatrix, SlabTamedField.sliceFrameAt, crossRows]
  rw [hrows]
  exact crossDet_tauField_pos hx


-- @@ L377-425 verbatim
theorem sliceFrameMatrix_mem_SO_of_regular
    (G : E₂ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (x : E₁)
    (hx : x ∈ regularSet (sliceMap G t)) :
    rowsMatrix (gramSchmidtNormed ℝ (SlabTamedField.sliceFrameAt G t x)) ∈
      SOGroup (n + 1) := by
  have hInd := linearIndependent_sliceFrameAt_of_regular G t x hx
  have horthonormal : Orthonormal ℝ
      (gramSchmidtNormed ℝ (SlabTamedField.sliceFrameAt G t x)) :=
    gramSchmidtNormed_orthonormal hInd
  set A := rowsMatrix
    (gramSchmidtNormed ℝ (SlabTamedField.sliceFrameAt G t x)) with hA
  have hmul : A * Aᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hentries : ∀ k, A i k * Aᵀ k j =
        (gramSchmidtNormed ℝ (SlabTamedField.sliceFrameAt G t x) i) k *
          (gramSchmidtNormed ℝ (SlabTamedField.sliceFrameAt G t x) j) k := by
      intro k
      rw [Matrix.transpose_apply]
      rfl
    rw [Finset.sum_congr rfl fun k _ => hentries k]
    have hinner := orthonormal_iff_ite.mp horthonormal i j
    rw [PiLp.inner_apply] at hinner
    simp only [RCLike.inner_apply, conj_trivial] at hinner
    rw [← hinner]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have horth : A ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin (n + 1)) ℝ).mpr hmul
  have hdetpos : 0 < A.det := by
    rw [hA, det_rowsMatrix_gramSchmidtNormed]
    apply mul_pos
    · apply Finset.prod_pos
      intro i _
      have hne : gramSchmidt ℝ (SlabTamedField.sliceFrameAt G t x) i ≠ 0 :=
        gramSchmidt_ne_zero i hInd
      have : 0 < ‖gramSchmidt ℝ (SlabTamedField.sliceFrameAt G t x) i‖ :=
        norm_pos_iff.mpr hne
      positivity
    · exact det_rowsMatrix_sliceFrameAt_pos G t x hx
  have hdetsq : A.det * A.det = 1 := by
    have hdet := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
    exact hdet
  have hdet1 : A.det = 1 := by
    rcases mul_self_eq_one_iff.mp hdetsq with h | h
    · exact h
    · rw [h] at hdetpos
      linarith
  exact Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨horth, hdet1⟩


-- @@ L427-427 verbatim
/-! ## The transported target circle -/


-- @@ L429-437 verbatim
@[simp] theorem positiveTransportedOrbitPoint_zero
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (u : I) :
    W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (0, u) =
      V₁.flow (V₁.orbitPoint O.1)
        ((u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1)) := by
  simp [positiveTransportedOrbitPoint, positiveIntermediateTime,
    PositiveSheetSlabTamedField.sliceTransport, SlabTamedField.sliceTransport]


-- @@ L439-449 verbatim
@[simp] theorem positiveTransportedOrbitPoint_one
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (u : I) :
    W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, u) =
      W.sliceTransport t₁ t₂
        (V₁.flow (V₁.orbitPoint O.1)
          ((u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1))) := by
  unfold positiveTransportedOrbitPoint positiveIntermediateTime
  congr 2
  norm_num


-- @@ L451-461 verbatim
theorem positiveTransportedOrbitPoint_closed
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (s : I) :
    W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (s, 0) =
      W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (s, 1) := by
  unfold positiveTransportedOrbitPoint
  apply congrArg
  simpa using
    (V₁.fundamentalPeriod_periodic (V₁.orbitPoint_mem_fiber O.1) 0).symm


-- @@ L463-586 verbatim
/-- The image of one source fundamental period is a genuine once-around
parametrization of its target positive component. -/
def positiveTargetOrbitParam
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData t₂ hreg₂) V₂ := by
  let p : E₁ := V₁.orbitPoint O.1
  let y : E₁ := W.sliceTransport t₁ t₂ p
  have hpPos : p ∈ positiveSliceFiber C t₁ :=
    sourceOrbit_subset_positiveSliceFiber (C := C) hreg₁ V₁ O.1
      ((V₁.mem_selectedOrbitFinset O.1).mp O.2)
      (by rw [V₁.orbitPoint_orbit O.1]; exact V₁.mem_orbit_self p)
  have hyPos : y ∈ positiveSliceFiber C t₂ :=
    W.sliceTransport_mapsTo ht₁ ht₂ hpPos
  let γ : C(I, E₁) :=
    ⟨fun u => W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, u),
      (W.continuous_positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O).comp
        (by
          simpa only using
            (continuous_const.prodMk continuous_id :
              Continuous fun u : I => ((1 : I), u)))⟩
  refine
    { p := y
      hp := hyPos.1
      curve := γ
      curve_zero := ?_
      curve_closed := ?_
      curve_mem_orbit := ?_
      curve_eq_cases := ?_ }
  · change W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, 0) = y
    rw [W.positiveTransportedOrbitPoint_one
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂)]
    simp [p, y]
  · change W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, 0) =
      W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, 1)
    exact W.positiveTransportedOrbitPoint_closed
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O 1
  · intro u
    change W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, u) ∈
      V₂.orbit y
    rw [W.positiveTransportedOrbitPoint_one
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂)]
    exact W.sliceTransport_mapsTo_positiveOrbit
      (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
      ht₁ ht₂ (V₁.orbitPoint_mem_fiber O.1)
      hpPos.2 (V₁.flow_mem_orbit _ _)
  · intro u v huv
    change W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, u) =
      W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, v) at huv
    rw [W.positiveTransportedOrbitPoint_one
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂),
      W.positiveTransportedOrbitPoint_one
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂)] at huv
    have huPos : V₁.flow p
          ((u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1)) ∈
        positiveSliceFiber C t₁ := by
      apply sourceOrbit_subset_positiveSliceFiber (C := C) hreg₁ V₁ O.1
        ((V₁.mem_selectedOrbitFinset O.1).mp O.2)
      rw [V₁.orbitPoint_orbit O.1]
      exact V₁.flow_mem_orbit _ _
    have hvPos : V₁.flow p
          ((v : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1)) ∈
        positiveSliceFiber C t₁ := by
      apply sourceOrbit_subset_positiveSliceFiber (C := C) hreg₁ V₁ O.1
        ((V₁.mem_selectedOrbitFinset O.1).mp O.2)
      rw [V₁.orbitPoint_orbit O.1]
      exact V₁.flow_mem_orbit _ _
    have hsource := (W.sliceTransport_bijOn ht₁ ht₂).injOn huPos hvPos huv
    have hmem := (V₁.flow_eq_iff_sub_mem_zmultiples
      (V₁.orbitPoint_mem_fiber O.1) _ _).mp hsource
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hTpos := V₁.fundamentalPeriod_pos (V₁.orbitPoint_mem_fiber O.1)
    have huvInt : (u : ℝ) - (v : ℝ) = (k : ℝ) := by
      have hk' : (k : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1) =
          (u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1) -
            (v : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O.1) := by
        simpa [zsmul_eq_mul] using hk
      nlinarith
    rcases lt_trichotomy (u : ℝ) (v : ℝ) with huvlt | huveq | huvgt
    · right; left
      have hknegR : (k : ℝ) < 0 := by rw [← huvInt]; linarith
      have hkneg : k < 0 := by exact_mod_cast hknegR
      have hkge : (-1 : ℤ) ≤ k := by
        have hkgeR : (-1 : ℝ) ≤ (k : ℝ) := by
          rw [← huvInt]; linarith [u.2.1, v.2.2]
        exact_mod_cast hkgeR
      have hkval : k = -1 := by omega
      constructor
      · apply Subtype.ext
        change (u : ℝ) = 0
        have hd : (u : ℝ) - (v : ℝ) = -1 := by rw [huvInt, hkval]; norm_num
        nlinarith [u.2.1, v.2.2]
      · apply Subtype.ext
        change (v : ℝ) = 1
        have hd : (u : ℝ) - (v : ℝ) = -1 := by rw [huvInt, hkval]; norm_num
        nlinarith [u.2.1, v.2.2]
    · exact Or.inl (Subtype.ext huveq)
    · right; right
      have hkposR : (0 : ℝ) < (k : ℝ) := by rw [← huvInt]; linarith
      have hkpos : 0 < k := by exact_mod_cast hkposR
      have hkle : k ≤ 1 := by
        have hkleR : (k : ℝ) ≤ 1 := by
          rw [← huvInt]; linarith [u.2.2, v.2.1]
        exact_mod_cast hkleR
      have hkval : k = 1 := by omega
      constructor
      · apply Subtype.ext
        change (u : ℝ) = 1
        have hd : (u : ℝ) - (v : ℝ) = 1 := by rw [huvInt, hkval]; norm_num
        nlinarith [u.2.2, v.2.1]
      · apply Subtype.ext
        change (v : ℝ) = 0
        have hd : (u : ℝ) - (v : ℝ) = 1 := by rw [huvInt, hkval]; norm_num
        nlinarith [u.2.2, v.2.1]


-- @@ L588-596 verbatim
@[simp] theorem positiveTargetOrbitParam_curve
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (u : I) :
    (W.positiveTargetOrbitParam
        (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
        ht₁ ht₂ O).curve u =
      W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, u) := rfl


-- @@ L598-598 verbatim
/-! ## Moving orthonormal frame -/


-- @@ L600-608 verbatim
def positiveTransportedFrameMatrix
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)})
    (q : I × I) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  rowsMatrix (gramSchmidtNormed ℝ
    (SlabTamedField.sliceFrameAt C.cobordism.G
      (positiveIntermediateTime t₁ t₂ q.1)
      (W.positiveTransportedOrbitPoint
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q)))


-- @@ L610-651 verbatim
theorem continuous_positiveTransportedFrameMatrix
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    Continuous (W.positiveTransportedFrameMatrix
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O) := by
  let τ : I × I → ℝ := fun q => positiveIntermediateTime t₁ t₂ q.1
  let x : I × I → E₁ := W.positiveTransportedOrbitPoint
    (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O
  let A : I × I → Fin (n + 1) → E₁ := fun q =>
    SlabTamedField.sliceFrameAt C.cobordism.G (τ q) (x q)
  have hτ : Continuous τ :=
    (continuous_positiveIntermediateTime t₁ t₂).comp continuous_fst
  have hx : Continuous x := W.continuous_positiveTransportedOrbitPoint
    (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O
  have hA : ∀ i, Continuous fun q => A q i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · change Continuous fun q => tauField (sliceMap C.cobordism.G (τ q)) (x q)
      rw [continuous_iff_continuousAt]
      intro q
      have hxreg : x q ∈ regularSet (sliceMap C.cobordism.G (τ q)) :=
        W.positiveTransportedOrbitPoint_regular
          (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O q
      simpa [Function.comp_def] using
        (continuousAt_sliceTau C.cobordism.smooth hxreg).comp
          (hτ.continuousAt.prodMk hx.continuousAt)
    · change Continuous fun q => gradVec (sliceMap C.cobordism.G (τ q)) k (x q)
      convert (contDiff_sliceGrad C.cobordism.smooth k).continuous.comp
        (hτ.prodMk hx) using 1
      · apply TopologicalSpace.ext
        rfl
      · rfl
  have hInd : ∀ q, LinearIndependent ℝ (A q) := by
    intro q
    exact linearIndependent_sliceFrameAt_of_regular C.cobordism.G (τ q) (x q)
      (W.positiveTransportedOrbitPoint_regular
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O q)
  apply continuous_matrix
  intro i j
  have hgs := continuous_gramSchmidtNormed_family' hA hInd i
  exact (EuclideanSpace.proj j).continuous.comp hgs


-- @@ L653-665 verbatim
theorem positiveTransportedFrameMatrix_mem_SO
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (q : I × I) :
    W.positiveTransportedFrameMatrix
        (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q ∈
      SOGroup (n + 1) := by
  exact sliceFrameMatrix_mem_SO_of_regular C.cobordism.G
    (positiveIntermediateTime t₁ t₂ q.1)
    (W.positiveTransportedOrbitPoint
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q)
    (W.positiveTransportedOrbitPoint_regular
      (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O q)


-- @@ L667-677 verbatim
def positiveTransportedFrame
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    C(I × I, SOGroup (n + 1)) where
  toFun q := ⟨W.positiveTransportedFrameMatrix
    (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O q,
    W.positiveTransportedFrameMatrix_mem_SO
      (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O q⟩
  continuous_toFun := (W.continuous_positiveTransportedFrameMatrix
    (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O).subtype_mk _


-- @@ L679-695 verbatim
@[simp] theorem positiveTransportedFrame_zero
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (u : I) :
    W.positiveTransportedFrame
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O (0, u) =
      V₁.orbitFrameLoop O.1 u := by
  apply Subtype.ext
  change W.positiveTransportedFrameMatrix
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (0, u) =
    V₁.orbitFrameLoop O.1 u
  unfold positiveTransportedFrameMatrix TamedField.orbitFrameLoop
    TamedField.fundamentalFrameLoop frameLoop SlabTamedField.sliceFrameAt
  rw [W.positiveTransportedOrbitPoint_zero
    (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂)]
  simp [positiveIntermediateTime, frameAt, SlabTamedField.sliceFLSAt, sliceFLS,
    FramedLevelCobordism.toLevelCobordismData]


-- @@ L697-712 verbatim
theorem positiveTransportedFrame_closed
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) (s : I) :
    W.positiveTransportedFrame
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O (s, 0) =
      W.positiveTransportedFrame
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O (s, 1) := by
  apply Subtype.ext
  change W.positiveTransportedFrameMatrix
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (s, 0) =
    W.positiveTransportedFrameMatrix
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (s, 1)
  unfold positiveTransportedFrameMatrix
  rw [W.positiveTransportedOrbitPoint_closed
    (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂)]


-- @@ L714-721 verbatim
def positiveTransportedTargetFrameLoop
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    C(I, SOGroup (n + 1)) :=
  (W.positiveTransportedFrame
      (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O).comp
    (ContinuousMap.const I (1 : I) |>.prodMk (ContinuousMap.id I))


-- @@ L723-732 verbatim
theorem positiveTransportedTargetFrameLoop_closed
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    W.positiveTransportedTargetFrameLoop
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O 0 =
      W.positiveTransportedTargetFrameLoop
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O 1 :=
  W.positiveTransportedFrame_closed
    (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O 1


-- @@ L734-747 verbatim
def positiveTransportedFrameHomotopy
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    ContinuousMap.Homotopy (V₁.orbitFrameLoop O.1)
      (W.positiveTransportedTargetFrameLoop
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O) where
  toFun := W.positiveTransportedFrame
    (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O
  continuous_toFun := (W.positiveTransportedFrame
    (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O).continuous
  map_zero_left := W.positiveTransportedFrame_zero
    (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O
  map_one_left := fun _ => rfl


-- @@ L749-777 verbatim
theorem positiveTransportedTargetFrameLoop_eq_paramFrameLoop
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    W.positiveTransportedTargetFrameLoop
        (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O =
      (W.positiveTargetOrbitParam
        (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
        ht₁ ht₂ O).paramFrameLoop := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  let P := W.positiveTargetOrbitParam
    (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
    ht₁ ht₂ O
  change W.positiveTransportedFrameMatrix
      (hreg₁ := hreg₁) (V₁ := V₁) (t₂ := t₂) O (1, u) =
    P.paramFrameLoop u
  unfold positiveTransportedFrameMatrix SimpleClosedOrbitParam.paramFrameLoop
    frameLoop frameAt SlabTamedField.sliceFrameAt
  change _ = rowsMatrix (gramSchmidtNormed ℝ
    (frameAt (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData t₂ hreg₂)
      (P.realCurve (u : ℝ))))
  rw [P.realCurve_coe]
  rw [W.positiveTargetOrbitParam_curve
    (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
    ht₁ ht₂ O]
  simp [frameAt, positiveIntermediateTime, SlabTamedField.sliceFLSAt, sliceFLS,
    FramedLevelCobordism.toLevelCobordismData]


-- @@ L779-779 verbatim
/-! ## Componentwise frame classes and selected delta transport -/


-- @@ L781-831 verbatim
theorem positiveOrbitFrameClass_eq
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (O : {O // O ∈ V₁.selectedOrbitFinset
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)}) :
    V₁.orbitFrameClass O.1 =
      V₂.orbitFrameClass
        (W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
          (V₁ := V₁) (V₂ := V₂) ht₁ ht₂ O).1 := by
  let P := W.positiveTargetOrbitParam
    (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
    ht₁ ht₂ O
  let Q : V₂.OrbitIndex :=
    (W.positiveOrbitMap (hreg₁ := hreg₁) (hreg₂ := hreg₂)
      (V₁ := V₁) (V₂ := V₂) ht₁ ht₂ O).1
  have htargetEq := W.positiveTransportedTargetFrameLoop_eq_paramFrameLoop
    (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
    ht₁ ht₂ O
  have hqOrbit : V₂.orbitPoint Q ∈ V₂.orbit P.p := by
    have hself := V₂.mem_orbit_self (V₂.orbitPoint Q)
    have hQpoint : (Q : Set E₁) = V₂.orbit (V₂.orbitPoint Q) :=
      V₂.orbitPoint_orbit Q
    have hQtarget : (Q : Set E₁) = V₂.orbit P.p := by
      rfl
    rwa [← hQtarget, hQpoint]
  unfold TamedField.orbitFrameClass
  calc
    loopClassZ2 (V₁.orbitFrameLoop O.1) (V₁.orbitFrameLoop_closed O.1) =
        loopClassZ2
          (W.positiveTransportedTargetFrameLoop
            (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O)
          (W.positiveTransportedTargetFrameLoop_closed
            (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O) :=
      loopClassZ2_congr
        (V₁.orbitFrameLoop_closed O.1)
        (W.positiveTransportedTargetFrameLoop_closed
          (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O)
        (W.positiveTransportedFrameHomotopy
          (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O)
        (W.positiveTransportedFrame_closed
          (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O)
    _ = loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed :=
      loopClassZ2_congr_fun
        (W.positiveTransportedTargetFrameLoop_closed
          (hreg₁ := hreg₁) (V₁ := V₁) ht₁ ht₂ O)
        P.paramFrameLoop_closed htargetEq
    _ = V₂.fundamentalFrameClass P.hp := P.paramFrameClass_eq_fundamental
    _ = V₂.fundamentalFrameClass (V₂.orbitPoint_mem_fiber Q) := by
      symm
      exact V₂.fundamentalFrameClass_eq_of_mem_orbit P.hp hqOrbit
    _ = loopClassZ2 (V₂.orbitFrameLoop Q) (V₂.orbitFrameLoop_closed Q) :=
      (V₂.orbitFrameClass_eq_fundamental Q).symm


-- @@ L833-849 verbatim
/-- The actual positive-sheet flow supplies exactly the selected finite-sum
transport required at a negative event. -/
def positiveSelectedDeltaTransport
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    V₁.SelectedDeltaTransport V₂
      ((C.sliceSign t₁ hreg₁).positiveOrbitCollection V₁)
      ((C.sliceSign t₂ hreg₂).positiveOrbitCollection V₂) where
  orbitEquiv := W.positiveOrbitEquiv
    (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
    ht₁ ht₂
  contribution_eq := by
    intro O
    unfold TamedField.orbitContribution
    rw [W.positiveOrbitFrameClass_eq
      (hreg₁ := hreg₁) (hreg₂ := hreg₂) (V₁ := V₁) (V₂ := V₂)
      ht₁ ht₂ O]
    rfl


-- @@ L851-851 verbatim
end PositiveSheetSlabTamedField


-- @@ L853-853 verbatim
namespace NegativeEventPositiveExteriorTransportData


-- @@ L855-855 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L856-856 verbatim
variable {P : MorsePosition C.cobordism} {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L858-882 verbatim
/-- A negative-labelled Morse event has the required complete positive
component transport, constructed from the localized positive-sheet flow. -/
def of_negative_event
    (hnegative : P.eventCenter t ht ∈
      (C.labelMorsePosition P).negativeCenters) :
    NegativeEventPositiveExteriorTransportData C P t ht := by
  let a := (P.eventBracket t ht).before
  let b := (P.eventBracket t ht).after
  let W : PositiveSheetSlabTamedField C a b :=
    (PositiveSheetSlabTamedField.nonempty_of_negative_event C P ht hnegative).some
  let Vbefore := P.eventBeforeField t ht
  let Vafter := P.eventAfterField t ht
  have hab : a ≤ b := by
    exact ((P.eventBracket t ht).before_lt.trans
      (P.eventBracket t ht).lt_after).le
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  refine
    { beforeField := Vbefore
      afterField := Vafter
      exteriorTransport := ?_ }
  exact W.positiveSelectedDeltaTransport
    (hreg₁ := (P.eventBracket t ht).before_regular)
    (hreg₂ := (P.eventBracket t ht).after_regular)
    (V₁ := Vbefore) (V₂ := Vafter) ha hb


-- @@ L884-889 verbatim
/-- Existence form consumed by the branchwise signed Morse schedule. -/
theorem nonempty_of_negative_event
    (hnegative : P.eventCenter t ht ∈
      (C.labelMorsePosition P).negativeCenters) :
    Nonempty (NegativeEventPositiveExteriorTransportData C P t ht) :=
  ⟨of_negative_event hnegative⟩


-- @@ L891-891 verbatim
end NegativeEventPositiveExteriorTransportData


-- @@ L893-893 verbatim
end Submission
