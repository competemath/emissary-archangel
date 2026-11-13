import Mathlib
import Submission.Delta


-- @@ L4-10 verbatim
/-!
# Concrete frame transport on a regular slab

This file supplies the componentwise frame-class input isolated in `Submission.Delta`.
The construction separates the geometric frame homotopy along the cobordism flow
from the harmless change of circle parametrization at the target orbit.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
set_option maxHeartbeats 1600000


-- @@ L16-16 verbatim
namespace Submission


-- @@ L18-18 verbatim
open Set Function Topology Module Submodule InnerProductSpace

-- @@ L19-19 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval BigOperators


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-23 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L26-26 verbatim
namespace TamedField


-- @@ L28-28 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L30-60 verbatim
/-- Equality of two points on a flow line is exactly equality modulo the fundamental
period. -/
theorem flow_eq_iff_sub_mem_zmultiples {p : E₁} (hp : p ∈ X.fiber) (s t : ℝ) :
    V.flow p s = V.flow p t ↔
      s - t ∈ AddSubgroup.zmultiples (V.fundamentalPeriod hp) := by
  constructor
  · intro hst
    have hshift : (fun u => V.flow p (s + u)) = fun u => V.flow p (t + u) := by
      rw [← V.flow_shift p s, ← V.flow_shift p t, hst]
    have hper : Function.Periodic (V.flow p) (s - t) := by
      intro u
      have h := congrFun hshift (u - t)
      convert h using 1 <;> ring
    let q : V.flowPeriods p := ⟨s - t, hper⟩
    have hq : q ∈ AddSubgroup.zmultiples (V.periodGenerator hp) := by
      rw [V.zmultiples_periodGenerator hp]
      exact Set.mem_univ q
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨if 0 ≤ ((V.periodGenerator hp : V.flowPeriods p) : ℝ) then k else -k, ?_⟩
    unfold fundamentalPeriod
    split_ifs with hgen
    · rw [abs_of_nonneg hgen]
      exact congrArg Subtype.val hk
    · rw [abs_of_neg (lt_of_not_ge hgen), neg_smul]
      simpa using congrArg Subtype.val hk
  · rintro ⟨k, hk⟩
    have hper := (V.fundamentalPeriod_periodic hp).zsmul k
    have h := hper t
    have harg : t + k • V.fundamentalPeriod hp = s := by linarith
    rwa [harg] at h


-- @@ L62-70 verbatim
/-- The intrinsic unit-speed flow identifies an orbit with the additive circle of
its fundamental period. -/
theorem orbitPeriodicMap {p : E₁} (hp : p ∈ X.fiber) :
    Function.Periodic
      (fun t => (⟨V.flow p t, ⟨t, rfl⟩⟩ : V.orbit p))
      (V.fundamentalPeriod hp) := by
  intro t
  apply Subtype.ext
  exact V.fundamentalPeriod_periodic hp t


-- @@ L72-75 verbatim
/-- The flow map descended to the period quotient. -/
def orbitCircleMap {p : E₁} (hp : p ∈ X.fiber) :
    AddCircle (V.fundamentalPeriod hp) → (V.orbit p) :=
  (V.orbitPeriodicMap hp).lift


-- @@ L77-80 verbatim
@[simp]
theorem orbitCircleMap_coe {p : E₁} (hp : p ∈ X.fiber) (t : ℝ) :
    (V.orbitCircleMap hp (t : AddCircle (V.fundamentalPeriod hp)) : E₁) =
      V.flow p t := rfl


-- @@ L82-100 verbatim
def orbitCircleEquiv {p : E₁} (hp : p ∈ X.fiber) :
    AddCircle (V.fundamentalPeriod hp) ≃ (V.orbit p) := by
  let f := V.orbitCircleMap hp
  have hf_inj : Function.Injective f := by
    intro q r hqr
    induction q using QuotientAddGroup.induction_on with
    | H s =>
      induction r using QuotientAddGroup.induction_on with
      | H t =>
        apply Quotient.sound'
        rw [QuotientAddGroup.leftRel_apply]
        have hmem := (V.flow_eq_iff_sub_mem_zmultiples hp s t).mp
          (congrArg Subtype.val hqr)
        simpa [sub_eq_add_neg, add_comm] using
          (AddSubgroup.neg_mem (AddSubgroup.zmultiples (V.fundamentalPeriod hp)) hmem)
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, t, rfl⟩
    exact ⟨(t : AddCircle (V.fundamentalPeriod hp)), rfl⟩
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩


-- @@ L102-107 verbatim
@[simp]
theorem orbitCircleEquiv_coe {p : E₁} (hp : p ∈ X.fiber) (t : ℝ) :
    (V.orbitCircleEquiv hp (t : AddCircle (V.fundamentalPeriod hp)) : E₁) =
      V.flow p t := by
  change (V.orbitCircleMap hp (t : AddCircle (V.fundamentalPeriod hp)) : E₁) = _
  rfl


-- @@ L109-117 verbatim
/-- Topological form of `orbitCircleEquiv`. -/
def orbitCircleHomeomorph {p : E₁} (hp : p ∈ X.fiber) :
    AddCircle (V.fundamentalPeriod hp) ≃ₜ (V.orbit p) := by
  let e := V.orbitCircleEquiv hp
  have hecont : Continuous e := by
    change Continuous (V.orbitCircleMap hp)
    exact ((V.continuous_flow p).subtype_mk _).quotient_lift _
  letI : Fact (0 < V.fundamentalPeriod hp) := ⟨V.fundamentalPeriod_pos hp⟩
  exact ⟨e, hecont, hecont.continuous_symm_of_equiv_compact_to_t2⟩


-- @@ L119-124 verbatim
@[simp]
theorem orbitCircleHomeomorph_coe {p : E₁} (hp : p ∈ X.fiber) (t : ℝ) :
    (V.orbitCircleHomeomorph hp
        (t : AddCircle (V.fundamentalPeriod hp)) : E₁) =
      V.flow p t := by
  exact V.orbitCircleEquiv_coe hp t


-- @@ L126-126 verbatim
end TamedField


-- @@ L128-128 verbatim
/-! ## The concrete moving frame along time transport -/


-- @@ L130-130 verbatim
namespace SlabTamedField


-- @@ L132-132 verbatim
variable {C₀ : LevelCobordismData n} {a b : ℝ} (W : SlabTamedField C₀ a b)


-- @@ L134-136 verbatim
/-- Linear interpolation between two slice times. -/
def intermediateTime (W : SlabTamedField C₀ a b) (t₁ t₂ : ℝ) (s : I) : ℝ :=
  t₁ + (s : ℝ) * (t₂ - t₁)


-- @@ L138-149 verbatim
theorem intermediateTime_mem_Icc {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (s : I) :
    W.intermediateTime t₁ t₂ s ∈ Icc a b := by
  constructor
  · have hs₀ : 0 ≤ (s : ℝ) := s.2.1
    have hs₁ : (s : ℝ) ≤ 1 := s.2.2
    rcases le_total t₁ t₂ with h | h <;>
      dsimp [intermediateTime] <;> nlinarith [ht₁.1, ht₂.1]
  · have hs₀ : 0 ≤ (s : ℝ) := s.2.1
    have hs₁ : (s : ℝ) ≤ 1 := s.2.2
    rcases le_total t₁ t₂ with h | h <;>
      dsimp [intermediateTime] <;> nlinarith [ht₁.2, ht₂.2]


-- @@ L151-153 verbatim
theorem continuous_intermediateTime (W : SlabTamedField C₀ a b) (t₁ t₂ : ℝ) :
    Continuous (W.intermediateTime t₁ t₂) :=
  continuous_const.add (continuous_subtype_val.mul continuous_const)


-- @@ L155-157 verbatim
variable {t₁ t₂ : ℝ} (hreg : regularSlab C₀.G a b)
  (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
  (V₁ : TamedField (sliceFLSAt C₀ t₁ (hreg.sliceRegular ht₁)))


-- @@ L159-164 verbatim
/-- The source fundamental orbit, transported to the intermediate slice. -/
def transportedOrbitPoint (O : V₁.OrbitIndex) (q : I × I) : E₁ :=
  let _ := ht₂
  W.sliceTransport t₁ (W.intermediateTime t₁ t₂ q.1)
    (V₁.flow (V₁.orbitPoint O)
      ((q.2 : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O)))


-- @@ L166-193 verbatim
theorem continuous_transportedOrbitPoint (O : V₁.OrbitIndex) :
    Continuous (W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O) := by
  let p : E₁ := V₁.orbitPoint O
  let T : ℝ := V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O)
  have hsource : Continuous fun q : I × I => V₁.flow p ((q.2 : ℝ) * T) :=
    (V₁.continuous_flow p).comp (continuous_subtype_val.comp continuous_snd |>.mul continuous_const)
  have hinit : Continuous fun q : I × I =>
      cobSpaceTime (V₁.flow p ((q.2 : ℝ) * T)) t₁ := by
    have hcob : Continuous fun z : E₁ => cobSpaceTime z t₁ := by
      rw [continuous_iff_continuousAt]
      exact fun z => (hasFDerivAt_cobSpaceTime t₁ z).continuousAt
    exact hcob.comp hsource
  have htime : Continuous fun q : I × I =>
      W.intermediateTime t₁ t₂ q.1 - t₁ :=
    ((W.continuous_intermediateTime t₁ t₂).comp continuous_fst).sub continuous_const
  have hflow : Continuous fun q : I × I =>
      W.flow (cobSpaceTime (V₁.flow p ((q.2 : ℝ) * T)) t₁)
        (W.intermediateTime t₁ t₂ q.1 - t₁) :=
    W.continuous_flow_uncurry.comp (hinit.prodMk htime)
  have hspace : Continuous (spacePart (n := n)) := by
    have hsp : LipschitzWith 1 (spacePart (n := n)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      change ‖spacePart (x - y)‖ ≤ ‖x - y‖
      exact norm_spacePart_le (x - y)
    exact hsp.continuous
  exact hspace.comp hflow


-- @@ L195-201 verbatim
theorem transportedOrbitPoint_mem_fiber (O : V₁.OrbitIndex) (q : I × I) :
    W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O q ∈
      (sliceFLSAt C₀ (W.intermediateTime t₁ t₂ q.1)
        (hreg.sliceRegular (W.intermediateTime_mem_Icc ht₁ ht₂ q.1))).fiber := by
  apply W.sliceTransport_mapsTo hreg ht₁
    (W.intermediateTime_mem_Icc ht₁ ht₂ q.1)
  exact V₁.flow_mem_fiber (V₁.orbitPoint_mem_fiber O) _


-- @@ L203-206 verbatim
/-- The slice frame written without proof-dependent `FramedLevelSet` packaging. -/
def sliceFrameAt (G : E₂ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (x : E₁) :
    Fin (n + 1) → E₁ :=
  Fin.cons (tauField (sliceMap G t) x) fun i => gradVec (sliceMap G t) i x


-- @@ L208-213 verbatim
/-- The raw orthonormal frame matrix at a point of the moving orbit. -/
def transportedFrameMatrix (O : V₁.OrbitIndex) (q : I × I) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  rowsMatrix (gramSchmidtNormed ℝ
    (sliceFrameAt C₀.G (W.intermediateTime t₁ t₂ q.1)
      (W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O q)))


-- @@ L215-255 verbatim
theorem continuous_transportedFrameMatrix (O : V₁.OrbitIndex) :
    Continuous (W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O) := by
  let τ : I × I → ℝ := fun q => W.intermediateTime t₁ t₂ q.1
  let x : I × I → E₁ := W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O
  let A : I × I → Fin (n + 1) → E₁ := fun q =>
    sliceFrameAt C₀.G (τ q) (x q)
  have hτ : Continuous τ :=
    (W.continuous_intermediateTime t₁ t₂).comp continuous_fst
  have hx : Continuous x := W.continuous_transportedOrbitPoint hreg ht₁ ht₂ V₁ O
  have hA : ∀ i, Continuous fun q => A q i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · change Continuous fun q => tauField (sliceMap C₀.G (τ q)) (x q)
      rw [continuous_iff_continuousAt]
      intro q
      have hxfib := W.transportedOrbitPoint_mem_fiber hreg ht₁ ht₂ V₁ O q
      have hxreg : x q ∈ regularSet (sliceMap C₀.G (τ q)) :=
        (sliceFLSAt C₀ (τ q)
          (hreg.sliceRegular (W.intermediateTime_mem_Icc ht₁ ht₂ q.1))).fiber_subset_regularSet
          hxfib
      simpa [Function.comp_def] using
        (continuousAt_sliceTau C₀.smooth hxreg).comp
          (hτ.continuousAt.prodMk hx.continuousAt)
    · change Continuous fun q => gradVec (sliceMap C₀.G (τ q)) k (x q)
      convert (contDiff_sliceGrad C₀.smooth k).continuous.comp (hτ.prodMk hx) using 1
      · apply TopologicalSpace.ext
        rfl
      · rfl
  have hInd : ∀ q, LinearIndependent ℝ (A q) := by
    intro q
    change LinearIndependent ℝ
      (frameAt (sliceFLSAt C₀ (τ q)
        (hreg.sliceRegular (W.intermediateTime_mem_Icc ht₁ ht₂ q.1))) (x q))
    exact linearIndependent_frameAt _
      ((sliceFLSAt C₀ (τ q)
        (hreg.sliceRegular (W.intermediateTime_mem_Icc ht₁ ht₂ q.1))).fiber_subset_regularSet
        (W.transportedOrbitPoint_mem_fiber hreg ht₁ ht₂ V₁ O q))
  apply continuous_matrix
  intro i j
  have hgs := continuous_gramSchmidtNormed_family' hA hInd i
  exact (EuclideanSpace.proj j).continuous.comp hgs


-- @@ L257-267 verbatim
theorem transportedFrameMatrix_mem_SO (O : V₁.OrbitIndex) (q : I × I) :
    W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O q ∈
      SOGroup (n + 1) := by
  change frameLoop
    (sliceFLSAt C₀ (W.intermediateTime t₁ t₂ q.1)
      (hreg.sliceRegular (W.intermediateTime_mem_Icc ht₁ ht₂ q.1)))
    (fun _ => W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O q) 0 ∈
      Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ
  apply frameLoop_mem_specialOrthogonalGroup
  intro _
  exact W.transportedOrbitPoint_mem_fiber hreg ht₁ ht₂ V₁ O q


-- @@ L269-274 verbatim
/-- The moving frame, as an `SO(n+1)`-valued map on the parameter square. -/
def transportedFrame (O : V₁.OrbitIndex) : C(I × I, SOGroup (n + 1)) where
  toFun q := ⟨W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O q,
    W.transportedFrameMatrix_mem_SO hreg ht₁ ht₂ V₁ O q⟩
  continuous_toFun :=
    (W.continuous_transportedFrameMatrix hreg ht₁ ht₂ V₁ O).subtype_mk _


-- @@ L276-281 verbatim
@[simp]
theorem transportedOrbitPoint_zero (O : V₁.OrbitIndex) (u : I) :
    W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (0, u) =
      V₁.flow (V₁.orbitPoint O)
        ((u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O)) := by
  simp [transportedOrbitPoint, intermediateTime, sliceTransport]


-- @@ L283-291 verbatim
@[simp]
theorem transportedOrbitPoint_one (O : V₁.OrbitIndex) (u : I) :
    W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (1, u) =
      W.sliceTransport t₁ t₂
        (V₁.flow (V₁.orbitPoint O)
          ((u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O))) := by
  unfold transportedOrbitPoint intermediateTime
  congr 2
  norm_num


-- @@ L293-298 verbatim
theorem transportedOrbitPoint_closed (O : V₁.OrbitIndex) (s : I) :
    W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (s, 0) =
      W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (s, 1) := by
  unfold transportedOrbitPoint
  apply congrArg
  simpa using (V₁.fundamentalPeriod_periodic (V₁.orbitPoint_mem_fiber O) 0).symm


-- @@ L300-306 verbatim
theorem transportedFrameMatrix_zero (O : V₁.OrbitIndex) (u : I) :
    W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O (0, u) =
      V₁.orbitFrameLoop O u := by
  unfold transportedFrameMatrix TamedField.orbitFrameLoop
    TamedField.fundamentalFrameLoop frameLoop sliceFrameAt
  rw [W.transportedOrbitPoint_zero hreg ht₁ ht₂ V₁ O u]
  simp [intermediateTime, frameAt, sliceFLSAt, sliceFLS]


-- @@ L308-312 verbatim
theorem transportedFrameMatrix_closed (O : V₁.OrbitIndex) (s : I) :
    W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O (s, 0) =
      W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O (s, 1) := by
  unfold transportedFrameMatrix
  rw [W.transportedOrbitPoint_closed hreg ht₁ ht₂ V₁ O s]


-- @@ L314-318 verbatim
@[simp]
theorem transportedFrame_zero (O : V₁.OrbitIndex) (u : I) :
    W.transportedFrame hreg ht₁ ht₂ V₁ O (0, u) = V₁.orbitFrameLoop O u := by
  apply Subtype.ext
  exact W.transportedFrameMatrix_zero hreg ht₁ ht₂ V₁ O u


-- @@ L320-324 verbatim
theorem transportedFrame_closed (O : V₁.OrbitIndex) (s : I) :
    W.transportedFrame hreg ht₁ ht₂ V₁ O (s, 0) =
      W.transportedFrame hreg ht₁ ht₂ V₁ O (s, 1) := by
  apply Subtype.ext
  exact W.transportedFrameMatrix_closed hreg ht₁ ht₂ V₁ O s


-- @@ L326-329 verbatim
/-- The frame loop obtained at the target by transporting the source orbit once. -/
def transportedTargetFrameLoop (O : V₁.OrbitIndex) : C(I, SOGroup (n + 1)) :=
  (W.transportedFrame hreg ht₁ ht₂ V₁ O).comp
    (ContinuousMap.const I (1 : I) |>.prodMk (ContinuousMap.id I))


-- @@ L331-334 verbatim
theorem transportedTargetFrameLoop_closed (O : V₁.OrbitIndex) :
    W.transportedTargetFrameLoop hreg ht₁ ht₂ V₁ O 0 =
      W.transportedTargetFrameLoop hreg ht₁ ht₂ V₁ O 1 :=
  W.transportedFrame_closed hreg ht₁ ht₂ V₁ O 1


-- @@ L336-343 verbatim
/-- The actual time-flow frame homotopy, before target reparametrization. -/
def transportedFrameHomotopy (O : V₁.OrbitIndex) : ContinuousMap.Homotopy
    (V₁.orbitFrameLoop O)
    (W.transportedTargetFrameLoop hreg ht₁ ht₂ V₁ O) where
  toFun := W.transportedFrame hreg ht₁ ht₂ V₁ O
  continuous_toFun := (W.transportedFrame hreg ht₁ ht₂ V₁ O).continuous
  map_zero_left := W.transportedFrame_zero hreg ht₁ ht₂ V₁ O
  map_one_left := fun _ => rfl


-- @@ L345-345 verbatim
end SlabTamedField


-- @@ L347-347 verbatim
/-! ## The target phase of the transported orbit -/


-- @@ L349-349 verbatim
namespace SlabTamedField


-- @@ L351-356 verbatim
variable {C₀ : LevelCobordismData n} {a b t₁ t₂ : ℝ}
  (W : SlabTamedField C₀ a b)
  (hreg : regularSlab C₀.G a b)
  (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
  (V₁ : TamedField (sliceFLSAt C₀ t₁ (hreg.sliceRegular ht₁)))
  (V₂ : TamedField (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂)))


-- @@ L358-362 verbatim
/-- The transported source base point in the target slice. -/
def targetTransportedBase (O : V₁.OrbitIndex) : E₁ :=
  let _ := ht₂
  let _ := V₂
  W.sliceTransport t₁ t₂ (V₁.orbitPoint O)


-- @@ L364-370 verbatim
theorem targetTransportedBase_mem_fiber (O : V₁.OrbitIndex) :
    W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O ∈
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂)).fiber := by
  rw [sliceFLSAt_fiber]
  apply W.sliceTransport_mapsTo hreg ht₁ ht₂
  rw [← sliceFLSAt_fiber]
  exact V₁.orbitPoint_mem_fiber O


-- @@ L372-384 verbatim
/-- The target curve, regarded as a path in the target flow orbit of its initial
point. -/
def transportedTargetOrbitPath (O : V₁.OrbitIndex) :
    C(I, V₂.orbit (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) where
  toFun u := ⟨W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (1, u), by
    rw [W.transportedOrbitPoint_one hreg ht₁ ht₂ V₁ O u]
    apply W.sliceTransport_mapsTo_orbit hreg ht₁ ht₂ V₁ V₂
      (V₁.orbitPoint_mem_fiber O)
    exact V₁.flow_mem_orbit _ _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (W.continuous_transportedOrbitPoint hreg ht₁ ht₂ V₁ O).comp
      (continuous_const.prodMk continuous_id)


-- @@ L386-395 verbatim
/-- Phase of the transported curve in the target orbit's intrinsic period circle. -/
def transportedTargetPhase (O : V₁.OrbitIndex) :
    C(I, AddCircle (V₂.fundamentalPeriod
      (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))) where
  toFun u := (V₂.orbitCircleHomeomorph
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)).symm
      (W.transportedTargetOrbitPath hreg ht₁ ht₂ V₁ V₂ O u)
  continuous_toFun := (V₂.orbitCircleHomeomorph
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)).symm.continuous.comp
      (W.transportedTargetOrbitPath hreg ht₁ ht₂ V₁ V₂ O).continuous


-- @@ L397-403 verbatim
theorem transportedTargetPhase_homeomorph_apply (O : V₁.OrbitIndex) (u : I) :
    V₂.orbitCircleHomeomorph
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)
        (W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O u) =
      W.transportedTargetOrbitPath hreg ht₁ ht₂ V₁ V₂ O u := by
  exact (V₂.orbitCircleHomeomorph
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)).apply_symm_apply _


-- @@ L405-430 verbatim
@[simp]
theorem transportedTargetPhase_zero (O : V₁.OrbitIndex) :
    W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O 0 = 0 := by
  apply (V₂.orbitCircleHomeomorph
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)).injective
  rw [W.transportedTargetPhase_homeomorph_apply hreg ht₁ ht₂ V₁ V₂ O]
  apply Subtype.ext
  have hhome :
      (V₂.orbitCircleHomeomorph
          (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)
          (0 : AddCircle (V₂.fundamentalPeriod
            (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))) : E₁) =
        V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O) 0 := by
    exact V₂.orbitCircleHomeomorph_coe
      (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O) 0
  rw [hhome]
  have hpath :
      ((W.transportedTargetOrbitPath hreg ht₁ ht₂ V₁ V₂ O 0 :
          V₂.orbit (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) : E₁) =
        W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (1, 0) := rfl
  rw [hpath, W.transportedOrbitPoint_one hreg ht₁ ht₂ V₁ O 0]
  change W.sliceTransport t₁ t₂
      (V₁.flow (V₁.orbitPoint O)
        (((0 : I) : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O))) =
    V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O) 0
  simp [targetTransportedBase]


-- @@ L432-440 verbatim
theorem transportedTargetPhase_closed (O : V₁.OrbitIndex) :
    W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O 0 =
      W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O 1 := by
  apply (V₂.orbitCircleHomeomorph
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)).injective
  rw [W.transportedTargetPhase_homeomorph_apply hreg ht₁ ht₂ V₁ V₂ O,
    W.transportedTargetPhase_homeomorph_apply hreg ht₁ ht₂ V₁ V₂ O]
  apply Subtype.ext
  exact W.transportedOrbitPoint_closed hreg ht₁ ht₂ V₁ O 1


-- @@ L442-510 verbatim
/-- The target phase is one-to-one on the half-open unit interval; its only possible
repetition on the closed interval is the identified pair of endpoints. -/
theorem transportedTargetPhase_eq_cases (O : V₁.OrbitIndex) {u v : I}
    (huv : W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O u =
      W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  have htarget : W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (1, u) =
      W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (1, v) := by
    have h := congrArg
      (V₂.orbitCircleHomeomorph
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)) huv
    rw [W.transportedTargetPhase_homeomorph_apply hreg ht₁ ht₂ V₁ V₂ O,
      W.transportedTargetPhase_homeomorph_apply hreg ht₁ ht₂ V₁ V₂ O] at h
    exact congrArg Subtype.val h
  rw [W.transportedOrbitPoint_one hreg ht₁ ht₂ V₁ O,
    W.transportedOrbitPoint_one hreg ht₁ ht₂ V₁ O] at htarget
  have hsource :
      V₁.flow (V₁.orbitPoint O)
          ((u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O)) =
        V₁.flow (V₁.orbitPoint O)
          ((v : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O)) := by
    apply (W.sliceTransport_bijOn hreg ht₁ ht₂).injOn
    · exact V₁.flow_mem_fiber (V₁.orbitPoint_mem_fiber O) _
    · exact V₁.flow_mem_fiber (V₁.orbitPoint_mem_fiber O) _
    · exact htarget
  have hmem := (V₁.flow_eq_iff_sub_mem_zmultiples
    (V₁.orbitPoint_mem_fiber O) _ _).mp hsource
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hTpos := V₁.fundamentalPeriod_pos (V₁.orbitPoint_mem_fiber O)
  have huvInt : (u : ℝ) - (v : ℝ) = (k : ℝ) := by
    have hk' : (k : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O) =
        (u : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O) -
          (v : ℝ) * V₁.fundamentalPeriod (V₁.orbitPoint_mem_fiber O) := by
      simpa [zsmul_eq_mul] using hk
    nlinarith
  rcases lt_trichotomy (u : ℝ) (v : ℝ) with huvlt | huveq | huvgt
  · right; left
    have hknegR : (k : ℝ) < 0 := by rw [← huvInt]; linarith
    have hkneg : k < 0 := by exact_mod_cast hknegR
    have hkge : (-1 : ℤ) ≤ k := by
      have hkgeR : (-1 : ℝ) ≤ (k : ℝ) := by rw [← huvInt]; linarith [u.2.1, v.2.2]
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
      have hkleR : (k : ℝ) ≤ 1 := by rw [← huvInt]; linarith [u.2.2, v.2.1]
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


-- @@ L512-512 verbatim
/-! ### Lift of the target phase and its winding number -/


-- @@ L514-521 verbatim
/-- The target phase lifted to real time, starting at time zero. -/
def transportedTargetPhaseLift (O : V₁.OrbitIndex) : C(I, ℝ) := by
  let hp := W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O
  let T := V₂.fundamentalPeriod hp
  letI : Fact (0 < T) := ⟨V₂.fundamentalPeriod_pos hp⟩
  exact (AddCircle.isCoveringMap_coe T).liftPath
    (W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O) 0
      (W.transportedTargetPhase_zero hreg ht₁ ht₂ V₁ V₂ O)


-- @@ L523-527 verbatim
@[simp]
theorem transportedTargetPhaseLift_zero (O : V₁.OrbitIndex) :
    W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 0 = 0 := by
  unfold transportedTargetPhaseLift
  apply IsCoveringMap.liftPath_zero


-- @@ L529-540 verbatim
theorem transportedTargetPhaseLift_coe (O : V₁.OrbitIndex) (u : I) :
    ((W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O u : ℝ) :
        AddCircle (V₂.fundamentalPeriod
          (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))) =
      W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O u := by
  let hp := W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O
  let T := V₂.fundamentalPeriod hp
  letI : Fact (0 < T) := ⟨V₂.fundamentalPeriod_pos hp⟩
  have h := congrFun ((AddCircle.isCoveringMap_coe T).liftPath_lifts
    (W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O) 0
      (W.transportedTargetPhase_zero hreg ht₁ ht₂ V₁ V₂ O)) u
  simpa [transportedTargetPhaseLift, hp, T] using h


-- @@ L542-559 verbatim
/-- The endpoint of the phase lift is an integral multiple of the target period. -/
theorem transportedTargetPhaseLift_endpoint_zsmul (O : V₁.OrbitIndex) :
    ∃ k : ℤ, W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 =
      k • V₂.fundamentalPeriod
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O) := by
  let ψ := W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O
  let T := V₂.fundamentalPeriod
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)
  have hcoe : ((ψ 1 : ℝ) : AddCircle T) = 0 := by
    calc
      ((ψ 1 : ℝ) : AddCircle T) =
          W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O 1 :=
        W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O 1
      _ = W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O 0 :=
        (W.transportedTargetPhase_closed hreg ht₁ ht₂ V₁ V₂ O).symm
      _ = 0 := W.transportedTargetPhase_zero hreg ht₁ ht₂ V₁ V₂ O
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff T).mp hcoe
  exact ⟨k, hk.symm⟩


-- @@ L561-651 verbatim
/-- A simple closed phase curve cannot have zero winding endpoint. -/
theorem transportedTargetPhaseLift_one_ne_zero (O : V₁.OrbitIndex) :
    W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 ≠ 0 := by
  let ψ := W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O
  let φ := W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O
  let m : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hm0 : (0 : I) < m := by change (0 : ℝ) < 1 / 2; norm_num
  have hm1 : m < (1 : I) := by change (1 / 2 : ℝ) < 1; norm_num
  have hφm : φ m ≠ φ 0 := by
    intro h
    rcases W.transportedTargetPhase_eq_cases hreg ht₁ ht₂ V₁ V₂ O h with
      hEq | hEnds | hEnds
    · exact (ne_of_gt hm0) hEq
    · exact (zero_ne_one : (0 : I) ≠ 1) hEnds.2
    · exact (ne_of_lt hm1) hEnds.1
  have hψm : ψ m ≠ 0 := by
    intro hzero
    apply hφm
    calc
      φ m = ((ψ m : ℝ) : AddCircle
          (V₂.fundamentalPeriod
            (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))) :=
        (W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O m).symm
      _ = ((ψ 0 : ℝ) : AddCircle
          (V₂.fundamentalPeriod
            (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))) := by
        rw [hzero, W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]
      _ = φ 0 :=
        W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O 0
  intro hψ1
  have hcont : Continuous ψ :=
    (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O).continuous
  rcases lt_or_gt_of_ne hψm with hneg | hpos
  · let z : ℝ := ψ m / 2
    have hzL : z ∈ Icc (ψ m) (ψ 0) := by
      rw [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨u, huI, hu⟩ := intermediate_value_Icc' (le_of_lt hm0)
      hcont.continuousOn hzL
    have hzR : z ∈ Icc (ψ m) (ψ 1) := by
      rw [hψ1]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨v, hvI, hv⟩ := intermediate_value_Icc (le_of_lt hm1)
      hcont.continuousOn hzR
    have hphase : φ u = φ v := by
      rw [← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O u,
        ← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O v,
        hu, hv]
    rcases W.transportedTargetPhase_eq_cases hreg ht₁ ht₂ V₁ V₂ O hphase with
      huv | hends | hends
    · subst v
      have : u = m := le_antisymm huI.2 hvI.1
      subst u
      dsimp [z] at hu
      linarith
    · rw [hends.1,
        W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O] at hu
      dsimp [z] at hu
      linarith
    · rw [hends.1, hψ1] at hu
      dsimp [z] at hu
      linarith
  · let z : ℝ := ψ m / 2
    have hzL : z ∈ Icc (ψ 0) (ψ m) := by
      rw [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨u, huI, hu⟩ := intermediate_value_Icc (le_of_lt hm0)
      hcont.continuousOn hzL
    have hzR : z ∈ Icc (ψ 1) (ψ m) := by
      rw [hψ1]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨v, hvI, hv⟩ := intermediate_value_Icc' (le_of_lt hm1)
      hcont.continuousOn hzR
    have hphase : φ u = φ v := by
      rw [← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O u,
        ← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O v,
        hu, hv]
    rcases W.transportedTargetPhase_eq_cases hreg ht₁ ht₂ V₁ V₂ O hphase with
      huv | hends | hends
    · subst v
      have : u = m := le_antisymm huI.2 hvI.1
      subst u
      dsimp [z] at hu
      linarith
    · rw [hends.1,
        W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O] at hu
      dsimp [z] at hu
      linarith
    · rw [hends.1, hψ1] at hu
      dsimp [z] at hu
      linarith


-- @@ L653-675 verbatim
/-- The real lift is injective: the only repetition of the circle phase occurs at the
two endpoints, whose lifts are distinct. -/
theorem transportedTargetPhaseLift_injective (O : V₁.OrbitIndex) :
    Function.Injective
      (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O) := by
  intro u v huv
  have hphase :
      W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O u =
        W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O v := by
    rw [← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O u,
      ← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O v,
      huv]
  rcases W.transportedTargetPhase_eq_cases hreg ht₁ ht₂ V₁ V₂ O hphase with
    hEq | hEnds | hEnds
  · exact hEq
  · exfalso
    apply W.transportedTargetPhaseLift_one_ne_zero hreg ht₁ ht₂ V₁ V₂ O
    rw [← hEnds.2, ← huv, hEnds.1,
      W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]
  · exfalso
    apply W.transportedTargetPhaseLift_one_ne_zero hreg ht₁ ht₂ V₁ V₂ O
    rw [← hEnds.1, huv, hEnds.2,
      W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]


-- @@ L677-757 verbatim
/-- A once-around simple phase has winding number `+1` or `-1`. -/
theorem transportedTargetPhaseLift_one_eq_period_or_neg (O : V₁.OrbitIndex) :
    W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 =
        V₂.fundamentalPeriod
          (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O) ∨
      W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 =
        -V₂.fundamentalPeriod
          (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O) := by
  let ψ := W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O
  let φ := W.transportedTargetPhase hreg ht₁ ht₂ V₁ V₂ O
  let T := V₂.fundamentalPeriod
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)
  have hT : 0 < T := V₂.fundamentalPeriod_pos
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)
  obtain ⟨k, hk⟩ :=
    W.transportedTargetPhaseLift_endpoint_zsmul hreg ht₁ ht₂ V₁ V₂ O
  have hkR : ψ 1 = (k : ℝ) * T := by simpa [ψ, T, zsmul_eq_mul] using hk
  have hmonoanti :=
    (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O).continuous
      |>.strictMono_of_inj_boundedOrder'
        (W.transportedTargetPhaseLift_injective hreg ht₁ ht₂ V₁ V₂ O)
  rcases hmonoanti with hmono | hanti
  · have hψ1pos : 0 < ψ 1 := by
      have h := hmono (show (0 : I) < 1 by norm_num)
      rwa [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O] at h
    have hkposR : (0 : ℝ) < (k : ℝ) := by nlinarith
    have hkpos : (0 : ℤ) < k := by exact_mod_cast hkposR
    have hkle : k ≤ 1 := by
      by_contra hknot
      have hkge : (2 : ℤ) ≤ k := by omega
      have hkgeR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkge
      have hmem : T ∈ Icc (ψ 0) (ψ 1) := by
        rw [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O, hkR]
        constructor <;> nlinarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
        (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O).continuous hmem
      have hphase : φ u = φ 0 := by
        rw [← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O u,
          ← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O 0,
          hu, W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]
        exact AddCircle.coe_period T
      rcases W.transportedTargetPhase_eq_cases hreg ht₁ ht₂ V₁ V₂ O hphase with
        hu0 | hbad | hu1
      · rw [hu0, W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O] at hu
        linarith
      · exact (zero_ne_one : (0 : I) ≠ 1) hbad.2
      · rw [hu1.1, hkR] at hu
        nlinarith
    have hkone : k = 1 := by omega
    left
    simpa [T, hkone] using hkR
  · have hψ1neg : ψ 1 < 0 := by
      have h := hanti (show (0 : I) < 1 by norm_num)
      rwa [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O] at h
    have hknegR : (k : ℝ) < 0 := by nlinarith
    have hkneg : k < (0 : ℤ) := by exact_mod_cast hknegR
    have hkge : (-1 : ℤ) ≤ k := by
      by_contra hknot
      have hkle : k ≤ (-2 : ℤ) := by omega
      have hkleR : (k : ℝ) ≤ -2 := by exact_mod_cast hkle
      have hmem : -T ∈ Icc (ψ 1) (ψ 0) := by
        rw [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O, hkR]
        constructor <;> nlinarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
        (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O).continuous hmem
      have hphase : φ u = φ 0 := by
        rw [← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O u,
          ← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O 0,
          hu, W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O]
        rw [AddCircle.coe_neg, AddCircle.coe_period, neg_zero]
        rfl
      rcases W.transportedTargetPhase_eq_cases hreg ht₁ ht₂ V₁ V₂ O hphase with
        hu0 | hbad | hu1
      · rw [hu0, W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O] at hu
        linarith
      · exact (zero_ne_one : (0 : I) ≠ 1) hbad.2
      · rw [hu1.1, hkR] at hu
        nlinarith
    have hkmone : k = -1 := by omega
    right
    simpa [T, hkmone] using hkR


-- @@ L759-759 verbatim
/-! ### Target frame written in lifted target time -/


-- @@ L761-770 verbatim
/-- The transported target point is the target flow evaluated at the lifted phase. -/
theorem transportedOrbitPoint_one_eq_target_flow_lift (O : V₁.OrbitIndex) (u : I) :
    W.transportedOrbitPoint hreg ht₁ ht₂ V₁ O (1, u) =
      V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)
        (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O u) := by
  have h := W.transportedTargetPhase_homeomorph_apply hreg ht₁ ht₂ V₁ V₂ O u
  rw [← W.transportedTargetPhaseLift_coe hreg ht₁ ht₂ V₁ V₂ O u] at h
  have hv := congrArg Subtype.val h
  rw [V₂.orbitCircleHomeomorph_coe] at hv
  simpa [transportedTargetOrbitPath] using hv.symm


-- @@ L772-790 verbatim
/-- The target frame loop parametrized by the lifted phase. -/
def liftedTargetFrameLoop (O : V₁.OrbitIndex) : C(I, SOGroup (n + 1)) where
  toFun u := ⟨frameLoop
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O u),
    frameLoop_mem_specialOrthogonalGroup
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow_mem_fiber
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.continuous_flow
        (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      (V₂.flow_mem_fiber
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))).comp
      (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O).continuous


-- @@ L792-811 verbatim
theorem transportedTargetFrameLoop_eq_liftedTargetFrameLoop (O : V₁.OrbitIndex) :
    W.transportedTargetFrameLoop hreg ht₁ ht₂ V₁ O =
      W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O := by
  apply ContinuousMap.ext
  intro u
  change W.transportedFrame hreg ht₁ ht₂ V₁ O (1, u) =
    W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O u
  apply Subtype.ext
  change W.transportedFrameMatrix hreg ht₁ ht₂ V₁ O (1, u) =
    frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      (W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O u)
  unfold transportedFrameMatrix frameLoop frameAt sliceFrameAt
  rw [W.transportedOrbitPoint_one_eq_target_flow_lift hreg ht₁ ht₂ V₁ V₂ O u]
  congr 3
  all_goals
    have htime : W.intermediateTime t₁ t₂ (1 : I) = t₂ := by
      simp [intermediateTime]
    rw [htime]
    rfl


-- @@ L813-833 verbatim
/-- Target frame loop run with orientation factor `ε`.  We use `ε = 1` and
`ε = -1` below. -/
def orientedTargetFrameLoop (O : V₁.OrbitIndex) (ε : ℝ) : C(I, SOGroup (n + 1)) where
  toFun u := ⟨frameLoop
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      (ε * (u : ℝ) * V₂.fundamentalPeriod
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)),
    frameLoop_mem_specialOrthogonalGroup
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow_mem_fiber
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.continuous_flow
        (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      (V₂.flow_mem_fiber
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))).comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)


-- @@ L835-885 verbatim
/-- Straight-line interpolation between the actual lifted target phase and either
orientation of the intrinsic target period. -/
def targetFrameReparamHomotopy (O : V₁.OrbitIndex) (ε : ℝ) :
    ContinuousMap.Homotopy
      (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
      (W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O ε) where
  toFun q := ⟨frameLoop
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      ((1 - (q.1 : ℝ)) *
          W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O q.2 +
        (q.1 : ℝ) * (ε * (q.2 : ℝ) * V₂.fundamentalPeriod
          (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))),
    frameLoop_mem_specialOrthogonalGroup
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.flow_mem_fiber
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (continuous_frameLoop
      (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
      (V₂.continuous_flow
        (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
      (V₂.flow_mem_fiber
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))).comp
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst) |>.mul
      ((W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O).continuous.comp
        continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
          continuous_const)))
  map_zero_left := fun u => by
    apply Subtype.ext
    change frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
        (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
        ((1 - (((0 : I) : ℝ))) *
            W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O u +
          (((0 : I) : ℝ) * (ε * (u : ℝ) * V₂.fundamentalPeriod
            (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)))) = _
    congr 2
    norm_num
  map_one_left := fun u => by
    apply Subtype.ext
    change frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
        (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O))
        ((1 - (((1 : I) : ℝ))) *
            W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O u +
          (((1 : I) : ℝ) * (ε * (u : ℝ) * V₂.fundamentalPeriod
            (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)))) = _
    congr 2
    norm_num


-- @@ L887-896 verbatim
theorem orientedTargetFrameLoop_one (O : V₁.OrbitIndex) :
    W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O 1 =
      V₂.fundamentalFrameLoop
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop _ _ (1 * (u : ℝ) * _) = frameLoop _ _ ((u : ℝ) * _)
  congr 2
  ring


-- @@ L898-914 verbatim
theorem orientedTargetFrameLoop_neg_one (O : V₁.OrbitIndex) :
    W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O (-1) =
      reverseLoop (V₂.fundamentalFrameLoop
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  let hp := W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O
  let F := fun t : ℝ => frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
    (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) t
  have hper : Function.Periodic F (V₂.fundamentalPeriod hp) :=
    frameLoop_periodic _ (V₂.fundamentalPeriod_periodic hp)
  change F ((-1 : ℝ) * (u : ℝ) * V₂.fundamentalPeriod hp) =
    F ((unitInterval.symm u : ℝ) * V₂.fundamentalPeriod hp)
  have h := hper ((-1 : ℝ) * (u : ℝ) * V₂.fundamentalPeriod hp)
  rw [show (unitInterval.symm u : ℝ) = 1 - (u : ℝ) by rfl]
  convert h.symm using 1 <;> ring


-- @@ L916-921 verbatim
theorem liftedTargetFrameLoop_closed (O : V₁.OrbitIndex) :
    W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O 0 =
      W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O 1 := by
  rw [← W.transportedTargetFrameLoop_eq_liftedTargetFrameLoop
    hreg ht₁ ht₂ V₁ V₂ O]
  exact W.transportedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ O


-- @@ L923-953 verbatim
theorem targetFrameReparamHomotopy_closed (O : V₁.OrbitIndex) (ε : ℝ)
    (hend : W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 =
      ε * V₂.fundamentalPeriod
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))
    (hperiod : Function.Periodic
      (fun t : ℝ => frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
        (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) t)
      (ε * V₂.fundamentalPeriod
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)))
    (s : I) :
    W.targetFrameReparamHomotopy hreg ht₁ ht₂ V₁ V₂ O ε (s, 0) =
      W.targetFrameReparamHomotopy hreg ht₁ ht₂ V₁ V₂ O ε (s, 1) := by
  apply Subtype.ext
  let T := V₂.fundamentalPeriod
    (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O)
  let F := fun t : ℝ => frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
    (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) t
  change F ((1 - (s : ℝ)) *
      W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 0 +
      (s : ℝ) * (ε * (((0 : I) : ℝ)) * T)) =
    F ((1 - (s : ℝ)) *
      W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 +
      (s : ℝ) * (ε * (((1 : I) : ℝ)) * T))
  rw [W.transportedTargetPhaseLift_zero hreg ht₁ ht₂ V₁ V₂ O, hend]
  change F ((1 - (s : ℝ)) * 0 + (s : ℝ) * (ε * 0 * T)) =
    F ((1 - (s : ℝ)) * (ε * T) + (s : ℝ) * (ε * 1 * T))
  have hleft : (1 - (s : ℝ)) * 0 + (s : ℝ) * (ε * 0 * T) = 0 := by ring
  have hright : (1 - (s : ℝ)) * (ε * T) + (s : ℝ) * (ε * 1 * T) =
      ε * T := by ring
  rw [hleft, hright]
  simpa [F, T] using (hperiod 0).symm


-- @@ L955-967 verbatim
theorem orientedTargetFrameLoop_closed (O : V₁.OrbitIndex) (ε : ℝ)
    (hperiod : Function.Periodic
      (fun t : ℝ => frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
        (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) t)
      (ε * V₂.fundamentalPeriod
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O))) :
    W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O ε 0 =
      W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O ε 1 := by
  apply Subtype.ext
  change frameLoop _ _ (ε * (((0 : I) : ℝ)) * _) =
    frameLoop _ _ (ε * (((1 : I) : ℝ)) * _)
  norm_num
  convert (hperiod 0).symm using 1 <;> ring


-- @@ L969-1034 verbatim
/-- The transported target loop has the intrinsic target frame class.  The possible
orientation reversal is invisible in `ZMod 2`. -/
theorem liftedTargetFrameClass_eq_fundamental (O : V₁.OrbitIndex) :
    loopClassZ2
        (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
        (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O) =
      V₂.fundamentalFrameClass
        (W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O) := by
  let hp := W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O
  let T := V₂.fundamentalPeriod hp
  let F := fun t : ℝ => frameLoop (sliceFLSAt C₀ t₂ (hreg.sliceRegular ht₂))
    (V₂.flow (W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O)) t
  have hper : Function.Periodic F T :=
    frameLoop_periodic _ (V₂.fundamentalPeriod_periodic hp)
  rcases W.transportedTargetPhaseLift_one_eq_period_or_neg
    hreg ht₁ ht₂ V₁ V₂ O with hplus | hminus
  · have hend : W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 =
        (1 : ℝ) * V₂.fundamentalPeriod hp := by simpa using hplus
    have hclosed := W.targetFrameReparamHomotopy_closed hreg ht₁ ht₂ V₁ V₂ O
      1 hend (by simpa [F, T] using hper)
    have horientedClosed := W.orientedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O
      1 (by simpa [F, T] using hper)
    calc
      loopClassZ2
          (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
          (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O) =
        loopClassZ2
          (W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O 1)
          horientedClosed :=
        loopClassZ2_congr
          (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O)
          horientedClosed
          (W.targetFrameReparamHomotopy hreg ht₁ ht₂ V₁ V₂ O 1)
          hclosed
      _ = V₂.fundamentalFrameClass hp := by
        unfold TamedField.fundamentalFrameClass
        exact loopClassZ2_congr_fun horientedClosed
          (V₂.fundamentalFrameLoop_closed hp)
          (W.orientedTargetFrameLoop_one hreg ht₁ ht₂ V₁ V₂ O)
  · have hend : W.transportedTargetPhaseLift hreg ht₁ ht₂ V₁ V₂ O 1 =
        (-1 : ℝ) * V₂.fundamentalPeriod hp := by simpa using hminus
    have hclosed := W.targetFrameReparamHomotopy_closed hreg ht₁ ht₂ V₁ V₂ O
      (-1) hend (by simpa [F, T] using hper.neg)
    have horientedClosed := W.orientedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O
      (-1) (by simpa [F, T] using hper.neg)
    calc
      loopClassZ2
          (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
          (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O) =
        loopClassZ2
          (W.orientedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O (-1))
          horientedClosed :=
        loopClassZ2_congr
          (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O)
          horientedClosed
          (W.targetFrameReparamHomotopy hreg ht₁ ht₂ V₁ V₂ O (-1))
          hclosed
      _ = loopClassZ2
          (reverseLoop (V₂.fundamentalFrameLoop hp))
          (reverseLoop_closed (V₂.fundamentalFrameLoop_closed hp)) := by
        exact loopClassZ2_congr_fun horientedClosed
          (reverseLoop_closed (V₂.fundamentalFrameLoop_closed hp))
          (W.orientedTargetFrameLoop_neg_one hreg ht₁ ht₂ V₁ V₂ O)
      _ = V₂.fundamentalFrameClass hp := by
        exact loopClassZ2_reverse (V₂.fundamentalFrameLoop hp)
          (V₂.fundamentalFrameLoop_closed hp)


-- @@ L1036-1061 verbatim
/-- The concrete flow homotopy identifies the source orbit class with the class of
the lifted target loop. -/
theorem orbitFrameClass_eq_liftedTargetFrameClass (O : V₁.OrbitIndex) :
    V₁.orbitFrameClass O =
      loopClassZ2
        (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
        (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O) := by
  unfold TamedField.orbitFrameClass
  calc
    loopClassZ2 (V₁.orbitFrameLoop O) (V₁.orbitFrameLoop_closed O) =
        loopClassZ2
          (W.transportedTargetFrameLoop hreg ht₁ ht₂ V₁ O)
          (W.transportedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ O) :=
      loopClassZ2_congr
        (V₁.orbitFrameLoop_closed O)
        (W.transportedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ O)
        (W.transportedFrameHomotopy hreg ht₁ ht₂ V₁ O)
        (W.transportedFrame_closed hreg ht₁ ht₂ V₁ O)
    _ = loopClassZ2
          (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
          (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O) :=
      loopClassZ2_congr_fun
        (W.transportedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ O)
        (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O)
        (W.transportedTargetFrameLoop_eq_liftedTargetFrameLoop
          hreg ht₁ ht₂ V₁ V₂ O)


-- @@ L1063-1089 verbatim
/-- Componentwise frame-class transport along a regular slab, with no additional
framing hypothesis. -/
theorem orbitFrameClass_eq_sliceOrbitEquiv (O : V₁.OrbitIndex) :
    V₁.orbitFrameClass O =
      V₂.orbitFrameClass (W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂ O) := by
  let e := W.sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂
  let y := W.targetTransportedBase hreg ht₁ ht₂ V₁ V₂ O
  let hy := W.targetTransportedBase_mem_fiber hreg ht₁ ht₂ V₁ V₂ O
  let q := V₂.orbitPoint (e O)
  have hqOrbit : q ∈ V₂.orbit y := by
    have hqmem : q ∈ ((e O : V₂.OrbitIndex) : Set E₁) := by
      rw [V₂.orbitPoint_orbit (e O)]
      exact V₂.mem_orbit_self q
    exact hqmem
  calc
    V₁.orbitFrameClass O =
        loopClassZ2
          (W.liftedTargetFrameLoop hreg ht₁ ht₂ V₁ V₂ O)
          (W.liftedTargetFrameLoop_closed hreg ht₁ ht₂ V₁ V₂ O) :=
      W.orbitFrameClass_eq_liftedTargetFrameClass hreg ht₁ ht₂ V₁ V₂ O
    _ = V₂.fundamentalFrameClass hy :=
      W.liftedTargetFrameClass_eq_fundamental hreg ht₁ ht₂ V₁ V₂ O
    _ = V₂.fundamentalFrameClass (V₂.orbitPoint_mem_fiber (e O)) := by
      symm
      exact V₂.fundamentalFrameClass_eq_of_mem_orbit hy hqOrbit
    _ = V₂.orbitFrameClass (e O) :=
      (V₂.orbitFrameClass_eq_fundamental (e O)).symm


-- @@ L1091-1091 verbatim
end SlabTamedField


-- @@ L1093-1093 verbatim
/-! ## Unconditional regular-slab frame transport for signed cobordisms -/


-- @@ L1095-1095 verbatim
namespace SignedFramedLevelCobordism


-- @@ L1097-1098 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L1100-1107 verbatim
variable {a b t₁ t₂ : ℝ}
  (W : SlabTamedField C.cobordism.toLevelCobordismData a b)
  (hreg : regularSlab C.cobordism.G a b)
  (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
  (V₁ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
    t₁ (hreg.sliceRegular ht₁)))
  (V₂ : TamedField (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
    t₂ (hreg.sliceRegular ht₂)))


-- @@ L1109-1114 verbatim
/-- The frame-transport input isolated in `Delta.lean` is supplied by the actual
time-flow moving frame and target phase reparametrization. -/
theorem concreteRegularSlabFrameTransport :
    C.RegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂ where
  frameClass_eq := fun O =>
    W.orbitFrameClass_eq_sliceOrbitEquiv hreg ht₁ ht₂ V₁ V₂ O


-- @@ L1116-1116 verbatim
include W


-- @@ L1118-1122 verbatim
/-- The total framed delta is unconditionally constant on a regular slab. -/
theorem framedDelta_eq_regularSlab :
    V₁.framedDelta = V₂.framedDelta :=
  RegularSlabFrameTransport.framedDelta_eq C
    (C.concreteRegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂)


-- @@ L1124-1129 verbatim
/-- The positive-sheet framed delta is unconditionally constant on a regular slab. -/
theorem positiveFramedDelta_eq_regularSlab :
    (C.sliceSign t₁ (hreg.sliceRegular ht₁)).positiveFramedDelta V₁ =
      (C.sliceSign t₂ (hreg.sliceRegular ht₂)).positiveFramedDelta V₂ :=
  RegularSlabFrameTransport.positiveFramedDelta_eq C
    (C.concreteRegularSlabFrameTransport W hreg ht₁ ht₂ V₁ V₂)


-- @@ L1131-1131 verbatim
end SignedFramedLevelCobordism


-- @@ L1133-1133 verbatim
end Submission
