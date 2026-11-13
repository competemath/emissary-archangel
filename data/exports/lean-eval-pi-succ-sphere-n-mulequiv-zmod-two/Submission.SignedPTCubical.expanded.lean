import Mathlib
import Submission.SignedPTEndpoint


-- @@ L4-12 verbatim
/-!
# Cubical representatives of signed endpoint collapses

A compactly supported signed endpoint cutoff gives a based cubical loop after
the cube is expanded far enough to contain its support.  Two cutoffs for the
same signed framed level set give homotopic loops on every common cubical
compactification.  This is the based version of cutoff independence needed by
the inverse Pontryagin--Thom argument.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace Submission


-- @@ L18-18 verbatim
open Set Function Metric Topology.Homotopy

-- @@ L19-19 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-23 verbatim
namespace FiberSign.PTCutoff


-- @@ L25-25 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L28-28 verbatim
local notation "Q" => I^(Fin (n + 1))


-- @@ L30-32 verbatim
/-- A cutoff vanishes outside the closed ball of radius `R`. -/
def VanishesOutside (κ : PTCutoff S) (R : ℝ) : Prop :=
  ∀ x : E, R ≤ ‖x‖ → κ x = 0


-- @@ L34-38 verbatim
lemma vanishesOutside_mono (κ : PTCutoff S) {R R' : ℝ}
    (h : VanishesOutside S κ R) (hRR' : R ≤ R') :
    VanishesOutside S κ R' := by
  intro x hx
  exact h x (hRR'.trans hx)


-- @@ L40-57 verbatim
/-- Compact support supplies a strictly positive support radius. -/
theorem exists_vanishesOutside (κ : PTCutoff S) :
    ∃ R : ℝ, 0 < R ∧ VanishesOutside S κ R := by
  obtain ⟨r, hr⟩ := κ.compact_support.isBounded.subset_closedBall (0 : E)
  let R : ℝ := |r| + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [abs_nonneg r]
  refine ⟨R, hR, ?_⟩
  intro x hx
  by_contra hκ
  have hxt : x ∈ tsupport κ := subset_tsupport κ hκ
  have hball := hr hxt
  rw [mem_closedBall, dist_zero_right] at hball
  have hrR : r < R := by
    dsimp [R]
    linarith [le_abs_self r]
  exact (not_lt_of_ge hball) (hrR.trans_le hx)


-- @@ L59-61 verbatim
/-- Affine expansion of the unit cube to the centered box `[-R,R]`. -/
def centeredCube (R : ℝ) (t : Q) : E :=
  WithLp.toLp 2 fun i => 2 * R * (t i : ℝ) - R


-- @@ L63-64 verbatim
@[simp] lemma centeredCube_apply (R : ℝ) (t : Q) (i : Fin (n + 1)) :
    centeredCube (n := n) R t i = 2 * R * (t i : ℝ) - R := rfl


-- @@ L66-76 verbatim
lemma continuous_centeredCube (R : ℝ) :
    Continuous (centeredCube (n := n) R) := by
  have h : centeredCube (n := n) R = fun t =>
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (fun i => 2 * R * (t i : ℝ) - R) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const


-- @@ L78-97 verbatim
/-- Every boundary point of the centered cube has norm at least its positive
radius. -/
lemma radius_le_norm_centeredCube {R : ℝ} (hR : 0 ≤ R) {t : Q}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    R ≤ ‖centeredCube (n := n) R t‖ := by
  obtain ⟨i, hi | hi⟩ := ht
  · have hcoord : centeredCube (n := n) R t i = -R := by
      rw [centeredCube_apply, hi, Set.Icc.coe_zero]
      ring
    have hle := PiLp.norm_apply_le (p := (2 : ENNReal))
      (centeredCube (n := n) R t) i
    rw [hcoord] at hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hR] using hle
  · have hcoord : centeredCube (n := n) R t i = R := by
      rw [centeredCube_apply, hi, Set.Icc.coe_one]
      ring
    have hle := PiLp.norm_apply_le (p := (2 : ENNReal))
      (centeredCube (n := n) R t) i
    rw [hcoord] at hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hR] using hle


-- @@ L99-105 verbatim
/-- Vanishing outside a ball makes the normalized endpoint collapse based on
the boundary of the corresponding centered cube. -/
lemma centeredCube_boundary_zero (κ : PTCutoff S) {R : ℝ}
    (hR : 0 ≤ R) (hsupp : VanishesOutside S κ R) {t : Q}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    κ (centeredCube (n := n) R t) = 0 :=
  hsupp _ (radius_le_norm_centeredCube (n := n) hR ht)


-- @@ L107-114 verbatim
/-- Pull a signed endpoint collapse back to any cubical compactification on
whose boundary the cutoff vanishes. -/
def cubicalLoop (κ : PTCutoff S) (φ : C(Q, E))
    (hφ : ∀ t ∈ Cube.boundary (Fin (n + 1)), κ (φ t) = 0) :
    Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n) :=
  ⟨(sphereMap S κ).comp φ, by
    intro t ht
    exact sphereMap_of_zero S κ (hφ t ht)⟩


-- @@ L116-118 verbatim
@[simp] lemma cubicalLoop_apply (κ : PTCutoff S) (φ : C(Q, E))
    (hφ : ∀ t ∈ Cube.boundary (Fin (n + 1)), κ (φ t) = 0) (t : Q) :
    cubicalLoop S κ φ hφ t = sphereMap S κ (φ t) := rfl


-- @@ L120-139 verbatim
/-- On a fixed compactifying cube, convex interpolation of two cutoffs is a
homotopy relative to the whole cube boundary. -/
def cubicalLoopHomotopy (κ₀ κ₁ : PTCutoff S) (φ : C(Q, E))
    (h₀ : ∀ t ∈ Cube.boundary (Fin (n + 1)), κ₀ (φ t) = 0)
    (h₁ : ∀ t ∈ Cube.boundary (Fin (n + 1)), κ₁ (φ t) = 0) :
    ContinuousMap.HomotopyRel (cubicalLoop S κ₀ φ h₀).1
      (cubicalLoop S κ₁ φ h₁).1 (Cube.boundary (Fin (n + 1))) where
  toFun st := lerpSphereMap S κ₀ κ₁ (st.1, φ st.2)
  continuous_toFun := (map_continuous (lerpSphereMap S κ₀ κ₁)).comp
    (continuous_fst.prodMk ((map_continuous φ).comp continuous_snd))
  map_zero_left t := by
    change lerpSphereMap S κ₀ κ₁ (0, φ t) = sphereMap S κ₀ (φ t)
    exact (sphereMapHomotopy S κ₀ κ₁).map_zero_left (φ t)
  map_one_left t := by
    change lerpSphereMap S κ₀ κ₁ (1, φ t) = sphereMap S κ₁ (φ t)
    exact (sphereMapHomotopy S κ₀ κ₁).map_one_left (φ t)
  prop' s t ht := by
    change lerpSphereMap S κ₀ κ₁ (s, φ t) = sphereMap S κ₀ (φ t)
    rw [lerpSphereMap_of_zero S κ₀ κ₁ (h₀ t ht) (h₁ t ht)]
    exact (sphereMap_of_zero S κ₀ (h₀ t ht)).symm


-- @@ L141-145 verbatim
theorem cubicalLoop_homotopic (κ₀ κ₁ : PTCutoff S) (φ : C(Q, E))
    (h₀ : ∀ t ∈ Cube.boundary (Fin (n + 1)), κ₀ (φ t) = 0)
    (h₁ : ∀ t ∈ Cube.boundary (Fin (n + 1)), κ₁ (φ t) = 0) :
    GenLoop.Homotopic (cubicalLoop S κ₀ φ h₀) (cubicalLoop S κ₁ φ h₁) :=
  ⟨cubicalLoopHomotopy S κ₀ κ₁ φ h₀ h₁⟩


-- @@ L147-153 verbatim
/-- The centered representative attached to an explicit support radius. -/
def centeredLoop (κ : PTCutoff S) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : VanishesOutside S κ R) :
    Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n) :=
  cubicalLoop S κ
    ⟨centeredCube (n := n) R, continuous_centeredCube (n := n) R⟩
    fun t ht => centeredCube_boundary_zero S κ hR hsupp ht


-- @@ L155-158 verbatim
@[simp] lemma centeredLoop_apply (κ : PTCutoff S) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : VanishesOutside S κ R) (t : Q) :
    centeredLoop S κ R hR hsupp t =
      sphereMap S κ (centeredCube (n := n) R t) := rfl


-- @@ L160-165 verbatim
/-- Cutoff independence on a common centered compactification. -/
theorem centeredLoop_homotopic (κ₀ κ₁ : PTCutoff S) (R : ℝ) (hR : 0 ≤ R)
    (h₀ : VanishesOutside S κ₀ R) (h₁ : VanishesOutside S κ₁ R) :
    GenLoop.Homotopic (centeredLoop S κ₀ R hR h₀)
      (centeredLoop S κ₁ R hR h₁) := by
  apply cubicalLoop_homotopic S κ₀ κ₁


-- @@ L167-183 verbatim
/-- Two compactly supported cutoffs possess one common centered
compactification, and their representatives there are homotopic. -/
theorem exists_common_centeredLoop_homotopy (κ₀ κ₁ : PTCutoff S) :
    ∃ R : ℝ, ∃ hR : 0 < R,
      ∃ h₀ : VanishesOutside S κ₀ R,
      ∃ h₁ : VanishesOutside S κ₁ R,
        GenLoop.Homotopic (centeredLoop S κ₀ R hR.le h₀)
          (centeredLoop S κ₁ R hR.le h₁) := by
  obtain ⟨R₀, hR₀, h₀⟩ := exists_vanishesOutside S κ₀
  obtain ⟨R₁, hR₁, h₁⟩ := exists_vanishesOutside S κ₁
  let R := max R₀ R₁
  have hR : 0 < R := hR₀.trans_le (le_max_left _ _)
  have h₀' : VanishesOutside S κ₀ R :=
    vanishesOutside_mono S κ₀ h₀ (le_max_left _ _)
  have h₁' : VanishesOutside S κ₁ R :=
    vanishesOutside_mono S κ₁ h₁ (le_max_right _ _)
  exact ⟨R, hR, h₀', h₁', centeredLoop_homotopic S κ₀ κ₁ R hR.le h₀' h₁'⟩


-- @@ L185-194 verbatim
/-- Every endpoint cutoff therefore has at least one honest based cubical
representative. -/
theorem exists_centeredCubicalLoop (κ : PTCutoff S) :
    ∃ R : ℝ, ∃ hR : 0 < R,
      Nonempty (Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n)) := by
  obtain ⟨R, hR, hsupp⟩ := exists_vanishesOutside S κ
  refine ⟨R, hR, ?_⟩
  let φ : C(Q, E) := ⟨centeredCube (n := n) R, continuous_centeredCube (n := n) R⟩
  exact ⟨cubicalLoop S κ φ fun t ht =>
    centeredCube_boundary_zero S κ hR.le hsupp ht⟩


-- @@ L196-196 verbatim
end FiberSign.PTCutoff


-- @@ L198-198 verbatim
namespace SignedFramedLevelCobordism.SignedSlabCutoff


-- @@ L200-201 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L203-203 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L204-204 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L205-205 verbatim
local notation "Q" => I^(Fin (n + 1))


-- @@ L207-209 verbatim
/-- Uniform spatial vanishing on every time slice of the slab. -/
def SpatialVanishesOutside (χ : SignedSlabCutoff C) (R : ℝ) : Prop :=
  ∀ (t : I) (x : E), R ≤ ‖x‖ → χ (spaceTime x (t : ℝ)) = 0


-- @@ L211-215 verbatim
lemma spatialVanishesOutside_mono (χ : SignedSlabCutoff C) {R R' : ℝ}
    (h : SpatialVanishesOutside C χ R) (hRR' : R ≤ R') :
    SpatialVanishesOutside C χ R' := by
  intro t x hx
  exact h t x (hRR'.trans hx)


-- @@ L217-242 verbatim
/-- Compact spacetime support is uniformly bounded in the spatial variables. -/
theorem exists_spatialVanishesOutside (χ : SignedSlabCutoff C) :
    ∃ R : ℝ, 0 < R ∧ SpatialVanishesOutside C χ R := by
  obtain ⟨r, hr⟩ := χ.compact_support.isBounded.subset_closedBall (0 : A)
  let R : ℝ := |r| + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [abs_nonneg r]
  refine ⟨R, hR, ?_⟩
  intro t x hx
  by_contra hχ
  have hst : spaceTime x (t : ℝ) ∈ tsupport χ := subset_tsupport χ hχ
  have hball := hr hst
  rw [mem_closedBall, dist_zero_right] at hball
  have hxspace : ‖x‖ ≤ ‖spaceTime x (t : ℝ)‖ := by
    have hinit : initCLM (n + 1) (spaceTime x (t : ℝ)) = x :=
      initCLM_spaceTime x (t : ℝ)
    calc
      ‖x‖ = ‖initCLM (n + 1) (spaceTime x (t : ℝ))‖ := congrArg norm hinit.symm
      _ ≤ ‖spaceTime x (t : ℝ)‖ := by
        simpa [spacePart, initCLM, initLM] using
          norm_spacePart_le (spaceTime x (t : ℝ))
  have hrR : r < R := by
    dsimp [R]
    linarith [le_abs_self r]
  exact (not_lt_of_ge hball) (hrR.trans_le (hx.trans hxspace))


-- @@ L244-248 verbatim
lemma source_vanishesOutside (χ : SignedSlabCutoff C) {R : ℝ}
    (h : SpatialVanishesOutside C χ R) :
    FiberSign.PTCutoff.VanishesOutside S₀ (sourcePTCutoff C χ) R := by
  intro x hx
  exact h 0 x hx


-- @@ L250-254 verbatim
lemma target_vanishesOutside (χ : SignedSlabCutoff C) {R : ℝ}
    (h : SpatialVanishesOutside C χ R) :
    FiberSign.PTCutoff.VanishesOutside S₁ (targetPTCutoff C χ) R := by
  intro x hx
  exact h 1 x hx


-- @@ L256-265 verbatim
/-- If the spacetime cutoff is zero, the slab collapse is exactly the south
pole. -/
lemma slabPTCM_of_cutoff_zero (χ : SignedSlabCutoff C) {p : I × E}
    (hχ : χ (slabSpaceTime p) = 0) :
    slabPTCM C χ p = southPole n := by
  apply Subtype.ext
  have hraw : raw C χ (slabSpaceTime p) = -eLast n := by
    simp [raw, hχ]
  change ‖raw C χ (slabSpaceTime p)‖⁻¹ • raw C χ (slabSpaceTime p) = -eLast n
  rw [hraw, norm_neg, norm_eLast, inv_one, one_smul]


-- @@ L267-303 verbatim
/-- Restrict the slab PT homotopy to a sufficiently large centered cube.  Its
whole boundary is fixed at the south pole. -/
def centeredSlabHomotopy (χ : SignedSlabCutoff C) (R : ℝ) (hR : 0 ≤ R)
    (hs : SpatialVanishesOutside C χ R) :
    ContinuousMap.HomotopyRel
      (FiberSign.PTCutoff.centeredLoop S₀ (sourcePTCutoff C χ) R hR
        (source_vanishesOutside C χ hs)).1
      (FiberSign.PTCutoff.centeredLoop S₁ (targetPTCutoff C χ) R hR
        (target_vanishesOutside C χ hs)).1
      (Cube.boundary (Fin (n + 1))) where
  toFun st := slabPTCM C χ
    (st.1, FiberSign.PTCutoff.centeredCube (n := n) R st.2)
  continuous_toFun := (map_continuous (slabPTCM C χ)).comp
    (continuous_fst.prodMk
      ((FiberSign.PTCutoff.continuous_centeredCube (n := n) R).comp continuous_snd))
  map_zero_left t := by
    change endpointPTCM C χ 0
      (FiberSign.PTCutoff.centeredCube (n := n) R t) =
      FiberSign.PTCutoff.sphereMap S₀ (sourcePTCutoff C χ)
        (FiberSign.PTCutoff.centeredCube (n := n) R t)
    rw [endpointPTCM_zero_eq]
  map_one_left t := by
    change endpointPTCM C χ 1
      (FiberSign.PTCutoff.centeredCube (n := n) R t) =
      FiberSign.PTCutoff.sphereMap S₁ (targetPTCutoff C χ)
        (FiberSign.PTCutoff.centeredCube (n := n) R t)
    rw [endpointPTCM_one_eq]
  prop' s t ht := by
    let x := FiberSign.PTCutoff.centeredCube (n := n) R t
    have hx : R ≤ ‖x‖ :=
      FiberSign.PTCutoff.radius_le_norm_centeredCube (n := n) hR ht
    have hχ : χ (slabSpaceTime (s, x)) = 0 := hs s x hx
    change slabPTCM C χ (s, x) =
      FiberSign.PTCutoff.sphereMap S₀ (sourcePTCutoff C χ) x
    rw [slabPTCM_of_cutoff_zero C χ hχ]
    exact (FiberSign.PTCutoff.sphereMap_of_zero S₀ (sourcePTCutoff C χ)
      (source_vanishesOutside C χ hs x hx)).symm


-- @@ L305-312 verbatim
theorem centered_endpointLoops_homotopic (χ : SignedSlabCutoff C)
    (R : ℝ) (hR : 0 ≤ R) (hs : SpatialVanishesOutside C χ R) :
    GenLoop.Homotopic
      (FiberSign.PTCutoff.centeredLoop S₀ (sourcePTCutoff C χ) R hR
        (source_vanishesOutside C χ hs))
      (FiberSign.PTCutoff.centeredLoop S₁ (targetPTCutoff C χ) R hR
        (target_vanishesOutside C χ hs)) :=
  ⟨centeredSlabHomotopy C χ R hR hs⟩


-- @@ L314-351 verbatim
/-- A signed cobordism identifies the centered PT representatives obtained from
arbitrary endpoint cutoffs.  The radius is chosen once for both endpoint
cutoffs and the whole spacetime homotopy. -/
theorem exists_endpointCutoffHomotopy (χ : SignedSlabCutoff C)
    (κ₀ : FiberSign.PTCutoff S₀) (κ₁ : FiberSign.PTCutoff S₁) :
    ∃ R : ℝ, ∃ hR : 0 < R,
      ∃ hR1 : 1 ≤ R,
      ∃ h₀ : FiberSign.PTCutoff.VanishesOutside S₀ κ₀ R,
      ∃ h₁ : FiberSign.PTCutoff.VanishesOutside S₁ κ₁ R,
        GenLoop.Homotopic
          (FiberSign.PTCutoff.centeredLoop S₀ κ₀ R hR.le h₀)
          (FiberSign.PTCutoff.centeredLoop S₁ κ₁ R hR.le h₁) := by
  obtain ⟨R₀, hR₀, h₀⟩ := FiberSign.PTCutoff.exists_vanishesOutside S₀ κ₀
  obtain ⟨R₁, hR₁, h₁⟩ := FiberSign.PTCutoff.exists_vanishesOutside S₁ κ₁
  obtain ⟨Rs, hRs, hs⟩ := exists_spatialVanishesOutside C χ
  let R : ℝ := max (max (max R₀ R₁) Rs) 1
  have hR : 0 < R := hR₀.trans_le
    (((le_max_left R₀ R₁).trans (le_max_left (max R₀ R₁) Rs)).trans
      (le_max_left (max (max R₀ R₁) Rs) 1))
  have hR1 : 1 ≤ R := le_max_right _ _
  have h₀' : FiberSign.PTCutoff.VanishesOutside S₀ κ₀ R :=
    FiberSign.PTCutoff.vanishesOutside_mono S₀ κ₀ h₀
      (((le_max_left R₀ R₁).trans (le_max_left (max R₀ R₁) Rs)).trans
        (le_max_left (max (max R₀ R₁) Rs) 1))
  have h₁' : FiberSign.PTCutoff.VanishesOutside S₁ κ₁ R :=
    FiberSign.PTCutoff.vanishesOutside_mono S₁ κ₁ h₁
      (((le_max_right R₀ R₁).trans (le_max_left (max R₀ R₁) Rs)).trans
        (le_max_left (max (max R₀ R₁) Rs) 1))
  have hs' : SpatialVanishesOutside C χ R :=
    spatialVanishesOutside_mono C χ hs
      ((le_max_right (max R₀ R₁) Rs).trans
        (le_max_left (max (max R₀ R₁) Rs) 1))
  have hleft := FiberSign.PTCutoff.centeredLoop_homotopic S₀ κ₀
    (sourcePTCutoff C χ) R hR.le h₀' (source_vanishesOutside C χ hs')
  have hmiddle := centered_endpointLoops_homotopic C χ R hR.le hs'
  have hright := FiberSign.PTCutoff.centeredLoop_homotopic S₁
    (targetPTCutoff C χ) κ₁ R hR.le (target_vanishesOutside C χ hs') h₁'
  exact ⟨R, hR, hR1, h₀', h₁', hleft.trans (hmiddle.trans hright)⟩


-- @@ L353-353 verbatim
end SignedFramedLevelCobordism.SignedSlabCutoff


-- @@ L355-355 verbatim
end Submission
