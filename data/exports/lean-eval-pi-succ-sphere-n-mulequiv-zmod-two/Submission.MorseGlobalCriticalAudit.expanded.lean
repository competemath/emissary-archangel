import Mathlib
import Submission.FiniteMorseJetInstallation
import Submission.IFTSurfaceCriticality
import Submission.MorseCriticalModelAssembly


-- @@ L6-26 verbatim
/-!
# Global critical-locus audit for finite local Morse jets

The exact finite jet installer controls the perturbation on the half-radius
core of each recorded event.  Two complementary facts explain why this local
contract alone cannot prove a global no-new-critical-points theorem.

* On a cutoff transition region the derivative of a localized affine jet has
  the extra product-rule term `h(v) • dχ(v)`.  None of the fields of
  `ExactFiniteMorseJetInstallation` controls this term along the old fiber.
* Away from the closed support balls, the finite forward perturbation is
  locally zero.  Hence the pulled-back time-criticality test is literally the
  unperturbed one there: an old critical point outside all event balls
  survives.

The final lemmas also record the useful repair principle.  If one global
cutoff is identically one along a whole local fiber chart, localization
introduces no transition term in the chart time.  This is the analytic API
needed by a future construction based on one fiber-wide cutoff and one
compatible global tilt, rather than independently localized event jets.
-/


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open Set Function Metric Filter

-- @@ L31-31 verbatim
open scoped RealInnerProductSpace ContDiff Topology BigOperators


-- @@ L33-33 verbatim
namespace Submission


-- @@ L35-35 verbatim
variable {n : ℕ}


-- @@ L37-37 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L38-38 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L40-40 verbatim
namespace SmoothCutoff


-- @@ L42-52 verbatim
/-- Product-rule formula for a localized smooth scalar function.  The second
summand is precisely the transition contribution which is absent on a region
where the cutoff is locally constant. -/
theorem fderiv_localize {K U : Set E'} (χ : SmoothCutoff K U)
    {h : E' → ℝ} (hh : ContDiff ℝ ∞ h) (v : E') :
    fderiv ℝ (χ.localize h) v =
      χ v • fderiv ℝ h v + h v • fderiv ℝ χ v := by
  have hχ := (χ.smooth.differentiable (by simp) v).hasFDerivAt
  have hh' := (hh.differentiable (by simp) v).hasFDerivAt
  change fderiv ℝ (χ.toFun * h) v = _
  simpa [add_comm] using (hχ.mul hh').fderiv


-- @@ L54-73 verbatim
/-- For an affine jet the ordinary derivative is its linear part, so the
uncontrolled transition contribution is completely explicit. -/
theorem fderiv_localize_affineJet {K U : Set E'}
    (χ : SmoothCutoff K U) (A : E' →L[ℝ] ℝ) (center : E') (c : ℝ)
    (v : E') :
    fderiv ℝ (χ.localize (affineJet A center c)) v =
      χ v • A + (A (v - center) + c) • fderiv ℝ χ v := by
  rw [χ.fderiv_localize (contDiff_affineJet A center c)]
  have hAffine : fderiv ℝ (affineJet A center c) v = A := by
    change fderiv ℝ (fun w => A (w - center) + c) v = A
    have hinner : HasFDerivAt (fun w => A (w - center)) A v := by
      have heq : (fun w : E' => A (w - center)) =
          fun w : E' => A w - A center := by
        funext w
        exact map_sub A w center
      rw [heq]
      exact A.hasFDerivAt.sub_const (A center)
    exact (hinner.add_const c).fderiv
  rw [hAffine]
  rfl


-- @@ L75-83 verbatim
/-- If a parameterized surface stays in the cutoff core near a parameter,
localization is eventually identical to the unlocalized function. -/
theorem eventuallyEq_localize_comp_of_eventually_mem_core
    {K U : Set E'} (χ : SmoothCutoff K U) (h : E' → ℝ)
    (param : E₂ → E') {u : E₂}
    (hcore : ∀ᶠ z in 𝓝 u, param z ∈ K) :
    (χ.localize h ∘ param) =ᶠ[𝓝 u] (h ∘ param) := by
  filter_upwards [hcore] with z hz
  exact χ.localize_eq h hz


-- @@ L85-93 verbatim
/-- Consequently a single cutoff which is one along a local fiber chart has
exactly the same chartwise derivative as the underlying global perturbation.
This is the no-transition mechanism needed by a fiber-wide installation. -/
theorem fderiv_localize_comp_of_eventually_mem_core
    {K U : Set E'} (χ : SmoothCutoff K U)
    (h : E' → ℝ) (param : E₂ → E') {u : E₂}
    (hcore : ∀ᶠ z in 𝓝 u, param z ∈ K) :
    fderiv ℝ (χ.localize h ∘ param) u = fderiv ℝ (h ∘ param) u := by
  exact (χ.eventuallyEq_localize_comp_of_eventually_mem_core h param hcore).fderiv_eq


-- @@ L95-95 verbatim
end SmoothCutoff


-- @@ L97-97 verbatim
/-! ## One cutoff for an entire compact interior subslab -/


-- @@ L99-102 verbatim
/-- The part of the compact cobordism fiber over a closed interior time
subinterval. -/
def compactInteriorFiber (C : FramedLevelCobordism n) (a b : ℝ) : Set E' :=
  C.fiber ∩ tcoord ⁻¹' Icc a b


-- @@ L104-107 verbatim
theorem isCompact_compactInteriorFiber (C : FramedLevelCobordism n)
    (a b : ℝ) : IsCompact (compactInteriorFiber C a b) := by
  exact C.isCompact_slabFiber.inter_right
    (isClosed_Icc.preimage continuous_tcoord)


-- @@ L109-115 verbatim
theorem compactInteriorFiber_subset_middle
    (C : FramedLevelCobordism n) {a b : ℝ}
    (ha : 1 / 4 < a) (hb : b < 3 / 4) :
    compactInteriorFiber C a b ⊆
      tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  rintro v ⟨_hv, ht⟩
  exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩


-- @@ L117-163 verbatim
/-- Compactness and the fixed regular collars give uniform interior time
bounds for the entire old critical locus. -/
theorem exists_interior_bounds_coreCriticalPoints
    (C : FramedLevelCobordism n) :
    ∃ a b : ℝ,
      1 / 4 < a ∧ a < b ∧ b < 3 / 4 ∧
      coreCriticalPoints C ⊆ tcoord ⁻¹' Icc a b := by
  let K : Set E' := coreCriticalPoints C
  have hK : IsCompact K := isCompact_coreCriticalPoints C
  have hlower : ∀ v ∈ K, (1 / 4 : ℝ) < tcoord v := by
    intro v hv
    by_contra h
    have hreg := C.sliceRegular_of_le_quarter (le_of_not_gt h)
    exact hv.1.2 (hreg v hv.1.1 rfl)
  have hupper : ∀ v ∈ K, tcoord v < (3 / 4 : ℝ) := by
    intro v hv
    by_contra h
    have hreg := C.sliceRegular_of_three_quarter_le (le_of_not_gt h)
    exact hv.1.2 (hreg v hv.1.1 rfl)
  obtain ⟨a₀, ha₀, hamin⟩ :=
    hK.exists_forall_le' continuous_tcoord.continuousOn hlower
  obtain ⟨b₀', hb₀', hbmax'⟩ :=
    hK.exists_forall_le' (α := ℝᵒᵈ)
      continuous_tcoord.continuousOn hupper
  let b₀ : ℝ := b₀'
  have hb₀ : b₀ < (3 / 4 : ℝ) := hb₀'
  have hbmax : ∀ v ∈ K, tcoord v ≤ b₀ := by
    intro v hv
    exact hbmax' v hv
  let a : ℝ := min a₀ (3 / 8)
  let b : ℝ := max b₀ (5 / 8)
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · exact lt_min ha₀ (by norm_num)
  · have ha : a ≤ (3 / 8 : ℝ) := min_le_right _ _
    have hb : (5 / 8 : ℝ) ≤ b := le_max_right _ _
    linarith
  · exact max_lt hb₀ (by norm_num)
  · intro v hv
    have hva : a ≤ tcoord v :=
      (min_le_left a₀ (3 / 8)).trans (hamin v hv)
    have hvb₀ : tcoord v ≤ b₀ := hbmax v hv
    have hb₀b : b₀ ≤ b := by
      dsimp [b]
      exact le_max_left _ _
    have hvb : tcoord v ≤ b :=
      hvb₀.trans hb₀b
    exact ⟨hva, hvb⟩


-- @@ L165-187 verbatim
/-- The interior bounds may be chosen with a strict margin around every old
critical point.  The margin is what lets compact stability rule out critical
points on the two cutoff-transition strips. -/
theorem exists_strictInterior_bounds_coreCriticalPoints
    (C : FramedLevelCobordism n) :
    ∃ a b : ℝ,
      1 / 4 < a ∧ a < b ∧ b < 3 / 4 ∧
      coreCriticalPoints C ⊆ tcoord ⁻¹' Ioo a b := by
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hcrit⟩ :=
    exists_interior_bounds_coreCriticalPoints C
  let a : ℝ := (1 / 4 + a₀) / 2
  let b : ℝ := (b₀ + 3 / 4) / 2
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    linarith
  · dsimp [a, b]
    linarith
  · dsimp [b]
    linarith
  · intro v hv
    have ht := hcrit hv
    dsimp [a, b]
    constructor <;> linarith [ht.1, ht.2]


-- @@ L189-204 verbatim
/-- If the compact middle critical locus lies strictly between `a` and `b`,
then so does the entire time-critical locus.  The fixed collar regularity
excludes critical points outside the middle slab. -/
theorem timeCritical_subset_strictInterior_of_coreCritical_subset
    (C : FramedLevelCobordism n) {a b : ℝ}
    (hcrit : coreCriticalPoints C ⊆ tcoord ⁻¹' Ioo a b) :
    timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b := by
  intro v hv
  have hlower : (1 / 4 : ℝ) < tcoord v := by
    by_contra h
    exact hv.2 ((C.sliceRegular_of_le_quarter (le_of_not_gt h)) v hv.1 rfl)
  have hupper : tcoord v < (3 / 4 : ℝ) := by
    by_contra h
    exact hv.2
      ((C.sliceRegular_of_three_quarter_le (le_of_not_gt h)) v hv.1 rfl)
  exact hcrit ⟨hv, ⟨hlower.le, hupper.le⟩⟩


-- @@ L206-236 verbatim
/-- A single compactly supported smooth cutoff can be chosen to equal one on
the *whole* fiber over any closed subslab strictly inside the collars, while
its support remains in the open middle slab.  Unlike event-by-event balls,
this construction puts no cutoff transition on that portion of the fiber. -/
theorem exists_globalCompactInteriorFiberCutoff
    (C : FramedLevelCobordism n) {a b : ℝ}
    (ha : 1 / 4 < a) (hb : b < 3 / 4) :
    ∃ U : Set E',
      U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) ∧
      Nonempty (SmoothCutoff (compactInteriorFiber C a b) U) := by
  let K : Set E' := compactInteriorFiber C a b
  let middle : Set E' := tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)
  have hK : IsCompact K := isCompact_compactInteriorFiber C a b
  have hopen : IsOpen middle :=
    isOpen_Ioo.preimage contDiff_vertC.continuous
  have hsub : K ⊆ middle :=
    compactInteriorFiber_subset_middle C ha hb
  obtain ⟨δ, hδ, hthick⟩ :=
    hK.exists_cthickening_subset_open hopen hsub
  let U : Set E' := Metric.thickening δ K
  have hKU : K ⊆ U := Metric.self_subset_thickening hδ K
  have hUsub : U ⊆ middle :=
    (Metric.thickening_subset_cthickening δ K).trans hthick
  have hUc : IsCompact (closure U) := by
    apply IsCompact.of_isClosed_subset hK.cthickening isClosed_closure
    exact closure_minimal
      (Metric.thickening_subset_cthickening δ K)
      Metric.isClosed_cthickening
  refine ⟨U, hUsub, ?_⟩
  exact SmoothCutoff.exists_of_isClosed_isOpen hK.isClosed
    Metric.isOpen_thickening hKU hUc


-- @@ L238-254 verbatim
/-- In particular, one genuine global cutoff can be chosen with a core that
contains every old critical point and an ambient support wholly inside the
middle slab. -/
theorem exists_globalCutoff_covering_coreCriticalPoints
    (C : FramedLevelCobordism n) :
    ∃ a b : ℝ, ∃ U : Set E',
      1 / 4 < a ∧ a < b ∧ b < 3 / 4 ∧
      coreCriticalPoints C ⊆ compactInteriorFiber C a b ∧
      U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) ∧
      Nonempty (SmoothCutoff (compactInteriorFiber C a b) U) := by
  obtain ⟨a, b, ha, hab, hb, hcrit⟩ :=
    exists_interior_bounds_coreCriticalPoints C
  obtain ⟨U, hU, hχ⟩ :=
    exists_globalCompactInteriorFiberCutoff C ha hb
  refine ⟨a, b, U, ha, hab, hb, ?_, hU, hχ⟩
  intro v hv
  exact ⟨coreCriticalPoints_subset_fiber C hv, hcrit hv⟩


-- @@ L256-256 verbatim
namespace IFTSurfaceChart


-- @@ L258-275 verbatim
/-- A valid surface chart whose time lies strictly inside `[a,b]` stays in the
global compact-interior fiber core on a whole parameter neighborhood. -/
theorem eventually_mem_compactInteriorFiber
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {u : E₂} (hdom : P.domain ∈ 𝓝 u)
    (ht : P.time u ∈ Ioo a b) :
    ∀ᶠ z in 𝓝 u, P.param z ∈ compactInteriorFiber C a b := by
  have htime : ∀ᶠ z in 𝓝 u, P.time z ∈ Ioo a b :=
    P.contDiff_time.continuous.continuousAt (isOpen_Ioo.mem_nhds ht)
  filter_upwards [hdom, htime] with z hzdom hzt
  refine ⟨?_, hzt.1.le, hzt.2.le⟩
  refine ⟨P.param_fiber z hzdom, ?_, ?_⟩
  · change 0 ≤ P.time z
    exact (by norm_num : (0 : ℝ) ≤ 1 / 4).trans
      (ha.le.trans hzt.1.le)
  · change P.time z ≤ 1
    exact hzt.2.le.trans (hb.le.trans (by norm_num : (3 / 4 : ℝ) ≤ 1))


-- @@ L277-288 verbatim
/-- On such a chart, the one global cutoff has exactly the same differential
as its unlocalized global perturbing function. -/
theorem fderiv_globalCutoff_comp_eq
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {U : Set E'} (χ : SmoothCutoff (compactInteriorFiber C a b) U)
    (h : E' → ℝ) {u : E₂} (hdom : P.domain ∈ 𝓝 u)
    (ht : P.time u ∈ Ioo a b) :
    fderiv ℝ (χ.localize h ∘ P.param) u =
      fderiv ℝ (h ∘ P.param) u := by
  exact χ.fderiv_localize_comp_of_eventually_mem_core h P.param
    (P.eventually_mem_compactInteriorFiber ha hb hdom ht)


-- @@ L290-290 verbatim
end IFTSurfaceChart


-- @@ L292-292 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L294-296 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceChartFamily C ι}
  {G : GenericFiniteIFTSurfaceAtlas B}


-- @@ L298-329 verbatim
/-- At a point outside every closed event support ball, the finite forward
amplitude is identically zero on a whole neighborhood. -/
theorem eventuallyEq_forwardAmplitude_zero_of_away
    (R : ExactFiniteMorseJetInstallation G) {v : E'}
    (haway : ∀ p : GenericMorseEvent G,
      v ∉ closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p)) :
    R.forwardAmplitude =ᶠ[𝓝 v] (0 : E' → ℝ) := by
  classical
  have hp : ∀ p : GenericMorseEvent G,
      R.eventRaw p =ᶠ[𝓝 v] (0 : E' → ℝ) := by
    intro p
    have hopen : IsOpen
        (closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p))ᶜ :=
      Metric.isClosed_closedBall.isOpen_compl
    have hnhds :
        (closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p))ᶜ ∈ 𝓝 v :=
      hopen.mem_nhds (haway p)
    filter_upwards [hnhds] with w hw
    apply (R.cutoffs.cutoff p).localize_eq_zero _
    intro hball
    exact hw (Metric.ball_subset_closedBall hball)
  have hsum :
      (fun w : E' => ∑ p : GenericMorseEvent G, R.eventRaw p w) =ᶠ[𝓝 v]
        (0 : E' → ℝ) := by
    have hall : ∀ᶠ w in 𝓝 v,
        ∀ p : GenericMorseEvent G, R.eventRaw p w = 0 :=
      Filter.eventually_all.mpr hp
    filter_upwards [hall] with w hw
    simpa using Finset.sum_eq_zero (fun p _ => hw p)
  filter_upwards [hsum] with w hw
  change FiniteGlobalVerticalAmplitude.totalRaw R.eventRaw w = 0
  simpa [FiniteGlobalVerticalAmplitude.totalRaw] using hw


-- @@ L331-342 verbatim
/-- The inverse diffeomorphism used to parameterize the pulled-back fiber is
locally the identity wherever the forward event amplitude is locally zero. -/
theorem eventuallyEq_amplitude_symm_identity_of_away
    (R : ExactFiniteMorseJetInstallation G) {v : E'}
    (haway : ∀ p : GenericMorseEvent G,
      v ∉ closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p)) :
    R.amplitude.diffeomorph.symm =ᶠ[𝓝 v] id := by
  have hzero := R.eventuallyEq_forwardAmplitude_zero_of_away haway
  filter_upwards [hzero] with w hw
  rw [R.amplitude_diffeomorph_symm,
    SmallVerticalAmplitude.diffeomorph_apply]
  simp [verticalShift, hw]


-- @@ L344-374 verbatim
/-- An unperturbed chart critical point outside every event support survives
as an actual critical point of the pulled-back cobordism.  More precisely,
criticality is equivalent on the two sides.  Thus the fields of
`ExactFiniteMorseJetInstallation` cannot by themselves imply the global
critical-cover field unless a separate theorem rules out such points. -/
theorem pullback_critical_iff_unperturbed_of_away
    (R : ExactFiniteMorseJetInstallation G) (i : ι) {u : E₂}
    (hdom : (B.chart i).domain ∈ 𝓝 u)
    (haway : ∀ p : GenericMorseEvent G,
      (B.chart i).param u ∉
        closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p)) :
    R.amplitude.diffeomorph.symm ((B.chart i).param u) ∈
        timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G ↔
      (B.chart i).param u ∈ timeCritical C.G := by
  let P := B.chart i
  have hsymm :
      (fun z : E₂ => R.amplitude.diffeomorph.symm (P.param z)) =ᶠ[𝓝 u]
        P.param := by
    have hlocal := R.eventuallyEq_amplitude_symm_identity_of_away haway
    have htend : Tendsto P.param (𝓝 u) (𝓝 (P.param u)) :=
      P.param_smooth.continuous.continuousAt
    exact (htend.eventually hlocal).mono fun z hz => by simpa using hz
  have htime :
      (fun z : E₂ => tcoord
        (R.amplitude.diffeomorph.symm (P.param z))) =ᶠ[𝓝 u] P.time := by
    exact hsymm.fun_comp tcoord
  rw [P.pullbackParam_mem_timeCritical_iff_chartGradient_eq_zero
      R.amplitude hdom,
    P.mem_timeCritical_iff_chartGradient_eq_zero hdom]
  unfold chartGradient
  rw [htime.fderiv_eq]


-- @@ L376-376 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L378-378 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L380-382 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L384-420 verbatim
/-- A point outside every full event ball cannot be represented by any of the
chosen, cutoff-controlled critical normal forms.  This is stronger than mere
absence from the event cores: it also accounts for the global inverse
diffeomorphism used in the installed parameterization. -/
theorem not_covered_by_criticalNormalForms_of_away
    (R : ExactFiniteMorseJetInstallation G) {v : E'}
    (haway : ∀ p : GenericMorseEvent G,
      v ∉ closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p)) :
    ¬ ∃ p : Σ _ : ι, E₂, ∃ hp : p ∈ G.criticalPoints, ∃ u : E₂,
      ‖u‖ < (R.criticalNormalForm p hp).radius ∧
      R.amplitude.diffeomorph.symm
        ((B.chart p.1).param
          (p.2 + (R.criticalNormalForm p hp).param u)) = v := by
  rintro ⟨p, hp, u, hu, huv⟩
  have hu' : ‖u‖ < (R.criticalModelShrink p hp).radius := by
    simpa using hu
  have hball :=
    LocalMorseNormalForm.SimultaneousShrink.ift_lifted_mem
      (M := G.localMorseNormalForm p hp)
      (R.criticalModelShrink p hp) u hu'
  have hsymm : R.amplitude.diffeomorph.symm v = v :=
    (R.eventuallyEq_amplitude_symm_identity_of_away haway).self_of_nhds
  have hdiffeo : R.amplitude.diffeomorph v = v := by
    have h := congrArg R.amplitude.diffeomorph hsymm
    simpa using h.symm
  have hparam :
      (B.chart p.1).param
          (p.2 + (R.criticalNormalForm p hp).param u) = v := by
    have h := congrArg R.amplitude.diffeomorph huv
    simpa [hdiffeo] using h
  apply haway ⟨p, hp⟩
  rw [← hparam]
  rw [R.criticalNormalForm_param]
  rw [mem_closedBall]
  rw [mem_ball] at hball
  have hr := R.cutoffs.radius_pos ⟨p, hp⟩
  exact hball.le.trans (by linarith)


-- @@ L422-454 verbatim
/-- Concrete failure certificate for the desired global cover: any old chart
critical point in the middle slab which lies outside all event balls remains a
critical point of the perturbed cobordism, but is not in the image of any
installed critical normal form. -/
theorem unperturbed_coreCritical_not_covered_of_away
    (R : ExactFiniteMorseJetInstallation G) (i : ι) {u : E₂}
    (hdom : (B.chart i).domain ∈ 𝓝 u)
    (hcrit : (B.chart i).param u ∈ timeCritical C.G)
    (htime : tcoord ((B.chart i).param u) ∈
      Icc (1 / 4 : ℝ) (3 / 4 : ℝ))
    (haway : ∀ p : GenericMorseEvent G,
      (B.chart i).param u ∉
        closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p)) :
    (B.chart i).param u ∈
        coreCriticalPoints (R.amplitude.toVerticalAmplitude.pullback C) ∧
      ¬ ∃ p : Σ _ : ι, E₂, ∃ hp : p ∈ G.criticalPoints, ∃ w : E₂,
        ‖w‖ < (R.criticalNormalForm p hp).radius ∧
        R.amplitude.diffeomorph.symm
          ((B.chart p.1).param
            (p.2 + (R.criticalNormalForm p hp).param w)) =
              (B.chart i).param u := by
  constructor
  · refine ⟨?_, htime⟩
    have hpull := (R.pullback_critical_iff_unperturbed_of_away
      (B := B.toSurfaceChartFamily) i hdom haway).2 hcrit
    have hsymm :
        R.amplitude.diffeomorph.symm ((B.chart i).param u) =
          (B.chart i).param u :=
      (R.eventuallyEq_amplitude_symm_identity_of_away haway).self_of_nhds
    change R.amplitude.diffeomorph.symm ((B.chart i).param u) ∈
      timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G at hpull
    rwa [hsymm] at hpull
  · exact R.not_covered_by_criticalNormalForms_of_away haway


-- @@ L456-456 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L458-458 verbatim
end Submission
