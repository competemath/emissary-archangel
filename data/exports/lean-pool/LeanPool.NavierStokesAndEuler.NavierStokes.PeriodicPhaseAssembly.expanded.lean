/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalParticularWave
import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds


-- @@ L12-19 verbatim
/-!
# A periodic phase with the actual native clock germs

An explicit compact smooth cutoff has a plateau around the entire native
core. Its clock-weighted copies are summed on the common cover. The phase
is therefore periodic on the full auxiliary lift and retains the original
clock, with every derivative, on each padded wave core.
-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace NavierStokes.PeriodicPhaseAssembly


-- @@ L28-28 verbatim
open Set Function Filter MeasureTheory

-- @@ L29-29 verbatim
open scoped ContDiff Topology BigOperators

-- @@ L30-30 verbatim
open CommonCoverSolve TorusInverse TorusAverages


-- @@ L32-36 verbatim
/-- A concrete smooth interval cutoff. Its plateau includes an extra
padding interval on each side of `[a,b]`. -/
noncomputable def intervalCutoff (a b d x : ℝ) : ℝ :=
  Real.smoothTransition ((x - (a - 2 * d)) / d) *
    Real.smoothTransition (((b + 2 * d) - x) / d)


-- @@ L38-40 verbatim
theorem intervalCutoff_contDiff (a b d : ℝ) : ContDiff ℝ ∞ (intervalCutoff a b d) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const d)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const d))


-- @@ L42-47 verbatim
theorem intervalCutoff_one {a b d x : ℝ} (hd : 0 < d)
    (ha : a - d ≤ x) (hb : x ≤ b + d) : intervalCutoff a b d x = 1 := by
  have h1 : 1 ≤ (x - (a - 2 * d)) / d := (le_div_iff₀ hd).2 (by linarith)
  have h2 : 1 ≤ ((b + 2 * d) - x) / d := (le_div_iff₀ hd).2 (by linarith)
  simp only [intervalCutoff, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2, mul_one]


-- @@ L49-61 verbatim
theorem intervalCutoff_support {a b d : ℝ} (hd : 0 < d) :
    support (intervalCutoff a b d) ⊆ Icc (a - 2 * d) (b + 2 * d) := by
  intro x hx
  have hne := mul_ne_zero_iff.mp hx
  constructor
  · by_contra hn
    have harg : (x - (a - 2 * d)) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    exact hne.1 (Real.smoothTransition.zero_of_nonpos harg)
  · by_contra hn
    have harg : ((b + 2 * d) - x) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    exact hne.2 (Real.smoothTransition.zero_of_nonpos harg)


-- @@ L63-72 verbatim
/-- Input geometry for the compact clock cutoff. The full sampled native
path and all wave cutoff supports are placed inside `core`. -/
structure ClockWindow where
  /-- Lower of `ClockWindow`, of type `Plane`. -/
  lower : Plane
  /-- Upper of `ClockWindow`, of type `Plane`. -/
  upper : Plane
  /-- Padding of `ClockWindow`, of type `ℝ`. -/
  padding : ℝ
  padding_pos : 0 < padding


-- @@ L74-74 verbatim
namespace ClockWindow


-- @@ L76-76 verbatim
variable (w : ClockWindow)


-- @@ L78-80 verbatim
/-- Core, given by `Icc w.lower.1 w.upper.1 ×ˢ Icc w.lower.2 w.upper.2`. -/
noncomputable def core : Set Plane :=
  Icc w.lower.1 w.upper.1 ×ˢ Icc w.lower.2 w.upper.2


-- @@ L82-86 verbatim
/-- Plateau, given by `Ioo (w.lower.1 - w.padding) (w.upper.1 + w.padding) ×ˢ Ioo (w.lower.2 -
w.padding) (w.upper.2 + w.padding)`. -/
noncomputable def plateau : Set Plane :=
  Ioo (w.lower.1 - w.padding) (w.upper.1 + w.padding) ×ˢ
    Ioo (w.lower.2 - w.padding) (w.upper.2 + w.padding)


-- @@ L88-92 verbatim
/-- Outer, given by `Icc (w.lower.1 - 2 * w.padding) (w.upper.1 + 2 * w.padding) ×ˢ Icc
(w.lower.2 - 2 * w.padding) (w.upper.2 + 2 * w.padding)`. -/
noncomputable def outer : Set Plane :=
  Icc (w.lower.1 - 2 * w.padding) (w.upper.1 + 2 * w.padding) ×ˢ
    Icc (w.lower.2 - 2 * w.padding) (w.upper.2 + 2 * w.padding)


-- @@ L94-98 verbatim
/-- Cutoff, given by `intervalCutoff w.lower.1 w.upper.1 w.padding z.1 * intervalCutoff
w.lower.2 w.upper.2 w.padding z.2`. -/
noncomputable def cutoff (z : Plane) : ℝ :=
  intervalCutoff w.lower.1 w.upper.1 w.padding z.1 *
    intervalCutoff w.lower.2 w.upper.2 w.padding z.2


-- @@ L100-100 verbatim
theorem core_compact : IsCompact w.core := isCompact_Icc.prod isCompact_Icc


-- @@ L102-102 verbatim
theorem outer_compact : IsCompact w.outer := isCompact_Icc.prod isCompact_Icc


-- @@ L104-104 verbatim
theorem plateau_open : IsOpen w.plateau := isOpen_Ioo.prod isOpen_Ioo


-- @@ L106-109 verbatim
theorem core_subset_plateau : w.core ⊆ w.plateau := by
  rintro z ⟨⟨hl1, hu1⟩, ⟨hl2, hu2⟩⟩
  have hd := w.padding_pos
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩


-- @@ L111-114 verbatim
theorem plateau_subset_outer : w.plateau ⊆ w.outer := by
  rintro z ⟨⟨hl1, hu1⟩, ⟨hl2, hu2⟩⟩
  have hd := w.padding_pos
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩


-- @@ L116-117 verbatim
theorem core_subset_outer : w.core ⊆ w.outer :=
  w.core_subset_plateau.trans w.plateau_subset_outer


-- @@ L119-121 verbatim
theorem cutoff_contDiff : ContDiff ℝ ∞ w.cutoff :=
  ((intervalCutoff_contDiff _ _ _).comp contDiff_fst).mul
    ((intervalCutoff_contDiff _ _ _).comp contDiff_snd)


-- @@ L123-127 verbatim
theorem cutoff_support : support w.cutoff ⊆ w.outer := by
  intro z hz
  have hne := mul_ne_zero_iff.mp hz
  exact ⟨intervalCutoff_support w.padding_pos hne.1,
    intervalCutoff_support w.padding_pos hne.2⟩


-- @@ L129-130 verbatim
theorem cutoff_compact : HasCompactSupport w.cutoff :=
  HasCompactSupport.of_support_subset_isCompact w.outer_compact w.cutoff_support


-- @@ L132-134 verbatim
theorem cutoff_one {z : Plane} (hz : z ∈ w.plateau) : w.cutoff z = 1 := by
  simp only [cutoff, intervalCutoff_one w.padding_pos hz.1.1.le hz.1.2.le,
    intervalCutoff_one w.padding_pos hz.2.1.le hz.2.2.le, mul_one]


-- @@ L136-138 verbatim
theorem cutoff_germ {z : Plane} (hz : z ∈ w.core) : w.cutoff =ᶠ[𝓝 z] fun _ => 1 :=
  eventually_of_mem (w.plateau_open.mem_nhds (w.core_subset_plateau hz))
    (fun _ hx => w.cutoff_one hx)


-- @@ L140-142 verbatim
theorem cutoff_germ_on_support {E : Type} [Zero E] {κ : Plane → E}
    (hκ : tsupport κ ⊆ w.core) {z : Plane} (hz : z ∈ tsupport κ) :
    w.cutoff =ᶠ[𝓝 z] fun _ => 1 := w.cutoff_germ (hκ hz)


-- @@ L144-144 verbatim
end ClockWindow


-- @@ L146-148 verbatim
/-- The literal lattice sum of a native scalar. -/
noncomputable def periodizeScalar (g : Geometry) (f : Plane → ℝ) (Y : Plane) : ℝ :=
  ∑' k : Frequency, f (g.coordinates k Y)


-- @@ L150-159 verbatim
theorem periodizeScalar_eventually_finite (g : Geometry) {f : Plane → ℝ}
    (hf : HasCompactSupport f) (Y : Plane) :
    ∃ J : Finset Frequency, periodizeScalar g f =ᶠ[𝓝 Y]
      fun Z => ∑ k ∈ J, f (g.coordinates k Z) := by
  classical
  obtain ⟨J, hJ⟩ := g.finite_copy_cutoffs hf (‖Y‖ + 1)
  refine ⟨J, ?_⟩
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
    (show ‖Y‖ < ‖Y‖ + 1 by linarith)] with Z hZ
  exact tsum_eq_sum (fun k hk => hJ Z hZ.le k hk)


-- @@ L161-169 verbatim
theorem periodizeScalar_contDiff (g : Geometry) {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (periodizeScalar g f) := by
  rw [contDiff_iff_contDiffAt]
  intro Y
  obtain ⟨J, hJ⟩ := periodizeScalar_eventually_finite g hc Y
  have hs : ContDiff ℝ ∞ (fun Z => ∑ k ∈ J, f (g.coordinates k Z)) :=
    ContDiff.sum (fun k _ => hf.comp (g.coordinates_contDiff k))
  exact hs.contDiffAt.congr_of_eventuallyEq hJ


-- @@ L171-177 verbatim
theorem periodizeScalar_periodic (g : Geometry) (f : Plane → ℝ) (Y : Plane) (n : Frequency) :
    periodizeScalar g f (Y + latticePoint n) = periodizeScalar g f Y := by
  change PeriodizedWaveBounds.copySum (fun k Y => f (g.coordinates k Y)) (Y + latticePoint n) = _
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + latticePoint n)
    (Equiv.addRight (coverIndex g.gap n))
  intro k Z
  exact congrArg f (g.coordinates_deck k n Z)


-- @@ L179-182 verbatim
theorem periodizeScalar_refine (g : Geometry) (f : Plane → ℝ) (d : ℕ) (Y : Plane) :
    periodizeScalar (CopySolveCompatibility.refineGeometry g d) f Y =
      periodizeScalar g f (coverPower d Y) :=
  CopySolveCompatibility.native_copy_sum_refine g d f Y


-- @@ L184-193 verbatim
theorem periodizeScalar_transport (g : Geometry) (f : Plane → ℝ) (d : ℕ)
    (shift rate : ℝ) (hrate : rate ≠ 0) (Y : Plane) :
    periodizeScalar (CopySolveCompatibility.transportGeometry g d shift rate hrate)
      (f ∘ CopySolveCompatibility.nativeTimeMap shift rate) Y =
      periodizeScalar g f (coverPower d Y) := by
  unfold periodizeScalar
  apply tsum_congr
  intro k
  simp only [comp_apply, CopySolveCompatibility.transportGeometry,
    CopySolveCompatibility.coordinates_refine, CopySolveCompatibility.coordinates_timeGeometry]


-- @@ L195-197 verbatim
/-- The clock itself is periodicized together with its cutoff. -/
noncomputable def periodicClock (g : Geometry) (χ : Plane → ℝ) : Plane → ℝ :=
  periodizeScalar g (fun z => χ z * z.2)


-- @@ L199-201 verbatim
theorem periodicClock_contDiff (g : Geometry) (w : ClockWindow) :
    ContDiff ℝ ∞ (periodicClock g w.cutoff) :=
  periodizeScalar_contDiff g (w.cutoff_contDiff.mul contDiff_snd) w.cutoff_compact.mul_right


-- @@ L203-205 verbatim
theorem periodicClock_periodic (g : Geometry) (χ : Plane → ℝ) (Y : Plane) (n : Frequency) :
    periodicClock g χ (Y + latticePoint n) = periodicClock g χ Y :=
  periodizeScalar_periodic g _ Y n


-- @@ L207-210 verbatim
theorem periodicClock_refine (g : Geometry) (χ : Plane → ℝ) (d : ℕ) (Y : Plane) :
    periodicClock (CopySolveCompatibility.refineGeometry g d) χ Y =
      periodicClock g χ (coverPower d Y) :=
  periodizeScalar_refine g _ d Y


-- @@ L212-219 verbatim
/-- Clock reparametrization transports the compact native scalar as a whole.
The shift is multiplied by the cutoff as well. -/
theorem periodicClock_transport (g : Geometry) (χ : Plane → ℝ) (d : ℕ)
    (shift rate : ℝ) (hrate : rate ≠ 0) (Y : Plane) :
    periodizeScalar (CopySolveCompatibility.transportGeometry g d shift rate hrate)
      (fun z => χ (CopySolveCompatibility.nativeTimeMap shift rate z) * (shift + rate * z.2)) Y =
      periodicClock g χ (coverPower d Y) :=
  periodizeScalar_transport g (fun z => χ z * z.2) d shift rate hrate Y


-- @@ L221-221 verbatim
section Germs


-- @@ L223-223 verbatim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L225-247 verbatim
omit [NormedSpace ℝ P] in
/-- Exact clock agreement on a neighborhood of every closed native core.
The geometric input is injectivity of the larger padded support cell. -/
theorem periodicClock_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (k : Frequency) {z : P × Plane} (hz : g.coordinates k z.2 ∈ w.core) :
    (fun x : P × Plane => periodicClock g w.cutoff x.2) =ᶠ[𝓝 z]
      fun x => (g.coordinates k x.2).2 := by
  let K := PeriodizedWaveBounds.nativeCells (P := P) (fun _ => g) (fun _ => w.outer)
    (fun _ => w.outer_compact) (fun _ => hinj)
  let f (j : Frequency) (x : P × Plane) : ℝ :=
    w.cutoff (g.coordinates j x.2) * (g.coordinates j x.2).2
  have hs : ∀ j, support (f j) ⊆ K.carrier 0 j := by
    intro j x hx
    exact w.cutoff_support (mul_ne_zero_iff.mp hx).1
  have he := PeriodizedWaveBounds.copySum_germ K 0 f hs (w.core_subset_outer hz)
  have hc : Continuous (fun x : P × Plane => g.coordinates k x.2) :=
    (g.coordinates_contDiff k).continuous.comp continuous_snd
  filter_upwards [he, hc.continuousAt.preimage_mem_nhds
    (w.plateau_open.mem_nhds (w.core_subset_plateau hz))] with x hx hp
  change (∑' j : Frequency, w.cutoff (g.coordinates j x.2) * (g.coordinates j x.2).2) = _ at hx ⊢
  change _ = w.cutoff (g.coordinates k x.2) * (g.coordinates k x.2).2 at hx
  rw [hx, w.cutoff_one hp, one_mul]


-- @@ L249-254 verbatim
theorem periodicClock_jets (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (k : Frequency) {z : P × Plane} (hz : g.coordinates k z.2 ∈ w.core) (m : ℕ) :
    iteratedFDeriv ℝ m (fun x : P × Plane => periodicClock g w.cutoff x.2) z =
      iteratedFDeriv ℝ m (fun x : P × Plane => (g.coordinates k x.2).2) z :=
  PeriodizedWaveBounds.jets_eq_of_germ (periodicClock_germ g w hinj k hz) m


-- @@ L256-256 verbatim
end Germs


-- @@ L258-272 verbatim
/-- The complete earlier-time Volterra path can be kept in the clock plateau.
This uses the full sampled interval, including points where the wave cutoff
itself vanishes. -/
theorem periodicClock_path (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (k : Frequency) (Y : Plane) (t : ℝ)
    (htransverse : (g.coordinates k Y).1 ∈ Icc w.lower.1 w.upper.1)
    (ht : t ∈ Icc w.lower.2 w.upper.2) :
    periodicClock g w.cutoff (g.path k Y t) = t := by
  have hc : g.coordinates k (g.path k Y t) ∈ w.core := by
    rw [g.coordinates_path]
    exact ⟨htransverse, ht⟩
  have he := (periodicClock_germ (P := ℝ) g w hinj k
    (z := (0, g.path k Y t)) hc).self_of_nhds
  simpa only [g.coordinates_path] using he


-- @@ L274-274 verbatim
/-! ## Actual phases and complete carriers -/


-- @@ L276-276 verbatim
section Phases


-- @@ L278-278 verbatim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L280-282 verbatim
/-- Phase, given by `A z.1 - periodicClock g χ z.2 * B z.1`. -/
noncomputable def phase (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (z : P × Plane) : ℝ := A z.1 - periodicClock g χ z.2 * B z.1


-- @@ L284-286 verbatim
/-- Native phase, given by `A z.1 - (g.coordinates k z.2).2 * B z.1`. -/
noncomputable def nativePhase (g : Geometry) (A B : P → ℝ) (k : Frequency)
    (z : P × Plane) : ℝ := A z.1 - (g.coordinates k z.2).2 * B z.1


-- @@ L288-292 verbatim
theorem phase_contDiff (g : Geometry) (w : ClockWindow) {A B : P → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (phase g w.cutoff A B) :=
  (hA.comp contDiff_fst).sub
    (((periodicClock_contDiff g w).comp contDiff_snd).mul (hB.comp contDiff_fst))


-- @@ L294-299 verbatim
theorem phase_contDiffOn (g : Geometry) (w : ClockWindow) {A B : P → ℝ} {U : Set P}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (phase g w.cutoff A B) (U ×ˢ univ) :=
  (hA.comp contDiffOn_fst (fun _ hx => hx.1)).sub
    (((periodicClock_contDiff g w).comp_contDiffOn contDiffOn_snd).mul
      (hB.comp contDiffOn_fst (fun _ hx => hx.1)))


-- @@ L301-305 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem phase_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (p : P) (Y : Plane) (n : Frequency) :
    phase g χ A B (p, Y + latticePoint n) = phase g χ A B (p, Y) := by
  simp only [phase, periodicClock_periodic]


-- @@ L307-314 verbatim
omit [NormedSpace ℝ P] in
theorem phase_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (k : Frequency) {z : P × Plane}
    (hz : g.coordinates k z.2 ∈ w.core) :
    phase g w.cutoff A B =ᶠ[𝓝 z] nativePhase g A B k := by
  filter_upwards [periodicClock_germ g w hinj k hz] with x hx
  simp only [phase, nativePhase, hx]


-- @@ L316-322 verbatim
theorem phase_jets (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (k : Frequency) {z : P × Plane}
    (hz : g.coordinates k z.2 ∈ w.core) (m : ℕ) :
    iteratedFDeriv ℝ m (phase g w.cutoff A B) z =
      iteratedFDeriv ℝ m (nativePhase g A B k) z :=
  PeriodizedWaveBounds.jets_eq_of_germ (phase_germ g w hinj A B k hz) m


-- @@ L324-331 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem phase_path (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (k : Frequency) (p : P) (Y : Plane) (t : ℝ)
    (htransverse : (g.coordinates k Y).1 ∈ Icc w.lower.1 w.upper.1)
    (ht : t ∈ Icc w.lower.2 w.upper.2) :
    phase g w.cutoff A B (p, g.path k Y t) = A p - t * B p := by
  simp only [phase, periodicClock_path g w hinj k Y t htransverse ht]


-- @@ L333-335 verbatim
/-- The angular coordinate is distinct from the auxiliary torus. -/
noncomputable def angularLift (Φ : P × Plane → ℝ) (angular : ℝ)
    (x : (P × ℝ) × Plane) : ℝ := Φ (x.1.1, x.2) + angular * x.1.2


-- @@ L337-340 verbatim
theorem angularLift_contDiff {Φ : P × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (angular : ℝ) :
    ContDiff ℝ ∞ (angularLift Φ angular) :=
  (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)).add
    (contDiff_const.mul contDiff_fst.snd)


-- @@ L342-348 verbatim
theorem angularLift_affine (Φ : P × Plane → ℝ) (angular : ℝ) :
    CopyAngularInvariance.AffinePhase (((0 : P), (1 : ℝ)), (0 : Plane)) angular
      (angularLift Φ angular) := by
  rintro ⟨⟨p, θ⟩, Y⟩ t
  simp only [angularLift, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, add_zero, smul_eq_mul, mul_one]
  ring


-- @@ L350-358 verbatim
omit [NormedSpace ℝ P] in
theorem angularLift_germ {Φ Ψ : P × Plane → ℝ} (angular : ℝ)
    {x : (P × ℝ) × Plane} (hΦ : Φ =ᶠ[𝓝 (x.1.1, x.2)] Ψ) :
    angularLift Φ angular =ᶠ[𝓝 x] angularLift Ψ angular := by
  have ht : Tendsto (fun z : (P × ℝ) × Plane => (z.1.1, z.2))
      (𝓝 x) (𝓝 (x.1.1, x.2)) :=
    (continuous_fst.fst.prodMk continuous_snd).continuousAt
  filter_upwards [ht.eventually hΦ] with y hy
  exact congrArg (fun t => t + angular * y.1.2) hy


-- @@ L360-367 verbatim
omit [NormedSpace ℝ P] in
theorem fullPhase_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (angular : ℝ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : g.coordinates k x.2 ∈ w.core) :
    angularLift (phase g w.cutoff A B) angular =ᶠ[𝓝 x]
      angularLift (nativePhase g A B k) angular :=
  angularLift_germ angular (phase_germ g w hinj A B k hx)


-- @@ L369-375 verbatim
theorem fullPhase_jets (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (angular : ℝ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : g.coordinates k x.2 ∈ w.core) (m : ℕ) :
    iteratedFDeriv ℝ m (angularLift (phase g w.cutoff A B) angular) x =
      iteratedFDeriv ℝ m (angularLift (nativePhase g A B k) angular) x :=
  PeriodizedWaveBounds.jets_eq_of_germ (fullPhase_germ g w hinj A B angular k hx) m


-- @@ L377-382 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem fullPhase_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (angular : ℝ) (p : P) (θ : ℝ) (Y : Plane) (n : Frequency) :
    angularLift (phase g χ A B) angular ((p, θ), Y + latticePoint n) =
      angularLift (phase g χ A B) angular ((p, θ), Y) := by
  simp only [angularLift, phase_periodic]


-- @@ L384-389 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem carrier_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (angular K : ℝ) (p : P) (θ : ℝ) (Y : Plane) (n : Frequency) :
    HarmonicCalculus.carrier K (angularLift (phase g χ A B) angular) ((p, θ), Y + latticePoint n) =
      HarmonicCalculus.carrier K (angularLift (phase g χ A B) angular) ((p, θ), Y) := by
  simp only [HarmonicCalculus.carrier, fullPhase_periodic]


-- @@ L391-398 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem fullMode_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (angular K : ℝ) (a : (P × ℝ) × Plane → ℂ)
    (ha : ∀ p θ Y n, a ((p, θ), Y + latticePoint n) = a ((p, θ), Y))
    (p : P) (θ : ℝ) (Y : Plane) (n : Frequency) :
    HarmonicCalculus.mode K (angularLift (phase g χ A B) angular) a ((p, θ), Y + latticePoint n) =
      HarmonicCalculus.mode K (angularLift (phase g χ A B) angular) a ((p, θ), Y) := by
  simp only [HarmonicCalculus.mode, ha, carrier_periodic]


-- @@ L400-409 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem carrier_angularLift_eq_character (Φ : P × Plane → ℝ) {K : ℝ} (hK : K ≠ 0)
    (m j : ℤ) (x : (P × ℝ) × Plane) :
    HarmonicCalculus.carrier ((j : ℝ) * K) (angularLift Φ ((m : ℝ) / K)) x =
      HarmonicFields.character j (K * Φ (x.1.1, x.2) + (m : ℝ) * x.1.2) := by
  unfold HarmonicCalculus.carrier HarmonicCalculus.phaseFactor angularLift HarmonicFields.character
  congr 1
  push_cast
  have hKc : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK
  field_simp [hKc]


-- @@ L411-424 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The integer angular character is retained by the actual global carrier. -/
theorem carrier_angular_periodic (Φ : P × Plane → ℝ) {K : ℝ} (hK : K ≠ 0)
    (m j : ℤ) (p : P) (Y : Plane) (θ : ℝ) :
    HarmonicCalculus.carrier ((j : ℝ) * K) (angularLift Φ ((m : ℝ) / K))
        ((p, θ + 2 * Real.pi), Y) =
      HarmonicCalculus.carrier ((j : ℝ) * K) (angularLift Φ ((m : ℝ) / K)) ((p, θ), Y) := by
  rw [carrier_angularLift_eq_character Φ hK, carrier_angularLift_eq_character Φ hK]
  have he : K * Φ (p, Y) + (m : ℝ) * (θ + 2 * Real.pi) =
      (K * Φ (p, Y) + (m : ℝ) * θ) + (m : ℝ) * HarmonicFields.period := by
    unfold HarmonicFields.period
    ring
  rw [he, HarmonicFields.character_phase_add, HarmonicFields.character_int_mul,
    HarmonicFields.character_period, mul_one]


-- @@ L426-426 verbatim
end Phases


-- @@ L428-428 verbatim
/-! ## The manuscript phase in physical slow-coordinate order `(R,(T,Z))` -/


-- @@ L430-431 verbatim
/-- Parameter: an abbreviation for `PhysicalParticularWave.Parameter`. -/
abbrev Parameter := PhysicalParticularWave.Parameter


-- @@ L433-434 verbatim
/-- Slow swap, given by `(p.1, (p.2.2, p.2.1))`. -/
noncomputable def slowSwap (p : Parameter) : PhaseCalculus.Slow := (p.1, (p.2.2, p.2.1))


-- @@ L436-438 verbatim
/-- Profile intercept, given by `(pz / ε) * s.2.2 + x0 * s.1`. -/
noncomputable def profileIntercept (ε pz x0 : ℝ) (s : Parameter) : ℝ :=
  (pz / ε) * s.2.2 + x0 * s.1


-- @@ L440-442 verbatim
/-- Profile rate, given by `p * F s + pz * G s`. -/
noncomputable def profileRate (p pz : ℝ) (F G : Parameter → ℝ) (s : Parameter) : ℝ :=
  p * F s + pz * G s


-- @@ L444-447 verbatim
/-- Profile phase, given by `phase g χ (profileIntercept ε pz x0) (profileRate p pz F G)`. -/
noncomputable def profilePhase (g : Geometry) (χ : Plane → ℝ) (ε p pz x0 : ℝ)
    (F G : Parameter → ℝ) : Parameter × Plane → ℝ :=
  phase g χ (profileIntercept ε pz x0) (profileRate p pz F G)


-- @@ L449-456 verbatim
theorem profilePhase_eq_literal (g : Geometry) (χ : Plane → ℝ) (ε p pz x0 : ℝ)
    (F G : Parameter → ℝ) (x : (Parameter × ℝ) × Plane) :
    angularLift (profilePhase g χ ε p pz x0 F G) p x =
      PhaseCalculus.phase ε p pz x0 (fun s => F (s.1, (s.2.2, s.2.1)))
        (fun s => G (s.1, (s.2.2, s.2.1)))
        (slowSwap x.1.1, (x.1.2, periodicClock g χ x.2)) := by
  unfold angularLift profilePhase phase profileIntercept profileRate slowSwap PhaseCalculus.phase
  ring


-- @@ L458-471 verbatim
theorem profilePhase_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (ε p pz x0 : ℝ) (F G : Parameter → ℝ) (k : Frequency)
    {x : (Parameter × ℝ) × Plane} (hx : g.coordinates k x.2 ∈ w.core) :
    angularLift (profilePhase g w.cutoff ε p pz x0 F G) p =ᶠ[𝓝 x]
      (fun y => PhaseCalculus.phase ε p pz x0 (fun s => F (s.1, (s.2.2, s.2.1)))
        (fun s => G (s.1, (s.2.2, s.2.1)))
        (slowSwap y.1.1, (y.1.2, (g.coordinates k y.2).2))) := by
  have he := fullPhase_germ g w hinj (profileIntercept ε pz x0) (profileRate p pz F G) p k hx
  filter_upwards [he] with y hy
  unfold profilePhase
  rw [hy]
  unfold angularLift nativePhase profileIntercept profileRate slowSwap PhaseCalculus.phase
  ring


-- @@ L473-481 verbatim
theorem profilePhase_jets (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (ε p pz x0 : ℝ) (F G : Parameter → ℝ) (k : Frequency)
    {x : (Parameter × ℝ) × Plane} (hx : g.coordinates k x.2 ∈ w.core) (m : ℕ) :
    iteratedFDeriv ℝ m (angularLift (profilePhase g w.cutoff ε p pz x0 F G) p) x =
      iteratedFDeriv ℝ m (fun y => PhaseCalculus.phase ε p pz x0
        (fun s => F (s.1, (s.2.2, s.2.1))) (fun s => G (s.1, (s.2.2, s.2.1)))
        (slowSwap y.1.1, (y.1.2, (g.coordinates k y.2).2))) x :=
  PeriodizedWaveBounds.jets_eq_of_germ (profilePhase_germ g w hinj ε p pz x0 F G k hx) m


-- @@ L483-483 verbatim
/-! ## One reference phase under actual clock and common-cover changes -/


-- @@ L485-499 verbatim
theorem periodicClock_scale_transport (g : Geometry) (χ : Plane → ℝ) (d : ℕ)
    (rate : ℝ) (hrate : rate ≠ 0) (Y : Plane) :
    rate * periodicClock (CopySolveCompatibility.transportGeometry g d 0 rate hrate)
      (χ ∘ CopySolveCompatibility.nativeTimeMap 0 rate) Y =
      periodicClock g χ (coverPower d Y) := by
  calc
    _ = periodizeScalar (CopySolveCompatibility.transportGeometry g d 0 rate hrate)
        (fun z => χ (CopySolveCompatibility.nativeTimeMap 0 rate z) * (0 + rate * z.2)) Y := by
      unfold periodicClock periodizeScalar
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      simp only [comp_apply, zero_add]
      ring
    _ = _ := periodicClock_transport g χ d 0 rate hrate Y


-- @@ L501-501 verbatim
section Transport


-- @@ L503-504 verbatim
variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]


-- @@ L506-509 verbatim
/-- Each target band is a view of one fixed reference phase. -/
noncomputable def transportPhase (Φ : P × Plane → ℝ) (φ : Q → P) (gap : ℕ)
    (K Kr : ℝ) (z : Q × Plane) : ℝ :=
  (Kr / K) * Φ (φ z.1, coverPower gap z.2)


-- @@ L511-516 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem transportPhase_weighted (Φ : P × Plane → ℝ) (φ : Q → P) (gap : ℕ)
    {K : ℝ} (hK : K ≠ 0) (Kr : ℝ) (z : Q × Plane) :
    K * transportPhase Φ φ gap K Kr z = Kr * Φ (φ z.1, coverPower gap z.2) := by
  unfold transportPhase
  field_simp


-- @@ L518-522 verbatim
theorem transportPhase_contDiff {Φ : P × Plane → ℝ} {φ : Q → P}
    (hΦ : ContDiff ℝ ∞ Φ) (hφ : ContDiff ℝ ∞ φ) (gap : ℕ) (K Kr : ℝ) :
    ContDiff ℝ ∞ (transportPhase Φ φ gap K Kr) :=
  contDiff_const.mul (hΦ.comp ((hφ.comp contDiff_fst).prodMk
    ((coverPower gap).contDiff.comp contDiff_snd)))


-- @@ L524-530 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem transportPhase_periodic {Φ : P × Plane → ℝ}
    (hΦ : ∀ p Y k, Φ (p, Y + latticePoint k) = Φ (p, Y))
    (φ : Q → P) (gap : ℕ) (K Kr : ℝ) (p : Q) (Y : Plane) (k : Frequency) :
    transportPhase Φ φ gap K Kr (p, Y + latticePoint k) =
      transportPhase Φ φ gap K Kr (p, Y) := by
  simp only [transportPhase, map_add, coverPower_lattice, hΦ]


-- @@ L532-541 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- Equality of the constructed fields, including off the native support. -/
theorem transportPhase_eq_refined (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (φ : Q → P) (gap : ℕ) (K Kr : ℝ) :
    transportPhase (phase g χ A B) φ gap K Kr =
      phase (CopySolveCompatibility.refineGeometry g gap) χ
        (fun p => (Kr / K) * A (φ p)) (fun p => (Kr / K) * B (φ p)) := by
  funext z
  simp only [transportPhase, phase, periodicClock_refine]
  ring


-- @@ L543-555 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- The actual physical clock rate and its rescaled cutoff give the same
global target phase as the weighted reference pullback. -/
theorem transportPhase_eq_scaled_clock (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (φ : Q → P) (gap : ℕ) (K Kr rate : ℝ) (hrate : rate ≠ 0) :
    transportPhase (phase g χ A B) φ gap K Kr =
      phase (CopySolveCompatibility.transportGeometry g gap 0 rate hrate)
        (χ ∘ CopySolveCompatibility.nativeTimeMap 0 rate)
        (fun p => (Kr / K) * A (φ p)) (fun p => (Kr / K) * rate * B (φ p)) := by
  funext z
  simp only [transportPhase, phase]
  rw [← periodicClock_scale_transport g χ gap rate hrate z.2]
  ring


-- @@ L557-591 verbatim
omit [NormedSpace ℝ P] [NormedSpace ℝ Q] in
/-- The full native phase, with its original anchor, agrees as a germ on
every transformed cell. Only continuity of the parameter change is needed
to transport the germ. -/
theorem transportPhase_native_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (φ : Q → P) (gap : ℕ) (K Kr shift rate : ℝ) (hrate : rate ≠ 0)
    (copy : Frequency) {z : Q × Plane} (hφ : ContinuousAt φ z.1)
    (hz : CopySolveCompatibility.nativeTimeMap shift rate
      ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy z.2) ∈
          w.core) :
    transportPhase (phase g w.cutoff A B) φ gap K Kr =ᶠ[𝓝 z]
      nativePhase (CopySolveCompatibility.transportGeometry g gap shift rate hrate)
        (fun p => (Kr / K) * (A (φ p) - shift * B (φ p)))
        (fun p => (Kr / K) * rate * B (φ p)) copy := by
  have hcoord (Y : Plane) :
      CopySolveCompatibility.nativeTimeMap shift rate
        ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy Y) =
          g.coordinates copy (coverPower gap Y) := by
    simp only [CopySolveCompatibility.transportGeometry,
      CopySolveCompatibility.coordinates_refine, CopySolveCompatibility.coordinates_timeGeometry]
  rw [hcoord] at hz
  have he := phase_germ g w hinj A B copy (z := (φ z.1, coverPower gap z.2)) hz
  have ht : Tendsto (fun y : Q × Plane => (φ y.1, coverPower gap y.2))
      (𝓝 z) (𝓝 (φ z.1, coverPower gap z.2)) :=
    (hφ.comp continuousAt_fst).prodMk
      ((coverPower gap).continuous.continuousAt.comp continuousAt_snd)
  filter_upwards [ht.eventually he] with y hy
  change (Kr / K) * phase g w.cutoff A B (φ y.1, coverPower gap y.2) = _
  rw [hy]
  have hc := congrArg Prod.snd (hcoord y.2)
  simp only [CopySolveCompatibility.nativeTimeMap] at hc
  simp only [nativePhase]
  rw [← hc]
  ring


-- @@ L593-608 verbatim
omit [NormedSpace ℝ P] in
theorem transportPhase_native_jets (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (φ : Q → P) (gap : ℕ) (K Kr shift rate : ℝ) (hrate : rate ≠ 0)
    (copy : Frequency) {z : Q × Plane} (hφ : ContinuousAt φ z.1)
    (hz : CopySolveCompatibility.nativeTimeMap shift rate
      ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy z.2) ∈
          w.core)
    (m : ℕ) :
    iteratedFDeriv ℝ m (transportPhase (phase g w.cutoff A B) φ gap K Kr) z =
      iteratedFDeriv ℝ m
        (nativePhase (CopySolveCompatibility.transportGeometry g gap shift rate hrate)
          (fun p => (Kr / K) * (A (φ p) - shift * B (φ p)))
          (fun p => (Kr / K) * rate * B (φ p)) copy) z :=
  PeriodizedWaveBounds.jets_eq_of_germ
    (transportPhase_native_germ g w hinj A B φ gap K Kr shift rate hrate copy hφ hz) m


-- @@ L610-616 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem transportPhase_angular_weighted (Φ : P × Plane → ℝ) (φ : Q → P) (gap : ℕ)
    {K Kr : ℝ} (hK : K ≠ 0) (hKr : Kr ≠ 0) (m : ℤ) (x : (Q × ℝ) × Plane) :
    K * angularLift (transportPhase Φ φ gap K Kr) ((m : ℝ) / K) x =
      Kr * angularLift Φ ((m : ℝ) / Kr) ((φ x.1.1, x.1.2), coverPower gap x.2) := by
  unfold angularLift transportPhase
  field_simp


-- @@ L618-618 verbatim
end Transport


-- @@ L620-625 verbatim
theorem parameterChange_self {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    PhysicalParticularWave.parameterChange h Q Q = id := by
  have hr (a : ℝ) : PhysicalParticularWave.ratioPower Q Q a = 1 :=
    div_self (Real.rpow_pos_of_pos hQ a).ne'
  funext p
  simp only [PhysicalParticularWave.parameterChange, hr, one_mul, id_eq]


-- @@ L627-638 verbatim
/-- A literal harmonic block with one reference phase and one angular
integer. Its amplitudes and pressure coefficients are supplied by the
existing block; its phase is the constructed common-cover view. -/
noncomputable def physicalBlock (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ) :
    CorrectionState.HarmonicBlock (Parameter × Plane) :=
  { b with
    phase := fun n => transportPhase (phase g w.cutoff A B)
      (PhysicalParticularWave.parameterChange h (Q n) (Q reference))
      (gap n) (b.frequency n) (b.frequency reference)
    angularFrequency := fun _ => angular }


-- @@ L640-647 verbatim
theorem physicalBlock_reference (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (hQ : 0 < Q reference) (hgap : gap reference = 0) (hK : b.frequency reference ≠ 0) :
    (physicalBlock b h Q gap reference angular g w A B).phase reference = phase g w.cutoff A B := by
  funext z
  simp only [physicalBlock, transportPhase, hgap, parameterChange_self hQ h, id_eq,
    coverPower, ContinuousLinearEquiv.refl_apply, div_self hK, one_mul]


-- @@ L649-661 verbatim
theorem physicalBlock_weighted (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (hQ : 0 < Q reference) (hgap : gap reference = 0)
    (hK : ∀ n, b.frequency n ≠ 0) (n : ℕ) (p : Parameter) (Y : Plane) :
    (physicalBlock b h Q gap reference angular g w A B).frequency n *
        (physicalBlock b h Q gap reference angular g w A B).phase n (p, Y) =
      (physicalBlock b h Q gap reference angular g w A B).frequency reference *
        (physicalBlock b h Q gap reference angular g w A B).phase reference
          (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p, coverPower (gap n) Y) :=
              by
  rw [physicalBlock_reference b h Q gap reference angular g w A B hQ hgap (hK reference)]
  exact transportPhase_weighted _ _ _ (hK n) _ _


-- @@ L663-669 verbatim
theorem physicalBlock_periodic (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (n : ℕ) (p : Parameter) (Y : Plane) (k : Frequency) :
    (physicalBlock b h Q gap reference angular g w A B).phase n (p, Y + latticePoint k) =
      (physicalBlock b h Q gap reference angular g w A B).phase n (p, Y) :=
  transportPhase_periodic (phase_periodic g w.cutoff A B) _ _ _ _ _ _ _


-- @@ L671-677 verbatim
theorem physicalBlock_contDiff (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) {A B : Parameter → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (n : ℕ) :
    ContDiff ℝ ∞ ((physicalBlock b h Q gap reference angular g w A B).phase n) :=
  transportPhase_contDiff (phase_contDiff g w hA hB)
    (PhysicalParticularWave.parameterChange_smooth h (Q n) (Q reference)) _ _ _


-- @@ L679-695 verbatim
/-- The exact PPW clock, with its cutoff transformed by the same rate. -/
theorem physicalBlock_eq_scaled_clock (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ) (n : ℕ)
    (hQn : 0 < Q n) (hQr : 0 < Q reference) :
    (physicalBlock b h Q gap reference angular g w A B).phase n =
      phase (CopySolveCompatibility.transportGeometry g (gap n) 0
        (PhysicalParticularWave.clockWeight h (Q n) (Q reference))
        (PhysicalParticularWave.ratioPower_pos hQn hQr _).ne')
        (w.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0
          (PhysicalParticularWave.clockWeight h (Q n) (Q reference)))
        (fun p => (b.frequency reference / b.frequency n) *
          A (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p))
        (fun p => (b.frequency reference / b.frequency n) *
          PhysicalParticularWave.clockWeight h (Q n) (Q reference) *
          B (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p)) :=
  transportPhase_eq_scaled_clock g w.cutoff A B _ _ _ _ _ _


-- @@ L697-702 verbatim
/-- Assign the constructed phase family to the literal assembly record. -/
noncomputable def periodicAssembly (D : ParticularWaveAssembly.AssemblyData Parameter)
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (angular : ℤ) (w : ClockWindow)
    (A B : Parameter → ℝ) : ParticularWaveAssembly.AssemblyData Parameter :=
  { D with carrierBlock := physicalBlock D.carrierBlock h Q gap D.reference.band angular
               D.reference.geometry w A B }


-- @@ L704-718 verbatim
theorem bandPhase_eq_actualCarrier (D : ParticularWaveAssembly.AssemblyData Parameter)
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (angular : ℤ) (w : ClockWindow)
    (A B : Parameter → ℝ) (hQ : 0 < Q D.reference.band)
    (hgap : gap D.reference.band = 0) (hK : ∀ n, D.carrierBlock.frequency n ≠ 0)
    (n : ℕ) (j : ℤ) (hj : j ≠ 0) :
    PhysicalParticularWave.bandPhase (periodicAssembly D h Q gap angular w A B)
        h (Q n) (Q D.reference.band) (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j =
      fun x => (ParticularWaveAssembly.actualCarrier D.background
        (periodicAssembly D h Q gap angular w A B).carrierBlock j).phase n
          (PhysicalParticularWave.waveEquiv x) := by
  apply PhysicalParticularWave.bandPhase_eq_actualCarrier
    (periodicAssembly D h Q gap angular w A B) h (Q n) (Q D.reference.band) (gap n) n j hj hK
  · exact physicalBlock_weighted D.carrierBlock h Q gap D.reference.band angular
      D.reference.geometry w A B hQ hgap hK n
  · rfl


-- @@ L720-720 verbatim
/-! ## Native support geometry and direct carrier adapters -/


-- @@ L722-732 verbatim
theorem transportGeometry_affine (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) (z : Plane) :
    (CopySolveCompatibility.transportGeometry g gap shift rate hrate).center +
        (CopySolveCompatibility.transportGeometry g gap shift rate hrate).basis z =
      g.center + g.basis (CopySolveCompatibility.nativeTimeMap shift rate z) := by
  simp only [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.refineGeometry,
    CopySolveCompatibility.timeGeometry, CommonCoverClass.scaledBasis_apply,
    CopySolveCompatibility.nativeTimeMap]
  rw [show (z.1, shift + rate * z.2) = (0, shift) + (z.1, rate * z.2) by ext <;> simp]
  rw [map_add]
  abel


-- @@ L734-744 verbatim
theorem transportGeometry_injective (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) {K : Set Plane}
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' K)) :
    InjOn quotientPoint
      ((fun z => (CopySolveCompatibility.transportGeometry g gap shift rate hrate).center +
        (CopySolveCompatibility.transportGeometry g gap shift rate hrate).basis z) ''
        (CopySolveCompatibility.nativeTimeMap shift rate ⁻¹' K)) := by
  apply hinj.mono
  rintro z ⟨x, hx, rfl⟩
  exact ⟨CopySolveCompatibility.nativeTimeMap shift rate x, hx,
    (transportGeometry_affine g gap shift rate hrate x).symm⟩


-- @@ L746-746 verbatim
section AdditionalTransport


-- @@ L748-749 verbatim
variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]


-- @@ L751-758 verbatim
theorem transportPhase_contDiffOn {Φ : P × Plane → ℝ} {φ : Q → P} {U : Set P} {V : Set Q}
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ univ)) (hφ : ContDiffOn ℝ ∞ φ V)
    (hmap : MapsTo φ V U) (gap : ℕ) (K Kr : ℝ) :
    ContDiffOn ℝ ∞ (transportPhase Φ φ gap K Kr) (V ×ˢ univ) :=
  contDiffOn_const.mul (hΦ.comp
    ((hφ.comp contDiffOn_fst (fun _ hx => hx.1)).prodMk
      ((coverPower gap).contDiff.comp_contDiffOn contDiffOn_snd))
    (fun _ hx => ⟨hmap hx.1, mem_univ _⟩))


-- @@ L760-785 verbatim
omit [NormedSpace ℝ P] [NormedSpace ℝ Q] in
/-- Exact values on the entire transformed sampling interval, with the
original reference anchor `shift + rate*t`. -/
theorem transportPhase_path (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (φ : Q → P) (gap : ℕ) (K Kr shift rate : ℝ) (hrate : rate ≠ 0)
    (copy : Frequency) (p : Q) (hφ : ContinuousAt φ p) (Y : Plane) (t : ℝ)
    (htransverse :
      ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy Y).1 ∈
        Icc w.lower.1 w.upper.1)
    (ht : shift + rate * t ∈ Icc w.lower.2 w.upper.2) :
    transportPhase (phase g w.cutoff A B) φ gap K Kr
        (p, (CopySolveCompatibility.transportGeometry g gap shift rate hrate).path copy Y t) =
      (Kr / K) * (A (φ p) - (shift + rate * t) * B (φ p)) := by
  let G := CopySolveCompatibility.transportGeometry g gap shift rate hrate
  have hz : CopySolveCompatibility.nativeTimeMap shift rate
      (G.coordinates copy (G.path copy Y t)) ∈ w.core := by
    rw [G.coordinates_path]
    exact ⟨htransverse, ht⟩
  have he := (transportPhase_native_germ g w hinj A B φ gap K Kr shift rate hrate copy
    (z := (p, G.path copy Y t)) hφ hz).self_of_nhds
  rw [he]
  change (Kr / K) * (A (φ p) - shift * B (φ p)) -
    (G.coordinates copy (G.path copy Y t)).2 * ((Kr / K) * rate * B (φ p)) = _
  rw [G.coordinates_path]
  ring


-- @@ L787-787 verbatim
end AdditionalTransport


-- @@ L789-789 verbatim
section CarrierAdapters


-- @@ L791-791 verbatim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L793-807 verbatim
/-- Periodicity of all joint derivative tensors follows from the proved
function identity under the constant lattice translation. -/
theorem latticePeriodic_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : P × Plane → E} (hf : ∀ p Y k, f (p, Y + latticePoint k) = f (p, Y))
    (m : ℕ) (p : P) (Y : Plane) (k : Frequency) :
    iteratedFDeriv ℝ m f (p, Y + latticePoint k) = iteratedFDeriv ℝ m f (p, Y) := by
  have hshift (z : P × Plane) : z + ((0 : P), latticePoint k) = (z.1, z.2 + latticePoint k) := by
    ext <;> simp
  have he : (fun z : P × Plane => f (z + ((0 : P), latticePoint k))) = f := by
    funext z
    rw [hshift]
    exact hf z.1 z.2 k
  have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) m ((0 : P), latticePoint k) (p, Y)
  rw [he, hshift] at ht
  exact ht.symm


-- @@ L809-813 verbatim
omit [NormedSpace ℝ P] in
theorem carrier_germ {Φ Ψ : P → ℝ} {x : P} (hΦ : Φ =ᶠ[𝓝 x] Ψ) (K : ℝ) :
    HarmonicCalculus.carrier K Φ =ᶠ[𝓝 x] HarmonicCalculus.carrier K Ψ := by
  filter_upwards [hΦ] with y hy
  simp only [HarmonicCalculus.carrier, hy]


-- @@ L815-820 verbatim
omit [NormedSpace ℝ P] in
theorem fullMode_germ {Φ Ψ : P → ℝ} {x : P} (hΦ : Φ =ᶠ[𝓝 x] Ψ)
    (K : ℝ) (a : P → ℂ) :
    HarmonicCalculus.mode K Φ a =ᶠ[𝓝 x] HarmonicCalculus.mode K Ψ a := by
  filter_upwards [carrier_germ hΦ K] with y hy
  exact congrArg (fun z => a y * z) hy


-- @@ L822-826 verbatim
theorem carrier_jets_of_phase_germ {Φ Ψ : P → ℝ} {x : P} (hΦ : Φ =ᶠ[𝓝 x] Ψ)
    (K : ℝ) (m : ℕ) :
    iteratedFDeriv ℝ m (HarmonicCalculus.carrier K Φ) x =
      iteratedFDeriv ℝ m (HarmonicCalculus.carrier K Ψ) x :=
  PeriodizedWaveBounds.jets_eq_of_germ (carrier_germ hΦ K) m


-- @@ L828-832 verbatim
theorem fullMode_jets_of_phase_germ {Φ Ψ : P → ℝ} {x : P} (hΦ : Φ =ᶠ[𝓝 x] Ψ)
    (K : ℝ) (a : P → ℂ) (m : ℕ) :
    iteratedFDeriv ℝ m (HarmonicCalculus.mode K Φ a) x =
      iteratedFDeriv ℝ m (HarmonicCalculus.mode K Ψ a) x :=
  PeriodizedWaveBounds.jets_eq_of_germ (fullMode_germ hΦ K a) m


-- @@ L834-841 verbatim
omit [NormedSpace ℝ P] in
theorem actualCarrier_phase_germ (base : LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane)) (j : ℤ) (n : ℕ)
    {Φ : P × Plane → ℝ} {x : (P × ℝ) × Plane}
    (hΦ : b.phase n =ᶠ[𝓝 (x.1.1, x.2)] Φ) :
    (ParticularWaveAssembly.actualCarrier base b j).phase n =ᶠ[𝓝 x]
      angularLift Φ ((b.angularFrequency n : ℝ) / b.frequency n) :=
  angularLift_germ _ hΦ


-- @@ L843-857 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem actualCarrier_periodic (base : LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane)) (j : ℤ) (n : ℕ)
    (hΦ : ∀ p Y k, b.phase n (p, Y + latticePoint k) = b.phase n (p, Y))
    (p : P) (θ : ℝ) (Y : Plane) (k : Frequency) :
    (ParticularWaveAssembly.actualCarrier base b j).phase n ((p, θ), Y + latticePoint k) =
      (ParticularWaveAssembly.actualCarrier base b j).phase n ((p, θ), Y) ∧
    HarmonicCalculus.carrier ((ParticularWaveAssembly.actualCarrier base b j).frequency n)
        ((ParticularWaveAssembly.actualCarrier base b j).phase n) ((p, θ), Y + latticePoint k) =
      HarmonicCalculus.carrier ((ParticularWaveAssembly.actualCarrier base b j).frequency n)
        ((ParticularWaveAssembly.actualCarrier base b j).phase n) ((p, θ), Y) := by
  have he : (ParticularWaveAssembly.actualCarrier base b j).phase n ((p, θ), Y + latticePoint k) =
      (ParticularWaveAssembly.actualCarrier base b j).phase n ((p, θ), Y) := by
    simp only [ParticularWaveAssembly.actualCarrier, hΦ]
  exact ⟨he, by simp only [HarmonicCalculus.carrier, he]⟩


-- @@ L859-867 verbatim
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem actualCarrier_angular_periodic (base : LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane)) (j : ℤ) (n : ℕ)
    (hK : b.frequency n ≠ 0) (p : P) (θ : ℝ) (Y : Plane) :
    HarmonicCalculus.carrier ((ParticularWaveAssembly.actualCarrier base b j).frequency n)
        ((ParticularWaveAssembly.actualCarrier base b j).phase n) ((p, θ + 2 * Real.pi), Y) =
      HarmonicCalculus.carrier ((ParticularWaveAssembly.actualCarrier base b j).frequency n)
        ((ParticularWaveAssembly.actualCarrier base b j).phase n) ((p, θ), Y) :=
  carrier_angular_periodic (b.phase n) hK (b.angularFrequency n) j p Y θ


-- @@ L869-869 verbatim
end CarrierAdapters


-- @@ L871-887 verbatim
theorem physicalBlock_native_germ (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (n : ℕ) (shift rate : ℝ) (hrate : rate ≠ 0) (copy : Frequency) {z : Parameter × Plane}
    (hz : CopySolveCompatibility.nativeTimeMap shift rate
      ((CopySolveCompatibility.transportGeometry g (gap n) shift rate hrate).coordinates copy z.2)
          ∈ w.core) :
    (physicalBlock b h Q gap reference angular g w A B).phase n =ᶠ[𝓝 z]
      nativePhase (CopySolveCompatibility.transportGeometry g (gap n) shift rate hrate)
        (fun p => (b.frequency reference / b.frequency n) *
          (A (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p) -
            shift * B (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p)))
        (fun p => (b.frequency reference / b.frequency n) * rate *
          B (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p)) copy :=
  transportPhase_native_germ g w hinj A B _ _ _ _ shift rate hrate copy
    (PhysicalParticularWave.parameterChange_smooth h (Q n) (Q reference)).continuous.continuousAt hz


-- @@ L889-915 verbatim
/-- Exact naturality of the complete carrier, including its unchanged
integer angular character, on the free lift. -/
theorem physicalBlock_carrier_natural (base : LinearWaveBounds.WaveCoefficients ((Parameter × ℝ) ×
    Plane))
    (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (hQ : 0 < Q reference) (hgap : gap reference = 0) (hK : ∀ n, b.frequency n ≠ 0)
    (j : ℤ) (n : ℕ) (p : Parameter) (θ : ℝ) (Y : Plane) :
    HarmonicCalculus.carrier ((j : ℝ) * b.frequency n)
      ((ParticularWaveAssembly.actualCarrier base
        (physicalBlock b h Q gap reference angular g w A B) j).phase n) ((p, θ), Y) =
    HarmonicCalculus.carrier ((j : ℝ) * b.frequency reference)
      ((ParticularWaveAssembly.actualCarrier base
        (physicalBlock b h Q gap reference angular g w A B) j).phase reference)
        ((PhysicalParticularWave.parameterChange h (Q n) (Q reference) p, θ), coverPower (gap n) Y)
            := by
  let Bp := physicalBlock b h Q gap reference angular g w A B
  change HarmonicCalculus.carrier ((j : ℝ) * b.frequency n)
      (angularLift (Bp.phase n) ((angular : ℝ) / b.frequency n)) ((p, θ), Y) =
    HarmonicCalculus.carrier ((j : ℝ) * b.frequency reference)
      (angularLift (Bp.phase reference) ((angular : ℝ) / b.frequency reference))
      ((PhysicalParticularWave.parameterChange h (Q n) (Q reference) p, θ), coverPower (gap n) Y)
  rw [carrier_angularLift_eq_character _ (hK n), carrier_angularLift_eq_character _ (hK reference)]
  congr 1
  exact congrArg (fun x => x + (angular : ℝ) * θ)
    (physicalBlock_weighted b h Q gap reference angular g w A B hQ hgap hK n p Y)


-- @@ L917-917 verbatim
end NavierStokes.PeriodicPhaseAssembly
