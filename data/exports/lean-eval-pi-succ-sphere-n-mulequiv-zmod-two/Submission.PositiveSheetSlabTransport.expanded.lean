import Mathlib
import Submission.Delta
import Submission.SignedMorseSheetRegularity


-- @@ L5-20 verbatim
/-!
# Time transport on only the positive sheet of a signed cobordism

A slab containing a negative-labelled Morse critical point is not a regular
slab, although its positive sheet can still be regular.  This file constructs
the corresponding flow rather than postulating a transport relation.

The closed positive core uses the weak inequality `0 ≤ C v`; nonvanishing of
the signed label on the zero fiber makes this equivalent to strict positivity.
If the spatial derivative is surjective on that core, compactness and a smooth
Urysohn cutoff produce a globally smooth, bounded and Lipschitz vector field.
It agrees with `timeField` on a neighbourhood of the core and lies in the
kernel of the defining map everywhere.  We package its global ODE data as a
`SlabTamedField` over the empty interval `[1,0]`, then prove unit time speed by
the same open-and-closed exit argument used for an ordinary regular slab.
-/


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
open Set Function Metric Module Submodule InnerProductSpace

-- @@ L27-27 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L32-32 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L34-34 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L36-36 verbatim
/-! ## A localized global field -/


-- @@ L38-51 verbatim
/-- A globally tame field which agrees with `timeField` near the positive
core.  The underlying `SlabTamedField` is indexed by the empty slab `[1,0]` so
that its global ODE implementation can be reused without asserting regularity
of the negative sheet. -/
structure PositiveSheetSlabTamedField
    (C : SignedFramedLevelCobordism S₀ S₁) (a b : ℝ) where
  base : SlabTamedField C.cobordism.toLevelCobordismData 1 0
  delta : ℝ
  delta_pos : 0 < delta
  eq_time : ∀ x ∈ Metric.cthickening delta (C.positiveSlabCore a b),
    base.w x = timeField C.cobordism.G x
  subset_slabRegular :
    Metric.cthickening delta (C.positiveSlabCore a b) ⊆
      slabRegularSet C.cobordism.G


-- @@ L53-53 verbatim
namespace PositiveSheetSlabTamedField


-- @@ L55-55 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁} {a b : ℝ}


-- @@ L57-64 verbatim
/-- The auxiliary interval used by the underlying global-flow package is
empty. -/
theorem slabFiber_one_zero
    (D : LevelCobordismData n) : slabFiber D 1 0 = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, ht⟩
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (ht.1.trans ht.2)


-- @@ L66-201 verbatim
/-- Actual construction of the positive-sheet field by a smooth Urysohn
cutoff. -/
theorem nonempty (C : SignedFramedLevelCobordism S₀ S₁) {a b : ℝ}
    (hKsub : C.positiveSlabCore a b ⊆ slabRegularSet C.cobordism.G) :
    Nonempty (PositiveSheetSlabTamedField C a b) := by
  let D := C.cobordism.toLevelCobordismData
  let K := C.positiveSlabCore a b
  have hKcompact : IsCompact K := C.isCompact_positiveSlabCore a b
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    hKcompact.exists_cthickening_subset_open
      (isOpen_slabRegularSet C.cobordism.smooth) hKsub
  set δ := δ₂ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have h2δ : 2 * δ = δ₂ := by rw [hδdef]; ring
  have hsub : Metric.cthickening (2 * δ) K ⊆
      slabRegularSet C.cobordism.G := by
    rw [h2δ]
    exact hδ₂sub
  have hs : IsClosed (Metric.thickening (2 * δ) K)ᶜ :=
    Metric.isOpen_thickening.isClosed_compl
  have ht : IsClosed (Metric.cthickening δ K) :=
    Metric.isClosed_cthickening
  have hd : Disjoint (Metric.thickening (2 * δ) K)ᶜ
      (Metric.cthickening δ K) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.cthickening_subset_thickening'
      (by positivity) (by linarith) K hx')
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (I := modelWithCornersSelf ℝ E₂) (n := (⊤ : ℕ∞)) hs ht hd
  have hχ : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  let w : E₂ → E₂ := fun x => f x • timeField C.cobordism.G x
  have hsmooth : ContDiff ℝ ∞ w := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ slabRegularSet C.cobordism.G
    · exact hχ.contDiffAt.smul
        (contDiffAt_timeField C.cobordism.smooth hx)
    · have hxC : x ∈ (Metric.cthickening (2 * δ) K)ᶜ :=
        fun hmem => hx (hsub hmem)
      have hU : IsOpen (Metric.cthickening (2 * δ) K)ᶜ :=
        Metric.isClosed_cthickening.isOpen_compl
      have hzero : ∀ y ∈ (Metric.cthickening (2 * δ) K)ᶜ, w y = 0 := by
        intro y hy
        have hy' : y ∈ (Metric.thickening (2 * δ) K)ᶜ :=
          fun hmem => hy (Metric.thickening_subset_cthickening _ _ hmem)
        have hfy : f y = 0 := hf0 hy'
        simp [w, hfy]
      have hev : w =ᶠ[𝓝 x] (fun _ => (0 : E₂)) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hxC) hzero
      exact (contDiffAt_const (c := (0 : E₂))).congr_of_eventuallyEq hev
  have hsupp : HasCompactSupport w := by
    have h1 : support w ⊆ Metric.thickening (2 * δ) K := by
      intro x hx
      by_contra hmem
      have hfx : f x = 0 := hf0 hmem
      apply hx
      simp [w, hfx]
    have h2 : tsupport w ⊆ Metric.cthickening (2 * δ) K :=
      closure_minimal (h1.trans (Metric.thickening_subset_cthickening _ _))
        Metric.isClosed_cthickening
    exact IsCompact.of_isClosed_subset hKcompact.cthickening
      isClosed_closure h2
  have hcont : ContinuousOn (timeField C.cobordism.G)
      (Metric.cthickening (2 * δ) K) := fun x hx =>
    (contDiffAt_timeField C.cobordism.smooth
      (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hKcompact.cthickening.exists_bound_of_continuousOn hcont
  have hnorm : ∀ x, ‖w x‖ ≤ Real.toNNReal M := by
    intro x
    by_cases hx : x ∈ Metric.cthickening (2 * δ) K
    · have h1 : ‖f x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hf01 x).1], (hf01 x).2⟩
      calc
        ‖w x‖ = ‖f x‖ * ‖timeField C.cobordism.G x‖ := by
          change ‖f x • timeField C.cobordism.G x‖ = _
          rw [norm_smul]
        _ ≤ 1 * M := by
          apply mul_le_mul h1 (hM x hx) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
        _ ≤ Real.toNNReal M := Real.le_coe_toNNReal M
    · have hx' : x ∈ (Metric.thickening (2 * δ) K)ᶜ :=
        fun hmem => hx (Metric.thickening_subset_cthickening _ _ hmem)
      have hfx : f x = 0 := hf0 hx'
      change ‖f x • timeField C.cobordism.G x‖ ≤ _
      rw [hfx, zero_smul, norm_zero]
      exact (Real.toNNReal M).coe_nonneg
  have heq : ∀ x ∈ Metric.cthickening δ K,
      w x = timeField C.cobordism.G x := by
    intro x hx
    have hfx : f x = 1 := hf1 hx
    simp [w, hfx]
  have hsmallsub : Metric.cthickening δ K ⊆
      slabRegularSet C.cobordism.G := by
    intro x hx
    apply hsub
    exact Metric.cthickening_mono (by linarith) K hx
  have hker : ∀ x, fderiv ℝ C.cobordism.G x (w x) = 0 := by
    intro x
    by_cases hx : x ∈ Metric.cthickening (2 * δ) K
    · have hxr := hsub hx
      change fderiv ℝ C.cobordism.G x
        (f x • timeField C.cobordism.G x) = 0
      rw [map_smul, fderiv_timeField hxr.1, smul_zero]
    · have hx' : x ∈ (Metric.thickening (2 * δ) K)ᶜ :=
        fun hmem => hx (Metric.thickening_subset_cthickening _ _ hmem)
      have hfx : f x = 0 := hf0 hx'
      change fderiv ℝ C.cobordism.G x
        (f x • timeField C.cobordism.G x) = 0
      rw [hfx, zero_smul, map_zero]
  have hlip : ∃ L : NNReal, LipschitzWith L w :=
    hsmooth.lipschitzWith_of_hasCompactSupport hsupp (by simp)
  let W₀ : SlabTamedField D 1 0 :=
    { w := w
      delta := δ
      delta_pos := hδpos
      smooth := hsmooth
      bound := Real.toNNReal M
      norm_le := hnorm
      eq_time := by
        intro x hx
        exfalso
        rw [slabFiber_one_zero D, Metric.cthickening_empty] at hx
        exact hx
      subset_slabRegular := by
        intro x hx
        exfalso
        rw [slabFiber_one_zero D, Metric.cthickening_empty] at hx
        exact hx
      fderiv_zero := hker
      lipschitz := hlip }
  exact ⟨⟨W₀, δ, hδpos, heq, hsmallsub⟩⟩


-- @@ L203-214 verbatim
/-- At a negative Morse event, the regularity theorem for the positive core
feeds the localized Urysohn construction with no extra geometric assumption. -/
theorem nonempty_of_negative_event
    (C : SignedFramedLevelCobordism S₀ S₁)
    (P : MorsePosition C.cobordism) {t : ℝ} (ht : t ∈ P.eventTimes)
    (hnegative : P.eventCenter t ht ∈
      (C.labelMorsePosition P).negativeCenters) :
    Nonempty (PositiveSheetSlabTamedField C
      (P.eventBracket t ht).before (P.eventBracket t ht).after) :=
  nonempty C
    (P.positiveSlabCore_subset_slabRegularSet_of_negative_event
      ht hnegative)


-- @@ L216-216 verbatim
variable (W : PositiveSheetSlabTamedField C a b)


-- @@ L218-220 verbatim
/-- The localized field reuses the globally defined flow of its empty-slab
`SlabTamedField` package. -/
abbrev flow (p : E₂) : ℝ → E₂ := W.base.flow p


-- @@ L222-223 verbatim
@[simp] theorem flow_zero (p : E₂) : W.flow p 0 = p :=
  W.base.flow_zero p


-- @@ L225-228 verbatim
theorem flow_mem_fiber {p : E₂}
    (hp : p ∈ C.cobordism.toLevelCobordismData.fiber) (s : ℝ) :
    W.flow p s ∈ C.cobordism.toLevelCobordismData.fiber :=
  W.base.flow_mem_fiber hp s


-- @@ L230-231 verbatim
theorem continuous_flow (p : E₂) : Continuous (W.flow p) :=
  W.base.continuous_flow p


-- @@ L233-246 verbatim
/-- Since the global field lies in the kernel of `G`, the nonvanishing signed
label cannot change sign along any of its fiber trajectories. -/
theorem pos_iff_flow {p : E₂}
    (hp : p ∈ C.cobordism.toLevelCobordismData.fiber) (s : ℝ) :
    0 < C p ↔ 0 < C (W.flow p s) := by
  let γ : C(Set.Icc (0 : ℝ) 1, E₂) :=
    ⟨fun u => W.flow p ((u : ℝ) * s),
      (W.continuous_flow p).comp
        (continuous_subtype_val.mul continuous_const)⟩
  have hγ : ∀ u, C.cobordism.G (γ u) = 0 := by
    intro u
    exact W.flow_mem_fiber hp ((u : ℝ) * s)
  have hsign := C.pos_iff_of_zeroFiber_path γ hγ
  simpa [γ] using hsign


-- @@ L248-328 verbatim
/-- Unit time speed on a positive fiber trajectory.  Negative critical points
in the same time interval play no role: the relatively open-and-closed set of
times at which the expected formula holds stays in the positive core. -/
theorem tcoord_flow_Icc {p : E₂}
    (hp : p ∈ C.cobordism.toLevelCobordismData.fiber)
    (hppos : 0 < C p) {t₀ l u : ℝ}
    (hpt : tcoord p = t₀) (_hlu : l ≤ u) (hl : l ≤ 0) (hu : 0 ≤ u)
    (ha : a ≤ t₀ + l) (hb : t₀ + u ≤ b) :
    ∀ s ∈ Icc l u, tcoord (W.flow p s) = t₀ + s := by
  let f : ℝ → ℝ := fun s => tcoord (W.flow p s)
  let g : ℝ → ℝ := fun s => t₀ + s
  let S : Set ℝ := Icc l u
  let A : Set ℝ := {s | s ∈ S ∧ f s = g s}
  have hSpre : IsPreconnected S := (convex_Icc l u).isPreconnected
  have hAS : A ⊆ S := fun _ hs => hs.1
  have hfcont : Continuous f := continuous_tcoord.comp (W.continuous_flow p)
  have hgcont : Continuous g := continuous_const.add continuous_id
  have hAclosed : IsClosed A :=
    isClosed_Icc.inter (isClosed_eq hfcont hgcont)
  have hAopen : ∀ s ∈ A, ∃ r > 0, S ∩ Metric.ball s r ⊆ A := by
    intro s hsA
    have hsS : s ∈ Icc l u := hsA.1
    have hqFiber : W.flow p s ∈
        C.cobordism.toLevelCobordismData.fiber :=
      W.flow_mem_fiber hp s
    have hqTime : tcoord (W.flow p s) = t₀ + s := hsA.2
    have hqPos : 0 < C (W.flow p s) := (W.pos_iff_flow hp s).mp hppos
    have hqCore : W.flow p s ∈ C.positiveSlabCore a b := by
      refine ⟨hqFiber, ?_, hqPos.le⟩
      rw [hqTime]
      constructor <;> linarith [hsS.1, hsS.2]
    have hopen : IsOpen ((W.flow p) ⁻¹'
        Metric.ball (W.flow p s) W.delta) :=
      Metric.isOpen_ball.preimage (W.continuous_flow p)
    have hmem : s ∈ (W.flow p) ⁻¹'
        Metric.ball (W.flow p s) W.delta :=
      Metric.mem_ball_self W.delta_pos
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen s hmem
    refine ⟨r, hr, ?_⟩
    have hcollar : ∀ q ∈ Metric.ball s r,
        W.flow p q ∈ Metric.cthickening W.delta
          (C.positiveSlabCore a b) := by
      intro q hq
      have hqBall : W.flow p q ∈ Metric.ball (W.flow p s) W.delta :=
        hrsub hq
      apply Metric.thickening_subset_cthickening
      exact Metric.mem_thickening_iff.mpr
        ⟨W.flow p s, hqCore, hqBall⟩
    have hfderiv : ∀ q ∈ Metric.ball s r, HasDerivAt f 1 q := by
      intro q hq
      have hflow := W.base.hasDerivAt_flow p q
      have hproj :=
        (EuclideanSpace.proj (Fin.last (n + 1)) (𝕜 := ℝ)).hasFDerivAt.comp
          q hflow.hasFDerivAt
      have ht : HasDerivAt f (tcoord (W.base.w (W.flow p q))) q := by
        simpa [f, tcoord, Function.comp_def] using hproj.hasDerivAt
      have hc := hcollar q hq
      have hspeed : tcoord (W.base.w (W.flow p q)) = 1 := by
        rw [W.eq_time _ hc]
        exact tcoord_timeField (W.subset_slabRegular hc)
      rwa [hspeed] at ht
    have hfg : Set.EqOn f g (Metric.ball s r) := by
      apply Metric.isOpen_ball.eqOn_of_deriv_eq
        (convex_ball _ _).isPreconnected
      · intro q hq
        exact (hfderiv q hq).differentiableAt.differentiableWithinAt
      · exact ((differentiable_const t₀).add differentiable_id).differentiableOn
      · intro q hq
        rw [(hfderiv q hq).deriv]
        simp [g]
      · exact Metric.mem_ball_self hr
      · exact hsA.2
    rintro q ⟨hqS, hqBall⟩
    exact ⟨hqS, hfg hqBall⟩
  have hA0 : A.Nonempty := by
    refine ⟨0, ⟨⟨hl, hu⟩, ?_⟩⟩
    simp [f, g, hpt]
  have hSA : S ⊆ A :=
    subset_of_relOpen_closed hSpre hAS hAclosed hAopen hA0
  intro s hs
  exact (hSA hs).2


-- @@ L330-338 verbatim
/-- Forward-time specialization. -/
theorem tcoord_flow_segment {p : E₂}
    (hp : p ∈ C.cobordism.toLevelCobordismData.fiber)
    (hppos : 0 < C p) {t₀ d : ℝ}
    (hpt : tcoord p = t₀) (hd : 0 ≤ d)
    (ha : a ≤ t₀) (hb : t₀ + d ≤ b) :
    ∀ s ∈ Icc (0 : ℝ) d, tcoord (W.flow p s) = t₀ + s := by
  exact W.tcoord_flow_Icc hp hppos hpt (by linarith) le_rfl hd
    (by simpa) hb


-- @@ L340-340 verbatim
/-! ## Transport of positive slice fibers -/


-- @@ L342-347 verbatim
/-- The strictly positive part of a time-slice zero fiber, without requiring
the whole slice to be regular. -/
def positiveSliceFiber (C : SignedFramedLevelCobordism S₀ S₁)
    (t : ℝ) : Set E₁ :=
  {x | C.cobordism.G (cobSpaceTime x t) = 0 ∧
    0 < C (cobSpaceTime x t)}


-- @@ L349-356 verbatim
/-- At a regular slice time, the set used by the localized flow is literally
the positive part of the existing signed slice presentation. -/
theorem positiveSliceFiber_eq_positivePart
    (C : SignedFramedLevelCobordism S₀ S₁) (t : ℝ)
    (ht : sliceRegular C.cobordism.G t) :
    positiveSliceFiber C t = (C.sliceSign t ht).positivePart := by
  ext x
  rfl


-- @@ L358-360 verbatim
/-- Flow a positive point between two slice times. -/
def sliceTransport (t₁ t₂ : ℝ) (x : E₁) : E₁ :=
  W.base.sliceTransport t₁ t₂ x


-- @@ L362-364 verbatim
theorem continuous_sliceTransport (t₁ t₂ : ℝ) :
    Continuous (W.sliceTransport t₁ t₂) :=
  W.base.continuous_sliceTransport t₁ t₂


-- @@ L366-404 verbatim
/-- The localized flow maps the complete positive sheet of one slice into the
complete positive sheet of another. -/
theorem sliceTransport_mapsTo {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    MapsTo (W.sliceTransport t₁ t₂)
      (positiveSliceFiber C t₁) (positiveSliceFiber C t₂) := by
  intro x hx
  let p : E₂ := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  have hp : p ∈ C.cobordism.toLevelCobordismData.fiber := hx.1
  have hppos : 0 < C p := hx.2
  have hpt : tcoord p = t₁ := tcoord_spaceTime x t₁
  have htflow : tcoord (W.flow p d) = t₂ := by
    rcases le_total t₁ t₂ with hle | hle
    · have hd : 0 ≤ d := by dsimp [d]; linarith
      have hb' : t₁ + d ≤ b := by dsimp [d]; linarith [ht₂.2]
      have h := W.tcoord_flow_segment hp hppos hpt hd ht₁.1 hb'
        d ⟨hd, le_rfl⟩
      dsimp [d] at h ⊢
      linarith
    · have hd : d ≤ 0 := by dsimp [d]; linarith
      have ha' : a ≤ t₁ + d := by dsimp [d]; linarith [ht₂.1]
      have hb' : t₁ + 0 ≤ b := by linarith [ht₁.2]
      have h := W.tcoord_flow_Icc hp hppos hpt hd hd le_rfl
        ha' hb' d ⟨le_rfl, hd⟩
      dsimp [d] at h ⊢
      linarith
  have hqFiber := W.flow_mem_fiber hp d
  have hqPos : 0 < C (W.flow p d) := (W.pos_iff_flow hp d).mp hppos
  have hspace : cobSpaceTime (spacePart (W.flow p d)) t₂ = W.flow p d := by
    rw [← htflow, spaceTime_spacePart]
  refine ⟨?_, ?_⟩
  · change C.cobordism.G
      (cobSpaceTime (spacePart (W.flow p d)) t₂) = 0
    rw [hspace]
    exact hqFiber
  · change 0 < C (cobSpaceTime (spacePart (W.flow p d)) t₂)
    rw [hspace]
    exact hqPos


-- @@ L406-434 verbatim
/-- Reattaching the target time recovers the actual positive flow point. -/
theorem cobSpaceTime_sliceTransport {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    {x : E₁} (hx : x ∈ positiveSliceFiber C t₁) :
    cobSpaceTime (W.sliceTransport t₁ t₂ x) t₂ =
      W.flow (cobSpaceTime x t₁) (t₂ - t₁) := by
  let p : E₂ := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  have hp : p ∈ C.cobordism.toLevelCobordismData.fiber := hx.1
  have hppos : 0 < C p := hx.2
  have hpt : tcoord p = t₁ := tcoord_spaceTime x t₁
  have htflow : tcoord (W.flow p d) = t₂ := by
    rcases le_total t₁ t₂ with hle | hle
    · have hd : 0 ≤ d := by dsimp [d]; linarith
      have hb' : t₁ + d ≤ b := by dsimp [d]; linarith [ht₂.2]
      have h := W.tcoord_flow_segment hp hppos hpt hd ht₁.1 hb'
        d ⟨hd, le_rfl⟩
      dsimp [d] at h ⊢
      linarith
    · have hd : d ≤ 0 := by dsimp [d]; linarith
      have ha' : a ≤ t₁ + d := by dsimp [d]; linarith [ht₂.1]
      have hb' : t₁ + 0 ≤ b := by linarith [ht₁.2]
      have h := W.tcoord_flow_Icc hp hppos hpt hd hd le_rfl
        ha' hb' d ⟨le_rfl, hd⟩
      dsimp [d] at h ⊢
      linarith
  unfold sliceTransport
  change cobSpaceTime (spacePart (W.flow p d)) t₂ = W.flow p d
  rw [← htflow, spaceTime_spacePart]


-- @@ L436-455 verbatim
/-- Reverse localized flow is a left inverse on the positive source slice. -/
theorem sliceTransport_leftInverse {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    {x : E₁} (hx : x ∈ positiveSliceFiber C t₁) :
    W.sliceTransport t₂ t₁ (W.sliceTransport t₁ t₂ x) = x := by
  let p : E₂ := cobSpaceTime x t₁
  let d : ℝ := t₂ - t₁
  have hspace := W.cobSpaceTime_sliceTransport ht₁ ht₂ hx
  unfold sliceTransport
  change spacePart (W.flow
    (cobSpaceTime (spacePart (W.flow p d)) t₂) (t₁ - t₂)) = x
  change cobSpaceTime (spacePart (W.flow p d)) t₂ = W.flow p d at hspace
  rw [hspace]
  have hshift := congrFun (W.base.flow_shift p d) (t₁ - t₂)
  have hshift' : W.flow (W.flow p d) (t₁ - t₂) =
      W.flow p (d + (t₁ - t₂)) := hshift
  rw [hshift']
  have htime : d + (t₁ - t₂) = 0 := by dsimp [d]; ring
  rw [htime, W.flow_zero]
  exact spacePart_spaceTime x t₁


-- @@ L457-471 verbatim
/-- The actual flow is a bijection between the complete positive parts of two
slices, even if the intervening negative sheet has a Morse critical point. -/
theorem sliceTransport_bijOn {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    Set.BijOn (W.sliceTransport t₁ t₂)
      (positiveSliceFiber C t₁) (positiveSliceFiber C t₂) := by
  refine ⟨W.sliceTransport_mapsTo ht₁ ht₂, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := congrArg (W.sliceTransport t₂ t₁) hxy
    simpa [W.sliceTransport_leftInverse ht₁ ht₂ hx,
      W.sliceTransport_leftInverse ht₁ ht₂ hy] using h
  · intro y hy
    refine ⟨W.sliceTransport t₂ t₁ y,
      W.sliceTransport_mapsTo ht₂ ht₁ hy, ?_⟩
    exact W.sliceTransport_leftInverse ht₂ ht₁ hy


-- @@ L473-505 verbatim
/-- A negative Morse event therefore admits an actual continuous bijection
between the complete positive parts of its canonical before/after slices. -/
theorem exists_continuous_bijOn_positiveSlices_of_negative_event
    (C : SignedFramedLevelCobordism S₀ S₁)
    (P : MorsePosition C.cobordism) {t : ℝ} (ht : t ∈ P.eventTimes)
    (hnegative : P.eventCenter t ht ∈
      (C.labelMorsePosition P).negativeCenters) :
    ∃ f : E₁ → E₁,
      Continuous f ∧
      Set.BijOn f
        ((C.sliceSign (P.eventBracket t ht).before
          (P.eventBracket t ht).before_regular).positivePart)
        ((C.sliceSign (P.eventBracket t ht).after
          (P.eventBracket t ht).after_regular).positivePart) := by
  obtain ⟨W⟩ := nonempty_of_negative_event C P ht hnegative
  let hab : (P.eventBracket t ht).before ≤
      (P.eventBracket t ht).after :=
    ((P.eventBracket t ht).before_lt.trans
      (P.eventBracket t ht).lt_after).le
  let hbefore : (P.eventBracket t ht).before ∈
      Icc (P.eventBracket t ht).before (P.eventBracket t ht).after :=
    ⟨le_rfl, hab⟩
  let hafter : (P.eventBracket t ht).after ∈
      Icc (P.eventBracket t ht).before (P.eventBracket t ht).after :=
    ⟨hab, le_rfl⟩
  refine ⟨W.sliceTransport (P.eventBracket t ht).before
      (P.eventBracket t ht).after,
    W.continuous_sliceTransport _ _, ?_⟩
  rw [← positiveSliceFiber_eq_positivePart C _
      (P.eventBracket t ht).before_regular,
    ← positiveSliceFiber_eq_positivePart C _
      (P.eventBracket t ht).after_regular]
  exact W.sliceTransport_bijOn hbefore hafter


-- @@ L507-507 verbatim
end PositiveSheetSlabTamedField


-- @@ L509-509 verbatim
end Submission
