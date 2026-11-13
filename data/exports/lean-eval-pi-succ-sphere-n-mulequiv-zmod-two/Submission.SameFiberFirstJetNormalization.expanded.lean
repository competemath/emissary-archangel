import Mathlib
import Submission.ConcreteConfigurationBridgeEntryClosure
import Submission.ConcreteConfigurationGaugeAlignmentExistence


-- @@ L5-63 verbatim
/-!
# First-jet discharge of the Sard-shell residual

`ConcreteConfigurationBridgeEntryClosure` reduced the whole bridge entry to
`ShellData`: one uniform outer bound along convex combinations of the two
defining maps, plus a *shell* around the common canonical fiber on which no
convex combination vanishes.  This module discharges the shell half by pure
analysis: **first-jet agreement on the fiber already produces the shell.**

The engine is a quantitative tube estimate for an arbitrary framed level set,
proved from the inverse function theorem:

* `exists_local_inverse_bound` — near each fiber point `p`, the chart
  `x ↦ (⟪τ_p, x - p⟫, g x)` is strictly differentiable with invertible
  derivative (the kernel of `fderiv g p` is exactly the line `ℝ ∙ τ_p`), so
  its Lipschitz local inverse converts a small value of `g` into a nearby
  actual zero of `g`;
* `exists_tube_bound` — by compactness of the fiber the local bounds glue to
  one inequality `infDist x fiber ≤ C * ‖g x‖` on a uniform tube;
* `exists_jet_difference_bound` — if two presentations share the fiber and
  their derivatives are `ε`-close there, the mean value inequality on the
  segment to a nearest fiber point gives
  `‖Y.g x - X.g x‖ ≤ ε · infDist x fiber` on a small tube;
* `exists_tube_threshold` / `tubeThreshold` — combining the two: there is a
  strictly positive tolerance `tubeThreshold X` (namely `1/(2C)` for the tube
  constant `C`), depending on `X` **alone**, such that on a small tube minus
  the fiber `‖(1-r) X.g + r Y.g‖ ≥ ‖X.g‖ - ‖Y.g - X.g‖ > 0` for every `Y`
  with the same fiber whose derivative is `tubeThreshold X`-close to `X`'s on
  it.  So *no* convex combination of the two defining maps vanishes near (but
  off) the fiber.  `exists_segMap_ne_zero` is the exact-agreement corollary.

`dataOfFderivClose` packages this as the full generic Sard-interpolation
residual `SameFiberSardInterpolation.Data`: the shell is a small
`infDist`-sublevel pair around the fiber, and the label agreement extends to
it by continuity; `dataOfFirstJet` is its exact-agreement corollary.
Compared with `Data.ofNoAntiparallel`, the *global* off-fiber
no-antiparallelism field is replaced by first-jet closeness **on the compact
fiber only** — antiparallelism away from the fiber is now allowed everywhere.

For the concrete pair, `ConcreteConfigurationBridgeEntryFirstJet` produces

* `shellDataOfFderivClose` / `nonempty_toFirstSource_of_fderivClose` —
  `ShellData` and the bridge-entry connector from the outer bound plus a
  quantitative first-jet closeness estimate on the canonical fiber, at the
  explicit positive tolerance `tubeThreshold (harmonizedEndpoint hm M F G)`
  (the sign-agreement half is the committed theorem
  `harmonized_mul_pos_on_fiber`);
* `shellDataOfFirstJet` — the exact-agreement special case;
* `nonempty_toFirstSource_of_firstJet` / `ofFirstJetAndTrace` — the
  bridge-entry connector and the complete bridge cobordism-trace data;
* `nonempty_toFirstSource_of_nearIdentityJet` / `ofNearIdentityJetAndTrace` —
  the *gauge-deformed* forms: a near-identity smooth codomain gauge `A` may
  first be applied to the harmonized endpoint (the committed
  `Path.ofNearIdentity` machinery absorbs it), and only the deformed map has
  to match first jets with the placed head.  This realizes the intended
  first-jet *normalization* interface: the caller supplies the normalizing
  gauge and the jet equation, and no shell or antiparallelism condition
  remains anywhere.
-/


-- @@ L65-65 verbatim
set_option autoImplicit false

-- @@ L66-66 verbatim
set_option maxHeartbeats 1600000


-- @@ L68-68 verbatim
noncomputable section


-- @@ L70-70 verbatim
namespace Submission

-- @@ L71-71 verbatim
namespace SameFiberFirstJetNormalization


-- @@ L73-73 verbatim
open Set Function Metric Module

-- @@ L74-74 verbatim
open SameFiberSegmentComparison

-- @@ L75-75 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L77-77 verbatim
variable {n : ℕ}


-- @@ L79-79 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L80-80 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L82-82 verbatim
/-! ## The pointwise inverse-function bound at a fiber point -/


-- @@ L84-221 verbatim
/-- **Local tube bound.**  Near a point of the fiber, the distance to an
actual zero of the defining map is controlled by the value of the map: the
chart `x ↦ (⟪τ, x - p⟫, g x)` has invertible strict derivative at `p`, and
its Lipschitz local inverse sends `(⟪τ, x - p⟫, 0)` to a genuine fiber point
close to `x`. -/
theorem exists_local_inverse_bound (X : FramedLevelSet n) {p : E}
    (hp : p ∈ X.fiber) :
    ∃ K : ℝ≥0, ∃ r : ℝ, 0 < r ∧ ∀ x : E, dist x p < r →
      ∃ q : E, q ∈ X.fiber ∧ dist x q ≤ K * ‖X.g x‖ := by
  classical
  have hp0 : X.g p = 0 := hp
  have hpreg : p ∈ regularSet X.g := X.fiber_subset_regularSet hp
  set tau : E := tauField X.g p with htaudef
  have htau1 : ‖tau‖ = 1 := norm_tauField hpreg
  set L : E →L[ℝ] F := fderiv ℝ X.g p with hLdef
  set Phi' : E →L[ℝ] ℝ × F := (innerSL ℝ tau).prod L with hPhi'def
  -- the chart and its strict derivative
  have hgstrict : HasStrictFDerivAt X.g L p :=
    (X.smooth.contDiffAt).hasStrictFDerivAt infty_ne_zero
  have hfst : HasStrictFDerivAt
      (fun x : E => innerSL ℝ tau x - innerSL ℝ tau p) (innerSL ℝ tau) p :=
    (innerSL ℝ tau).hasStrictFDerivAt.sub_const _
  have hstrict : HasStrictFDerivAt
      (fun x : E => (innerSL ℝ tau x - innerSL ℝ tau p, X.g x)) Phi' p :=
    hfst.prodMk hgstrict
  -- the derivative is injective, hence bijective by dimension count
  have hker : ∀ v : E, Phi' v = 0 → v = 0 := by
    intro v hv
    have h1 : innerSL ℝ tau v = 0 := by
      have h := congrArg Prod.fst hv
      simpa [hPhi'def] using h
    have h2 : L v = 0 := by
      have h := congrArg Prod.snd hv
      simpa [hPhi'def] using h
    have hmem : v ∈ Submodule.span ℝ {tauField X.g p} :=
      (fderiv_eq_zero_iff_mem_span_tauField hpreg v).mp h2
    rw [← htaudef] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hcv : innerSL ℝ tau (c • tau) = 0 := by
      rw [hc]
      exact h1
    have hc0 : c = 0 := by
      rw [innerSL_apply_apply, real_inner_smul_right,
        real_inner_self_eq_norm_sq, htau1] at hcv
      simpa using hcv
    rw [← hc, hc0, zero_smul]
  have hinj : Function.Injective Phi' := by
    intro v w hvw
    have hsub : Phi' (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker _ hsub)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) =
      finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin, Module.finrank_prod,
      finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  -- upgrade to a continuous linear equivalence
  set eqv : E ≃L[ℝ] ℝ × F :=
    (Phi'.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    with heqvdef
  have hcoefun : ∀ v : E, eqv v = Phi' v := by
    intro v
    have h1 : eqv v =
        Phi'.toLinearMap.linearEquivOfInjective hinj hdim v := rfl
    rw [h1, LinearMap.linearEquivOfInjective_apply]
    rfl
  have hcoe : (eqv : E →L[ℝ] ℝ × F) = Phi' :=
    ContinuousLinearMap.ext hcoefun
  have hPhie : HasStrictFDerivAt
      (fun x : E => (innerSL ℝ tau x - innerSL ℝ tau p, X.g x))
      (eqv : E →L[ℝ] ℝ × F) p := by
    rw [hcoe]
    exact hstrict
  set Phi : E → ℝ × F :=
    fun x : E => (innerSL ℝ tau x - innerSL ℝ tau p, X.g x) with hPhidef
  set ginv : ℝ × F → E := hPhie.localInverse Phi eqv p with hginvdef
  -- the local inverse is Lipschitz near the center value
  obtain ⟨K, s, hs, hK⟩ := hPhie.to_localInverse.exists_lipschitzOnWith
  have hright : ∀ᶠ y in 𝓝 (Phi p), Phi (ginv y) = y :=
    hPhie.eventually_right_inverse
  have hleft : ∀ᶠ x in 𝓝 p, ginv (Phi x) = x :=
    hPhie.eventually_left_inverse
  have hΦp : Phi p = (0 : ℝ × EuclideanSpace ℝ (Fin n)) := by
    rw [hPhidef]
    simp [hp0, Prod.ext_iff]
  -- shrink everything to metric balls
  have hmem2 : s ∩ {y : ℝ × F | Phi (ginv y) = y} ∈ 𝓝 (Phi p) :=
    Filter.inter_mem hs hright
  obtain ⟨rho, hrhopos, hrhosub⟩ := Metric.mem_nhds_iff.mp hmem2
  have hPhicont : Continuous Phi := by
    rw [hPhidef]
    exact ((innerSL ℝ tau).continuous.sub continuous_const).prodMk
      X.smooth.continuous
  have hpre : {x : E | ginv (Phi x) = x} ∩
      Phi ⁻¹' Metric.ball (Phi p) rho ∈ 𝓝 p :=
    Filter.inter_mem hleft
      (hPhicont.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hrhopos))
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨K, r, hrpos, ?_⟩
  intro x hx
  obtain ⟨hgx, hxball⟩ := hrsub (Metric.mem_ball.mpr hx)
  have hxball' : dist (Phi x) (Phi p) < rho := Metric.mem_ball.mp hxball
  -- the projected target
  set y0 : ℝ × F := ((Phi x).1, (0 : EuclideanSpace ℝ (Fin n))) with hy0def
  have hxnorm : ‖Phi x‖ < rho := by
    have h := hxball'
    rwa [hΦp, dist_zero_right] at h
  have hy0close : dist y0 (Phi p) < rho := by
    rw [hΦp, dist_zero_right]
    have hle : ‖y0‖ ≤ ‖Phi x‖ := by
      rw [hy0def, Prod.norm_def, Prod.norm_def]
      simp only [norm_zero]
      exact max_le (le_max_left _ _) (le_max_of_le_right (norm_nonneg _))
    exact lt_of_le_of_lt hle hxnorm
  have hy0mem := hrhosub (Metric.mem_ball.mpr hy0close)
  have hxmem := hrhosub (Metric.mem_ball.mpr hxball')
  set q : E := ginv y0 with hqdef
  have hq : Phi q = y0 := hy0mem.2
  have hqfiber : q ∈ X.fiber := by
    have h := congrArg Prod.snd hq
    have h2 : X.g q = 0 := by
      simpa [hPhidef, hy0def] using h
    exact h2
  refine ⟨q, hqfiber, ?_⟩
  have hdistPhi : dist (Phi x) y0 = ‖X.g x‖ := by
    rw [Prod.dist_eq]
    have h1 : dist (Phi x).1 y0.1 = 0 := by
      rw [hy0def]
      exact dist_self _
    have h2 : dist (Phi x).2 y0.2 = ‖X.g x‖ := by
      show dist (X.g x) (0 : EuclideanSpace ℝ (Fin n)) = ‖X.g x‖
      exact dist_zero_right _
    rw [h1, h2]
    exact max_eq_right (norm_nonneg _)
  calc dist x q = dist (ginv (Phi x)) (ginv y0) := by rw [hgx]
    _ ≤ K * dist (Phi x) y0 := hK.dist_le_mul _ hxmem.1 _ hy0mem.1
    _ = K * ‖X.g x‖ := by rw [hdistPhi]


-- @@ L223-223 verbatim
/-! ## The uniform tube bound -/


-- @@ L225-287 verbatim
/-- **Uniform tube bound.**  On a tube around the (compact) fiber, the
distance to the fiber is controlled by the norm of the defining map. -/
theorem exists_tube_bound (X : FramedLevelSet n) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x : E,
      Metric.infDist x X.fiber ≤ δ →
        Metric.infDist x X.fiber ≤ C * ‖X.g x‖ := by
  classical
  by_cases hne : X.fiber.Nonempty
  · choose K r hr hloc using
      fun p : X.fiber => exists_local_inverse_bound X p.2
    have hcover : X.fiber ⊆
        ⋃ p : X.fiber, Metric.ball (p : E) (r p / 2) := by
      intro q hq
      exact Set.mem_iUnion.mpr
        ⟨⟨q, hq⟩, Metric.mem_ball_self (half_pos (hr ⟨q, hq⟩))⟩
    obtain ⟨t, ht⟩ := X.isCompact_fiber.elim_finite_subcover
      (fun p : X.fiber => Metric.ball (p : E) (r p / 2))
      (fun _ => Metric.isOpen_ball) hcover
    have htne : t.Nonempty := by
      obtain ⟨q, hq⟩ := hne
      have hmem := ht hq
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨p, hpt, -⟩ := hmem
      exact ⟨p, hpt⟩
    refine ⟨1 + ((t.sup K : ℝ≥0) : ℝ), by positivity,
      t.inf' htne r / 2, ?_, ?_⟩
    · have hall : (0 : ℝ) < t.inf' htne r := by
        rw [Finset.lt_inf'_iff]
        intro p _
        exact hr p
      linarith
    · intro x hx
      obtain ⟨q₀, hq₀mem, hq₀d⟩ :=
        X.isCompact_fiber.exists_infDist_eq_dist hne x
      have hmem := ht hq₀mem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨p, hpt, hq₀ball⟩ := hmem
      have hq₀p : dist q₀ (p : E) < r p / 2 := Metric.mem_ball.mp hq₀ball
      have hinf_le : t.inf' htne r ≤ r p := Finset.inf'_le r hpt
      have hxq₀ : dist x q₀ ≤ t.inf' htne r / 2 := by
        rw [← hq₀d]
        exact hx
      have hxp : dist x (p : E) < r p := by
        calc dist x (p : E) ≤ dist x q₀ + dist q₀ (p : E) := dist_triangle _ _ _
          _ < t.inf' htne r / 2 + r p / 2 := by
              exact add_lt_add_of_le_of_lt hxq₀ hq₀p
          _ ≤ r p / 2 + r p / 2 := by linarith
          _ = r p := by ring
      obtain ⟨q, hqfib, hqd⟩ := hloc p x hxp
      have hKle : ((K p : ℝ≥0) : ℝ) ≤ 1 + ((t.sup K : ℝ≥0) : ℝ) := by
        have h1 : (K p : ℝ≥0) ≤ t.sup K := Finset.le_sup hpt
        have h2 : ((K p : ℝ≥0) : ℝ) ≤ ((t.sup K : ℝ≥0) : ℝ) :=
          NNReal.coe_le_coe.mpr h1
        linarith
      calc Metric.infDist x X.fiber ≤ dist x q :=
            Metric.infDist_le_dist_of_mem hqfib
        _ ≤ (K p : ℝ) * ‖X.g x‖ := hqd
        _ ≤ (1 + ((t.sup K : ℝ≥0) : ℝ)) * ‖X.g x‖ :=
            mul_le_mul_of_nonneg_right hKle (norm_nonneg _)
  · refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro x _
    rw [Set.not_nonempty_iff_eq_empty.mp hne, Metric.infDist_empty]
    positivity


-- @@ L289-289 verbatim
/-! ## The jet-difference bound -/


-- @@ L291-358 verbatim
/-- **Jet smallness.**  If two presentations share the fiber and their
derivatives are `ε`-close on it, the difference of the defining maps is
`ε`-controlled by the distance to the fiber on a small tube.  Only
*closeness* of the first jets is used, not equality. -/
theorem exists_jet_difference_bound (X Y : FramedLevelSet n)
    (hne : X.fiber.Nonempty)
    (fiber_eq : Y.fiber = X.fiber)
    {eps : ℝ}
    (hjet : ∀ x ∈ X.fiber, ‖fderiv ℝ Y.g x - fderiv ℝ X.g x‖ < eps) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, Metric.infDist x X.fiber ≤ δ →
      ‖Y.g x - X.g x‖ ≤ eps * Metric.infDist x X.fiber := by
  classical
  have hcontD : Continuous
      fun z : E => fderiv ℝ Y.g z - fderiv ℝ X.g z :=
    (Y.smooth.continuous_fderiv infty_ne_zero).sub
      (X.smooth.continuous_fderiv infty_ne_zero)
  have hopen : IsOpen
      {z : E | ‖fderiv ℝ Y.g z - fderiv ℝ X.g z‖ < eps} :=
    isOpen_lt hcontD.norm continuous_const
  have hsubset : X.fiber ⊆
      {z : E | ‖fderiv ℝ Y.g z - fderiv ℝ X.g z‖ < eps} :=
    fun z hz => hjet z hz
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ :=
    X.isCompact_fiber.exists_thickening_subset_open hopen hsubset
  refine ⟨δ₀ / 2, by positivity, ?_⟩
  intro x hx
  obtain ⟨p, hpmem, hpd⟩ := X.isCompact_fiber.exists_infDist_eq_dist hne x
  have hpY : Y.g p = 0 := by
    have hmem : p ∈ Y.fiber := by
      rw [fiber_eq]
      exact hpmem
    exact hmem
  have hpX : X.g p = 0 := hpmem
  have hd0 : 0 ≤ dist x p := dist_nonneg
  -- the derivative bound on the ball around the nearest point
  have hbound : ∀ z ∈ Metric.closedBall p (dist x p),
      ‖fderiv ℝ (fun w => Y.g w - X.g w) z‖ ≤ eps := by
    intro z hz
    have hzp : dist z p ≤ dist x p := Metric.mem_closedBall.mp hz
    have hzfib : Metric.infDist z X.fiber < δ₀ := by
      have h1 : Metric.infDist z X.fiber ≤ dist z p :=
        Metric.infDist_le_dist_of_mem hpmem
      have h2 : dist x p ≤ δ₀ / 2 := by
        rw [← hpd]
        exact hx
      linarith
    have hzmem : z ∈ Metric.thickening δ₀ X.fiber :=
      (Metric.mem_thickening_iff_infDist_lt hne).mpr hzfib
    have hzV := hδ₀sub hzmem
    have hfd : fderiv ℝ (fun w => Y.g w - X.g w) z =
        fderiv ℝ Y.g z - fderiv ℝ X.g z :=
      fderiv_sub (Y.smooth.differentiable infty_ne_zero z)
        (X.smooth.differentiable infty_ne_zero z)
    rw [hfd]
    exact le_of_lt hzV
  have hdiff : ∀ z ∈ Metric.closedBall p (dist x p),
      DifferentiableAt ℝ (fun w => Y.g w - X.g w) z :=
    fun z _ => (Y.smooth.differentiable infty_ne_zero z).sub
      (X.smooth.differentiable infty_ne_zero z)
  have hmvt := (convex_closedBall p (dist x p)).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (Metric.mem_closedBall_self hd0)
    (Metric.mem_closedBall.mpr le_rfl)
  have hmvt' : ‖(Y.g x - X.g x) - (Y.g p - X.g p)‖ ≤ eps * ‖x - p‖ := hmvt
  have hzero : Y.g p - X.g p = 0 := by
    rw [hpY, hpX, sub_zero]
  rw [hzero, sub_zero, ← dist_eq_norm] at hmvt'
  rw [hpd]
  exact hmvt'


-- @@ L360-360 verbatim
/-! ## No convex combination vanishes near (but off) the fiber -/


-- @@ L362-424 verbatim
/-- **The shell from `C¹`-closeness on the fiber.**  There is a positive
threshold `c`, depending on the *first* presentation alone, such that any
second presentation with the same fiber whose derivative is `c`-close to the
first on that fiber admits a small punctured tube on which no convex
combination of the two defining maps vanishes.

The threshold is `1 / (2C)` for the tube constant `C` of
`exists_tube_bound`; it is exposed existentially because `C` is. -/
theorem exists_tube_threshold (X : FramedLevelSet n) :
    ∃ c : ℝ, 0 < c ∧ ∀ Y : FramedLevelSet n, X.fiber.Nonempty →
      Y.fiber = X.fiber →
      (∀ p ∈ X.fiber, ‖fderiv ℝ Y.g p - fderiv ℝ X.g p‖ < c) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, x ∉ X.fiber →
        Metric.infDist x X.fiber ≤ δ →
          ∀ r : ℝ, 0 ≤ r → r ≤ 1 → segMap X Y r x ≠ 0 := by
  obtain ⟨C, hC, δB, hδB, hB⟩ := exists_tube_bound X
  refine ⟨1 / (2 * C), by positivity, ?_⟩
  intro Y hne fiber_eq hclose
  obtain ⟨δA, hδA, hA⟩ :=
    exists_jet_difference_bound X Y hne fiber_eq hclose
  refine ⟨min δA δB, lt_min hδA hδB, ?_⟩
  intro x hxf hx r hr0 hr1 hzero
  set d : ℝ := Metric.infDist x X.fiber with hddef
  have hd0 : (0 : ℝ) ≤ d := by
    rw [hddef]
    exact Metric.infDist_nonneg
  have hdpos : 0 < d := by
    rcases lt_or_eq_of_le hd0 with h | h
    · exact h
    · exfalso
      apply hxf
      have hz : Metric.infDist x X.fiber = 0 := by
        rw [← hddef]
        exact h.symm
      have hcl : x ∈ closure X.fiber :=
        (Metric.mem_closure_iff_infDist_zero hne).mpr hz
      rwa [X.isClosed_fiber.closure_eq] at hcl
  have hXg : d ≤ C * ‖X.g x‖ := hB x (hx.trans (min_le_right _ _))
  have hdiffb : ‖Y.g x - X.g x‖ ≤ 1 / (2 * C) * d :=
    hA x (hx.trans (min_le_left _ _))
  -- rewrite the vanishing convex combination
  have hzero' : (1 - r) • X.g x + r • Y.g x = 0 := hzero
  have hEq : (1 - r) • X.g x + r • Y.g x =
      X.g x + r • (Y.g x - X.g x) := by
    module
  have h1 : X.g x + r • (Y.g x - X.g x) = 0 := by
    rw [← hEq]
    exact hzero'
  have h2 : X.g x = -(r • (Y.g x - X.g x)) :=
    eq_neg_of_add_eq_zero_left h1
  have hnormX : ‖X.g x‖ ≤ 1 / (2 * C) * d := by
    rw [h2, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    calc r * ‖Y.g x - X.g x‖ ≤ 1 * ‖Y.g x - X.g x‖ :=
          mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)
      _ = ‖Y.g x - X.g x‖ := one_mul _
      _ ≤ 1 / (2 * C) * d := hdiffb
  have hfinal : d ≤ d / 2 := by
    have hstep : C * ‖X.g x‖ ≤ C * (1 / (2 * C) * d) :=
      mul_le_mul_of_nonneg_left hnormX hC.le
    have hCd : C * (1 / (2 * C) * d) = d / 2 := by
      field_simp
    linarith
  linarith


-- @@ L426-430 verbatim
/-- **The first-jet closeness threshold of a presentation.**  Any second
presentation with the same fiber whose derivative stays within
`tubeThreshold X` of `X`'s on that fiber already produces the shell. -/
def tubeThreshold (X : FramedLevelSet n) : ℝ :=
  (exists_tube_threshold X).choose


-- @@ L432-433 verbatim
theorem tubeThreshold_pos (X : FramedLevelSet n) : 0 < tubeThreshold X :=
  (exists_tube_threshold X).choose_spec.1


-- @@ L435-444 verbatim
/-- **The shell from `C¹`-closeness on the fiber**, named-threshold form. -/
theorem exists_segMap_ne_zero_of_fderiv_close (X Y : FramedLevelSet n)
    (hne : X.fiber.Nonempty)
    (fiber_eq : Y.fiber = X.fiber)
    (hclose : ∀ p ∈ X.fiber,
      ‖fderiv ℝ Y.g p - fderiv ℝ X.g p‖ < tubeThreshold X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, x ∉ X.fiber →
      Metric.infDist x X.fiber ≤ δ →
        ∀ r : ℝ, 0 ≤ r → r ≤ 1 → segMap X Y r x ≠ 0 :=
  (exists_tube_threshold X).choose_spec.2 Y hne fiber_eq hclose


-- @@ L446-461 verbatim
/-- **The shell from first jets.**  If two presentations share their compact
fiber and their derivatives agree on it, then no convex combination of the
two defining maps vanishes on a small tube around the fiber, off the fiber
itself.  This is the exact-agreement special case of
`exists_segMap_ne_zero_of_fderiv_close`. -/
theorem exists_segMap_ne_zero (X Y : FramedLevelSet n)
    (hne : X.fiber.Nonempty)
    (fiber_eq : Y.fiber = X.fiber)
    (hjet : ∀ x ∈ X.fiber, fderiv ℝ Y.g x = fderiv ℝ X.g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, x ∉ X.fiber →
      Metric.infDist x X.fiber ≤ δ →
        ∀ r : ℝ, 0 ≤ r → r ≤ 1 → segMap X Y r x ≠ 0 :=
  exists_segMap_ne_zero_of_fderiv_close X Y hne fiber_eq (by
    intro p hp
    rw [hjet p hp, sub_self, norm_zero]
    exact tubeThreshold_pos X)


-- @@ L463-491 verbatim
/-- **One radius does everything.**  A single positive radius `ρ` whose
`infDist`-sublevel set simultaneously carries strict label sign agreement and
carries no zero of any convex combination off the fiber.  Stated as a `Prop`
so that the shell data below can extract the radius with `Exists.choose`. -/
theorem exists_shell_radius (X Y : FramedLevelSet n) (S : FiberSign X)
    (T : FiberSign Y)
    (hne : X.fiber.Nonempty)
    (fiber_eq : Y.fiber = X.fiber)
    (hagree : ∀ x ∈ X.fiber, 0 < S x * T x)
    (hclose : ∀ p ∈ X.fiber,
      ‖fderiv ℝ Y.g p - fderiv ℝ X.g p‖ < tubeThreshold X) :
    ∃ rho : ℝ, 0 < rho ∧
      (∀ x : E, Metric.infDist x X.fiber ≤ rho → 0 < S x * T x) ∧
      (∀ x : E, x ∉ X.fiber → Metric.infDist x X.fiber ≤ rho →
        ∀ r : ℝ, 0 ≤ r → r ≤ 1 → segMap X Y r x ≠ 0) := by
  obtain ⟨δseg, hδseg, hseg⟩ :=
    exists_segMap_ne_zero_of_fderiv_close X Y hne fiber_eq hclose
  have hopen : IsOpen {x : E | 0 < S x * T x} :=
    isOpen_lt continuous_const (S.continuous.mul T.continuous)
  obtain ⟨δ₀, hδ₀, hsub⟩ :=
    X.isCompact_fiber.exists_thickening_subset_open hopen
      fun x hx => hagree x hx
  refine ⟨min (δ₀ / 2) δseg, lt_min (by positivity) hδseg, ?_, ?_⟩
  · intro x hx
    have h1 : Metric.infDist x X.fiber ≤ δ₀ / 2 := hx.trans (min_le_left _ _)
    have h2 : Metric.infDist x X.fiber < δ₀ := by linarith
    exact hsub ((Metric.mem_thickening_iff_infDist_lt hne).mpr h2)
  · intro x hxf hx r hr0 hr1
    exact hseg x hxf (hx.trans (min_le_right _ _)) r hr0 hr1


-- @@ L493-493 verbatim
/-! ## The generic residual from first-jet closeness -/


-- @@ L495-590 verbatim
/-- **The Sard-interpolation residual from `C¹`-closeness on the fiber.**
Two same-fiber signed presentations whose labels agree in sign on the fiber
and whose derivatives are `tubeThreshold`-close on the fiber admit the full
shell datum: the shell is a pair of small `infDist`-sublevel neighborhoods,
nonvanishing of convex combinations on the closed shell being
`exists_segMap_ne_zero_of_fderiv_close`.  Only the outer bound remains an
input.  Compared with `Data.ofNoAntiparallel`, the global off-fiber
no-antiparallelism field is gone. -/
def dataOfFderivClose (X Y : FramedLevelSet n) (S : FiberSign X)
    (T : FiberSign Y)
    (fiber_eq : Y.fiber = X.fiber)
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : E, R ≤ ‖x‖ → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      eps ≤ ‖segMap X Y r x‖)
    (hagree : ∀ x ∈ X.fiber, 0 < S x * T x)
    (hclose : ∀ p ∈ X.fiber,
      ‖fderiv ℝ Y.g p - fderiv ℝ X.g p‖ < tubeThreshold X) :
    SameFiberSardInterpolation.Data X Y S T := by
  classical
  by_cases hne : X.fiber.Nonempty
  · have hex := exists_shell_radius X Y S T hne fiber_eq hagree hclose
    have hρpos : 0 < hex.choose := hex.choose_spec.1
    have hρagree := hex.choose_spec.2.1
    have hρshell := hex.choose_spec.2.2
    have hclosure : ∀ c : ℝ,
        closure {x : E | Metric.infDist x X.fiber < c} ⊆
          {x : E | Metric.infDist x X.fiber ≤ c} := by
      intro c
      refine closure_minimal (fun x hx => ?_) ?_
      · exact le_of_lt (show Metric.infDist x X.fiber < c from hx)
      · exact isClosed_le (Metric.continuous_infDist_pt X.fiber)
          continuous_const
    refine
      { fiber_eq := fiber_eq
        R := R
        eps := eps
        eps_pos := eps_pos
        outer := outer
        W₁ := {x : E | Metric.infDist x X.fiber < hex.choose / 2}
        W₂ := {x : E | Metric.infDist x X.fiber < hex.choose}
        isOpen_W₁ := isOpen_lt (Metric.continuous_infDist_pt X.fiber) continuous_const
        isOpen_W₂ := isOpen_lt (Metric.continuous_infDist_pt X.fiber) continuous_const
        fiber_subset := ?_
        agree := ?_
        closure_subset := ?_
        isBounded_W₂ := ?_
        shell := ?_ }
    · intro x hx
      show Metric.infDist x X.fiber < hex.choose / 2
      rw [Metric.infDist_zero_of_mem hx]
      positivity
    · intro x hx
      have hle : Metric.infDist x X.fiber ≤ hex.choose / 2 := hclosure _ hx
      exact hρagree x (by linarith)
    · intro x hx
      have hle : Metric.infDist x X.fiber ≤ hex.choose / 2 := hclosure _ hx
      show Metric.infDist x X.fiber < hex.choose
      linarith
    · have hcpt : IsCompact (Metric.cthickening hex.choose X.fiber) :=
        X.isCompact_fiber.cthickening
      apply hcpt.isBounded.subset
      intro x hx
      exact Metric.thickening_subset_cthickening _ _
        ((Metric.mem_thickening_iff_infDist_lt hne).mpr hx)
    · intro x hx r hr0 hr1
      obtain ⟨hxW₂, hxW₁⟩ := hx
      have hle : Metric.infDist x X.fiber ≤ hex.choose := hclosure _ hxW₂
      have hxnf : x ∉ X.fiber := by
        intro hmem
        apply hxW₁
        show Metric.infDist x X.fiber < hex.choose / 2
        rw [Metric.infDist_zero_of_mem hmem]
        positivity
      exact hρshell x hxnf hle r hr0 hr1
  · have hempty : X.fiber = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine
      { fiber_eq := fiber_eq
        R := R
        eps := eps
        eps_pos := eps_pos
        outer := outer
        W₁ := ∅
        W₂ := ∅
        isOpen_W₁ := isOpen_empty
        isOpen_W₂ := isOpen_empty
        fiber_subset := by rw [hempty]
        agree := ?_
        closure_subset := by rw [closure_empty]
        isBounded_W₂ := Bornology.isBounded_empty
        shell := ?_ }
    · intro x hx
      rw [closure_empty] at hx
      exact absurd hx (Set.notMem_empty x)
    · intro x hx
      rw [closure_empty] at hx
      exact absurd hx.1 (Set.notMem_empty x)


-- @@ L592-607 verbatim
/-- **The Sard-interpolation residual from exact first-jet agreement**, the
special case of `dataOfFderivClose` in which the two derivatives are literally
equal on the fiber. -/
def dataOfFirstJet (X Y : FramedLevelSet n) (S : FiberSign X)
    (T : FiberSign Y)
    (fiber_eq : Y.fiber = X.fiber)
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : E, R ≤ ‖x‖ → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      eps ≤ ‖segMap X Y r x‖)
    (hagree : ∀ x ∈ X.fiber, 0 < S x * T x)
    (hjet : ∀ x ∈ X.fiber, fderiv ℝ Y.g x = fderiv ℝ X.g x) :
    SameFiberSardInterpolation.Data X Y S T :=
  dataOfFderivClose X Y S T fiber_eq R eps eps_pos outer hagree (by
    intro p hp
    rw [hjet p hp, sub_self, norm_zero]
    exact tubeThreshold_pos X)


-- @@ L609-617 verbatim
/-- A pointwise near-identity continuous linear map is bijective (Neumann
series). -/
theorem bijective_of_one_sub_norm_lt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (T : G →L[ℝ] G) (h : ‖(1 : G →L[ℝ] G) - T‖ < 1) :
    Function.Bijective T := by
  have hb := SameFiberGaugeAlignment.bijective_one_sub_of_norm_lt
    ((1 : G →L[ℝ] G) - T) h
  rwa [sub_sub_cancel] at hb


-- @@ L619-619 verbatim
end SameFiberFirstJetNormalization


-- @@ L621-621 verbatim
/-! ## The concrete pair: discharging `ShellData` from first jets -/


-- @@ L623-623 verbatim
namespace ConcreteConfigurationBridgeEntryFirstJet


-- @@ L625-625 verbatim
open Set Function

-- @@ L626-626 verbatim
open scoped Topology ContDiff RealInnerProductSpace

-- @@ L627-627 verbatim
open ConcreteConfigurationMorseReduction

-- @@ L628-628 verbatim
open ConcreteConfigurationBridgeExactReduction

-- @@ L629-629 verbatim
open ConcreteConfigurationBridgeCobordismTrace

-- @@ L630-630 verbatim
open ConcreteConfigurationSignedFramedActualGaugeBridgeEntry

-- @@ L631-631 verbatim
open ConcreteConfigurationFirstHeadPlacedGaugeEntry

-- @@ L632-632 verbatim
open ConcreteConfigurationBridgeEntryChain

-- @@ L633-633 verbatim
open ConcreteConfigurationBridgeEntryClosure

-- @@ L634-634 verbatim
open SameFiberSegmentComparison


-- @@ L636-636 verbatim
variable {m : ℕ} {z : StableSpherePi (m + 2)}

-- @@ L637-637 verbatim
variable {B : BridgeData (m + 2) z}

-- @@ L638-638 verbatim
variable {Z : ZeroPairSaddleModel m}

-- @@ L639-639 verbatim
variable {kind : CompactMoveKind}

-- @@ L640-640 verbatim
variable {tail : FlatSignedConfiguration (m + 2) (compactBackground m)}


-- @@ L642-694 verbatim
/-- **`ShellData` from `C¹`-closeness on the canonical fiber.**  The whole
shell half of the Sard-shell residual is discharged: only the outer bound and
a *quantitative first-jet closeness* estimate on the canonical fiber remain.
The tolerance
`SameFiberFirstJetNormalization.tubeThreshold (harmonizedEndpoint hm M F G)`
is a strictly positive number depending on the harmonized endpoint alone
(`tubeThreshold_pos`), so exact first-jet agreement is *not* needed — the
normalizing gauge only has to normalize the first jet approximately.  The
sign-agreement field is the committed theorem
`harmonized_mul_pos_on_fiber`. -/
def shellDataOfFderivClose
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖segMap (harmonizedEndpoint hm M F G)
          (firstSourcePlacement hm Z kind tail).endpointX r x‖)
    (hclose : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      ‖fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x -
          fderiv ℝ (harmonizedEndpoint hm M F G).g x‖ <
        SameFiberFirstJetNormalization.tubeThreshold
          (harmonizedEndpoint hm M F G)) :
    ShellData hm M F G := by
  have hgeneric :=
    SameFiberFirstJetNormalization.dataOfFderivClose
      (harmonizedEndpoint hm M F G)
      (firstSourcePlacement hm Z kind tail).endpointX
      (harmonizedSign hm M F G)
      (placedSign hm Z kind tail)
      (placed_fiber_eq_harmonized_fiber hm M F G)
      R eps eps_pos outer
      (harmonized_mul_pos_on_fiber hm M F G)
      hclose
  exact
    { R := hgeneric.R
      eps := hgeneric.eps
      eps_pos := hgeneric.eps_pos
      outer := hgeneric.outer
      W₁ := hgeneric.W₁
      W₂ := hgeneric.W₂
      isOpen_W₁ := hgeneric.isOpen_W₁
      isOpen_W₂ := hgeneric.isOpen_W₂
      fiber_subset := hgeneric.fiber_subset
      agree := hgeneric.agree
      closure_subset := hgeneric.closure_subset
      isBounded_W₂ := hgeneric.isBounded_W₂
      shell := hgeneric.shell }


-- @@ L696-719 verbatim
/-- **`ShellData` from exact first-jet agreement**, the special case of
`shellDataOfFderivClose` in which the two derivatives are literally equal on
the canonical fiber. -/
def shellDataOfFirstJet
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖segMap (harmonizedEndpoint hm M F G)
          (firstSourcePlacement hm Z kind tail).endpointX r x‖)
    (hjet : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x =
        fderiv ℝ (harmonizedEndpoint hm M F G).g x) :
    ShellData hm M F G :=
  shellDataOfFderivClose hm M F G R eps eps_pos outer (by
    intro x hx
    rw [hjet x hx, sub_self, norm_zero]
    exact SameFiberFirstJetNormalization.tubeThreshold_pos _)


-- @@ L721-745 verbatim
/-- Bridge-entry connector from the outer bound and `C¹`-closeness on the
canonical fiber alone. -/
theorem nonempty_toFirstSource_of_fderivClose
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖segMap (harmonizedEndpoint hm M F G)
          (firstSourcePlacement hm Z kind tail).endpointX r x‖)
    (hclose : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      ‖fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x -
          fderiv ℝ (harmonizedEndpoint hm M F G).g x‖ <
        SameFiberFirstJetNormalization.tubeThreshold
          (harmonizedEndpoint hm M F G)) :
    Nonempty (SignedFramedLevelCobordism
      (gaugeEndpointSign hm M F)
      (firstSourceFlat Z kind tail).sign) :=
  nonempty_toFirstSource_of_shellData hm M F G
    (shellDataOfFderivClose hm M F G R eps eps_pos outer hclose)


-- @@ L747-769 verbatim
/-- Bridge-entry connector from the outer bound and first-jet agreement on
the canonical fiber alone. -/
theorem nonempty_toFirstSource_of_firstJet
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖segMap (harmonizedEndpoint hm M F G)
          (firstSourcePlacement hm Z kind tail).endpointX r x‖)
    (hjet : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x =
        fderiv ℝ (harmonizedEndpoint hm M F G).g x) :
    Nonempty (SignedFramedLevelCobordism
      (gaugeEndpointSign hm M F)
      (firstSourceFlat Z kind tail).sign) :=
  nonempty_toFirstSource_of_shellData hm M F G
    (shellDataOfFirstJet hm M F G R eps eps_pos outer hjet)


-- @@ L771-799 verbatim
/-- **Complete bridge entry from the outer bound, first-jet agreement on the
canonical fiber, and a compact trace.** -/
def ofFirstJetAndTrace
    (hm : 0 < m)
    (Z : ZeroPairSaddleModel m)
    (kind : CompactMoveKind)
    (tail : FlatSignedConfiguration (m + 2) (compactBackground m))
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖segMap (harmonizedEndpoint hm M F G)
          (firstSourcePlacement hm Z kind tail).endpointX r x‖)
    (hjet : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x =
        fderiv ℝ (harmonizedEndpoint hm M F G).g x)
    (trace : CobordismTrace m Z
      ((kind.model m Z).sourceWithTailSign tail)
      (DiagonalStandardConfiguration.standard m
        (ConcreteConfigurationConfigure.positiveLedger
          m B.fiberSign).delta).sign) :
    ConcreteConfigurationBridgeCobordismTrace.Data m B :=
  ofShellDataAndTrace hm Z kind tail M F G
    (shellDataOfFirstJet hm M F G R eps eps_pos outer hjet) trace


-- @@ L801-801 verbatim
/-! ## The gauge-normalized form: near-identity deformation plus first jets -/


-- @@ L803-875 verbatim
/-- **Bridge-entry connector from a near-identity first-jet normalization.**
A smooth codomain gauge field `A` with distortion `‖1 - A x‖ < 1` may first
be applied pointwise to the harmonized endpoint — the committed
`Path.ofNearIdentity` machinery turns it into a defining-map homotopy — and
only the *deformed* value field `x ↦ A x (g x)` has to agree to first order
with the placed head on the canonical fiber.  The Sard interpolation then
carries the deformed presentation to the placed head with no shell or
antiparallelism input. -/
theorem nonempty_toFirstSource_of_nearIdentityJet
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (A : EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 2)))
    (hA : ContDiff ℝ ∞ A)
    (hnorm : ∀ x : EuclideanSpace ℝ (Fin (m + 3)),
      ‖(1 : EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ]
        EuclideanSpace ℝ (Fin (m + 2))) - A x‖ < 1)
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖(1 - r) • A x ((harmonizedEndpoint hm M F G).g x) +
          r • (firstSourcePlacement hm Z kind tail).endpointX.g x‖)
    (hjet : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x =
        fderiv ℝ (fun y => A y ((harmonizedEndpoint hm M F G).g y)) x) :
    Nonempty (SignedFramedLevelCobordism
      (gaugeEndpointSign hm M F)
      (firstSourceFlat Z kind tail).sign) := by
  have hAbij : ∀ x : EuclideanSpace ℝ (Fin (m + 3)),
      Function.Bijective (A x) := fun x =>
    SameFiberFirstJetNormalization.bijective_of_one_sub_norm_lt (A x)
      (hnorm x)
  -- the deformed presentation and the near-identity leg
  set X' : FramedLevelSet (m + 2) :=
    (harmonizedEndpoint hm M F G).gaugeTransform A hA hAbij with hX'def
  have hfib : X'.fiber = (harmonizedEndpoint hm M F G).fiber :=
    FramedLevelSet.gaugeTransform_fiber _ A hA hAbij
  have hP : SameFiberGaugeAlignment.Path
      (harmonizedEndpoint hm M F G) X' :=
    SameFiberGaugeAlignment.Path.ofNearIdentity A hA hnorm fun x => rfl
  have h₂ : DefiningMapHomotopy (harmonizedEndpoint hm M F G) X' :=
    hP.homotopy
  -- the Sard leg from first-jet agreement of the deformed pair
  have hdata :=
    SameFiberFirstJetNormalization.dataOfFirstJet X'
      (firstSourcePlacement hm Z kind tail).endpointX
      ((harmonizedSign hm M F G).restrict h₂.fiber_subset)
      (placedSign hm Z kind tail)
      (by rw [hfib]; exact placed_fiber_eq_harmonized_fiber hm M F G)
      R eps eps_pos
      (fun x hx r hr0 hr1 => outer x hx r hr0 hr1)
      (by
        intro x hx
        rw [hfib] at hx
        simpa using harmonized_mul_pos_on_fiber hm M F G x hx)
      (by
        intro x hx
        rw [hfib] at hx
        exact hjet x hx)
  exact SignedFramedLevelCobordism.nonempty_trans
    ⟨(legOne hm M F G).signedCobordism (gaugeEndpointSign hm M F)⟩
    (SignedFramedLevelCobordism.nonempty_trans
      ⟨h₂.signedCobordism (harmonizedSign hm M F G)⟩
      (SignedFramedLevelCobordism.nonempty_trans
        hdata.nonempty_signedCobordism
        (SignedFramedLevelCobordism.nonempty_symm
          ⟨(firstSourcePlacement hm Z kind tail).signedCobordism
            (firstSourceFlat Z kind tail).sign⟩)))


-- @@ L877-922 verbatim
/-- **Complete bridge entry from a near-identity first-jet normalization and
a compact trace.** -/
def ofNearIdentityJetAndTrace
    (hm : 0 < m)
    (Z : ZeroPairSaddleModel m)
    (kind : CompactMoveKind)
    (tail : FlatSignedConfiguration (m + 2) (compactBackground m))
    (M : SignedFramedOrbitEquiv
      (ConcreteConfigurationConfigure.field m : TamedField B.fls)
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (G : BridgeCompactBackgroundGauge.Data (-B.y) (compactBackground m))
    (A : EuclideanSpace ℝ (Fin (m + 3)) →
      EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 2)))
    (hA : ContDiff ℝ ∞ A)
    (hnorm : ∀ x : EuclideanSpace ℝ (Fin (m + 3)),
      ‖(1 : EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ]
        EuclideanSpace ℝ (Fin (m + 2))) - A x‖ < 1)
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : EuclideanSpace ℝ (Fin (m + 3)), R ≤ ‖x‖ →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        eps ≤ ‖(1 - r) • A x ((harmonizedEndpoint hm M F G).g x) +
          r • (firstSourcePlacement hm Z kind tail).endpointX.g x‖)
    (hjet : ∀ x ∈ (harmonizedEndpoint hm M F G).fiber,
      fderiv ℝ (firstSourcePlacement hm Z kind tail).endpointX.g x =
        fderiv ℝ (fun y => A y ((harmonizedEndpoint hm M F G).g y)) x)
    (trace : CobordismTrace m Z
      ((kind.model m Z).sourceWithTailSign tail)
      (DiagonalStandardConfiguration.standard m
        (ConcreteConfigurationConfigure.positiveLedger
          m B.fiberSign).delta).sign) :
    ConcreteConfigurationBridgeCobordismTrace.Data m B := by
  let P : ConcreteConfigurationBridgeCobordismTrace.Plan m Z
      (ConcreteConfigurationConfigure.positiveLedger m B.fiberSign)
      (ConcreteConfigurationConfigure.negativeLedger m B.fiberSign) :=
    ConcreteConfigurationBridgeCobordismTrace.Plan.ofLocalHeadTrace
      kind tail trace
  refine
    { zeroPairSaddle := Z
      plan := P
      initial := ?_ }
  exact SignedFramedLevelCobordism.nonempty_trans
    (nonempty_toGaugeEndpoint hm M F)
    (nonempty_toFirstSource_of_nearIdentityJet hm M F G A hA hnorm
      R eps eps_pos outer hjet)


-- @@ L924-924 verbatim
end ConcreteConfigurationBridgeEntryFirstJet

-- @@ L925-925 verbatim
end Submission
