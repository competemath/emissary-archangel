import Mathlib
import Submission.LevelSet
import Submission.LevelOrbit
import Submission.LevelFrame
import Submission.CobordSlice


-- @@ L7-53 verbatim
/-!
# Level-set cobordisms: the regular-interval flow

For a level-set cobordism `C : LevelCobordismData n` and a time interval `[a, b]`
containing no critical time (`regularSlab C.G a b`), we construct a tamed version of
the time-flow field `timeField` (`SlabTamedField`, mirroring `TamedField` from
`LevelOrbit`), prove global existence/uniqueness for its flow, establish

* fiber invariance (`flow_mem_fiber`) and **unit time speed on the fiber part**
  (`tcoord_flow` : `tcoord (flow p s) = tcoord p + s`, proved by a
  connectedness/exit-time argument),
* Lipschitz dependence on the initial condition (`dist_flow_flow_le`, Grönwall),

and derive the **slice transport theorem**: `sliceTransport W t₁ t₂` is a
homeomorphism-like correspondence between the slice fibers at times `t₁, t₂ ∈ [a, b]`
(`sliceTransport_bijOn`, `continuous_sliceTransport`, inverse = reverse flow), which

* maps orbits onto orbits (`sliceTransport_orbit`, stated **per-orbit** so that any
  union of orbits — e.g. the northern part of a split fiber — transports as well), and
* transports frame loops up to free homotopy (`frameTransportHomotopy` and its
  `..._zero/_last/_periodic/_mem_SO/continuousOn_...` lemmas).

## Interface notes for 4C (δ-invariance)

`δ` of a slice will be `Σ_orbits w(frameLoop) + #orbits (mod 2)`. To prove
`δ (sliceFLS a) = δ (sliceFLS b)` from this file:

1. Orbits of the two end slices are in bijection: `sliceTransport_orbit` shows that
   `sliceTransport W a b` maps each `Va`-orbit onto a `Vb`-orbit; together with
   `sliceTransport_bijOn` (bijection of fibers) this induces a bijection of the orbit
   sets (orbits partition the fibers by `TamedField.orbit_eq_or_disjoint`).
   The statement is per-orbit, hence restricts to any union of orbits (clopen parts).
2. For each source orbit with flow parametrization `γ = Va.flow x₀` and period `T`
   (`Va.exists_period`), `frameTransportHomotopy W γ` is a continuous family on
   `[0, b-a] × ℝ` of `T`-periodic `SO(n+1)`-valued loops connecting
   `frameLoop (sliceFLS a) γ` (at `σ = 0`) to
   `frameLoop (sliceFLS b) (sliceTransport W a b ∘ γ)` (at `σ = b - a`).
   Hence `w(frameLoop (sliceFLS a) γ over T) = w(transported loop over T)` by
   free-homotopy invariance of `w`.
3. `sliceTransport W a b ∘ γ` is a `T`-periodic continuous parametrization of the
   **image orbit** `Vb.orbit (sliceTransport W a b x₀)` (by `sliceTransport_orbit`),
   related to the flow parametrization `Vb.flow` through the flow-box/uniqueness
   machinery of `LevelOrbit`; 4C should either define `w` of an orbit through an
   arbitrary injective periodic parametrization, or add the reparametrization step
   using `TamedField.exists_flowbox` (the transported curve is injective on a minimal
   period since `sliceTransport` is injective on the fiber and flow lines are).
-/


-- @@ L55-55 verbatim
noncomputable section


-- @@ L57-57 verbatim
namespace Submission


-- @@ L59-59 verbatim
open Set Function Metric Module Submodule InnerProductSpace

-- @@ L60-60 verbatim
open scoped RealInnerProductSpace ContDiff Topology Matrix


-- @@ L62-62 verbatim
variable {n : ℕ}


-- @@ L64-64 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L65-65 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L66-66 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L68-68 verbatim
/-! ## A relative-clopen connectedness helper -/


-- @@ L70-96 verbatim
/-- If `A ⊆ S` is nonempty, closed, and relatively open in `S` (in the metric sense),
and `S` is preconnected, then `S ⊆ A`. -/
lemma subset_of_relOpen_closed {α : Type*} [MetricSpace α] {S A : Set α}
    (hS : IsPreconnected S) (hsub : A ⊆ S) (hclosed : IsClosed A)
    (hopen : ∀ z ∈ A, ∃ r > 0, S ∩ Metric.ball z r ⊆ A)
    (hne : A.Nonempty) : S ⊆ A := by
  classical
  choose! rad hradpos hradsub using hopen
  set U : Set α := ⋃ z ∈ A, Metric.ball z (rad z) with hU
  have hUopen : IsOpen U := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hAU : A ⊆ U := fun z hz => Set.mem_biUnion hz (Metric.mem_ball_self (hradpos z hz))
  have hUS : U ∩ S ⊆ A := by
    rintro x ⟨hxU, hxS⟩
    obtain ⟨z, hzA, hxball⟩ := Set.mem_iUnion₂.mp hxU
    exact hradsub z hzA ⟨hxS, hxball⟩
  intro s hs
  by_contra hsA
  have hcover : S ⊆ U ∪ Aᶜ := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl (hAU hxA)
    · exact Or.inr hxA
  obtain ⟨z0, hz0⟩ := hne
  have h1 : (S ∩ U).Nonempty := ⟨z0, hsub hz0, hAU hz0⟩
  have h2 : (S ∩ Aᶜ).Nonempty := ⟨s, hs, hsA⟩
  obtain ⟨w, hwS, hwU, hwA⟩ := hS U Aᶜ hUopen hclosed.isOpen_compl hcover h1 h2
  exact hwA (hUS ⟨hwU, hwS⟩)


-- @@ L98-101 verbatim
/-! ## Gram–Schmidt continuity over a general parameter space

(The versions in `LevelFrame` are stated for families over `ℝ`; the frame homotopy
below needs two parameters, so we redo them over an arbitrary topological space.) -/


-- @@ L103-103 verbatim
variable {m : ℕ}


-- @@ L105-145 verbatim
/-- Gram–Schmidt is continuous along a pointwise linearly independent continuous
family of frames, over any parameter space. -/
lemma continuous_gramSchmidt_family' {X : Type*} [TopologicalSpace X]
    {A : X → Fin m → EuclideanSpace ℝ (Fin m)}
    (hA : ∀ i, Continuous fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t)) (i : Fin m) :
    Continuous fun t => gramSchmidt ℝ (A t) i := by
  have key : ∀ N : ℕ, ∀ i : Fin m, (i : ℕ) = N →
      Continuous fun t => gramSchmidt ℝ (A t) i := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro i hi
      have hrw : (fun t => gramSchmidt ℝ (A t) i) = fun t => A t i -
          ∑ j ∈ Finset.Iio i,
            (⟪gramSchmidt ℝ (A t) j, A t i⟫ / ((‖gramSchmidt ℝ (A t) j‖ : ℝ) ^ 2)) •
              gramSchmidt ℝ (A t) j := by
        funext t
        rw [gramSchmidt_def]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [starProjection_singleton]
        norm_num
      rw [hrw]
      apply (hA i).sub
      apply continuous_finsetSum
      intro j hj
      have hjN : (j : ℕ) < N := by
        have h1 : j < i := Finset.mem_Iio.mp hj
        have h2 : (j : ℕ) < (i : ℕ) := h1
        omega
      have hcj : Continuous fun t => gramSchmidt ℝ (A t) j := IH (j : ℕ) hjN j rfl
      have hdiv : Continuous fun t =>
          ⟪gramSchmidt ℝ (A t) j, A t i⟫ / ‖gramSchmidt ℝ (A t) j‖ ^ 2 := by
        apply Continuous.div
        · exact hcj.inner (hA i)
        · exact (hcj.norm).pow 2
        · intro t
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hInd t)))
      exact hdiv.smul hcj
  exact key (i : ℕ) i rfl


-- @@ L147-164 verbatim
/-- Normalized Gram–Schmidt is continuous along a pointwise independent continuous
family of frames, over any parameter space. -/
lemma continuous_gramSchmidtNormed_family' {X : Type*} [TopologicalSpace X]
    {A : X → Fin m → EuclideanSpace ℝ (Fin m)}
    (hA : ∀ i, Continuous fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t)) (i : Fin m) :
    Continuous fun t => gramSchmidtNormed ℝ (A t) i := by
  have hgs := continuous_gramSchmidt_family' hA hInd i
  have hnorm : Continuous fun t => ‖gramSchmidt ℝ (A t) i‖⁻¹ :=
    (hgs.norm).inv₀ fun t =>
      norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i (hInd t))
  have heq : (fun t => gramSchmidtNormed ℝ (A t) i)
      = fun t => ‖gramSchmidt ℝ (A t) i‖⁻¹ • gramSchmidt ℝ (A t) i := by
    funext t
    rw [gramSchmidtNormed]
    norm_num
  rw [heq]
  exact hnorm.smul hgs


-- @@ L166-166 verbatim
/-! ## The slab fiber -/


-- @@ L168-170 verbatim
/-- The part of the fiber with time coordinate in `[a, b]`. -/
def slabFiber (C : LevelCobordismData n) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
  C.fiber ∩ tcoord ⁻¹' Icc a b


-- @@ L172-199 verbatim
lemma isCompact_slabFiber (C : LevelCobordismData n) (a b : ℝ) :
    IsCompact (slabFiber C a b) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact C.isClosed_fiber.inter (isClosed_Icc.preimage continuous_tcoord)
  · obtain ⟨R, hR⟩ := C.spatial_bounded
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|R| + |a| + |b|, fun v hv => ?_⟩
    have hspace : ‖spacePart v‖ ≤ |R| :=
      (hR v hv.1).trans (le_abs_self R)
    have htime : |tcoord v| ≤ |a| + |b| := by
      rw [abs_le]
      constructor
      · have ha := neg_abs_le a
        have habs := abs_nonneg b
        linarith [hv.2.1]
      · have hb := le_abs_self b
        have haabs := abs_nonneg a
        linarith [hv.2.2]
    calc
      ‖v‖ = ‖cobSpaceTime (spacePart v) (tcoord v)‖ := by
        rw [spaceTime_spacePart]
      _ = ‖spaceInclL (spacePart v) + tcoord v • timeVec‖ := by
        rw [spaceTime_eq]
      _ ≤ ‖spaceInclL (spacePart v)‖ + ‖tcoord v • timeVec‖ := norm_add_le _ _
      _ = ‖spacePart v‖ + |tcoord v| := by
        rw [norm_spaceInclL, norm_smul, norm_timeVec, mul_one, Real.norm_eq_abs]
      _ ≤ |R| + (|a| + |b|) := add_le_add hspace htime
      _ = |R| + |a| + |b| := by ring


-- @@ L201-205 verbatim
lemma slabFiber_subset_slabRegularSet (C : LevelCobordismData n) {a b : ℝ}
    (hreg : regularSlab C.G a b) :
    slabFiber C a b ⊆ slabRegularSet C.G := by
  rintro v ⟨hf, ht⟩
  exact C.mem_slabRegularSet hf (hreg.sliceRegular ht)


-- @@ L207-207 verbatim
/-! ## The tamed time field -/


-- @@ L209-226 verbatim
/-- A tamed version of the time-flow field: a globally smooth, compactly supported,
globally bounded and Lipschitz vector field agreeing with `timeField` on a
`δ`-neighbourhood of the slab fiber, that neighbourhood being slab-regular, and
annihilating `fderiv C.G` everywhere. -/
structure SlabTamedField (C : LevelCobordismData n) (a b : ℝ) where
  /-- The vector field. -/
  w : EuclideanSpace ℝ (Fin (n + 2)) → EuclideanSpace ℝ (Fin (n + 2))
  /-- Radius of the collar around the slab fiber on which `w` equals `timeField`. -/
  delta : ℝ
  delta_pos : 0 < delta
  smooth : ContDiff ℝ ∞ w
  /-- A global bound for the field. -/
  bound : NNReal
  norm_le : ∀ x, ‖w x‖ ≤ bound
  eq_time : ∀ x ∈ Metric.cthickening delta (slabFiber C a b), w x = timeField C.G x
  subset_slabRegular : Metric.cthickening delta (slabFiber C a b) ⊆ slabRegularSet C.G
  fderiv_zero : ∀ x, fderiv ℝ C.G x (w x) = 0
  lipschitz : ∃ K : NNReal, LipschitzWith K w


-- @@ L228-336 verbatim
/-- Construction of a tamed time field over a regular slab, via a smooth Urysohn
cutoff. -/
theorem exists_slabTamedField (C : LevelCobordismData n) {a b : ℝ}
    (hreg : regularSlab C.G a b) : Nonempty (SlabTamedField C a b) := by
  -- choose a collar inside the slab-regular set
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    (isCompact_slabFiber C a b).exists_cthickening_subset_open
      (isOpen_slabRegularSet C.smooth) (slabFiber_subset_slabRegularSet C hreg)
  set δ := δ₂ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have h2δ : 2 * δ = δ₂ := by rw [hδdef]; ring
  have hsub : Metric.cthickening (2 * δ) (slabFiber C a b) ⊆ slabRegularSet C.G := by
    rw [h2δ]; exact hδ₂sub
  -- smooth Urysohn function: 0 outside the collar, 1 near the slab fiber
  have hs : IsClosed (Metric.thickening (2 * δ) (slabFiber C a b))ᶜ :=
    Metric.isOpen_thickening.isClosed_compl
  have ht : IsClosed (Metric.cthickening δ (slabFiber C a b)) := Metric.isClosed_cthickening
  have hd : Disjoint (Metric.thickening (2 * δ) (slabFiber C a b))ᶜ
      (Metric.cthickening δ (slabFiber C a b)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.cthickening_subset_thickening' (by positivity) (by linarith) _ hx')
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + 2))))
      (n := (⊤ : ℕ∞)) hs ht hd
  have hχ : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  -- smoothness of the field
  have hsmooth : ContDiff ℝ ∞ fun x => f x • timeField C.G x := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ slabRegularSet C.G
    · exact hχ.contDiffAt.smul (contDiffAt_timeField C.smooth hx)
    · -- outside the slab-regular set the field vanishes on a neighbourhood
      have hxC : x ∈ (Metric.cthickening (2 * δ) (slabFiber C a b))ᶜ := fun hmem =>
        hx (hsub hmem)
      have hU : IsOpen (Metric.cthickening (2 * δ) (slabFiber C a b))ᶜ :=
        Metric.isClosed_cthickening.isOpen_compl
      have hzero : ∀ y ∈ (Metric.cthickening (2 * δ) (slabFiber C a b))ᶜ,
          f y • timeField C.G y = 0 := by
        intro y hy
        have hy' : y ∈ (Metric.thickening (2 * δ) (slabFiber C a b))ᶜ := fun hmem =>
          hy (Metric.thickening_subset_cthickening _ _ hmem)
        have hfy : f y = 0 := hf0 hy'
        rw [hfy, zero_smul]
      have hev : (fun y => f y • timeField C.G y) =ᶠ[𝓝 x] (fun _ => (0 : E')) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hxC) hzero
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq hev
  -- compact support
  have hsupp : HasCompactSupport fun x => f x • timeField C.G x := by
    have h1 : support (fun x => f x • timeField C.G x) ⊆
        Metric.thickening (2 * δ) (slabFiber C a b) := by
      intro x hx
      by_contra hmem
      have hfx : f x = 0 := hf0 hmem
      apply hx
      show f x • timeField C.G x = 0
      rw [hfx, zero_smul]
    have h2 : tsupport (fun x => f x • timeField C.G x) ⊆
        Metric.cthickening (2 * δ) (slabFiber C a b) :=
      closure_minimal (h1.trans (Metric.thickening_subset_cthickening _ _))
        Metric.isClosed_cthickening
    exact IsCompact.of_isClosed_subset ((isCompact_slabFiber C a b).cthickening)
      isClosed_closure h2
  -- a bound for the field
  have hcont : ContinuousOn (timeField C.G)
      (Metric.cthickening (2 * δ) (slabFiber C a b)) := fun x hx =>
    (contDiffAt_timeField C.smooth (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ :=
    ((isCompact_slabFiber C a b).cthickening).exists_bound_of_continuousOn hcont
  -- the tamed field
  refine ⟨⟨fun x => f x • timeField C.G x, δ, hδpos, hsmooth, Real.toNNReal M, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- norm bound
    intro x
    by_cases hx : x ∈ Metric.cthickening (2 * δ) (slabFiber C a b)
    · have h1 : ‖f x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hf01 x).1], (hf01 x).2⟩
      calc ‖f x • timeField C.G x‖ = ‖f x‖ * ‖timeField C.G x‖ := norm_smul _ _
        _ ≤ 1 * M := by
            apply mul_le_mul h1 (hM x hx) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
        _ ≤ Real.toNNReal M := Real.le_coe_toNNReal M
    · have hy' : x ∈ (Metric.thickening (2 * δ) (slabFiber C a b))ᶜ := fun hmem =>
        hx (Metric.thickening_subset_cthickening _ _ hmem)
      have hfx : f x = 0 := hf0 hy'
      rw [hfx, zero_smul, norm_zero]
      exact (Real.toNNReal M).coe_nonneg
  · -- equality with `timeField` near the slab fiber
    intro x hx
    have hfx : f x = 1 := hf1 hx
    rw [hfx, one_smul]
  · -- the collar is slab-regular
    intro x hx
    apply hsub
    exact Metric.cthickening_mono (by linarith) _ hx
  · -- the field lies in the kernel of `fderiv C.G` everywhere
    intro x
    by_cases hx : x ∈ Metric.cthickening (2 * δ) (slabFiber C a b)
    · have hxr : x ∈ slabRegularSet C.G := hsub hx
      rw [map_smul, fderiv_timeField hxr.1, smul_zero]
    · have hy' : x ∈ (Metric.thickening (2 * δ) (slabFiber C a b))ᶜ := fun hmem =>
        hx (Metric.thickening_subset_cthickening _ _ hmem)
      have hfx : f x = 0 := hf0 hy'
      rw [hfx, zero_smul, map_zero]
  · -- Lipschitz, via compact support
    exact hsmooth.lipschitzWith_of_hasCompactSupport hsupp (by simp)


-- @@ L338-338 verbatim
/-! ## Global flow of a tamed time field -/


-- @@ L340-340 verbatim
namespace SlabTamedField


-- @@ L342-342 verbatim
variable {C : LevelCobordismData n} {a b : ℝ} (W : SlabTamedField C a b)


-- @@ L344-352 verbatim
/-- Global uniqueness for solutions of the tamed ODE. -/
theorem solution_unique {γ₁ γ₂ : ℝ → EuclideanSpace ℝ (Fin (n + 2))}
    (h₁ : ∀ t, HasDerivAt γ₁ (W.w (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (W.w (γ₂ t)) t)
    {t₀ : ℝ} (heq : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  obtain ⟨K, hK⟩ := W.lipschitz
  exact ODE_solution_unique_univ (v := fun _ x => W.w x) (s := fun _ => univ)
    (t₀ := t₀) (fun _ => hK.lipschitzOnWith)
    (fun t => ⟨h₁ t, mem_univ _⟩) (fun t => ⟨h₂ t, mem_univ _⟩) heq


-- @@ L354-439 verbatim
/-- Global existence for the tamed ODE: the field is bounded and globally Lipschitz,
so Picard–Lindelöf solutions on arbitrarily large intervals can be glued. -/
theorem exists_solution (p : EuclideanSpace ℝ (Fin (n + 2))) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 2)),
      γ 0 = p ∧ ∀ t, HasDerivAt γ (W.w (γ t)) t := by
  obtain ⟨K, hK⟩ := W.lipschitz
  -- solutions on `Ioo (-(T+1)) (T+1)` for every `T : ℕ`
  have main : ∀ T : ℕ, ∃ α : ℝ → EuclideanSpace ℝ (Fin (n + 2)),
      α 0 = p ∧ ∀ t ∈ Ioo (-(T + 1 : ℝ)) (T + 1 : ℝ), HasDerivAt α (W.w (α t)) t := by
    intro T
    have h0mem : (0 : ℝ) ∈ Icc (-(T + 1 : ℝ)) (T + 1 : ℝ) := by
      constructor
      · have h0T : (0 : ℝ) ≤ T := T.cast_nonneg
        linarith
      · have h0T : (0 : ℝ) ≤ T := T.cast_nonneg
        linarith
    have hpl : IsPicardLindelof (fun (_ : ℝ) x => W.w x)
        (⟨0, h0mem⟩ : Icc (-(T + 1 : ℝ)) (T + 1 : ℝ)) p
        (W.bound * ((T : NNReal) + 2)) 0 W.bound K := by
      constructor
      · exact fun t _ => hK.lipschitzOnWith
      · exact fun x _ => continuousOn_const
      · intro t _ x _
        simpa using W.norm_le x
      · show (W.bound : ℝ) * max ((T + 1 : ℝ) - 0) (0 - -(T + 1 : ℝ))
          ≤ ((W.bound * ((T : NNReal) + 2) : NNReal) : ℝ) - ((0 : NNReal) : ℝ)
        have h1 : max ((T + 1 : ℝ) - 0) (0 - -(T + 1 : ℝ)) = (T + 1 : ℝ) := by
          rw [sub_zero, zero_sub, neg_neg, max_self]
        rw [h1]
        push_cast
        have hb : (0 : ℝ) ≤ (W.bound : ℝ) := W.bound.coe_nonneg
        nlinarith
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (mem_closedBall_self le_rfl)
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose α hα0 hαs using main
  -- any two of the local solutions agree on the common interval
  have agree : ∀ (T S : ℕ) (t : ℝ), |t| < T + 1 → |t| < S + 1 → α T t = α S t := by
    intro T S t hT hS
    set m' : ℕ := min T S with hm
    have hmT : (m' : ℝ) + 1 ≤ (T : ℝ) + 1 := by
      have h1 : (m' : ℕ) ≤ T := min_le_left T S
      exact_mod_cast by omega
    have hmS : (m' : ℝ) + 1 ≤ (S : ℝ) + 1 := by
      have h1 : (m' : ℕ) ≤ S := min_le_right T S
      exact_mod_cast by omega
    have htm : |t| < (m' : ℝ) + 1 := by
      rcases min_choice T S with h | h <;> rw [hm, h]
      · exact hT
      · exact hS
    have hsub : Ioo (-(m' + 1 : ℝ)) (m' + 1 : ℝ) ⊆ Ioo (-(T + 1 : ℝ)) (T + 1 : ℝ) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have hsub' : Ioo (-(m' + 1 : ℝ)) (m' + 1 : ℝ) ⊆ Ioo (-(S + 1 : ℝ)) (S + 1 : ℝ) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have h0m : (0 : ℝ) ∈ Ioo (-(m' + 1 : ℝ)) (m' + 1 : ℝ) := by
      constructor
      · have h0 : (0 : ℝ) ≤ m' := m'.cast_nonneg
        linarith
      · have h0 : (0 : ℝ) ≤ m' := m'.cast_nonneg
        linarith
    have huniq := ODE_solution_unique_of_mem_Ioo (v := fun (_ : ℝ) x => W.w x)
      (s := fun _ => univ) (K := K)
      (fun t _ => hK.lipschitzOnWith) h0m
      (fun u hu => ⟨hαs T u (hsub hu), mem_univ _⟩)
      (fun u hu => ⟨hαs S u (hsub' hu), mem_univ _⟩)
      ((hα0 T).trans (hα0 S).symm)
    exact huniq ⟨(abs_lt.mp htm).1, (abs_lt.mp htm).2⟩
  -- glue: at time `t` use the solution with index `⌊|t|⌋`
  refine ⟨fun t => α (Nat.floor |t|) t, ?_, ?_⟩
  · simpa using hα0 (Nat.floor |(0 : ℝ)|)
  · intro t
    set N : ℕ := Nat.floor |t| with hN
    have htN : |t| < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hev : (fun s => α (Nat.floor |s|) s) =ᶠ[𝓝 t] α N := by
      have hUopen : IsOpen {s : ℝ | |s| < (N : ℝ) + 1} :=
        isOpen_lt (continuous_abs) continuous_const
      refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds htN) fun s hs => ?_
      exact agree (Nat.floor |s|) N s (Nat.lt_floor_add_one _) hs
    have hder : HasDerivAt (α N) (W.w (α N t)) t := by
      apply hαs N t
      have habs := abs_lt.mp htN
      exact ⟨habs.1, habs.2⟩
    have hda : HasDerivAt (fun s => α (Nat.floor |s|) s) (W.w (α N t)) t :=
      (Filter.EventuallyEq.hasDerivAt_iff hev).mpr hder
    simpa [← hN] using hda


-- @@ L441-443 verbatim
/-- The canonical global solution through `p`. -/
def flow (p : EuclideanSpace ℝ (Fin (n + 2))) : ℝ → EuclideanSpace ℝ (Fin (n + 2)) :=
  Classical.choose (W.exists_solution p)


-- @@ L445-446 verbatim
@[simp] lemma flow_zero (p : EuclideanSpace ℝ (Fin (n + 2))) : W.flow p 0 = p :=
  (Classical.choose_spec (W.exists_solution p)).1


-- @@ L448-450 verbatim
lemma hasDerivAt_flow (p : EuclideanSpace ℝ (Fin (n + 2))) (t : ℝ) :
    HasDerivAt (W.flow p) (W.w (W.flow p t)) t :=
  (Classical.choose_spec (W.exists_solution p)).2 t


-- @@ L452-453 verbatim
lemma continuous_flow (p : EuclideanSpace ℝ (Fin (n + 2))) : Continuous (W.flow p) :=
  continuous_iff_continuousAt.mpr fun t => (W.hasDerivAt_flow p t).continuousAt


-- @@ L455-474 verbatim
/-- Invariance: a solution of the tamed ODE starting on the fiber stays on the fiber
(the value of `C.G` is constant along any solution). -/
theorem solution_mem_fiber {γ : ℝ → EuclideanSpace ℝ (Fin (n + 2))}
    (hγ : ∀ t, HasDerivAt γ (W.w (γ t)) t) (h0 : γ 0 ∈ C.fiber) :
    ∀ t, γ t ∈ C.fiber := by
  have hcomp : ∀ t, HasDerivAt (fun s => C.G (γ s)) 0 t := by
    intro t
    have hgdiff : HasFDerivAt C.G (fderiv ℝ C.G (γ t)) (γ t) :=
      (C.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h1 := hgdiff.comp_hasDerivAt t (hγ t)
    rwa [W.fderiv_zero (γ t)] at h1
  have hconst : ∀ t, C.G (γ t) = C.G (γ 0) := by
    intro t
    exact is_const_of_deriv_eq_zero
      (fun s => (hcomp s).differentiableAt)
      (fun s => (hcomp s).deriv) t 0
  intro t
  have h2 := hconst t
  rw [show C.G (γ 0) = 0 from h0] at h2
  exact h2


-- @@ L476-478 verbatim
lemma flow_mem_fiber {p : EuclideanSpace ℝ (Fin (n + 2))} (hp : p ∈ C.fiber) (t : ℝ) :
    W.flow p t ∈ C.fiber :=
  W.solution_mem_fiber (W.hasDerivAt_flow p) (by rw [W.flow_zero]; exact hp) t


-- @@ L480-486 verbatim
/-- Time-shifts of solutions are solutions. -/
lemma hasDerivAt_shift {γ : ℝ → EuclideanSpace ℝ (Fin (n + 2))}
    (hγ : ∀ t, HasDerivAt γ (W.w (γ t)) t) (c : ℝ) (u : ℝ) :
    HasDerivAt (fun z => γ (c + z)) (W.w (γ (c + u))) u := by
  have h1 : HasDerivAt (fun z : ℝ => c + z) 1 u := (hasDerivAt_id u).const_add c
  have h2 := (hγ (c + u)).scomp u h1
  simpa [Function.comp_def] using h2


-- @@ L488-494 verbatim
/-- The flow shifted in time is the flow of the shifted starting point. -/
lemma flow_shift (p : EuclideanSpace ℝ (Fin (n + 2))) (c : ℝ) :
    W.flow (W.flow p c) = fun u => W.flow p (c + u) := by
  apply W.solution_unique (t₀ := 0)
  · exact W.hasDerivAt_flow (W.flow p c)
  · exact fun u => W.hasDerivAt_shift (W.hasDerivAt_flow p) c u
  · simp


-- @@ L496-496 verbatim
/-! ## Grönwall: Lipschitz dependence on the initial condition -/


-- @@ L498-539 verbatim
/-- Distance between flow lines grows at most exponentially. -/
lemma dist_flow_flow_le {K : NNReal} (hK : LipschitzWith K W.w)
    (p q : EuclideanSpace ℝ (Fin (n + 2))) (s : ℝ) :
    dist (W.flow p s) (W.flow q s) ≤ dist p q * Real.exp (K * |s|) := by
  rcases le_or_gt 0 s with hs | hs
  · have h := dist_le_of_trajectories_ODE (v := fun (_ : ℝ) x => W.w x) (K := K)
      (fun _ => hK)
      ((W.continuous_flow p).continuousOn : ContinuousOn (W.flow p) (Icc 0 s))
      (fun t _ => (W.hasDerivAt_flow p t).hasDerivWithinAt)
      ((W.continuous_flow q).continuousOn : ContinuousOn (W.flow q) (Icc 0 s))
      (fun t _ => (W.hasDerivAt_flow q t).hasDerivWithinAt)
      (by simp : dist (W.flow p 0) (W.flow q 0) ≤ dist p q)
      s ⟨hs, le_refl s⟩
    rwa [sub_zero, abs_of_nonneg hs] at *
    -- (the `rwa at *` also normalizes `s - 0` inside `h`)
  · -- reverse time: the backward flows solve the ODE for `-w`
    have hKn : LipschitzWith K fun x => -W.w x :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_neg_neg]; exact hK.dist_le_mul x y
    have htraj : ∀ (r : EuclideanSpace ℝ (Fin (n + 2))) (t : ℝ),
        HasDerivAt (fun z => W.flow r (-z)) (-W.w (W.flow r (-t))) t := by
      intro r t
      have h1 : HasDerivAt (fun z : ℝ => -z) (-1) t := (hasDerivAt_id t).neg
      have h2 := (W.hasDerivAt_flow r (-t)).scomp t h1
      have h3 : HasDerivAt (fun z => W.flow r (-z))
          ((-1 : ℝ) • W.w (W.flow r (-t))) t := h2
      have h4 : ((-1 : ℝ) • W.w (W.flow r (-t))) = -W.w (W.flow r (-t)) :=
        neg_one_smul ℝ _
      rw [h4] at h3
      exact h3
    have h := dist_le_of_trajectories_ODE (v := fun (_ : ℝ) x => -W.w x) (K := K)
      (fun _ => hKn)
      (f := fun z => W.flow p (-z))
      ((W.continuous_flow p).comp continuous_neg).continuousOn
      (fun t _ => (htraj p t).hasDerivWithinAt)
      (g := fun z => W.flow q (-z))
      ((W.continuous_flow q).comp continuous_neg).continuousOn
      (fun t _ => (htraj q t).hasDerivWithinAt)
      (by simp : dist (W.flow p (-(0 : ℝ))) (W.flow q (-(0 : ℝ))) ≤ dist p q)
      (-s) ⟨by linarith, le_refl (-s)⟩
    rw [neg_neg, sub_zero] at h
    rwa [abs_of_neg hs]


-- @@ L541-552 verbatim
/-- The time-`s` flow map is Lipschitz. -/
lemma lipschitzWith_flow_apply {K : NNReal} (hK : LipschitzWith K W.w) (s : ℝ) :
    LipschitzWith (Real.toNNReal (Real.exp (K * |s|))) (fun p => W.flow p s) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  calc dist (W.flow p s) (W.flow q s) ≤ dist p q * Real.exp (K * |s|) :=
        W.dist_flow_flow_le hK p q s
    _ = Real.exp (K * |s|) * dist p q := mul_comm _ _
    _ ≤ Real.toNNReal (Real.exp (K * |s|)) * dist p q := by
        have h1 : Real.exp (K * |s|) ≤ Real.toNNReal (Real.exp (K * |s|)) :=
          Real.le_coe_toNNReal _
        exact mul_le_mul_of_nonneg_right h1 dist_nonneg


-- @@ L554-556 verbatim
lemma continuous_flow_apply (s : ℝ) : Continuous (fun p => W.flow p s) := by
  obtain ⟨K, hK⟩ := W.lipschitz
  exact (W.lipschitzWith_flow_apply hK s).continuous


-- @@ L558-578 verbatim
/-- The flow is Lipschitz in time, with constant the field bound. -/
lemma dist_flow_self_le (p : EuclideanSpace ℝ (Fin (n + 2))) (s s' : ℝ) :
    dist (W.flow p s) (W.flow p s') ≤ (W.bound : ℝ) * |s - s'| := by
  -- MVT with the global speed bound, on the segment between `s'` and `s`
  have key : ∀ u u' : ℝ, u' ≤ u →
      ‖W.flow p u - W.flow p u'‖ ≤ (W.bound : ℝ) * (u - u') := by
    intro u u' huu
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := W.flow p) (f' := fun z => W.w (W.flow p z)) (a := u') (b := u)
      (C := (W.bound : ℝ))
      (fun z _ => (W.hasDerivAt_flow p z).hasDerivWithinAt)
      (fun z _ => W.norm_le _)
      u ⟨huu, le_refl u⟩
    exact h
  rcases le_total s' s with h | h
  · rw [dist_eq_norm, abs_of_nonneg (by linarith : (0:ℝ) ≤ s - s')]
    exact key s s' h
  · rw [dist_comm, dist_eq_norm, abs_of_nonpos (by linarith : s - s' ≤ 0)]
    have h1 := key s' s h
    calc ‖W.flow p s' - W.flow p s‖ ≤ (W.bound : ℝ) * (s' - s) := h1
      _ = (W.bound : ℝ) * -(s - s') := by ring


-- @@ L580-629 verbatim
/-- Joint continuity of the flow in (initial point, time). -/
lemma continuous_flow_uncurry :
    Continuous fun q : EuclideanSpace ℝ (Fin (n + 2)) × ℝ => W.flow q.1 q.2 := by
  obtain ⟨K, hK⟩ := W.lipschitz
  rw [Metric.continuous_iff]
  rintro ⟨p₀, s₀⟩ ε hε
  set M := Real.exp ((K : ℝ) * (|s₀| + 1)) with hM
  have hMpos : 0 < M := Real.exp_pos _
  set D : ℝ := M + (W.bound : ℝ) + 1 with hD
  have hDpos : 0 < D := by
    have h1 := W.bound.coe_nonneg
    have h2 := hMpos
    rw [hD]; linarith
  refine ⟨min 1 (ε / D), lt_min one_pos (by positivity), ?_⟩
  rintro ⟨p, s⟩ hdist
  have hpair : max (dist p p₀) (dist s s₀) < min 1 (ε / D) := by
    rw [Prod.dist_eq] at hdist
    exact hdist
  have hd1 : dist p p₀ < min 1 (ε / D) := lt_of_le_of_lt (le_max_left _ _) hpair
  have hd2 : dist s s₀ < min 1 (ε / D) := lt_of_le_of_lt (le_max_right _ _) hpair
  have habs : |s - s₀| < min 1 (ε / D) := by
    rw [← Real.dist_eq]
    exact hd2
  have hs1 : |s| ≤ |s₀| + 1 := by
    have h1 : |s - s₀| < 1 := lt_of_lt_of_le habs (min_le_left _ _)
    have h2 : |s| - |s₀| ≤ |s - s₀| := abs_sub_abs_le_abs_sub s s₀
    linarith
  have hexp : Real.exp ((K : ℝ) * |s|) ≤ M := by
    rw [hM]
    apply Real.exp_le_exp.mpr
    have hKnn := K.coe_nonneg
    nlinarith
  have hεD1 : dist p p₀ ≤ ε / D := le_of_lt (lt_of_lt_of_le hd1 (min_le_right _ _))
  have hεD2 : |s - s₀| ≤ ε / D := le_of_lt (lt_of_lt_of_le habs (min_le_right _ _))
  calc dist (W.flow p s) (W.flow p₀ s₀)
      ≤ dist (W.flow p s) (W.flow p₀ s) + dist (W.flow p₀ s) (W.flow p₀ s₀) :=
        dist_triangle _ _ _
    _ ≤ dist p p₀ * Real.exp ((K : ℝ) * |s|) + (W.bound : ℝ) * |s - s₀| :=
        add_le_add (W.dist_flow_flow_le hK p p₀ s) (W.dist_flow_self_le p₀ s s₀)
    _ ≤ (ε / D) * M + (W.bound : ℝ) * (ε / D) := by
        apply add_le_add
        · exact mul_le_mul hεD1 hexp (le_of_lt (Real.exp_pos _)) (by positivity)
        · exact mul_le_mul_of_nonneg_left hεD2 W.bound.coe_nonneg
    _ = (ε / D) * (M + (W.bound : ℝ)) := by ring
    _ < ε := by
        have h3 : M + (W.bound : ℝ) < D := by rw [hD]; linarith
        have h4 : (ε / D) * (M + (W.bound : ℝ)) < (ε / D) * D :=
          mul_lt_mul_of_pos_left h3 (by positivity)
        have h5 : (ε / D) * D = ε := div_mul_cancel₀ ε (ne_of_gt hDpos)
        linarith


-- @@ L631-631 verbatim
end SlabTamedField


-- @@ L633-633 verbatim
end Submission
