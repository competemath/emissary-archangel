import Mathlib
import Submission.SmallAmbientDisplacementIsotopy


-- @@ L4-27 verbatim
/-!
# Tubes around arbitrary smoothly framed periodic circles

This file isolates the differential-topological engine used by the orbit
normalization construction.  Its input is an arbitrary smooth period-one
embedded circle in Euclidean space, equipped with a smooth period-one
orthonormal frame.  The derivative of the real lift is required to be a
positive multiple of the first frame vector.

From these hypotheses we construct:

* a framed tube on `ℝ × ℝⁿ` and its quotient on
  `AddCircle 1 × ℝⁿ`;
* an inverse-function-theorem chart at every point of the zero section;
* one positive radius on which the quotient tube is globally embedded and
  its derivative is everywhere invertible;
* a global inverse on the tube image, with compatible smooth real-phase
  inverse germs;
* a compactly supported smooth extension of every smooth period-one
  displacement, localized by a radial bump.

Thus the construction depends only on a framed embedded circle, not on the
ambient tamed-field or orbit machinery which originally supplied one.
-/


-- @@ L29-29 verbatim
set_option autoImplicit false

-- @@ L30-30 verbatim
set_option maxHeartbeats 2000000


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
open Set Function Module Finset InnerProductSpace Metric Filter

-- @@ L35-35 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L37-37 verbatim
namespace Submission


-- @@ L39-39 verbatim
local notation "E[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L40-40 verbatim
local notation "N[" n "]" => EuclideanSpace ℝ (Fin n)

-- @@ L41-41 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L43-59 verbatim
/-- An arbitrary smoothly framed period-one embedded circle.  The positive
speed equation fixes the orientation of the first frame vector. -/
structure SmoothFramedPeriodicCircle (n : ℕ) where
  lift : ℝ → E[n]
  circle : C → E[n]
  smooth_lift : ContDiff ℝ ∞ lift
  periodic_lift : Function.Periodic lift 1
  circle_coe : ∀ u : ℝ, circle (u : C) = lift u
  isEmbedding_circle : Topology.IsEmbedding circle
  frame : ℝ → Fin (n + 1) → E[n]
  smooth_frame : ∀ i, ContDiff ℝ ∞ (fun u => frame u i)
  periodic_frame : ∀ i, Function.Periodic (fun u => frame u i) 1
  orthonormal_frame : ∀ u, Orthonormal ℝ (frame u)
  speed : ℝ → ℝ
  smooth_speed : ContDiff ℝ ∞ speed
  speed_pos : ∀ u, 0 < speed u
  hasDerivAt_lift : ∀ u, HasDerivAt lift (speed u • frame u 0) u


-- @@ L61-61 verbatim
namespace SmoothFramedPeriodicCircle


-- @@ L63-63 verbatim
variable {n : ℕ} (F : SmoothFramedPeriodicCircle n)


-- @@ L65-65 verbatim
/-! ## The lifted and quotient tubes -/


-- @@ L67-68 verbatim
/-- The `j`-th normal vector of the chosen frame. -/
def normal (j : Fin n) (u : ℝ) : E[n] := F.frame u j.succ


-- @@ L70-71 verbatim
theorem smooth_normal (j : Fin n) : ContDiff ℝ ∞ (F.normal j) :=
  F.smooth_frame j.succ


-- @@ L73-75 verbatim
theorem periodic_normal (j : Fin n) :
    Function.Periodic (F.normal j) 1 :=
  F.periodic_frame j.succ


-- @@ L77-79 verbatim
/-- The framed tube before descending the phase modulo one. -/
def tubeLift (q : ℝ × N[n]) : E[n] :=
  F.lift q.1 + ∑ j : Fin n, q.2 j • F.normal j q.1


-- @@ L81-86 verbatim
theorem smooth_tubeLift : ContDiff ℝ ∞ F.tubeLift := by
  apply F.smooth_lift.comp contDiff_fst |>.add
  apply ContDiff.sum
  intro j _
  exact ((EuclideanSpace.proj j).contDiff.comp contDiff_snd).smul
    ((F.smooth_normal j).comp contDiff_fst)


-- @@ L88-90 verbatim
@[simp] theorem tubeLift_zero (u : ℝ) :
    F.tubeLift (u, 0) = F.lift u := by
  simp [tubeLift]


-- @@ L92-100 verbatim
theorem periodic_tubeLift (z : N[n]) :
    Function.Periodic (fun u => F.tubeLift (u, z)) 1 := by
  intro u
  simp only [tubeLift]
  rw [F.periodic_lift u]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [F.periodic_normal j u]


-- @@ L102-104 verbatim
/-- The framed tube descended to `AddCircle 1 × ℝⁿ`. -/
def tube (q : C × N[n]) : E[n] :=
  (F.periodic_tubeLift q.2).lift q.1


-- @@ L106-108 verbatim
@[simp] theorem tube_coe (u : ℝ) (z : N[n]) :
    F.tube ((u : C), z) = F.tubeLift (u, z) := by
  simp [tube]


-- @@ L110-115 verbatim
theorem continuous_tube : Continuous F.tube := by
  have hq : IsOpenQuotientMap
      (Prod.map (fun u : ℝ => (u : C)) (id : N[n] → N[n])) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  simpa [Function.comp_def, Prod.map] using F.smooth_tubeLift.continuous


-- @@ L117-119 verbatim
@[simp] theorem tube_zero (a : C) : F.tube (a, 0) = F.circle a := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [F.tube_coe, F.tubeLift_zero, F.circle_coe]


-- @@ L121-121 verbatim
/-! ## Derivative and local inverse-function charts -/


-- @@ L123-129 verbatim
/-- The derivative of the lifted tube on its zero section. -/
def tubeDeriv (u : ℝ) : (ℝ × N[n]) →L[ℝ] E[n] :=
  (ContinuousLinearMap.toSpanSingleton ℝ (F.speed u • F.frame u 0)).comp
      (ContinuousLinearMap.fst ℝ ℝ N[n]) +
    ∑ j : Fin n,
      (((EuclideanSpace.proj j).comp
        (ContinuousLinearMap.snd ℝ ℝ N[n])).smulRight (F.normal j u))


-- @@ L131-135 verbatim
@[simp] theorem tubeDeriv_apply (u a : ℝ) (z : N[n]) :
    F.tubeDeriv u (a, z) =
      a • (F.speed u • F.frame u 0) +
        ∑ j : Fin n, z j • F.normal j u := by
  simp [tubeDeriv]


-- @@ L137-180 verbatim
theorem hasFDerivAt_tubeLift_zero (u : ℝ) :
    HasFDerivAt F.tubeLift (F.tubeDeriv u) (u, 0) := by
  have hfst : HasFDerivAt (fun q : ℝ × N[n] => q.1)
      (ContinuousLinearMap.fst ℝ ℝ N[n]) (u, 0) :=
    hasFDerivAt_fst
  have hbase : HasFDerivAt
      (fun q : ℝ × N[n] => F.lift q.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (F.speed u • F.frame u 0)).comp
        (ContinuousLinearMap.fst ℝ ℝ N[n])) (u, 0) := by
    exact F.hasDerivAt_lift u |>.hasFDerivAt.comp
      (f := fun q : ℝ × N[n] => q.1) (g := F.lift) (u, 0) hfst
  have hnormal' : HasFDerivAt
      (∑ j : Fin n, fun q : ℝ × N[n] =>
        q.2 j • F.normal j q.1)
      (∑ j : Fin n,
        (((EuclideanSpace.proj j).comp
          (ContinuousLinearMap.snd ℝ ℝ N[n])).smulRight
            (F.normal j u))) (u, 0) := by
    apply HasFDerivAt.sum
    intro j _
    have hc := ((EuclideanSpace.proj j).comp
      (ContinuousLinearMap.snd ℝ ℝ N[n])).hasFDerivAt
      (x := (u, (0 : N[n])))
    have hN : HasFDerivAt
        (fun q : ℝ × N[n] => F.normal j q.1)
        (fderiv ℝ (fun q : ℝ × N[n] => F.normal j q.1) (u, 0))
        (u, 0) :=
      ((F.smooth_normal j).comp contDiff_fst).differentiable
        (by simp) (u, 0) |>.hasFDerivAt
    convert hc.smul hN using 1
    · rfl
    · simp
  have hnormal : HasFDerivAt
      (fun q : ℝ × N[n] =>
        ∑ j : Fin n, q.2 j • F.normal j q.1)
      (∑ j : Fin n,
        (((EuclideanSpace.proj j).comp
          (ContinuousLinearMap.snd ℝ ℝ N[n])).smulRight
            (F.normal j u))) (u, 0) := by
    convert hnormal' using 1
    funext q
    simp
  exact hbase.add hnormal


-- @@ L182-231 verbatim
theorem tubeDeriv_bijective (u : ℝ) :
    Function.Bijective (F.tubeDeriv u) := by
  let B : Fin (n + 1) → E[n] := F.frame u
  have hinner : ∀ i j, ⟪B i, B j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp (F.orthonormal_frame u)
  have hinj : Function.Injective (F.tubeDeriv u) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, z⟩ hzero
    have hformula :
        a • (F.speed u • B 0) + ∑ j : Fin n, z j • B j.succ = 0 := by
      simpa [B, normal] using hzero
    have haeq : a * F.speed u = 0 := by
      have h := congrArg (fun x : E[n] => ⟪B 0, x⟫_ℝ) hformula
      simp only [inner_add_right, real_inner_smul_right, inner_sum,
        inner_zero_right] at h
      rw [hinner 0 0] at h
      have hsum : ∑ j : Fin n, z j * ⟪B 0, B j.succ⟫_ℝ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hinner 0 j.succ, if_neg (Ne.symm j.succ_ne_zero)]
        simp
      rw [hsum, add_zero] at h
      simpa [smul_eq_mul] using h
    have ha : a = 0 :=
      (mul_eq_zero.mp haeq).resolve_right (ne_of_gt (F.speed_pos u))
    have hz : z = 0 := by
      ext j
      have h := congrArg (fun x : E[n] => ⟪B j.succ, x⟫_ℝ) hformula
      simp only [inner_add_right, real_inner_smul_right, inner_sum,
        inner_zero_right] at h
      rw [ha, zero_mul, zero_add] at h
      have hsum :
          ∑ k : Fin n, z k * ⟪B j.succ, B k.succ⟫_ℝ = z j := by
        rw [Finset.sum_eq_single j]
        · rw [hinner j.succ j.succ]
          simp
        · intro k _ hkj
          rw [hinner j.succ k.succ]
          rw [if_neg ((Fin.succ_injective n).ne (Ne.symm hkj))]
          simp
        · simp
      rw [hsum] at h
      simpa using h
    exact Prod.ext ha hz
  refine ⟨hinj, ?_⟩
  have hfr : finrank ℝ (ℝ × N[n]) = finrank ℝ E[n] := by
    rw [Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj


-- @@ L233-237 verbatim
/-- The zero-section derivative as a continuous linear equivalence. -/
def tubeDerivEquiv (u : ℝ) : (ℝ × N[n]) ≃L[ℝ] E[n] :=
  (LinearEquiv.ofBijective
      ((F.tubeDeriv u) : (ℝ × N[n]) →ₗ[ℝ] E[n])
      (F.tubeDeriv_bijective u)).toContinuousLinearEquiv


-- @@ L239-243 verbatim
@[simp] theorem tubeDerivEquiv_coe (u : ℝ) :
    (F.tubeDerivEquiv u : (ℝ × N[n]) →L[ℝ] E[n]) = F.tubeDeriv u := by
  apply ContinuousLinearMap.ext
  intro q
  rfl


-- @@ L245-253 verbatim
/-- A local inverse-function-theorem chart at every point of the zero
section. -/
def tubeLocalHomeomorph (u : ℝ) :
    OpenPartialHomeomorph (ℝ × N[n]) E[n] :=
  F.smooth_tubeLift.contDiffAt.toOpenPartialHomeomorph F.tubeLift
    (by
      rw [F.tubeDerivEquiv_coe u]
      exact F.hasFDerivAt_tubeLift_zero u)
    (by simp)


-- @@ L255-256 verbatim
@[simp] theorem tubeLocalHomeomorph_coe (u : ℝ) :
    (F.tubeLocalHomeomorph u : (ℝ × N[n]) → E[n]) = F.tubeLift := rfl


-- @@ L258-265 verbatim
theorem tube_center_mem_localSource (u : ℝ) :
    (u, (0 : N[n])) ∈ (F.tubeLocalHomeomorph u).source := by
  exact F.smooth_tubeLift.contDiffAt
    |>.mem_toOpenPartialHomeomorph_source
      (by
        rw [F.tubeDerivEquiv_coe u]
        exact F.hasFDerivAt_tubeLift_zero u)
      (by simp)


-- @@ L267-270 verbatim
theorem tube_injOn_localSource (u : ℝ) :
    Set.InjOn F.tubeLift (F.tubeLocalHomeomorph u).source := by
  rw [← F.tubeLocalHomeomorph_coe u]
  exact (F.tubeLocalHomeomorph u).injOn


-- @@ L272-272 verbatim
/-! ## Uniform local boxes and global injectivity -/


-- @@ L274-286 verbatim
theorem exists_tube_local_box (u : ℝ) :
    ∃ ε > 0, ∃ r > 0,
      Ioo (u - ε) (u + ε) ×ˢ Metric.ball (0 : N[n]) r ⊆
        (F.tubeLocalHomeomorph u).source := by
  have hnhds : (F.tubeLocalHomeomorph u).source ∈ 𝓝 (u, (0 : N[n])) :=
    (F.tubeLocalHomeomorph u).open_source.mem_nhds
      (F.tube_center_mem_localSource u)
  rcases mem_nhds_prod_iff.mp hnhds with ⟨U, hU, W, hW, hUW⟩
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hεU⟩
  rcases Metric.mem_nhds_iff.mp hW with ⟨r, hr, hrW⟩
  refine ⟨ε, hε, r, hr, ?_⟩
  rw [← Real.ball_eq_Ioo]
  exact (prod_mono hεU hrW).trans hUW


-- @@ L288-296 verbatim
structure TubeLocalBoxData (u : ℝ) where
  phaseRadius : ℝ
  phaseRadius_pos : 0 < phaseRadius
  normalRadius : ℝ
  normalRadius_pos : 0 < normalRadius
  box_subset_source :
    Ioo (u - phaseRadius) (u + phaseRadius) ×ˢ
        Metric.ball (0 : N[n]) normalRadius ⊆
      (F.tubeLocalHomeomorph u).source


-- @@ L298-307 verbatim
theorem nonempty_tubeLocalBoxData (u : ℝ) :
    Nonempty (F.TubeLocalBoxData u) := by
  obtain ⟨ε, hε, r, hr, hbox⟩ := F.exists_tube_local_box u
  exact ⟨{
    phaseRadius := ε
    phaseRadius_pos := hε
    normalRadius := r
    normalRadius_pos := hr
    box_subset_source := hbox
  }⟩


-- @@ L309-310 verbatim
def tubeLocalBoxData (u : ℝ) : F.TubeLocalBoxData u :=
  Classical.choice (F.nonempty_tubeLocalBoxData u)


-- @@ L312-315 verbatim
@[simp] theorem mem_tubeLocalBox_phase (u : ℝ) :
    u ∈ Ioo (u - (F.tubeLocalBoxData u).phaseRadius)
      (u + (F.tubeLocalBoxData u).phaseRadius) := by
  constructor <;> linarith [(F.tubeLocalBoxData u).phaseRadius_pos]


-- @@ L317-321 verbatim
def tubeQuotientBox (u : ℝ) : Set (C × N[n]) :=
  ((fun t : ℝ => (t : C)) '' Ioo
      (u - (F.tubeLocalBoxData u).phaseRadius)
      (u + (F.tubeLocalBoxData u).phaseRadius)) ×ˢ
    Metric.ball (0 : N[n]) (F.tubeLocalBoxData u).normalRadius


-- @@ L323-326 verbatim
theorem isOpen_tubeQuotientBox (u : ℝ) : IsOpen (F.tubeQuotientBox u) := by
  apply IsOpen.prod
  · exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  · exact Metric.isOpen_ball


-- @@ L328-331 verbatim
@[simp] theorem tube_zero_mem_quotientBox (u : ℝ) :
    ((u : C), (0 : N[n])) ∈ F.tubeQuotientBox u := by
  exact ⟨⟨u, F.mem_tubeLocalBox_phase u, rfl⟩,
    Metric.mem_ball_self (F.tubeLocalBoxData u).normalRadius_pos⟩


-- @@ L333-345 verbatim
theorem tube_injOn_quotientBox (u : ℝ) :
    Set.InjOn F.tube (F.tubeQuotientBox u) := by
  rintro ⟨a, z⟩ ⟨⟨ua, hua, rfl⟩, hz⟩
    ⟨b, w⟩ ⟨⟨ub, hub, rfl⟩, hw⟩ heq
  have heqLift : F.tubeLift (ua, z) = F.tubeLift (ub, w) := by
    simpa using heq
  have hmema : (ua, z) ∈ (F.tubeLocalHomeomorph u).source :=
    (F.tubeLocalBoxData u).box_subset_source ⟨hua, hz⟩
  have hmemb : (ub, w) ∈ (F.tubeLocalHomeomorph u).source :=
    (F.tubeLocalBoxData u).box_subset_source ⟨hub, hw⟩
  have hpair := F.tube_injOn_localSource u hmema hmemb heqLift
  cases hpair
  rfl


-- @@ L347-381 verbatim
/-- The quotient tube is injective on one full constant-radius tube around
the compact embedded circle. -/
theorem exists_tube_global_injOn :
    ∃ r > 0, Set.InjOn F.tube
      ((Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) r) := by
  let Z : Set (C × N[n]) := Set.range fun a : C => (a, (0 : N[n]))
  have hZinj : Set.InjOn F.tube Z := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    have hab' : F.circle a = F.circle b := by simpa using hab
    have habase : a = b := F.isEmbedding_circle.injective hab'
    subst b
    rfl
  have hZcompact : IsCompact Z :=
    isCompact_range (continuous_id.prodMk continuous_const)
  have hlocal : ∀ q ∈ Z, ∃ U ∈ 𝓝 q, Set.InjOn F.tube U := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    exact ⟨F.tubeQuotientBox u,
      (F.isOpen_tubeQuotientBox u).mem_nhds (F.tube_zero_mem_quotientBox u),
      F.tube_injOn_quotientBox u⟩
  obtain ⟨T, hTopen, hZT, hTinj⟩ := hZinj.exists_isOpen_superset
    hZcompact (fun _ _ => F.continuous_tube.continuousAt) hlocal
  have hzeroSection : (Set.univ : Set C) ×ˢ ({0} : Set N[n]) ⊆ T := by
    rintro ⟨a, z⟩ ⟨-, hz⟩
    rw [Set.mem_singleton_iff] at hz
    change z = 0 at hz
    subst z
    exact hZT ⟨a, rfl⟩
  obtain ⟨U, W, hUopen, hWopen, hCU, hzeroW, hUWT⟩ :=
    generalized_tube_lemma (X := C) (Y := N[n])
      isCompact_univ isCompact_singleton hTopen hzeroSection
  have hzero_mem_W : (0 : N[n]) ∈ W := hzeroW (Set.mem_singleton 0)
  rcases (Metric.isOpen_iff.mp hWopen) 0 hzero_mem_W with ⟨r, hr, hrW⟩
  refine ⟨r, hr, hTinj.mono ?_⟩
  exact (prod_mono hCU hrW).trans hUWT


-- @@ L383-422 verbatim
/-- After shrinking, the full open tube is an embedded copy of the product. -/
theorem exists_tube_global_embedding :
    ∃ r > 0,
      Set.InjOn F.tube
        ((Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) r) ∧
      Topology.IsEmbedding
        (fun q : ↥((Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) r) =>
          F.tube q.1) := by
  obtain ⟨R, hR, hRinj⟩ := F.exists_tube_global_injOn
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  let Dopen : Set (C × N[n]) :=
    (Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) r
  let Dclosed : Set (C × N[n]) :=
    (Set.univ : Set C) ×ˢ Metric.closedBall (0 : N[n]) r
  have hopenClosed : Dopen ⊆ Dclosed :=
    prod_mono Subset.rfl Metric.ball_subset_closedBall
  have hclosedBig : Dclosed ⊆
      (Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) R :=
    prod_mono Subset.rfl (Metric.closedBall_subset_ball hrR)
  have hinjClosed : Set.InjOn F.tube Dclosed := hRinj.mono hclosedBig
  have hcompact : IsCompact Dclosed :=
    isCompact_univ.prod (isCompact_closedBall (0 : N[n]) r)
  letI : CompactSpace Dclosed := isCompact_iff_compactSpace.mp hcompact
  have hcontClosed : Continuous (fun q : Dclosed => F.tube q.1) :=
    F.continuous_tube.comp continuous_subtype_val
  have hinjClosed' : Function.Injective (fun q : Dclosed => F.tube q.1) := by
    intro p q hpq
    apply Subtype.ext
    exact hinjClosed p.property q.property hpq
  have hembClosed : Topology.IsEmbedding (fun q : Dclosed => F.tube q.1) :=
    (hcontClosed.isClosedEmbedding hinjClosed').isEmbedding
  have hembOpen : Topology.IsEmbedding (fun q : Dopen => F.tube q.1) := by
    simpa [Function.comp_def, Set.inclusion] using
      hembClosed.comp (Topology.IsEmbedding.inclusion hopenClosed)
  refine ⟨r, hr, ?_, ?_⟩
  · exact hRinj.mono (prod_mono Subset.rfl
      (Metric.ball_subset_ball (le_of_lt hrR)))
  · exact hembOpen


-- @@ L424-424 verbatim
/-! ## A uniform derivative radius -/


-- @@ L426-437 verbatim
theorem periodic_fderiv_tubeLift :
    Function.Periodic (fun q : ℝ × N[n] => fderiv ℝ F.tubeLift q)
      ((1 : ℝ), (0 : N[n])) := by
  have hfun :
      (fun q : ℝ × N[n] => F.tubeLift (q + ((1 : ℝ), (0 : N[n])))) =
      F.tubeLift := by
    funext q
    rcases q with ⟨u, z⟩
    simpa only [Prod.mk_add_mk, add_zero] using F.periodic_tubeLift z u
  intro q
  have h := congrArg (fun f : (ℝ × N[n]) → E[n] => fderiv ℝ f q) hfun
  simpa only [fderiv_comp_add_right] using h


-- @@ L439-444 verbatim
theorem isOpen_tubeLift_regularSet :
    IsOpen ((fderiv ℝ F.tubeLift) ⁻¹'
      Set.range ((↑) : (((ℝ × N[n]) ≃L[ℝ] E[n]) →
        ((ℝ × N[n]) →L[ℝ] E[n])))) := by
  exact ContinuousLinearEquiv.isOpen.preimage
    (F.smooth_tubeLift.continuous_fderiv (by simp))


-- @@ L446-452 verbatim
theorem tubeLift_zero_mem_regularSet (u : ℝ) :
    (u, (0 : N[n])) ∈ (fderiv ℝ F.tubeLift) ⁻¹'
      Set.range ((↑) : (((ℝ × N[n]) ≃L[ℝ] E[n]) →
        ((ℝ × N[n]) →L[ℝ] E[n]))) := by
  refine ⟨F.tubeDerivEquiv u, ?_⟩
  rw [F.tubeDerivEquiv_coe u]
  exact (F.hasFDerivAt_tubeLift_zero u).fderiv.symm


-- @@ L454-499 verbatim
theorem exists_tubeLift_uniform_deriv_equiv :
    ∃ r > 0, ∀ (u : ℝ) (z : N[n]), z ∈ Metric.ball (0 : N[n]) r →
      ∃ e : (ℝ × N[n]) ≃L[ℝ] E[n],
        (e : (ℝ × N[n]) →L[ℝ] E[n]) = fderiv ℝ F.tubeLift (u, z) := by
  let A := Set.Icc (0 : ℝ) 1
  let R : Set (ℝ × N[n]) :=
    (fderiv ℝ F.tubeLift) ⁻¹' Set.range
      ((↑) : (((ℝ × N[n]) ≃L[ℝ] E[n]) →
        ((ℝ × N[n]) →L[ℝ] E[n])))
  let j : A × N[n] → ℝ × N[n] := fun q => (q.1.1, q.2)
  let T : Set (A × N[n]) := j ⁻¹' R
  have hAcompact : IsCompact A := isCompact_Icc
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAcompact
  have hj : Continuous j :=
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd
  have hTopen : IsOpen T := F.isOpen_tubeLift_regularSet.preimage hj
  have hzero : (Set.univ : Set A) ×ˢ ({0} : Set N[n]) ⊆ T := by
    rintro ⟨a, z⟩ ⟨-, hz⟩
    rw [Set.mem_singleton_iff] at hz
    change z = 0 at hz
    subst z
    exact F.tubeLift_zero_mem_regularSet a.1
  obtain ⟨U, W, hUopen, hWopen, hAU, hzeroW, hUWT⟩ :=
    generalized_tube_lemma (X := A) (Y := N[n])
      isCompact_univ isCompact_singleton hTopen hzero
  have hzero_mem_W : (0 : N[n]) ∈ W := hzeroW (Set.mem_singleton 0)
  rcases (Metric.isOpen_iff.mp hWopen) 0 hzero_mem_W with ⟨r, hr, hrW⟩
  refine ⟨r, hr, ?_⟩
  intro u z hz
  let a : A := ⟨Int.fract u, Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hregFract : (Int.fract u, z) ∈ R := by
    have ht : (a, z) ∈ T := hUWT ⟨hAU (Set.mem_univ a), hrW hz⟩
    exact ht
  have hperiod := F.periodic_fderiv_tubeLift.zsmul ⌊u⌋
  have heq : fderiv ℝ F.tubeLift (u, z) =
      fderiv ℝ F.tubeLift (Int.fract u, z) := by
    have h := hperiod (Int.fract u, z)
    have hpoint :
        (Int.fract u, z) + ⌊u⌋ • ((1 : ℝ), (0 : N[n])) = (u, z) := by
      ext
      · simpa [add_comm] using Int.fract_add_floor u
      · simp
    rw [hpoint] at h
    exact h
  rw [heq]
  exact hregFract


-- @@ L501-501 verbatim
/-! ## One global inverse with smooth local real-phase lifts -/


-- @@ L503-525 verbatim
structure GlobalSmoothTube where
  radius : ℝ
  radius_pos : 0 < radius
  inverse : E[n] → C × N[n]
  injOn : Set.InjOn F.tube
    ((Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) radius)
  embedding : Topology.IsEmbedding
    (fun q : ↥((Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) radius) =>
      F.tube q.1)
  inverse_left : ∀ q ∈
      ((Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) radius),
    inverse (F.tube q) = q
  local_smooth_lift : ∀ (u : ℝ) (z : N[n]),
      z ∈ Metric.ball (0 : N[n]) radius →
    ∃ e : (ℝ × N[n]) ≃L[ℝ] E[n], ∃ g : E[n] → ℝ × N[n],
      HasFDerivAt F.tubeLift (e : (ℝ × N[n]) →L[ℝ] E[n]) (u, z) ∧
      ContDiffAt ℝ ∞ g (F.tubeLift (u, z)) ∧
      HasFDerivAt g (e.symm : E[n] →L[ℝ] (ℝ × N[n]))
        (F.tubeLift (u, z)) ∧
      g (F.tubeLift (u, z)) = (u, z) ∧
      ∀ᶠ p in 𝓝 (u, z),
        inverse (F.tubeLift p) =
          (((g (F.tubeLift p)).1 : C), (g (F.tubeLift p)).2)


-- @@ L527-612 verbatim
theorem nonempty_globalSmoothTube : Nonempty F.GlobalSmoothTube := by
  obtain ⟨R, hR, hRinj, hRemb⟩ := F.exists_tube_global_embedding
  obtain ⟨S, hS, hSderiv⟩ := F.exists_tubeLift_uniform_deriv_equiv
  let r : ℝ := min R S
  have hr : 0 < r := lt_min hR hS
  have hrR : r ≤ R := min_le_left R S
  have hrS : r ≤ S := min_le_right R S
  let D : Set (C × N[n]) :=
    (Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) r
  let DR : Set (C × N[n]) :=
    (Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) R
  have hDR : D ⊆ DR := prod_mono Subset.rfl (Metric.ball_subset_ball hrR)
  have hinj : Set.InjOn F.tube D := hRinj.mono hDR
  have hemb : Topology.IsEmbedding (fun q : D => F.tube q.1) := by
    simpa [Function.comp_def, Set.inclusion, D, DR] using
      hRemb.comp (Topology.IsEmbedding.inclusion hDR)
  have hzeroD : ((0 : C), (0 : N[n])) ∈ D :=
    ⟨Set.mem_univ _, Metric.mem_ball_self hr⟩
  let qzero : D := ⟨((0 : C), (0 : N[n])), hzeroD⟩
  letI : Nonempty D := ⟨qzero⟩
  let tubeD : D → E[n] := fun q => F.tube q.1
  have htube_inj : Function.Injective tubeD := by
    intro p q hpq
    apply Subtype.ext
    exact hinj p.property q.property hpq
  let invTube : E[n] → D := Function.invFun tubeD
  let inverse : E[n] → C × N[n] := fun y => (invTube y).1
  have hinverse_left : ∀ q ∈ D, inverse (F.tube q) = q := by
    intro q hq
    let qs : D := ⟨q, hq⟩
    have hi : invTube (tubeD qs) = qs :=
      Function.leftInverse_invFun htube_inj qs
    exact congrArg Subtype.val hi
  refine ⟨{
    radius := r
    radius_pos := hr
    inverse := inverse
    injOn := hinj
    embedding := hemb
    inverse_left := hinverse_left
    local_smooth_lift := ?_
  }⟩
  intro u z hz
  have hzS : z ∈ Metric.ball (0 : N[n]) S :=
    Metric.ball_subset_ball hrS hz
  obtain ⟨e, he⟩ := hSderiv u z hzS
  have hf : HasFDerivAt F.tubeLift (e : (ℝ × N[n]) →L[ℝ] E[n]) (u, z) := by
    have hf' := F.smooth_tubeLift.differentiable (by simp) (u, z) |>.hasFDerivAt
    rw [he]
    exact hf'
  let chart : OpenPartialHomeomorph (ℝ × N[n]) E[n] :=
    F.smooth_tubeLift.contDiffAt.toOpenPartialHomeomorph F.tubeLift hf (by simp)
  let g : E[n] → ℝ × N[n] := chart.symm
  have hsource : (u, z) ∈ chart.source :=
    F.smooth_tubeLift.contDiffAt
      |>.mem_toOpenPartialHomeomorph_source hf (by simp)
  have htarget : F.tubeLift (u, z) ∈ chart.target := chart.map_source hsource
  have hgcenter : g (F.tubeLift (u, z)) = (u, z) := by
    change chart.symm (F.tubeLift (u, z)) = (u, z)
    rw [← show (chart : (ℝ × N[n]) → E[n]) = F.tubeLift by rfl]
    exact chart.left_inv hsource
  have hforwardDeriv : HasFDerivAt chart
      (e : (ℝ × N[n]) →L[ℝ] E[n])
      (chart.symm (F.tubeLift (u, z))) := by
    rw [show chart.symm (F.tubeLift (u, z)) = (u, z) by exact hgcenter]
    exact hf
  have hforwardSmooth : ContDiffAt ℝ ∞ chart
      (chart.symm (F.tubeLift (u, z))) := by
    rw [show chart.symm (F.tubeLift (u, z)) = (u, z) by exact hgcenter]
    exact F.smooth_tubeLift.contDiffAt
  have hgsmooth : ContDiffAt ℝ ∞ g (F.tubeLift (u, z)) :=
    chart.contDiffAt_symm htarget hforwardDeriv hforwardSmooth
  have hgderiv : HasFDerivAt g (e.symm : E[n] →L[ℝ] (ℝ × N[n]))
      (F.tubeLift (u, z)) :=
    chart.hasFDerivAt_symm htarget hforwardDeriv
  have hlocal : ∀ᶠ p in 𝓝 (u, z), g (F.tubeLift p) = p :=
    chart.eventually_left_inverse hsource
  have hball : ∀ᶠ p in 𝓝 (u, z), p.2 ∈ Metric.ball (0 : N[n]) r :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hz)
  refine ⟨e, g, hf, hgsmooth, hgderiv, hgcenter, ?_⟩
  filter_upwards [hlocal, hball] with p hp hpr
  have hglobal := hinverse_left (((p.1 : ℝ) : C), p.2)
    ⟨Set.mem_univ _, hpr⟩
  rw [F.tube_coe p.1 p.2] at hglobal
  simpa [hp] using hglobal


-- @@ L614-616 verbatim
/-- A fixed choice of the global smooth tube. -/
def globalSmoothTube : F.GlobalSmoothTube :=
  Classical.choice F.nonempty_globalSmoothTube


-- @@ L618-622 verbatim
@[simp] theorem globalSmoothTube_inverse_apply (q : C × N[n])
    (hq : q ∈ (Set.univ : Set C) ×ˢ
      Metric.ball (0 : N[n]) F.globalSmoothTube.radius) :
    F.globalSmoothTube.inverse (F.tube q) = q :=
  F.globalSmoothTube.inverse_left q hq


-- @@ L624-624 verbatim
/-! ## Radially localized extension of a periodic displacement -/


-- @@ L626-632 verbatim
/-- Input for extending a period-one displacement along the circle. -/
structure PeriodicDisplacementExtensionData where
  displacement : ℝ → E[n]
  displacement_smooth : ContDiff ℝ ∞ displacement
  displacement_periodic : Function.Periodic displacement 1
  radialBump : ContDiffBump (0 : N[n])
  radialBump_rOut_lt : radialBump.rOut < F.globalSmoothTube.radius


-- @@ L634-634 verbatim
namespace PeriodicDisplacementExtensionData


-- @@ L636-636 verbatim
variable {F : SmoothFramedPeriodicCircle n}

-- @@ L637-637 verbatim
variable (D : F.PeriodicDisplacementExtensionData)


-- @@ L639-640 verbatim
def quotientDisplacement (a : C) : E[n] :=
  D.displacement_periodic.lift a


-- @@ L642-643 verbatim
@[simp] theorem quotientDisplacement_coe (u : ℝ) :
    D.quotientDisplacement (u : C) = D.displacement u := rfl


-- @@ L645-646 verbatim
def tubeDomain (D : F.PeriodicDisplacementExtensionData) : Set (C × N[n]) :=
  (Set.univ : Set C) ×ˢ Metric.ball (0 : N[n]) F.globalSmoothTube.radius


-- @@ L648-648 verbatim
def tubeImage : Set E[n] := F.tube '' D.tubeDomain


-- @@ L650-652 verbatim
def supportCore : Set E[n] :=
  F.tube '' ((Set.univ : Set C) ×ˢ
    Metric.closedBall (0 : N[n]) D.radialBump.rOut)


-- @@ L654-657 verbatim
theorem isCompact_supportCore : IsCompact D.supportCore := by
  exact (isCompact_univ.prod
    (isCompact_closedBall (0 : N[n]) D.radialBump.rOut)).image
      F.continuous_tube


-- @@ L659-660 verbatim
theorem isClosed_supportCore : IsClosed D.supportCore :=
  D.isCompact_supportCore.isClosed


-- @@ L662-668 verbatim
/-- The radial extension, set to zero outside the open tube. -/
def ambientField (x : E[n]) : E[n] := by
  classical
  exact if x ∈ D.tubeImage then
    D.radialBump (F.globalSmoothTube.inverse x).2 •
      D.quotientDisplacement (F.globalSmoothTube.inverse x).1
  else 0


-- @@ L670-673 verbatim
theorem tube_inverse_right {x : E[n]} (hx : x ∈ D.tubeImage) :
    F.tube (F.globalSmoothTube.inverse x) = x := by
  rcases hx with ⟨q, hq, rfl⟩
  rw [F.globalSmoothTube.inverse_left q hq]


-- @@ L675-679 verbatim
theorem inverse_mem_tubeDomain {x : E[n]} (hx : x ∈ D.tubeImage) :
    F.globalSmoothTube.inverse x ∈ D.tubeDomain := by
  rcases hx with ⟨q, hq, rfl⟩
  rw [F.globalSmoothTube.inverse_left q hq]
  exact hq


-- @@ L681-685 verbatim
theorem ambientField_tube (q : C × N[n]) (hq : q ∈ D.tubeDomain) :
    D.ambientField (F.tube q) =
      D.radialBump q.2 • D.quotientDisplacement q.1 := by
  rw [ambientField, if_pos ⟨q, hq, rfl⟩,
    F.globalSmoothTube.inverse_left q hq]


-- @@ L687-693 verbatim
theorem ambientField_tubeLift (u : ℝ) (z : N[n])
    (hz : z ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius) :
    D.ambientField (F.tubeLift (u, z)) =
      D.radialBump z • D.displacement u := by
  rw [← F.tube_coe u z,
    D.ambientField_tube ((u : C), z) ⟨Set.mem_univ _, hz⟩,
    D.quotientDisplacement_coe]


-- @@ L695-703 verbatim
theorem ambientField_zeroSection (u : ℝ) :
    D.ambientField (F.tubeLift (u, (0 : N[n]))) = D.displacement u := by
  have hz : (0 : N[n]) ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius :=
    Metric.mem_ball_self F.globalSmoothTube.radius_pos
  rw [D.ambientField_tubeLift u 0 hz]
  have hb : D.radialBump (0 : N[n]) = 1 := by
    apply D.radialBump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall] using D.radialBump.rIn_pos.le
  simp [hb]


-- @@ L705-707 verbatim
theorem ambientField_eq_zero_of_not_mem_tubeImage {x : E[n]}
    (hx : x ∉ D.tubeImage) : D.ambientField x = 0 := by
  simp [ambientField, hx]


-- @@ L709-724 verbatim
theorem ambientField_eq_zero_of_not_mem_supportCore {x : E[n]}
    (hx : x ∉ D.supportCore) : D.ambientField x = 0 := by
  by_cases ht : x ∈ D.tubeImage
  · let q : C × N[n] := F.globalSmoothTube.inverse x
    have hq : q ∈ D.tubeDomain := D.inverse_mem_tubeDomain ht
    have houter : D.radialBump.rOut ≤ ‖q.2‖ := by
      by_contra hnot
      have hle : ‖q.2‖ ≤ D.radialBump.rOut := (lt_of_not_ge hnot).le
      apply hx
      refine ⟨q, ⟨Set.mem_univ _, ?_⟩, D.tube_inverse_right ht⟩
      simpa [Metric.mem_closedBall, dist_zero_left] using hle
    have hb : D.radialBump q.2 = 0 :=
      D.radialBump.zero_of_le_dist (by simpa [dist_zero_right] using houter)
    rw [ambientField, if_pos ht]
    simp [q, hb]
  · exact D.ambientField_eq_zero_of_not_mem_tubeImage ht


-- @@ L726-728 verbatim
theorem hasCompactSupport_ambientField : HasCompactSupport D.ambientField :=
  HasCompactSupport.intro D.isCompact_supportCore
    (fun x hx => D.ambientField_eq_zero_of_not_mem_supportCore hx)


-- @@ L730-792 verbatim
theorem contDiffAt_ambientField_tubeLift (u : ℝ) (z : N[n])
    (hz : z ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius) :
    ContDiffAt ℝ ∞ D.ambientField (F.tubeLift (u, z)) := by
  obtain ⟨e, g₀, hf, hg₀, hg₀deriv, hg₀center, hg₀local⟩ :=
    F.globalSmoothTube.local_smooth_lift u z hz
  let chart : OpenPartialHomeomorph (ℝ × N[n]) E[n] :=
    F.smooth_tubeLift.contDiffAt.toOpenPartialHomeomorph F.tubeLift hf (by simp)
  let g : E[n] → ℝ × N[n] := chart.symm
  have hsource : (u, z) ∈ chart.source :=
    F.smooth_tubeLift.contDiffAt
      |>.mem_toOpenPartialHomeomorph_source hf (by simp)
  have htarget : F.tubeLift (u, z) ∈ chart.target := chart.map_source hsource
  have hgcenter : g (F.tubeLift (u, z)) = (u, z) := by
    change chart.symm (F.tubeLift (u, z)) = (u, z)
    rw [← show (chart : (ℝ × N[n]) → E[n]) = F.tubeLift by rfl]
    exact chart.left_inv hsource
  have hforwardDeriv : HasFDerivAt chart
      (e : (ℝ × N[n]) →L[ℝ] E[n])
      (chart.symm (F.tubeLift (u, z))) := by
    rw [show chart.symm (F.tubeLift (u, z)) = (u, z) by exact hgcenter]
    exact hf
  have hforwardSmooth : ContDiffAt ℝ ∞ chart
      (chart.symm (F.tubeLift (u, z))) := by
    rw [show chart.symm (F.tubeLift (u, z)) = (u, z) by exact hgcenter]
    exact F.smooth_tubeLift.contDiffAt
  have hgsmooth : ContDiffAt ℝ ∞ g (F.tubeLift (u, z)) :=
    chart.contDiffAt_symm htarget hforwardDeriv hforwardSmooth
  have hgball : ∀ᶠ y in 𝓝 (F.tubeLift (u, z)),
      (g y).2 ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius := by
    have hg2continuous : ContinuousAt (fun y : E[n] => (g y).2)
        (F.tubeLift (u, z)) :=
      continuous_snd.continuousAt.comp' hgsmooth.continuousAt
    have hzcenter : (g (F.tubeLift (u, z))).2 ∈
        Metric.ball (0 : N[n]) F.globalSmoothTube.radius := by
      rw [hgcenter]
      exact hz
    exact hg2continuous.eventually (Metric.isOpen_ball.mem_nhds hzcenter)
  have hright : ∀ᶠ y in 𝓝 (F.tubeLift (u, z)), F.tubeLift (g y) = y := by
    filter_upwards [chart.eventually_right_inverse htarget] with y hy
    exact hy
  have hlocal : ∀ᶠ y in 𝓝 (F.tubeLift (u, z)),
      D.ambientField y =
        D.radialBump (g y).2 • D.displacement (g y).1 := by
    filter_upwards [hright, hgball] with y hy hgy
    let q : C × N[n] := (((g y).1 : C), (g y).2)
    have hq : q ∈ D.tubeDomain := ⟨Set.mem_univ _, hgy⟩
    have hyq : F.tube q = y := by
      rw [F.tube_coe]
      exact hy
    have hytube : y ∈ D.tubeImage := ⟨q, hq, hyq⟩
    have hinv : F.globalSmoothTube.inverse y = q := by
      rw [← hyq]
      exact F.globalSmoothTube.inverse_left q hq
    rw [ambientField, if_pos hytube, hinv, D.quotientDisplacement_coe]
  have hg1 : ContDiffAt ℝ ∞ (fun y : E[n] => (g y).1)
      (F.tubeLift (u, z)) := contDiffAt_fst.comp _ hgsmooth
  have hg2 : ContDiffAt ℝ ∞ (fun y : E[n] => (g y).2)
      (F.tubeLift (u, z)) := contDiffAt_snd.comp _ hgsmooth
  have hb : ContDiffAt ℝ ∞ (fun y : E[n] => D.radialBump (g y).2)
      (F.tubeLift (u, z)) := D.radialBump.contDiffAt.comp _ hg2
  have hd : ContDiffAt ℝ ∞ (fun y : E[n] => D.displacement (g y).1)
      (F.tubeLift (u, z)) := D.displacement_smooth.contDiffAt.comp _ hg1
  exact (hb.smul hd).congr_of_eventuallyEq hlocal


-- @@ L794-811 verbatim
theorem contDiff_ambientField : ContDiff ℝ ∞ D.ambientField := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ D.supportCore
  · rcases hx with ⟨⟨a, z⟩, hzcore, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hzle : ‖z‖ ≤ D.radialBump.rOut := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hzcore.2
    have hz : z ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius := by
      simpa [Metric.mem_ball, dist_zero_left] using
        (lt_of_le_of_lt hzle D.radialBump_rOut_lt)
    simpa only [F.tube_coe] using D.contDiffAt_ambientField_tubeLift u z hz
  · have hnear : D.supportCoreᶜ ∈ 𝓝 x :=
      D.isClosed_supportCore.isOpen_compl.mem_nhds hx
    apply (show ContDiffAt ℝ ∞ (fun _ : E[n] => (0 : E[n])) x from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    exact D.ambientField_eq_zero_of_not_mem_supportCore hy


-- @@ L813-816 verbatim
theorem exists_lipschitzWith_ambientField :
    ∃ K : ℝ≥0, LipschitzWith K D.ambientField := by
  exact D.contDiff_ambientField.lipschitzWith_of_hasCompactSupport
    D.hasCompactSupport_ambientField (by simp)


-- @@ L818-833 verbatim
/-- A sufficiently small scalar multiple of the radial extension produces a
global smooth ambient isotopy with the prescribed scaled action on the
circle. -/
theorem exists_scaledSmallAmbientDisplacement :
    ∃ ε : ℝ, ε > 0 ∧ ∃ S : SmallAmbientDisplacement n,
      S.field = (fun x => ε • D.ambientField x) ∧
      ∀ u : ℝ,
        S.toSmoothAmbientIsotopy.forward 1 (F.lift u) =
          F.lift u + ε • D.displacement u := by
  obtain ⟨ε, hε, S, hS⟩ := SmallAmbientDisplacement.exists_scaled
    D.ambientField D.contDiff_ambientField D.hasCompactSupport_ambientField
  refine ⟨ε, hε, S, hS, ?_⟩
  intro u
  rw [S.toSmoothAmbientIsotopy_forward_one, hS]
  change F.lift u + ε • D.ambientField (F.lift u) = _
  rw [← F.tubeLift_zero u, D.ambientField_zeroSection]


-- @@ L835-841 verbatim
/-- A canonical radial bump strictly inside the chosen global tube. -/
def canonicalRadialBump (F : SmoothFramedPeriodicCircle n) :
    ContDiffBump (0 : N[n]) where
  rIn := F.globalSmoothTube.radius / 3
  rOut := F.globalSmoothTube.radius / 2
  rIn_pos := by linarith [F.globalSmoothTube.radius_pos]
  rIn_lt_rOut := by linarith [F.globalSmoothTube.radius_pos]


-- @@ L843-846 verbatim
theorem canonicalRadialBump_rOut_lt :
    (canonicalRadialBump F).rOut < F.globalSmoothTube.radius := by
  dsimp [canonicalRadialBump]
  linarith [F.globalSmoothTube.radius_pos]


-- @@ L848-857 verbatim
/-- Every smooth period-one displacement has canonical radial extension
data. -/
def canonical (F : SmoothFramedPeriodicCircle n)
    (d : ℝ → E[n]) (hd : ContDiff ℝ ∞ d)
    (hp : Function.Periodic d 1) : F.PeriodicDisplacementExtensionData where
  displacement := d
  displacement_smooth := hd
  displacement_periodic := hp
  radialBump := canonicalRadialBump F
  radialBump_rOut_lt := canonicalRadialBump_rOut_lt (F := F)


-- @@ L859-859 verbatim
end PeriodicDisplacementExtensionData

-- @@ L860-860 verbatim
end SmoothFramedPeriodicCircle

-- @@ L861-861 verbatim
end Submission
