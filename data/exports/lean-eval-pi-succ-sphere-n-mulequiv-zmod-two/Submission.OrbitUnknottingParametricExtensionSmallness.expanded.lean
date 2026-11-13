import Mathlib
import Submission.OrbitUnknottingLocalTrackStepBridge


-- @@ L4-17 verbatim
/-!
# Parametric smallness of framed-circle displacement extensions

For a fixed framed circle and a fixed radial bump, radial tube extension is
a continuous linear operation at the level of first derivatives.  This file
records the form needed by finite track subdivision: a jointly smooth
periodic displacement family which vanishes at a base time has ambient
extensions with arbitrarily small global Lipschitz constant near that time.

The support core is independent of the parameter.  Joint smoothness across
the boundary of the tube is proved by the same local inverse and closed-core
argument as for a single displacement in
`OrbitUnknottingFramedCircleTube`.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 2000000


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function Module InnerProductSpace Metric Filter

-- @@ L25-25 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
local notation "E[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L30-30 verbatim
local notation "N[" n "]" => EuclideanSpace ℝ (Fin n)

-- @@ L31-31 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L33-33 verbatim
namespace SmoothFramedPeriodicCircle


-- @@ L35-35 verbatim
variable {n : ℕ} (F : SmoothFramedPeriodicCircle n)


-- @@ L37-45 verbatim
/-- A jointly smooth family of period-one displacements, all extended using
one fixed framed tube and one fixed radial bump. -/
structure ParametricPeriodicDisplacementExtensionData where
  displacement : ℝ × ℝ → E[n]
  displacement_smooth : ContDiff ℝ ∞ displacement
  displacement_periodic : ∀ t : ℝ,
    Function.Periodic (fun u => displacement (t, u)) 1
  radialBump : ContDiffBump (0 : N[n])
  radialBump_rOut_lt : radialBump.rOut < F.globalSmoothTube.radius


-- @@ L47-47 verbatim
namespace ParametricPeriodicDisplacementExtensionData


-- @@ L49-49 verbatim
variable {F : SmoothFramedPeriodicCircle n}

-- @@ L50-50 verbatim
variable (P : F.ParametricPeriodicDisplacementExtensionData)


-- @@ L52-59 verbatim
/-- The ordinary extension data at one parameter value. -/
def slice (t : ℝ) : F.PeriodicDisplacementExtensionData where
  displacement := fun u => P.displacement (t, u)
  displacement_smooth :=
    P.displacement_smooth.comp (contDiff_const.prodMk contDiff_id)
  displacement_periodic := P.displacement_periodic t
  radialBump := P.radialBump
  radialBump_rOut_lt := P.radialBump_rOut_lt


-- @@ L61-64 verbatim
/-- The parameter-independent compact support core. -/
def supportCore : Set E[n] :=
  F.tube '' ((Set.univ : Set C) ×ˢ
    Metric.closedBall (0 : N[n]) P.radialBump.rOut)


-- @@ L66-68 verbatim
@[simp] theorem slice_supportCore (t : ℝ) :
    (P.slice t).supportCore = P.supportCore :=
  rfl


-- @@ L70-73 verbatim
theorem isCompact_supportCore : IsCompact P.supportCore := by
  exact (isCompact_univ.prod
    (isCompact_closedBall (0 : N[n]) P.radialBump.rOut)).image
      F.continuous_tube


-- @@ L75-76 verbatim
theorem isClosed_supportCore : IsClosed P.supportCore :=
  P.isCompact_supportCore.isClosed


-- @@ L78-80 verbatim
/-- The whole parameterized ambient field. -/
def ambientField (p : ℝ × E[n]) : E[n] :=
  (P.slice p.1).ambientField p.2


-- @@ L82-84 verbatim
@[simp] theorem ambientField_apply (t : ℝ) (x : E[n]) :
    P.ambientField (t, x) = (P.slice t).ambientField x :=
  rfl


-- @@ L86-90 verbatim
theorem ambientField_tubeLift (t u : ℝ) (z : N[n])
    (hz : z ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius) :
    P.ambientField (t, F.tubeLift (u, z)) =
      P.radialBump z • P.displacement (t, u) := by
  exact (P.slice t).ambientField_tubeLift u z hz


-- @@ L92-96 verbatim
theorem ambientField_eq_zero_of_not_mem_supportCore
    (t : ℝ) {x : E[n]} (hx : x ∉ P.supportCore) :
    P.ambientField (t, x) = 0 := by
  exact (P.slice t).ambientField_eq_zero_of_not_mem_supportCore
    (by simpa using hx)


-- @@ L98-98 verbatim
/-! ## Joint smoothness -/


-- @@ L100-185 verbatim
/-- Joint smoothness at a point represented in real tube coordinates. -/
theorem contDiffAt_ambientField_tubeLift (t u : ℝ) (z : N[n])
    (hz : z ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius) :
    ContDiffAt ℝ ∞ P.ambientField (t, F.tubeLift (u, z)) := by
  obtain ⟨e, g₀, hf, hg₀, hg₀deriv, hg₀center, hg₀local⟩ :=
    F.globalSmoothTube.local_smooth_lift u z hz
  let chart : OpenPartialHomeomorph (ℝ × N[n]) E[n] :=
    F.smooth_tubeLift.contDiffAt.toOpenPartialHomeomorph F.tubeLift hf (by simp)
  let g : E[n] → ℝ × N[n] := chart.symm
  have hsource : (u, z) ∈ chart.source :=
    F.smooth_tubeLift.contDiffAt
      |>.mem_toOpenPartialHomeomorph_source hf (by simp)
  have htarget : F.tubeLift (u, z) ∈ chart.target :=
    chart.map_source hsource
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
  have hlocal : ∀ᶠ y in 𝓝 (F.tubeLift (u, z)), ∀ a : ℝ,
      P.ambientField (a, y) =
        P.radialBump (g y).2 • P.displacement (a, (g y).1) := by
    filter_upwards [hright, hgball] with y hy hgy
    intro a
    let q : C × N[n] := (((g y).1 : C), (g y).2)
    have hq : q ∈ (P.slice a).tubeDomain := ⟨Set.mem_univ _, hgy⟩
    have hyq : F.tube q = y := by
      rw [F.tube_coe]
      exact hy
    have hytube : y ∈ (P.slice a).tubeImage := ⟨q, hq, hyq⟩
    have hinv : F.globalSmoothTube.inverse y = q := by
      rw [← hyq]
      exact F.globalSmoothTube.inverse_left q hq
    rw [ambientField, PeriodicDisplacementExtensionData.ambientField,
      if_pos hytube, hinv, (P.slice a).quotientDisplacement_coe]
    rfl
  have hlocalProd : ∀ᶠ p in 𝓝 (t, F.tubeLift (u, z)),
      P.ambientField p =
        P.radialBump (g p.2).2 •
          P.displacement (p.1, (g p.2).1) := by
    have hsnd : ContinuousAt (fun p : ℝ × E[n] => p.2)
        (t, F.tubeLift (u, z)) := continuous_snd.continuousAt
    have hpre := hsnd.eventually hlocal
    filter_upwards [hpre] with p hp
    exact hp p.1
  have hgpair : ContDiffAt ℝ ∞ (fun p : ℝ × E[n] => g p.2)
      (t, F.tubeLift (u, z)) :=
    hgsmooth.comp (t, F.tubeLift (u, z))
      (show ContDiffAt ℝ ∞ (fun p : ℝ × E[n] => p.2)
        (t, F.tubeLift (u, z)) from contDiffAt_snd)
  have hb : ContDiffAt ℝ ∞
      (fun p : ℝ × E[n] => P.radialBump (g p.2).2)
      (t, F.tubeLift (u, z)) :=
    P.radialBump.contDiffAt.comp _ (contDiffAt_snd.comp _ hgpair)
  have hphase : ContDiffAt ℝ ∞
      (fun p : ℝ × E[n] => (p.1, (g p.2).1))
      (t, F.tubeLift (u, z)) :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp _ hgpair)
  have hd : ContDiffAt ℝ ∞
      (fun p : ℝ × E[n] => P.displacement (p.1, (g p.2).1))
      (t, F.tubeLift (u, z)) :=
    P.displacement_smooth.contDiffAt.comp _ hphase
  exact (hb.smul hd).congr_of_eventuallyEq hlocalProd


-- @@ L187-212 verbatim
/-- The parameterized ambient extension is jointly smooth in parameter and
ambient position, including across the fixed support boundary. -/
theorem contDiff_ambientField : ContDiff ℝ ∞ P.ambientField := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, x⟩
  by_cases hx : x ∈ P.supportCore
  · rcases hx with ⟨⟨a, z⟩, hzcore, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hzle : ‖z‖ ≤ P.radialBump.rOut := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hzcore.2
    have hz : z ∈ Metric.ball (0 : N[n]) F.globalSmoothTube.radius := by
      simpa [Metric.mem_ball, dist_zero_left] using
        (lt_of_le_of_lt hzle P.radialBump_rOut_lt)
    simpa only [F.tube_coe] using
      P.contDiffAt_ambientField_tubeLift t u z hz
  · have hnear : P.supportCoreᶜ ∈ 𝓝 x :=
      P.isClosed_supportCore.isOpen_compl.mem_nhds hx
    have hsnd : ContinuousAt (fun p : ℝ × E[n] => p.2) (t, x) :=
      continuous_snd.continuousAt
    have hnearProd : ∀ᶠ p in 𝓝 (t, x), p.2 ∉ P.supportCore :=
      hsnd.eventually hnear
    apply (show ContDiffAt ℝ ∞
      (fun _ : ℝ × E[n] => (0 : E[n])) (t, x) from
        contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hnearProd] with p hp
    exact P.ambientField_eq_zero_of_not_mem_supportCore p.1 hp


-- @@ L214-214 verbatim
/-! ## Spatial derivative and uniform smallness -/


-- @@ L216-219 verbatim
/-- The spatial part of the derivative of the jointly smooth extension. -/
def spatialFDeriv (p : ℝ × E[n]) : E[n] →L[ℝ] E[n] :=
  (fderiv ℝ P.ambientField p).comp
    (ContinuousLinearMap.inr ℝ ℝ E[n])


-- @@ L221-223 verbatim
theorem continuous_spatialFDeriv : Continuous P.spatialFDeriv := by
  exact (P.contDiff_ambientField.continuous_fderiv (by simp)).clm_comp
    continuous_const


-- @@ L225-237 verbatim
/-- The spatial part of the total derivative is the derivative of the
ordinary ambient extension at the fixed parameter. -/
theorem fderiv_at_ambientField (t : ℝ) (x : E[n]) :
    fderiv ℝ (P.slice t).ambientField x = P.spatialFDeriv (t, x) := by
  have htotal :=
    (P.contDiff_ambientField.differentiable (by simp) (t, x)).hasFDerivAt
  have hin : HasFDerivAt (fun y : E[n] => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ E[n]) x :=
    hasFDerivAt_prodMk_right t x
  have hcomp := htotal.comp x hin
  change fderiv ℝ (fun y : E[n] => P.ambientField (t, y)) x =
    P.spatialFDeriv (t, x)
  simpa [spatialFDeriv, Function.comp_def] using hcomp.fderiv


-- @@ L239-250 verbatim
/-- Outside the fixed support core the spatial derivative vanishes. -/
theorem fderiv_at_ambientField_eq_zero_of_not_mem_supportCore
    (t : ℝ) {x : E[n]} (hx : x ∉ P.supportCore) :
    fderiv ℝ (P.slice t).ambientField x = 0 := by
  have hnear : P.supportCoreᶜ ∈ 𝓝 x :=
    P.isClosed_supportCore.isOpen_compl.mem_nhds hx
  have heq : (P.slice t).ambientField =ᶠ[𝓝 x]
      (fun _ : E[n] => (0 : E[n])) := by
    filter_upwards [hnear] with y hy
    exact P.ambientField_eq_zero_of_not_mem_supportCore t hy
  rw [heq.fderiv_eq]
  exact fderiv_const_apply 0


-- @@ L252-266 verbatim
/-- Vanishing of the displacement at one parameter makes the entire
ambient extension vanish at that parameter. -/
theorem ambientField_base_eq_zero {s : ℝ}
    (hzero : ∀ u : ℝ, P.displacement (s, u) = 0) (x : E[n]) :
    P.ambientField (s, x) = 0 := by
  by_cases ht : x ∈ (P.slice s).tubeImage
  · let q : C × N[n] := F.globalSmoothTube.inverse x
    obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective q.1
    rw [ambientField, PeriodicDisplacementExtensionData.ambientField,
      if_pos ht]
    change P.radialBump q.2 • (P.slice s).quotientDisplacement q.1 = 0
    rw [← hu, (P.slice s).quotientDisplacement_coe]
    change P.radialBump q.2 • P.displacement (s, u) = 0
    rw [hzero u, smul_zero]
  · exact (P.slice s).ambientField_eq_zero_of_not_mem_tubeImage ht


-- @@ L268-276 verbatim
theorem spatialFDeriv_base_eq_zero {s : ℝ}
    (hzero : ∀ u : ℝ, P.displacement (s, u) = 0) (x : E[n]) :
    P.spatialFDeriv (s, x) = 0 := by
  rw [← P.fderiv_at_ambientField s x]
  have hfun : (P.slice s).ambientField = fun _ : E[n] => 0 := by
    funext y
    exact P.ambientField_base_eq_zero hzero y
  rw [hfun]
  exact fderiv_const_apply 0


-- @@ L278-318 verbatim
/-- Quantitative parametric smallness.  For every positive prescribed
Lipschitz constant `K`, all sufficiently nearby parameter slices have that
global Lipschitz bound.  This is the uniform `x`-derivative convergence to
zero on the fixed compact support core. -/
theorem exists_uniform_lipschitzWith_of_base_zero {s : ℝ}
    (hzero : ∀ u : ℝ, P.displacement (s, u) = 0)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      LipschitzWith K (P.slice t).ambientField := by
  let W : Set (ℝ × E[n]) :=
    {p | ‖P.spatialFDeriv p‖ < (K : ℝ)}
  have hWopen : IsOpen W := by
    exact isOpen_lt P.continuous_spatialFDeriv.norm continuous_const
  have hbase : ({s} : Set ℝ) ×ˢ P.supportCore ⊆ W := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [Set.mem_singleton_iff] at ht
    change t = s at ht
    subst t
    change ‖P.spatialFDeriv (s, x)‖ < (K : ℝ)
    rw [P.spatialFDeriv_base_eq_zero hzero x, norm_zero]
    exact_mod_cast hK
  obtain ⟨U, Z, hUopen, hZopen, hsU, hcoreZ, hUZ⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := s))
      P.isCompact_supportCore hWopen hbase
  have hs_mem : s ∈ U := hsU (Set.mem_singleton s)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUopen s hs_mem
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((P.slice t).contDiff_ambientField.differentiable (by simp))
  intro x
  by_cases hx : x ∈ P.supportCore
  · rw [P.fderiv_at_ambientField]
    have htU : t ∈ U := hball (by
      simpa [Real.dist_eq] using ht)
    have hsmall : ‖P.spatialFDeriv (t, x)‖ < (K : ℝ) :=
      hUZ ⟨htU, hcoreZ hx⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hsmall.le
  · rw [P.fderiv_at_ambientField_eq_zero_of_not_mem_supportCore t hx]
    simp


-- @@ L320-333 verbatim
/-- In particular, nearby extensions have a Lipschitz constant strictly
below one, so they define `SmallAmbientDisplacement`s without rescaling the
desired displacement. -/
theorem exists_lipschitzWith_lt_one_of_base_zero {s : ℝ}
    (hzero : ∀ u : ℝ, P.displacement (s, u) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      ∃ K : ℝ≥0, K < 1 ∧ LipschitzWith K (P.slice t).ambientField := by
  let K : ℝ≥0 := 1 / 2
  have hK : 0 < K := by norm_num [K]
  obtain ⟨δ, hδ, hLip⟩ :=
    P.exists_uniform_lipschitzWith_of_base_zero hzero K hK
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  exact ⟨K, by norm_num [K], hLip t ht⟩


-- @@ L335-335 verbatim
end ParametricPeriodicDisplacementExtensionData

-- @@ L336-336 verbatim
end SmoothFramedPeriodicCircle


-- @@ L338-338 verbatim
/-! ## Application to Fourier embedded-circle tracks -/


-- @@ L340-340 verbatim
namespace TamedField

-- @@ L341-341 verbatim
namespace FourierEmbeddingTrack

-- @@ L342-342 verbatim
namespace EmbeddedCircleTrack

-- @@ L343-343 verbatim
namespace SmoothSliceFrame


-- @@ L345-345 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L346-346 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}

-- @@ L347-347 verbatim
variable {T : EmbeddedCircleTrack (V := V) h2 O}


-- @@ L349-367 verbatim
/-- The chord from a fixed framed slice to every parameter slice, viewed as
a jointly smooth periodic displacement family on the fixed source tube. -/
def parametricChordExtensionData {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    SmoothFramedPeriodicCircle.ParametricPeriodicDisplacementExtensionData
      (G.toFramedPeriodicCircle (T := T) hs) where
  displacement := fun p => T.lift p.1 p.2 - T.lift s p.2
  displacement_smooth :=
    T.smooth_lift.sub
      (T.contDiff_lift_slice s |>.comp contDiff_snd)
  displacement_periodic := fun t u => by
    simp only
    rw [T.periodic_lift t u, T.periodic_lift s u]
  radialBump :=
    SmoothFramedPeriodicCircle.PeriodicDisplacementExtensionData.canonicalRadialBump
      (G.toFramedPeriodicCircle (T := T) hs)
  radialBump_rOut_lt :=
    SmoothFramedPeriodicCircle.PeriodicDisplacementExtensionData.canonicalRadialBump_rOut_lt
      (F := G.toFramedPeriodicCircle (T := T) hs)


-- @@ L369-379 verbatim
@[simp] theorem parametricChordExtensionData_slice {s : ℝ}
    (G : T.SmoothSliceFrame s) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (G.parametricChordExtensionData (T := T) hs).slice t =
      G.chordExtensionData (T := T) hs t :=
  by
    simp [parametricChordExtensionData,
      SmoothFramedPeriodicCircle.ParametricPeriodicDisplacementExtensionData.slice,
      chordExtensionData,
      SmoothFramedPeriodicCircle.PeriodicDisplacementExtensionData.canonical]
    funext u
    rfl


-- @@ L381-397 verbatim
/-- The local analytic estimate required by `ambientTrackStep_chord`:
the unscaled literal chord extension has arbitrarily small global
Lipschitz constant when the target slice approaches the source slice. -/
theorem exists_uniform_lipschitzWith_chordExtensionData
    {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      LipschitzWith K
        (G.chordExtensionData (T := T) hs t).ambientField := by
  have hzero : ∀ u : ℝ,
      (G.parametricChordExtensionData (T := T) hs).displacement (s, u) = 0 := by
    intro u
    simp [parametricChordExtensionData]
  simpa only [G.parametricChordExtensionData_slice (T := T) hs] using
    (G.parametricChordExtensionData (T := T) hs).exists_uniform_lipschitzWith_of_base_zero
      hzero K hK


-- @@ L399-414 verbatim
/-- A convenient fixed bound strictly below one for nearby chord
extensions. -/
theorem exists_lipschitzWith_lt_one_chordExtensionData
    {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      ∃ K : ℝ≥0, K < 1 ∧
        LipschitzWith K
          (G.chordExtensionData (T := T) hs t).ambientField := by
  have hzero : ∀ u : ℝ,
      (G.parametricChordExtensionData (T := T) hs).displacement (s, u) = 0 := by
    intro u
    simp [parametricChordExtensionData]
  simpa only [G.parametricChordExtensionData_slice (T := T) hs] using
    (G.parametricChordExtensionData (T := T) hs).exists_lipschitzWith_lt_one_of_base_zero
      hzero


-- @@ L416-416 verbatim
end SmoothSliceFrame

-- @@ L417-417 verbatim
end EmbeddedCircleTrack

-- @@ L418-418 verbatim
end FourierEmbeddingTrack

-- @@ L419-419 verbatim
end TamedField


-- @@ L421-421 verbatim
end Submission
