import Mathlib
import Submission.CanonicalRoundOrbitUnknotting
import Submission.OrbitUnknottingSmoothOrbit
import Submission.OrbitUnknottingFourierBadLocus


-- @@ L6-18 verbatim
/-!
# A genuine embedded-circle track from Fourier avoidance

For one intrinsic orbit, this file joins its period-one lift to the assigned
canonical round lift by the straight homotopy and adds the endpoint-fixed
two-mode Fourier perturbation.  The explicit secant and tangent bad-locus
maps then supply one parameter for which every interior slice is both
injective on `AddCircle 1` and immersed.  Compactness upgrades the descended
continuous injections to embeddings.

This is the moving-core input for the subsequent finite normal-graph ambient
extension; no ambient isotopy is postulated here.
-/


-- @@ L20-20 verbatim
set_option autoImplicit false

-- @@ L21-21 verbatim
set_option maxHeartbeats 300000


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace TamedField

-- @@ L30-30 verbatim
namespace FourierEmbeddingTrack


-- @@ L32-32 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L34-34 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L35-35 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L37-37 verbatim
variable {V} (h2 : 2 ≤ n) (O : V.OrbitIndex)


-- @@ L39-41 verbatim
/-- Real period-one lift of the canonical target circle. -/
def targetLift (u : ℝ) : E :=
  CanonicalRoundOrbit.point V h2 O (2 * Real.pi * u)


-- @@ L43-49 verbatim
theorem targetLift_eq_circlePoint (u : ℝ) :
    targetLift (V := V) h2 O u =
      CanonicalRoundOrbit.circlePoint V h2 O (u : C) := by
  rw [targetLift, CanonicalRoundOrbit.point,
    CanonicalRoundOrbit.circlePoint,
    ← OrbitUnknottingFourier.circleLift_eq_addCircleCartesian]
  rfl


-- @@ L51-57 verbatim
theorem contDiff_targetLift : ContDiff ℝ ∞ (targetLift (V := V) h2 O) := by
  unfold targetLift CanonicalRoundOrbit.point
  exact (contDiff_const.add
      ((Real.contDiff_cos.comp
        (contDiff_const.mul contDiff_id)).smul contDiff_const)).add
    ((Real.contDiff_sin.comp
      (contDiff_const.mul contDiff_id)).smul contDiff_const)


-- @@ L59-63 verbatim
theorem periodic_targetLift : Function.Periodic (targetLift (V := V) h2 O) 1 := by
  intro u
  rw [targetLift_eq_circlePoint (V := V), targetLift_eq_circlePoint (V := V)]
  congr 1
  simp


-- @@ L65-76 verbatim
theorem injective_circlePoint :
    Function.Injective (CanonicalRoundOrbit.circlePoint V h2 O) := by
  intro a b hab
  have h₀ := congrArg
    (fun x : E => x (⟨0, by omega⟩ : Fin (n + 1))) hab
  have h₁ := congrArg
    (fun x : E => x (⟨1, by omega⟩ : Fin (n + 1))) hab
  simp [CanonicalRoundOrbit.circlePoint, CanonicalRoundOrbit.center,
    CanonicalRoundOrbit.e₀, CanonicalRoundOrbit.e₁,
    CanonicalRoundOrbit.e₂] at h₀ h₁
  apply OrbitUnknottingFourier.injective_addCircleCartesian
  exact Prod.ext h₀ h₁


-- @@ L78-81 verbatim
theorem isEmbedding_circlePoint :
    Topology.IsEmbedding (CanonicalRoundOrbit.circlePoint V h2 O) :=
  (CanonicalRoundOrbit.continuous_circlePoint V h2 O).isClosedEmbedding
    (injective_circlePoint (V := V) h2 O) |>.isEmbedding


-- @@ L83-86 verbatim
/-- Straight base track between the source and canonical target lifts. -/
def baseTrack (s u : ℝ) : E :=
  (1 - s) • V.intrinsicOrbitLift O u +
    s • targetLift (V := V) h2 O u


-- @@ L88-92 verbatim
/-- Its actual phase derivative.  Defining this from `deriv` lets the smooth
partial-derivative theorem handle the joint `(time, phase)` dependence
without a coordinate calculation. -/
def baseTangent (s u : ℝ) : E :=
  deriv (baseTrack (V := V) h2 O s) u


-- @@ L94-100 verbatim
theorem contDiff_baseTrack :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ => baseTrack (V := V) h2 O q.1 q.2) := by
  exact ((contDiff_const.sub contDiff_fst).smul
      ((V.contDiff_intrinsicOrbitLift O).comp contDiff_snd)).add
    (contDiff_fst.smul
      ((contDiff_targetLift (V := V) h2 O).comp contDiff_snd))


-- @@ L102-114 verbatim
theorem contDiff_baseTangent :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ => baseTangent (V := V) h2 O q.1 q.2) := by
  let f : (ℝ × ℝ) → ℝ → E := fun q u =>
    baseTrack (V := V) h2 O q.1 u
  have hf : ContDiff ℝ ∞ (Function.uncurry f) := by
    exact (contDiff_baseTrack (V := V) h2 O).comp
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hd := ContDiff.fderiv_apply (m := ∞) (n := ∞) hf
    (g := fun q : ℝ × ℝ => q.2)
    (k := fun _ : ℝ × ℝ => (1 : ℝ))
    contDiff_snd contDiff_const (by simp)
  simpa [f, baseTangent, fderiv_apply_one_eq_deriv] using hd


-- @@ L116-120 verbatim
theorem periodic_baseTrack (s : ℝ) :
    Function.Periodic (baseTrack (V := V) h2 O s) 1 := by
  intro u
  rw [baseTrack, baseTrack, V.periodic_intrinsicOrbitLift O u,
    periodic_targetLift (V := V) h2 O u]


-- @@ L122-128 verbatim
theorem hasDerivAt_baseTrack (s u : ℝ) :
    HasDerivAt (baseTrack (V := V) h2 O s)
      (baseTangent (V := V) h2 O s u) u := by
  have hs : ContDiff ℝ ∞ (baseTrack (V := V) h2 O s) :=
    (contDiff_baseTrack (V := V) h2 O).comp
      (contDiff_const.prodMk contDiff_id)
  exact (hs.differentiable (by simp) u).hasDerivAt


-- @@ L130-149 verbatim
/-- Phase derivative of the perturbed lift.  This is exactly the expression
whose nonvanishing is certified by the tangent bad-locus avoidance. -/
theorem hasDerivAt_perturbedLift
    (p : OrbitUnknottingFourier.Parameter E) (s u : ℝ) :
    HasDerivAt
      (OrbitUnknottingFourier.perturbedTrack
        (baseTrack (V := V) h2 O) p s)
      (baseTangent (V := V) h2 O s u +
        OrbitUnknottingFourier.endpointWeight s •
          ((2 * Real.pi) •
            OrbitUnknottingFourier.pairCombination
              (OrbitUnknottingFourier.circleTangent u) p)) u := by
  change HasDerivAt
    (fun z : ℝ => baseTrack (V := V) h2 O s z +
      OrbitUnknottingFourier.endpointWeight s •
        OrbitUnknottingFourier.perturbation p z) _ u
  exact (hasDerivAt_baseTrack (V := V) h2 O s u).add
    (HasDerivAt.const_smul
      (OrbitUnknottingFourier.endpointWeight s)
      (OrbitUnknottingFourier.hasDerivAt_perturbation p u))


-- @@ L151-171 verbatim
/-- In ambient dimension at least four, one parameter avoids both all
interior self-secants and all interior tangent failures. -/
theorem exists_goodParameter (h3 : 3 ≤ n) :
    ∃ p : OrbitUnknottingFourier.Parameter E,
      p ∉ Set.range
        (OrbitUnknottingFourier.secantBadMap
          (baseTrack (V := V) h2 O)) ∧
      p ∉ Set.range
        (OrbitUnknottingFourier.tangentBadMap
          (baseTangent (V := V) h2 O)) := by
  have hdim : 4 ≤ Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨p, _hpU, hpsec, hptan⟩ :=
    OrbitUnknottingFourier.exists_parameter_avoiding_badRanges
      (baseTrack (V := V) h2 O)
      (baseTangent (V := V) h2 O)
      (contDiff_baseTrack (V := V) h2 O)
      (contDiff_baseTangent (V := V) h2 O)
      hdim (U := Set.univ) isOpen_univ Set.univ_nonempty
  exact ⟨p, hpsec, hptan⟩


-- @@ L173-177 verbatim
/-- Descent of a perturbed period-one lift to the quotient circle. -/
def circleTrack (p : OrbitUnknottingFourier.Parameter E) (s : ℝ) : C → E :=
  (OrbitUnknottingFourier.periodic_perturbedTrack
    (baseTrack (V := V) h2 O)
    (fun t => periodic_baseTrack (V := V) h2 O t) p s).lift


-- @@ L179-184 verbatim
@[simp] theorem circleTrack_coe
    (p : OrbitUnknottingFourier.Parameter E) (s u : ℝ) :
    circleTrack (V := V) h2 O p s (u : C) =
      OrbitUnknottingFourier.perturbedTrack
        (baseTrack (V := V) h2 O) p s u := by
  rfl


-- @@ L186-216 verbatim
theorem continuous_circleTrack
    (p : OrbitUnknottingFourier.Parameter E) (s : ℝ) :
    Continuous (circleTrack (V := V) h2 O p s) := by
  have hs : ContDiff ℝ ∞
      (OrbitUnknottingFourier.perturbedTrack
        (baseTrack (V := V) h2 O) p s) :=
    (OrbitUnknottingFourier.contDiff_perturbedTrack
      (baseTrack (V := V) h2 O)
      (contDiff_baseTrack (V := V) h2 O) p).comp
        (contDiff_const.prodMk contDiff_id)
  have hraw : Continuous (fun a : C => fun i : Fin (n + 1) =>
      circleTrack (V := V) h2 O p s a i) := by
    apply continuous_pi
    intro i
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    have hi : Continuous (fun u : ℝ =>
        (OrbitUnknottingFourier.perturbedTrack
          (baseTrack (V := V) h2 O) p s u) i) :=
      (EuclideanSpace.proj i).continuous.comp hs.continuous
    apply hi.congr
    intro u
    change
      (OrbitUnknottingFourier.perturbedTrack
        (baseTrack (V := V) h2 O) p s u) i =
      circleTrack (V := V) h2 O p s (u : C) i
    rw [circleTrack_coe]
  have htop :=
    (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin (n + 1) => ℝ)).comp hraw
  apply htop.congr
  intro a
  exact WithLp.toLp_ofLp (2 : ENNReal) (circleTrack (V := V) h2 O p s a)


-- @@ L218-231 verbatim
theorem injective_circleTrack_of_interior
    (p : OrbitUnknottingFourier.Parameter E)
    (hp : p ∉ Set.range
      (OrbitUnknottingFourier.secantBadMap
        (baseTrack (V := V) h2 O)))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Function.Injective (circleTrack (V := V) h2 O p s) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective b
  apply OrbitUnknottingFourier.addCircle_eq_of_perturbedTrack_eq
    (baseTrack (V := V) h2 O)
    (fun t => periodic_baseTrack (V := V) h2 O t) p hp hs0 hs1
  simpa using hab


-- @@ L233-242 verbatim
theorem isEmbedding_circleTrack_of_interior
    (p : OrbitUnknottingFourier.Parameter E)
    (hp : p ∉ Set.range
      (OrbitUnknottingFourier.secantBadMap
        (baseTrack (V := V) h2 O)))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Topology.IsEmbedding (circleTrack (V := V) h2 O p s) :=
  (continuous_circleTrack (V := V) h2 O p s).isClosedEmbedding
    (injective_circleTrack_of_interior (V := V) h2 O p hp hs0 hs1)
    |>.isEmbedding


-- @@ L244-250 verbatim
theorem circleTrack_zero
    (p : OrbitUnknottingFourier.Parameter E) :
    circleTrack (V := V) h2 O p 0 = V.intrinsicOrbitEmbedding O := by
  funext a
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [circleTrack_coe, V.intrinsicOrbitEmbedding_coe]
  simp [OrbitUnknottingFourier.perturbedTrack, baseTrack]


-- @@ L252-259 verbatim
theorem circleTrack_one
    (p : OrbitUnknottingFourier.Parameter E) :
    circleTrack (V := V) h2 O p 1 =
      CanonicalRoundOrbit.circlePoint V h2 O := by
  funext a
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [circleTrack_coe, ← targetLift_eq_circlePoint (V := V) h2 O]
  simp [OrbitUnknottingFourier.perturbedTrack, baseTrack]


-- @@ L261-277 verbatim
theorem isEmbedding_circleTrack
    (p : OrbitUnknottingFourier.Parameter E)
    (hp : p ∉ Set.range
      (OrbitUnknottingFourier.secantBadMap
        (baseTrack (V := V) h2 O)))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Topology.IsEmbedding (circleTrack (V := V) h2 O p s) := by
  rcases hs with ⟨hs0, hs1⟩
  by_cases hzero : s = 0
  · rw [hzero, circleTrack_zero]
    exact V.isEmbedding_intrinsicOrbitEmbedding O
  by_cases hone : s = 1
  · rw [hone, circleTrack_one]
    exact isEmbedding_circlePoint (V := V) h2 O
  exact isEmbedding_circleTrack_of_interior (V := V) h2 O p hp
    (lt_of_le_of_ne hs0 (Ne.symm hzero))
    (lt_of_le_of_ne hs1 hone)


-- @@ L279-289 verbatim
theorem deriv_perturbedLift_ne_zero_of_interior
    (p : OrbitUnknottingFourier.Parameter E)
    (hp : p ∉ Set.range
      (OrbitUnknottingFourier.tangentBadMap
        (baseTangent (V := V) h2 O)))
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    deriv (OrbitUnknottingFourier.perturbedTrack
      (baseTrack (V := V) h2 O) p s) u ≠ 0 := by
  rw [(hasDerivAt_perturbedLift (V := V) h2 O p s u).deriv]
  exact OrbitUnknottingFourier.tangent_ne_zero_of_avoids_range
    (baseTangent (V := V) h2 O) p hp hs0 hs1


-- @@ L291-302 verbatim
/-- The complete embedded-circle path used by ambient extension. -/
structure EmbeddedCircleTrack where
  lift : ℝ → ℝ → E
  circle : ℝ → C → E
  smooth_lift : ContDiff ℝ ∞ (fun q : ℝ × ℝ => lift q.1 q.2)
  periodic_lift : ∀ s, Function.Periodic (lift s) 1
  circle_coe : ∀ (s u : ℝ), circle s (u : C) = lift s u
  start_circle : circle 0 = V.intrinsicOrbitEmbedding O
  finish_circle : circle 1 = CanonicalRoundOrbit.circlePoint V h2 O
  isEmbedding_circle : ∀ s ∈ Set.Icc (0 : ℝ) 1,
    Topology.IsEmbedding (circle s)
  interior_deriv_ne_zero : ∀ s u, 0 < s → s < 1 → deriv (lift s) u ≠ 0


-- @@ L304-331 verbatim
/-- Package a parameter avoiding both bad ranges into a verified embedded
circle track. -/
def embeddedCircleTrackOfParameter
    (p : OrbitUnknottingFourier.Parameter E)
    (hpsec : p ∉ Set.range
      (OrbitUnknottingFourier.secantBadMap
        (baseTrack (V := V) h2 O)))
    (hptan : p ∉ Set.range
      (OrbitUnknottingFourier.tangentBadMap
        (baseTangent (V := V) h2 O))) :
    EmbeddedCircleTrack (V := V) h2 O where
  lift := OrbitUnknottingFourier.perturbedTrack
    (baseTrack (V := V) h2 O) p
  circle := circleTrack (V := V) h2 O p
  smooth_lift := OrbitUnknottingFourier.contDiff_perturbedTrack
    (baseTrack (V := V) h2 O)
    (contDiff_baseTrack (V := V) h2 O) p
  periodic_lift := OrbitUnknottingFourier.periodic_perturbedTrack
    (baseTrack (V := V) h2 O)
    (fun t => periodic_baseTrack (V := V) h2 O t) p
  circle_coe := circleTrack_coe (V := V) h2 O p
  start_circle := circleTrack_zero (V := V) h2 O p
  finish_circle := circleTrack_one (V := V) h2 O p
  isEmbedding_circle := fun s hs =>
    isEmbedding_circleTrack (V := V) h2 O p hpsec hs
  interior_deriv_ne_zero := fun s u hs0 hs1 =>
    deriv_perturbedLift_ne_zero_of_interior
      (V := V) h2 O p hptan hs0 hs1


-- @@ L333-337 verbatim
theorem exists_embeddedCircleTrack (h3 : 3 ≤ n) :
    Nonempty (EmbeddedCircleTrack (V := V) h2 O) := by
  obtain ⟨p, hpsec, hptan⟩ := exists_goodParameter (V := V) h2 O h3
  exact ⟨embeddedCircleTrackOfParameter
    (V := V) h2 O p hpsec hptan⟩


-- @@ L339-339 verbatim
end FourierEmbeddingTrack

-- @@ L340-340 verbatim
end TamedField

-- @@ L341-341 verbatim
end Submission
