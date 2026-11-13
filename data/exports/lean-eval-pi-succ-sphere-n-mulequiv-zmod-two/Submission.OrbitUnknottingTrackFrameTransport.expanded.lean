import Mathlib
import Submission.OrbitUnknottingFourierFiniteC1Subdivision
import Submission.OrbitUnknottingTubularChart


-- @@ L5-21 verbatim
/-!
# Smooth full-frame transport along a Fourier circle track

The first slice of the Fourier track carries the canonical orbit frame.  For
two slices whose positive unit tangents are never antipodal, reflection in
the pointwise bisector line transports the whole orthonormal frame from the
first tangent to the second.  The reflection is written by its rational
formula, so its dependence on the phase is visibly smooth.

The only quantitative hypothesis needed by one transport step is

`-1 < ⟪unitTangent s u, unitTangent t u⟫`.

At the end of the file, compact uniform continuity produces a finite equal
subdivision for which this condition holds at every adjacent pair and every
real phase.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 800000


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open Set Function Module Finset InnerProductSpace

-- @@ L29-29 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L31-31 verbatim
namespace Submission

-- @@ L32-32 verbatim
namespace TamedField

-- @@ L33-33 verbatim
namespace FourierEmbeddingTrack

-- @@ L34-34 verbatim
namespace EmbeddedCircleTrack


-- @@ L36-36 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}


-- @@ L38-38 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L40-40 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L42-42 verbatim
/-! ## The positive unit phase tangent -/


-- @@ L44-44 verbatim
variable (T : EmbeddedCircleTrack (V := V) h2 O)


-- @@ L46-49 verbatim
/-- The phase derivative normalized with a positive scalar.  All uses below
carry a proof that the derivative is nonzero. -/
def unitPhaseTangent (s u : ℝ) : E :=
  ‖deriv (T.lift s) u‖⁻¹ • deriv (T.lift s) u


-- @@ L51-55 verbatim
theorem norm_unitPhaseTangent {s u : ℝ}
    (hD : deriv (T.lift s) u ≠ 0) :
    ‖T.unitPhaseTangent s u‖ = 1 := by
  have hn : ‖deriv (T.lift s) u‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  simp [unitPhaseTangent, norm_smul, hn]


-- @@ L57-61 verbatim
theorem inner_unitPhaseTangent_self {s u : ℝ}
    (hD : deriv (T.lift s) u ≠ 0) :
    ⟪T.unitPhaseTangent s u, T.unitPhaseTangent s u⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, T.norm_unitPhaseTangent hD]
  norm_num


-- @@ L63-73 verbatim
/-- Smoothness of a normalized slice tangent, under the exact nonvanishing
hypothesis needed for normalization. -/
theorem contDiff_unitPhaseTangent (s : ℝ)
    (hD : ∀ u, deriv (T.lift s) u ≠ 0) :
    ContDiff ℝ ∞ (T.unitPhaseTangent s) := by
  have hderiv : ContDiff ℝ ∞ (fun u => deriv (T.lift s) u) := by
    exact (FourierFiniteC1Subdivision.EmbeddedCircleTrack.contDiff_phaseDeriv
      (V := V) (h2 := h2) (O := O) T).comp
        (contDiff_const.prodMk contDiff_id)
  exact (ContDiff.norm ℝ hderiv hD).inv
      (fun u => norm_ne_zero_iff.mpr (hD u)) |>.smul hderiv


-- @@ L75-83 verbatim
/-- The positive unit phase tangent is period one. -/
theorem periodic_unitPhaseTangent (s : ℝ) :
    Function.Periodic (T.unitPhaseTangent s) 1 := by
  intro u
  have hperiod :=
    FourierFiniteC1Subdivision.EmbeddedCircleTrack.periodic_phaseDeriv
      (V := V) (h2 := h2) (O := O) T s u
  simp only [unitPhaseTangent]
  rw [show deriv (T.lift s) (u + 1) = deriv (T.lift s) u from hperiod]


-- @@ L85-94 verbatim
/-- Reduce a unit tangent at an arbitrary real phase to the compact
fundamental interval. -/
theorem unitPhaseTangent_eq_fract (s u : ℝ) :
    T.unitPhaseTangent s u = T.unitPhaseTangent s (Int.fract u) := by
  have hperiod := (T.periodic_unitPhaseTangent s).zsmul ⌊u⌋
  have h := hperiod (Int.fract u)
  have hpoint : Int.fract u + ⌊u⌋ • (1 : ℝ) = u := by
    simpa only [Int.smul_one_eq_cast] using Int.fract_add_floor u
  rw [hpoint] at h
  exact h


-- @@ L96-96 verbatim
/-! ## Endpoint nonvanishing -/


-- @@ L98-106 verbatim
/-- The lift at the source endpoint is literally the intrinsic orbit lift. -/
theorem track_lift_zero (u : ℝ) :
    T.lift 0 u = V.intrinsicOrbitLift O u := by
  calc
    T.lift 0 u = T.circle 0 (u : AddCircle (1 : ℝ)) :=
      (T.circle_coe 0 u).symm
    _ = V.intrinsicOrbitEmbedding O (u : AddCircle (1 : ℝ)) := by
      rw [T.start_circle]
    _ = V.intrinsicOrbitLift O u := V.intrinsicOrbitEmbedding_coe O u


-- @@ L108-112 verbatim
theorem track_deriv_zero (u : ℝ) :
    deriv (T.lift 0) u = deriv (V.intrinsicOrbitLift O) u := by
  congr 1
  funext v
  exact T.track_lift_zero v


-- @@ L114-124 verbatim
/-- The lift at the target endpoint is literally the canonical round lift. -/
theorem track_lift_one (u : ℝ) :
    T.lift 1 u = targetLift (V := V) h2 O u := by
  calc
    T.lift 1 u = T.circle 1 (u : AddCircle (1 : ℝ)) :=
      (T.circle_coe 1 u).symm
    _ = CanonicalRoundOrbit.circlePoint V h2 O
        (u : AddCircle (1 : ℝ)) := by
      rw [T.finish_circle]
    _ = targetLift (V := V) h2 O u :=
      (targetLift_eq_circlePoint (V := V) h2 O u).symm


-- @@ L126-148 verbatim
theorem hasDerivAt_targetLift (u : ℝ) :
    HasDerivAt (targetLift (V := V) h2 O)
      ((2 * Real.pi) • OrbitUnknottingFourier.pairCombination
        (OrbitUnknottingFourier.circleTangent u)
        (CanonicalRoundOrbit.e₀ (n := n) h2,
          CanonicalRoundOrbit.e₁ (n := n) h2)) u := by
  have hfun : targetLift (V := V) h2 O =
      (fun _ : ℝ => CanonicalRoundOrbit.center V h2 O) +
        OrbitUnknottingFourier.perturbation
          (CanonicalRoundOrbit.e₀ (n := n) h2,
            CanonicalRoundOrbit.e₁ (n := n) h2) := by
    funext y
    simp [targetLift, CanonicalRoundOrbit.point,
      OrbitUnknottingFourier.perturbation,
      OrbitUnknottingFourier.pairCombination,
      OrbitUnknottingFourier.circleLift]
    abel
  have h := (hasDerivAt_const u (CanonicalRoundOrbit.center V h2 O)).add
    (OrbitUnknottingFourier.hasDerivAt_perturbation
      (CanonicalRoundOrbit.e₀ (n := n) h2,
        CanonicalRoundOrbit.e₁ (n := n) h2) u)
  rw [hfun]
  simpa using h


-- @@ L150-167 verbatim
theorem deriv_targetLift_ne_zero (u : ℝ) :
    deriv (targetLift (V := V) h2 O) u ≠ 0 := by
  rw [(hasDerivAt_targetLift (V := V) (h2 := h2) (O := O) u).deriv]
  intro hzero
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcomb : OrbitUnknottingFourier.pairCombination
      (OrbitUnknottingFourier.circleTangent u)
      (CanonicalRoundOrbit.e₀ (n := n) h2,
        CanonicalRoundOrbit.e₁ (n := n) h2) = 0 :=
    (smul_eq_zero.mp hzero).resolve_left hpi
  have h₀ := congrArg
    (fun x : E => x (⟨0, by omega⟩ : Fin (n + 1))) hcomb
  have h₁ := congrArg
    (fun x : E => x (⟨1, by omega⟩ : Fin (n + 1))) hcomb
  simp [OrbitUnknottingFourier.pairCombination,
    OrbitUnknottingFourier.circleTangent,
    CanonicalRoundOrbit.e₀, CanonicalRoundOrbit.e₁] at h₀ h₁
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * u)]


-- @@ L169-173 verbatim
theorem track_deriv_one (u : ℝ) :
    deriv (T.lift 1) u = deriv (targetLift (V := V) h2 O) u := by
  congr 1
  funext v
  exact T.track_lift_one v


-- @@ L175-190 verbatim
/-- Every slice in the closed track interval is an immersion, including the
two explicitly controlled endpoints. -/
theorem deriv_ne_zero_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (u : ℝ) :
    deriv (T.lift s) u ≠ 0 := by
  rcases hs with ⟨hs0, hs1⟩
  by_cases h0 : s = 0
  · subst s
    rw [T.track_deriv_zero]
    exact V.deriv_intrinsicOrbitLift_ne_zero O u
  by_cases h1 : s = 1
  · subst s
    rw [T.track_deriv_one]
    exact deriv_targetLift_ne_zero (V := V) (h2 := h2) (O := O) u
  exact T.interior_deriv_ne_zero s u
    (lt_of_le_of_ne hs0 (Ne.symm h0))
    (lt_of_le_of_ne hs1 h1)


-- @@ L192-192 verbatim
/-! ## A smooth frame at one slice -/


-- @@ L194-202 verbatim
/-- A smooth, period-one orthonormal full frame along one track slice.  Its
first vector is exactly the positive unit phase derivative. -/
structure SmoothSliceFrame (s : ℝ) where
  frame : ℝ → Fin (n + 1) → E
  smooth : ∀ i, ContDiff ℝ ∞ (fun u => frame u i)
  periodic : ∀ i, Function.Periodic (fun u => frame u i) 1
  orthonormal : ∀ u, Orthonormal ℝ (frame u)
  deriv_ne_zero : ∀ u, deriv (T.lift s) u ≠ 0
  tangent_first : ∀ u, frame u 0 = T.unitPhaseTangent s u


-- @@ L204-204 verbatim
namespace SmoothSliceFrame


-- @@ L206-230 verbatim
/-- The canonical orbit frame supplies the frame at time zero. -/
def initial : T.SmoothSliceFrame 0 where
  frame := fun u i => V.orbitFrameVector O i u
  smooth := fun i => V.contDiff_orbitFrameVector O i
  periodic := fun i u => by
    simp [TamedField.orbitFrameVector, V.periodic_intrinsicOrbitLift O u]
  orthonormal := fun u => by
    apply gramSchmidtNormed_orthonormal
    exact linearIndependent_frameAt X (X.fiber_subset_regularSet
      (V.flow_mem_fiber (V.orbitPoint_mem_fiber O)
        (u * V.orbitPeriod O)))
  deriv_ne_zero := fun u => by
    rw [T.track_deriv_zero]
    exact V.deriv_intrinsicOrbitLift_ne_zero O u
  tangent_first := fun u => by
    have hmem : V.intrinsicOrbitLift O u ∈ X.fiber :=
      V.flow_mem_fiber (V.orbitPoint_mem_fiber O)
        (u * V.orbitPeriod O)
    rw [TamedField.orbitFrameVector, V.orbitFrameVector_zero O u,
      unitPhaseTangent, T.track_deriv_zero,
      V.norm_deriv_intrinsicOrbitLift O u,
      (V.hasDerivAt_intrinsicOrbitLift O u).deriv,
      V.v_eq_tau_of_mem_fiber hmem, smul_smul]
    field_simp [ne_of_gt (V.orbitPeriod_pos O)]
    simp


-- @@ L232-232 verbatim
end SmoothSliceFrame


-- @@ L234-234 verbatim
/-! ## Smooth bisector reflection -/


-- @@ L236-239 verbatim
/-- Reflection in the line generated by `a+b`, written in a form whose
smooth dependence on non-antipodal `a,b` is explicit. -/
def bisectorReflection (a b x : E) : E :=
  (2 * (⟪a + b, x⟫_ℝ / ⟪a + b, a + b⟫_ℝ)) • (a + b) - x


-- @@ L241-253 verbatim
theorem contDiff_bisectorReflection
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {a b x : A → E}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hx : ContDiff ℝ ∞ x) (hne : ∀ q, a q + b q ≠ 0) :
    ContDiff ℝ ∞ (fun q => bisectorReflection (a q) (b q) (x q)) := by
  have hc : ContDiff ℝ ∞ (fun q => a q + b q) := ha.add hb
  have hden : ∀ q, ⟪a q + b q, a q + b q⟫_ℝ ≠ 0 := by
    intro q
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne q))
  exact (((contDiff_const.mul ((ContDiff.inner ℝ hc hx).div
      (ContDiff.inner ℝ hc hc) hden))).smul hc).sub hx


-- @@ L255-259 verbatim
theorem bisectorReflection_eq_reflection {a b x : E} :
    bisectorReflection a b x = (ℝ ∙ (a + b)).reflection x := by
  unfold bisectorReflection
  rw [Submodule.reflection_singleton_apply, real_inner_self_eq_norm_sq]
  module


-- @@ L261-271 verbatim
theorem add_ne_zero_of_unit_inner_gt_neg_one {a b : E}
    (ha : ⟪a, a⟫_ℝ = 1)
    (hab : -1 < ⟪a, b⟫_ℝ) : a + b ≠ 0 := by
  intro hzero
  have hinner : ⟪a, a⟫_ℝ + ⟪a, b⟫_ℝ = 0 := by
    calc
      ⟪a, a⟫_ℝ + ⟪a, b⟫_ℝ = ⟪a, a + b⟫_ℝ := by
        rw [inner_add_right]
      _ = 0 := by rw [hzero, inner_zero_right]
  rw [ha] at hinner
  linarith


-- @@ L273-291 verbatim
theorem bisectorReflection_self_to_target {a b : E}
    (ha : ⟪a, a⟫_ℝ = 1) (hb : ⟪b, b⟫_ℝ = 1)
    (hab : -1 < ⟪a, b⟫_ℝ) :
    bisectorReflection a b a = b := by
  have hba : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := (real_inner_comm b a).symm
  have hnum : ⟪a + b, a⟫_ℝ = 1 + ⟪a, b⟫_ℝ := by
    rw [inner_add_left, ha, hba]
  have hden : ⟪a + b, a + b⟫_ℝ = 2 * (1 + ⟪a, b⟫_ℝ) := by
    rw [inner_add_left, inner_add_right, inner_add_right, ha, hb,
      hba]
    ring
  have hne : 1 + ⟪a, b⟫_ℝ ≠ 0 := by linarith
  unfold bisectorReflection
  rw [hnum, hden]
  have hcoef : 2 * ((1 + ⟪a, b⟫_ℝ) /
      (2 * (1 + ⟪a, b⟫_ℝ))) = 1 := by
    field_simp
  rw [hcoef, one_smul]
  abel


-- @@ L293-298 verbatim
theorem inner_bisectorReflection {a b x y : E} :
    ⟪bisectorReflection a b x, bisectorReflection a b y⟫_ℝ =
      ⟪x, y⟫_ℝ := by
  rw [bisectorReflection_eq_reflection,
    bisectorReflection_eq_reflection]
  exact LinearIsometryEquiv.inner_map_map _ _ _


-- @@ L300-300 verbatim
/-! ## One frame-transport step -/


-- @@ L302-302 verbatim
namespace SmoothSliceFrame


-- @@ L304-342 verbatim
/-- Transport a framed slice to a second slice by the canonical smooth
bisector reflection.  Non-antipodality of the two positive unit tangents is
the sole geometric hypothesis. -/
def transport {s t : ℝ} (F : T.SmoothSliceFrame s)
    (ht : ∀ u, deriv (T.lift t) u ≠ 0)
    (hshort : ∀ u,
      -1 < ⟪T.unitPhaseTangent s u, T.unitPhaseTangent t u⟫_ℝ) :
    T.SmoothSliceFrame t where
  frame := fun u i => bisectorReflection
    (F.frame u 0) (T.unitPhaseTangent t u) (F.frame u i)
  smooth := fun i => by
    apply contDiff_bisectorReflection (F.smooth 0)
      (T.contDiff_unitPhaseTangent t ht) (F.smooth i)
    intro u
    rw [F.tangent_first u]
    exact add_ne_zero_of_unit_inner_gt_neg_one
      (T.inner_unitPhaseTangent_self (F.deriv_ne_zero u))
      (hshort u)
  periodic := fun i u => by
    change bisectorReflection
      (F.frame (u + 1) 0) (T.unitPhaseTangent t (u + 1))
        (F.frame (u + 1) i) =
      bisectorReflection (F.frame u 0) (T.unitPhaseTangent t u)
        (F.frame u i)
    rw [show F.frame (u + 1) 0 = F.frame u 0 from F.periodic 0 u,
      show F.frame (u + 1) i = F.frame u i from F.periodic i u,
      show T.unitPhaseTangent t (u + 1) = T.unitPhaseTangent t u from
        T.periodic_unitPhaseTangent t u]
  orthonormal := fun u => by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_bisectorReflection]
    exact orthonormal_iff_ite.mp (F.orthonormal u) i j
  deriv_ne_zero := ht
  tangent_first := fun u => by
    rw [F.tangent_first u]
    exact bisectorReflection_self_to_target
      (T.inner_unitPhaseTangent_self (F.deriv_ne_zero u))
      (T.inner_unitPhaseTangent_self (ht u)) (hshort u)


-- @@ L344-344 verbatim
end SmoothSliceFrame


-- @@ L346-346 verbatim
/-! ## A uniformly short finite subdivision -/


-- @@ L348-366 verbatim
/-- Joint continuity of the positive unit tangent on the compact
time--phase square. -/
theorem continuousOn_unitPhaseTangent_square :
    ContinuousOn
      (fun q : ℝ × ℝ => T.unitPhaseTangent q.1 q.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  intro q hq
  have hderiv : ContDiffAt ℝ ∞
      (fun z : ℝ × ℝ =>
        FourierFiniteC1Subdivision.EmbeddedCircleTrack.phaseDeriv
          (V := V) (h2 := h2) (O := O) T z.1 z.2) q :=
    (FourierFiniteC1Subdivision.EmbeddedCircleTrack.contDiff_phaseDeriv
      (V := V) (h2 := h2) (O := O) T).contDiffAt
  have hne : FourierFiniteC1Subdivision.EmbeddedCircleTrack.phaseDeriv
      (V := V) (h2 := h2) (O := O) T q.1 q.2 ≠ 0 := by
    exact T.deriv_ne_zero_of_mem_Icc hq.1 q.2
  have hnorm := hderiv.norm ℝ hne
  have hsmooth := (hnorm.inv (norm_ne_zero_iff.mpr hne)).smul hderiv
  exact hsmooth.continuousAt.continuousWithinAt


-- @@ L368-428 verbatim
/-- Adjacent normalized tangents of a sufficiently fine equal subdivision
are uniformly closer than `2`, for every real phase. -/
theorem exists_uniform_unitTangent_equisubdivision :
    ∃ m : ℕ, 0 < m ∧
      ∀ k : ℕ, k < m → ∀ u : ℝ,
        ‖T.unitPhaseTangent ((k : ℝ) / (m : ℝ)) u -
          T.unitPhaseTangent (((k + 1 : ℕ) : ℝ) / (m : ℝ)) u‖ < 2 := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have huniform : UniformContinuousOn
      (fun q : ℝ × ℝ => T.unitPhaseTangent q.1 q.2) K :=
    hK.uniformContinuousOn_of_continuous
      T.continuousOn_unitPhaseTangent_square
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform 2 (by norm_num)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨j + 1, Nat.succ_pos j, ?_⟩
  intro k hk u
  let v : ℝ := Int.fract u
  have hv : v ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hmpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hk_le : k ≤ j + 1 := Nat.le_of_lt hk
  have hk_succ_le : k + 1 ≤ j + 1 := by omega
  have htime₀ : (k : ℝ) / ((j + 1 : ℕ) : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hmpos).2 (by exact_mod_cast hk_le)
  have htime₁ : ((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ∈
      Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hmpos).2 (by exact_mod_cast hk_succ_le)
  have hstep :
      dist ((k : ℝ) / ((j + 1 : ℕ) : ℝ))
          (((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) =
        1 / ((j + 1 : ℕ) : ℝ) := by
    rw [Real.dist_eq]
    have hle :
        (k : ℝ) / ((j + 1 : ℕ) : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.le_succ k) hmpos.le
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    field_simp
    norm_num
  have hdist :
      dist (((k : ℝ) / ((j + 1 : ℕ) : ℝ)), v)
        ((((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)), v) < δ := by
    rw [dist_prod_same_right, hstep]
    simpa only [Nat.cast_add, Nat.cast_one] using hj
  have hout := hnear
    (((k : ℝ) / ((j + 1 : ℕ) : ℝ)), v) ⟨htime₀, hv⟩
    ((((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)), v) ⟨htime₁, hv⟩
    hdist
  rw [dist_eq_norm] at hout
  rw [T.unitPhaseTangent_eq_fract
      ((k : ℝ) / ((j + 1 : ℕ) : ℝ)) u,
    T.unitPhaseTangent_eq_fract
      (((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) u]
  exact hout


-- @@ L430-460 verbatim
/-- The preceding `< 2` estimate is exactly the non-antipodality condition
required by `SmoothSliceFrame.transport`. -/
theorem exists_uniform_nonantipodal_equisubdivision :
    ∃ m : ℕ, 0 < m ∧
      ∀ k : ℕ, k < m → ∀ u : ℝ,
        -1 < ⟪T.unitPhaseTangent ((k : ℝ) / (m : ℝ)) u,
          T.unitPhaseTangent (((k + 1 : ℕ) : ℝ) / (m : ℝ)) u⟫_ℝ := by
  obtain ⟨m, hm, hclose⟩ := T.exists_uniform_unitTangent_equisubdivision
  refine ⟨m, hm, ?_⟩
  intro k hk u
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hk0 : (k : ℝ) / (m : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hmR).2 (by exact_mod_cast Nat.le_of_lt hk)
  have hk1 : ((k + 1 : ℕ) : ℝ) / (m : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hmR).2 (by exact_mod_cast hk)
  let a := T.unitPhaseTangent ((k : ℝ) / (m : ℝ)) u
  let b := T.unitPhaseTangent (((k + 1 : ℕ) : ℝ) / (m : ℝ)) u
  have ha : ‖a‖ = 1 :=
    T.norm_unitPhaseTangent (T.deriv_ne_zero_of_mem_Icc hk0 u)
  have hb : ‖b‖ = 1 :=
    T.norm_unitPhaseTangent (T.deriv_ne_zero_of_mem_Icc hk1 u)
  have hsq : ‖a - b‖ ^ 2 = 2 - 2 * ⟪a, b⟫_ℝ := by
    rw [norm_sub_sq_real, ha, hb]
    ring
  have hnonneg : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hlt : ‖a - b‖ < 2 := hclose k hk u
  nlinarith


-- @@ L462-490 verbatim
/-- Starting from the canonical frame at grid point zero, the short-step
reflection constructs a smooth framed slice at every grid point.  The proof
is a literal recursion in the grid index. -/
theorem nonempty_smoothSliceFrame_at_equisubdivision
    {m : ℕ} (hm : 0 < m)
    (hshort : ∀ k : ℕ, k < m → ∀ u : ℝ,
      -1 < ⟪T.unitPhaseTangent ((k : ℝ) / (m : ℝ)) u,
        T.unitPhaseTangent (((k + 1 : ℕ) : ℝ) / (m : ℝ)) u⟫_ℝ) :
    ∀ k : ℕ, k ≤ m →
      Nonempty (T.SmoothSliceFrame ((k : ℝ) / (m : ℝ))) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa using (Nonempty.intro (SmoothSliceFrame.initial (T := T)))
  | succ k ih =>
      intro hk
      have hkbase : k ≤ m := Nat.le_trans (Nat.le_succ k) hk
      obtain ⟨F⟩ := ih hkbase
      have hklt : k < m := Nat.lt_of_succ_le hk
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have htarget : ((k + 1 : ℕ) : ℝ) / (m : ℝ) ∈
          Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · exact (div_le_one hmR).2 (by exact_mod_cast hk)
      exact ⟨SmoothSliceFrame.transport (T := T) F
        (fun u => T.deriv_ne_zero_of_mem_Icc htarget u)
        (hshort k hklt)⟩


-- @@ L492-503 verbatim
/-- A finite equal subdivision simultaneously has short adjacent tangents
and recursively transported smooth orthonormal frames at all grid points. -/
theorem exists_framed_nonantipodal_equisubdivision :
    ∃ m : ℕ, 0 < m ∧
      (∀ k : ℕ, k < m → ∀ u : ℝ,
        -1 < ⟪T.unitPhaseTangent ((k : ℝ) / (m : ℝ)) u,
          T.unitPhaseTangent (((k + 1 : ℕ) : ℝ) / (m : ℝ)) u⟫_ℝ) ∧
      (∀ k : ℕ, k ≤ m →
        Nonempty (T.SmoothSliceFrame ((k : ℝ) / (m : ℝ)))) := by
  obtain ⟨m, hm, hshort⟩ := T.exists_uniform_nonantipodal_equisubdivision
  exact ⟨m, hm, hshort,
    T.nonempty_smoothSliceFrame_at_equisubdivision hm hshort⟩


-- @@ L505-505 verbatim
end EmbeddedCircleTrack

-- @@ L506-506 verbatim
end FourierEmbeddingTrack

-- @@ L507-507 verbatim
end TamedField

-- @@ L508-508 verbatim
end Submission
