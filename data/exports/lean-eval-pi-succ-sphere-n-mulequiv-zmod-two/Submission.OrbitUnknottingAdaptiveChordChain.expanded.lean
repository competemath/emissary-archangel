import Mathlib
import Submission.OrbitUnknottingChordStepAssembly
import Submission.OrbitUnknottingFourierTraceSupport
import Submission.OrbitUnknottingFramedCircleRelativeSupport


-- @@ L6-26 verbatim
/-!
# Adaptive supported chord chains along a relative circle track

The canonical tube attached to a framed slice need not have support disjoint
from the other orbit components.  Nor is there an a priori uniform lower
bound for the radii of those independently chosen tubes.  This file avoids
both issues.

First, frame transport and connectedness give a smooth full frame on every
slice of the track.  At each time we then choose a radial bump whose support
lies in one fixed open thickening of the complete relative track trace.  The
parametric extension theorem supplies a (time-dependent) neighborhood on
which the literal chord is a small ambient displacement.

The resulting neighborhoods form an open cover of the compact parameter
interval.  A Lebesgue-number partition refines that cover.  Each small
partition interval is connected through the center of one cover member;
the first half is the inverse of a local chord move.  Thus no uniform tube
radius and no circular ``choose a mesh, then inspect its radii'' argument is
required.
-/


-- @@ L28-28 verbatim
set_option autoImplicit false

-- @@ L29-29 verbatim
set_option maxHeartbeats 2000000


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
open Set Function Module InnerProductSpace Metric Filter

-- @@ L34-34 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L36-36 verbatim
namespace Submission


-- @@ L38-38 verbatim
local notation "E[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L39-39 verbatim
local notation "N[" n "]" => EuclideanSpace ℝ (Fin n)

-- @@ L40-40 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L42-42 verbatim
/-! ## Reversing and composing ambient track steps -/


-- @@ L44-44 verbatim
namespace SmoothAmbientIsotopy


-- @@ L46-46 verbatim
variable {n : ℕ}


-- @@ L48-78 verbatim
/-- The spatial derivative of the forward map of an ambient isotopy is
surjective on the geometric time interval.  This is the forward analogue of
the field stored in `SmoothAmbientIsotopy`, obtained by differentiating the
right-inverse identity. -/
theorem forward_fderiv_surjective (A : SmoothAmbientIsotopy n)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : E[n]) :
    Surjective (fderiv ℝ (A.forward s) x) := by
  let f : E[n] → E[n] := A.forward s
  let g : E[n] → E[n] := A.inverse s
  have hf : ContDiff ℝ ∞ f := A.contDiff_forward_slice s
  have hg : ContDiff ℝ ∞ g := A.contDiff_inverse_slice s
  let y : E[n] := f x
  have hgy : g y = x := A.left_inv s hs x
  have hfg : (fun z => f (g z)) = id := by
    funext z
    exact A.right_inv s hs z
  have hcomp : HasFDerivAt (fun z => f (g z))
      ((fderiv ℝ f (g y)).comp (fderiv ℝ g y)) y :=
    ((hf.differentiable (by simp) (g y)).hasFDerivAt.comp y
      (hg.differentiable (by simp) y).hasFDerivAt)
  rw [hfg] at hcomp
  have hderiv0 : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) =
      ContinuousLinearMap.id ℝ E[n] :=
    hcomp.fderiv.symm.trans (hasFDerivAt_id y).fderiv
  have hderiv : (fderiv ℝ f x).comp (fderiv ℝ g y) =
      ContinuousLinearMap.id ℝ E[n] := by
    rwa [hgy] at hderiv0
  intro z
  refine ⟨fderiv ℝ g y z, ?_⟩
  have hz := congrArg (fun L : E[n] →L[ℝ] E[n] => L z) hderiv
  simpa [ContinuousLinearMap.comp_apply] using hz


-- @@ L80-93 verbatim
/-- Reverse an ambient isotopy by exchanging its forward and inverse
families. -/
def symm (A : SmoothAmbientIsotopy n) : SmoothAmbientIsotopy n where
  forward := A.inverse
  inverse := A.forward
  forward_smooth := A.inverse_smooth
  inverse_smooth := A.forward_smooth
  forward_zero := by
    funext x
    exact A.inverse_zero x
  left_inv := fun s hs => A.right_inv s hs
  right_inv := fun s hs => A.left_inv s hs
  inverse_fderiv_surjective := fun s hs x =>
    A.forward_fderiv_surjective s hs x


-- @@ L95-97 verbatim
@[simp] theorem symm_forward (A : SmoothAmbientIsotopy n) (s : ℝ) (x : E[n]) :
    A.symm.forward s x = A.inverse s x :=
  rfl


-- @@ L99-101 verbatim
@[simp] theorem symm_inverse (A : SmoothAmbientIsotopy n) (s : ℝ) (x : E[n]) :
    A.symm.inverse s x = A.forward s x :=
  rfl


-- @@ L103-106 verbatim
theorem FixedOn.symm {A : SmoothAmbientIsotopy n} {K : Set E[n]}
    (hA : A.FixedOn K) : A.symm.FixedOn K := by
  intro s hs x hx
  exact hA.inverse_eq hs hx


-- @@ L108-108 verbatim
end SmoothAmbientIsotopy


-- @@ L110-110 verbatim
namespace TamedField

-- @@ L111-111 verbatim
namespace FourierEmbeddingTrack


-- @@ L113-113 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L114-114 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}

-- @@ L115-115 verbatim
variable {T : EmbeddedCircleTrack (V := V) h2 O}


-- @@ L117-117 verbatim
namespace AmbientTrackStep


-- @@ L119-127 verbatim
/-- Reverse a track step using the inverse ambient isotopy. -/
def symm {s t : ℝ} (M : AmbientTrackStep T s t) :
    AmbientTrackStep T t s where
  move := M.move.symm
  endpoint_lift u := by
    change M.move.inverse 1 (T.lift t u) = T.lift s u
    rw [← M.endpoint_lift u]
    exact M.move.left_inv 1 ⟨zero_le_one, le_rfl⟩ (T.lift s u)
  fixed_obstacle := M.fixed_obstacle.symm


-- @@ L129-136 verbatim
/-- Compose two compatible track steps into one step. -/
def trans {s t r : ℝ} (M₁ : AmbientTrackStep T s t)
    (M₂ : AmbientTrackStep T t r) : AmbientTrackStep T s r where
  move := M₁.move.followedBy M₂.move
  endpoint_lift u := by
    rw [SmoothAmbientIsotopy.followedBy_forward,
      M₁.endpoint_lift, M₂.endpoint_lift]
  fixed_obstacle := M₁.fixed_obstacle.followedBy M₂.fixed_obstacle


-- @@ L138-138 verbatim
end AmbientTrackStep


-- @@ L140-140 verbatim
namespace AmbientTrackChain


-- @@ L142-148 verbatim
/-- Assemble the first `m` steps of an arbitrary parameter sequence. -/
def sequencePrefix (q : ℕ → ℝ)
    (steps : ∀ k : ℕ, AmbientTrackStep T (q k) (q (k + 1))) :
    ∀ m : ℕ, AmbientTrackChain T (q 0) (q m)
  | 0 => .refl _
  | m + 1 => append (sequencePrefix q steps m)
      (.cons (steps m) (.refl _))


-- @@ L150-150 verbatim
end AmbientTrackChain


-- @@ L152-152 verbatim
namespace EmbeddedCircleTrack


-- @@ L154-154 verbatim
variable (T : EmbeddedCircleTrack (V := V) h2 O)


-- @@ L156-156 verbatim
/-! ## A frame on every slice -/


-- @@ L158-186 verbatim
/-- A connectedness helper stated in the metric form used below. -/
private theorem subset_of_relOpen_closed_metric
    {S A : Set ℝ} (hS : IsPreconnected S) (hsub : A ⊆ S)
    (hclosed : IsClosed A)
    (hopen : ∀ z ∈ A, ∃ r > 0, S ∩ Metric.ball z r ⊆ A)
    (hne : A.Nonempty) : S ⊆ A := by
  classical
  choose! rad hradpos hradsub using hopen
  let U : Set ℝ := ⋃ z ∈ A, Metric.ball z (rad z)
  have hUopen : IsOpen U := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hAU : A ⊆ U := fun z hz =>
    Set.mem_biUnion hz (Metric.mem_ball_self (hradpos z hz))
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
  obtain ⟨z₀, hz₀⟩ := hne
  have h₁ : (S ∩ U).Nonempty := ⟨z₀, hsub hz₀, hAU hz₀⟩
  have h₂ : (S ∩ Aᶜ).Nonempty := ⟨s, hs, hsA⟩
  obtain ⟨w, hwS, hwU, hwA⟩ :=
    hS U Aᶜ hUopen hclosed.isOpen_compl hcover h₁ h₂
  exact hwA (hUS ⟨hwU, hwS⟩)


-- @@ L188-227 verbatim
/-- Uniformly close times have non-antipodal positive unit tangents, at
every real phase. -/
theorem exists_uniform_nonantipodal_radius :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {s t : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        |t - s| < δ → ∀ u : ℝ,
          -1 < ⟪T.unitPhaseTangent s u,
            T.unitPhaseTangent t u⟫_ℝ := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have huniform : UniformContinuousOn
      (fun q : ℝ × ℝ => T.unitPhaseTangent q.1 q.2) K :=
    hK.uniformContinuousOn_of_continuous
      T.continuousOn_unitPhaseTangent_square
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform 2 (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht hst u
  let v : ℝ := Int.fract u
  have hv : v ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hdist : dist (s, v) (t, v) < δ := by
    rw [dist_prod_same_right, Real.dist_eq]
    simpa [abs_sub_comm] using hst
  have hout := hnear (s, v) ⟨hs, hv⟩ (t, v) ⟨ht, hv⟩ hdist
  rw [dist_eq_norm] at hout
  rw [T.unitPhaseTangent_eq_fract s u,
    T.unitPhaseTangent_eq_fract t u]
  let a := T.unitPhaseTangent s v
  let b := T.unitPhaseTangent t v
  have ha : ‖a‖ = 1 :=
    T.norm_unitPhaseTangent (T.deriv_ne_zero_of_mem_Icc hs v)
  have hb : ‖b‖ = 1 :=
    T.norm_unitPhaseTangent (T.deriv_ne_zero_of_mem_Icc ht v)
  have hsq : ‖a - b‖ ^ 2 = 2 - 2 * ⟪a, b⟫_ℝ := by
    rw [norm_sub_sq_real, ha, hb]
    ring
  have hnonneg : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hlt : ‖a - b‖ < 2 := hout
  nlinarith


-- @@ L229-277 verbatim
/-- Every time in the closed track interval carries a smooth periodic full
frame.  The framed-time set is relatively open by forward transport and
closed by backward transport from nearby framed times; connectedness of the
interval then propagates the canonical initial frame to every slice. -/
theorem nonempty_smoothSliceFrame_of_mem_Icc {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    Nonempty (T.SmoothSliceFrame s) := by
  obtain ⟨δ, hδ, hshort⟩ := T.exists_uniform_nonantipodal_radius
  let A : Set ℝ :=
    {t | t ∈ Icc (0 : ℝ) 1 ∧ Nonempty (T.SmoothSliceFrame t)}
  have hsub : A ⊆ Icc (0 : ℝ) 1 := fun _ ht => ht.1
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    apply Metric.isOpen_iff.mpr
    intro t htA
    by_cases htI : t ∈ Icc (0 : ℝ) 1
    · refine ⟨δ, hδ, ?_⟩
      intro r hr
      show r ∈ Aᶜ
      intro hrA
      obtain ⟨F⟩ := hrA.2
      have hrt : |t - r| < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using hr
      have G : T.SmoothSliceFrame t :=
        SmoothSliceFrame.transport (T := T) F
          (fun u => T.deriv_ne_zero_of_mem_Icc htI u)
          (hshort hrA.1 htI hrt)
      exact htA ⟨htI, ⟨G⟩⟩
    · obtain ⟨r, hr, hrsub⟩ :=
        Metric.isOpen_iff.mp isClosed_Icc.isOpen_compl t htI
      exact ⟨r, hr, fun x hx => by
        exact fun hxA => hrsub hx hxA.1⟩
  have hopen : ∀ z ∈ A, ∃ r > 0,
      Icc (0 : ℝ) 1 ∩ Metric.ball z r ⊆ A := by
    intro z hz
    refine ⟨δ, hδ, ?_⟩
    rintro t ⟨htI, htz⟩
    obtain ⟨F⟩ := hz.2
    have hzt : |t - z| < δ := by
      simpa [Real.dist_eq] using htz
    exact ⟨htI, ⟨SmoothSliceFrame.transport (T := T) F
      (fun u => T.deriv_ne_zero_of_mem_Icc htI u)
      (hshort hz.1 htI hzt)⟩⟩
  have hne : A.Nonempty := by
    refine ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ?_⟩⟩
    exact ⟨SmoothSliceFrame.initial (T := T)⟩
  have hall : Icc (0 : ℝ) 1 ⊆ A :=
    subset_of_relOpen_closed_metric isPreconnected_Icc hsub hclosed hopen hne
  exact (hall hs).2


-- @@ L279-279 verbatim
namespace SmoothSliceFrame


-- @@ L281-297 verbatim
/-- The chord family based at a framed slice, using a caller-specified
radial bump. -/
def parametricChordExtensionDataWithBump {s : ℝ}
    (G : T.SmoothSliceFrame s) (hs : s ∈ Icc (0 : ℝ) 1)
    (b : ContDiffBump (0 : N[n]))
    (hb : b.rOut < (G.toFramedPeriodicCircle (T := T) hs).globalSmoothTube.radius) :
    SmoothFramedPeriodicCircle.ParametricPeriodicDisplacementExtensionData
      (G.toFramedPeriodicCircle (T := T) hs) where
  displacement := fun p => T.lift p.1 p.2 - T.lift s p.2
  displacement_smooth :=
    T.smooth_lift.sub (T.contDiff_lift_slice s |>.comp contDiff_snd)
  displacement_periodic := fun t u => by
    change T.lift t (u + 1) - T.lift s (u + 1) =
      T.lift t u - T.lift s u
    rw [T.periodic_lift t u, T.periodic_lift s u]
  radialBump := b
  radialBump_rOut_lt := hb


-- @@ L299-299 verbatim
end SmoothSliceFrame


-- @@ L301-301 verbatim
end EmbeddedCircleTrack

-- @@ L302-302 verbatim
end FourierEmbeddingTrack


-- @@ L304-304 verbatim
/-! ## Supported local moves and compact adaptive assembly -/


-- @@ L306-306 verbatim
namespace FourierRelativeTrack

-- @@ L307-307 verbatim
namespace RelativeEmbeddedCircleTrack


-- @@ L309-309 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L310-310 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}

-- @@ L311-311 verbatim
variable (R : RelativeEmbeddedCircleTrack (V := V) h2 O)


-- @@ L313-368 verbatim
/-- A framed slice has a whole neighborhood of exact chord moves supported
inside any prescribed open neighborhood of the complete track trace. -/
theorem exists_supported_local_ambientTrackStep
    {U : Set E[n]} (hUopen : IsOpen U)
    (htraceU : FourierTraceSupport.RelativeEmbeddedCircleTrack.trace
      (V := V) h2 O R ⊆ U)
    (hUdisj : Disjoint U (OrbitUnknottingSupport.obstacleSet V h2 O))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      Nonempty (FourierEmbeddingTrack.AmbientTrackStep R.track s t) := by
  obtain ⟨G⟩ := R.track.nonempty_smoothSliceFrame_of_mem_Icc hs
  let F := G.toFramedPeriodicCircle (T := R.track) hs
  have hcircle : Set.range F.circle ⊆ U := by
    rintro x ⟨a, rfl⟩
    apply htraceU
    exact ⟨(⟨s, hs⟩, a), rfl⟩
  obtain ⟨b, hb, hbU⟩ :=
    F.exists_radialBump_supportCore_subset hUopen hcircle
  let P := G.parametricChordExtensionDataWithBump
    (T := R.track) hs b hb
  have hsupport : P.supportCore ⊆ U := by
    change F.tube '' ((Set.univ : Set C) ×ˢ
      Metric.closedBall (0 : N[n]) b.rOut) ⊆ U
    exact hbU
  have hzero : ∀ u : ℝ, P.displacement (s, u) = 0 := by
    intro u
    simp [P,
      FourierEmbeddingTrack.EmbeddedCircleTrack.SmoothSliceFrame.parametricChordExtensionDataWithBump]
  obtain ⟨δ, hδ, hLip⟩ :=
    P.exists_uniform_lipschitzWith_of_base_zero hzero
      FourierEmbeddingTrack.localChordLipschitzBound
      FourierEmbeddingTrack.localChordLipschitzBound_pos
  refine ⟨δ, hδ, ?_⟩
  intro t hst
  let D := P.slice t
  have hLipD : LipschitzWith
      FourierEmbeddingTrack.localChordLipschitzBound D.ambientField :=
    hLip t hst
  refine ⟨R.track.ambientTrackStepOfExplicitScaledExtension
    F D 1 FourierEmbeddingTrack.localChordLipschitzBound hLipD
    (by simpa using FourierEmbeddingTrack.localChordLipschitzBound_lt_one)
    ?_⟩
  refine {
    source_lift := fun u => rfl
    target_lift := ?_
    field_zero_on_obstacle := ?_
  }
  · intro u
    change R.track.lift t u = R.track.lift s u +
      1 • (R.track.lift t u - R.track.lift s u)
    simp
  · intro x hx
    apply D.ambientField_eq_zero_of_not_mem_supportCore
    intro hxcore
    have hxP : x ∈ P.supportCore := by simpa [D] using hxcore
    exact Set.disjoint_left.mp hUdisj (hsupport hxP) hx


-- @@ L370-424 verbatim
/-- The full relative track admits a finite ambient chain from time zero to
time one.  The partition is adaptive: every interval is contained in one
locally supported chord neighborhood. -/
theorem nonempty_adaptive_supported_ambientTrackChain :
    Nonempty (FourierEmbeddingTrack.AmbientTrackChain R.track 0 1) := by
  obtain ⟨ρ, hρ, htrace, hUopen, hclosureDisj⟩ :=
    FourierTraceSupport.RelativeEmbeddedCircleTrack.exists_trace_thickening
      (V := V) (h2 := h2) (O := O) R
  let U : Set E[n] := Metric.thickening ρ
    (FourierTraceSupport.RelativeEmbeddedCircleTrack.trace
      (V := V) h2 O R)
  have hUdisj : Disjoint U
      (OrbitUnknottingSupport.obstacleSet V h2 O) :=
    hclosureDisj.mono subset_closure Subset.rfl
  have hlocal : ∀ c : Set.Icc (0 : ℝ) 1,
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - (c : ℝ)| < δ →
        Nonempty (FourierEmbeddingTrack.AmbientTrackStep
          R.track (c : ℝ) t) := by
    intro c
    exact R.exists_supported_local_ambientTrackStep hUopen htrace hUdisj c.property
  choose! rad hrad hstep using hlocal
  let cover : Set.Icc (0 : ℝ) 1 → Set (Set.Icc (0 : ℝ) 1) :=
    fun c => {x | |(x : ℝ) - (c : ℝ)| < rad c}
  have hopen : ∀ c, IsOpen (cover c) := by
    intro c
    exact isOpen_lt
      ((continuous_subtype_val.sub continuous_const).abs)
      continuous_const
  have hcover : (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ⊆
      ⋃ c, cover c := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_⟩
    change |(x : ℝ) - (x : ℝ)| < rad x
    simpa using hrad x
  obtain ⟨q, hq₀, hmono, ⟨m, hm⟩, hinter⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc
      (a := (0 : ℝ)) (b := 1) zero_le_one hopen hcover
  have hqm : (q m : ℝ) = 1 := hm m le_rfl
  have hsteps : ∀ k : ℕ,
      Nonempty (FourierEmbeddingTrack.AmbientTrackStep R.track
        (q k : ℝ) (q (k + 1) : ℝ)) := by
    intro k
    obtain ⟨c, hc⟩ := hinter k
    have hk : q k ≤ q (k + 1) := hmono (Nat.le_succ k)
    have hleft : q k ∈ cover c := hc ⟨le_rfl, hk⟩
    have hright : q (k + 1) ∈ cover c := hc ⟨hk, le_rfl⟩
    obtain ⟨Mleft⟩ := hstep c (q k : ℝ) hleft
    obtain ⟨Mright⟩ := hstep c (q (k + 1) : ℝ) hright
    exact ⟨Mleft.symm.trans Mright⟩
  let chain := FourierEmbeddingTrack.AmbientTrackChain.sequencePrefix
    (T := R.track) (fun k => (q k : ℝ))
      (fun k => Classical.choice (hsteps k)) m
  refine ⟨?_⟩
  simpa [hq₀, hqm] using chain


-- @@ L426-433 verbatim
/-- Unconditional relative canonical orbit move supplied by the relative
embedded-circle track itself. -/
theorem nonempty_relativeCanonicalOrbitMove_of_relativeTrack
    (R : RelativeEmbeddedCircleTrack (V := V) h2 O) :
    Nonempty (RelativeCanonicalOrbitMove V h2 O) := by
  obtain ⟨chain⟩ :=
    nonempty_adaptive_supported_ambientTrackChain (R := R)
  exact ⟨R.relativeCanonicalOrbitMoveOfChain chain⟩


-- @@ L435-435 verbatim
end RelativeEmbeddedCircleTrack

-- @@ L436-436 verbatim
end FourierRelativeTrack


-- @@ L438-438 verbatim
end TamedField

-- @@ L439-439 verbatim
end Submission
