import Mathlib
import Submission.OrbitUnknottingFramedCircleTube
import Submission.OrbitUnknottingTrackFrameTransport
import Submission.OrbitUnknottingFiniteTrackAssembly


-- @@ L6-29 verbatim
/-!
# From a framed track slice to one exact ambient track step

The generic framed-circle tube construction extends a smooth periodic
displacement to a compactly supported ambient field.  This file supplies the
small but important interface between that construction and
`FourierEmbeddingTrack.AmbientTrackStep`.

There are two layers.

* An explicit scalar multiple of a periodic extension is packaged as a
  `SmallAmbientDisplacement` whenever its Lipschitz constant is below one.
  Unlike an existential scaling lemma, this lets a finite-subdivision
  argument prescribe the actual track increment.
* A smooth frame on one Fourier-track slice is converted to an arbitrary
  `SmoothFramedPeriodicCircle`.  The chord displacement to a second slice is
  then smooth and periodic.  Under the literal affine-chord identity, the
  explicit scalar move has endpoint
  `s + r * (t - s)` exactly.

The relative geometric input is deliberately minimal: the extended ambient
field must vanish on the obstacle set.  A disjoint-support variant turns the
usual geometric separation statement into that pointwise condition.
-/


-- @@ L31-31 verbatim
set_option autoImplicit false


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Function Module InnerProductSpace

-- @@ L36-36 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L38-38 verbatim
namespace Submission


-- @@ L40-40 verbatim
local notation "E[" n "]" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L42-42 verbatim
namespace SmoothFramedPeriodicCircle

-- @@ L43-43 verbatim
namespace PeriodicDisplacementExtensionData


-- @@ L45-45 verbatim
variable {n : ℕ} {F : SmoothFramedPeriodicCircle n}

-- @@ L46-46 verbatim
variable (D : F.PeriodicDisplacementExtensionData)


-- @@ L48-61 verbatim
/-- The generic framed-tube extension with a caller-specified scalar.  This
is the form needed by a finite mesh, where the mesh increment itself is the
scalar multiplying the chord displacement. -/
def toExplicitScaledSmallAmbientDisplacement
    (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) : SmallAmbientDisplacement n where
  field := fun x => r • D.ambientField x
  smooth := D.contDiff_ambientField.const_smul r
  K := ‖r‖₊ * K
  K_lt_one := hsmall
  lipschitz := by
    simpa [Function.comp_def] using
      (lipschitzWith_smul r).comp hLip


-- @@ L63-75 verbatim
/-- The explicit scaled extension has the prescribed action on the framed
circle, with no reparametrization of its phase. -/
theorem toExplicitScaledSmallAmbientDisplacement_forward_lift
    (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) (u : ℝ) :
    (SmallAmbientDisplacement.toSmoothAmbientIsotopy
        (D.toExplicitScaledSmallAmbientDisplacement r K hLip hsmall)).forward
      1 (F.lift u) =
      F.lift u + r • D.displacement u := by
  rw [SmallAmbientDisplacement.toSmoothAmbientIsotopy_forward_one]
  change F.lift u + r • D.ambientField (F.lift u) = _
  rw [← F.tubeLift_zero u, D.ambientField_zeroSection]


-- @@ L77-89 verbatim
/-- Pointwise vanishing of the raw extension gives relative fixedness for
every explicit scalar multiple. -/
theorem toExplicitScaledSmallAmbientDisplacement_fixedOn
    (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) {A : Set E[n]}
    (hzero : ∀ x ∈ A, D.ambientField x = 0) :
    (SmallAmbientDisplacement.toSmoothAmbientIsotopy
      (D.toExplicitScaledSmallAmbientDisplacement r K hLip hsmall)).FixedOn A := by
  apply SmallAmbientDisplacement.fixedOn_of_field_eq_zero
  intro x hx
  change r • D.ambientField x = 0
  rw [hzero x hx, smul_zero]


-- @@ L91-104 verbatim
/-- Disjointness from the closed support core is a geometric sufficient
condition for relative fixedness. -/
theorem toExplicitScaledSmallAmbientDisplacement_fixedOn_of_disjoint
    (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1) {A : Set E[n]}
    (hdisj : Disjoint D.supportCore A) :
    (SmallAmbientDisplacement.toSmoothAmbientIsotopy
      (D.toExplicitScaledSmallAmbientDisplacement r K hLip hsmall)).FixedOn A := by
  apply D.toExplicitScaledSmallAmbientDisplacement_fixedOn
    r K hLip hsmall
  intro x hx
  apply D.ambientField_eq_zero_of_not_mem_supportCore
  exact fun hsupp => Set.disjoint_left.mp hdisj hsupp hx


-- @@ L106-106 verbatim
end PeriodicDisplacementExtensionData

-- @@ L107-107 verbatim
end SmoothFramedPeriodicCircle


-- @@ L109-109 verbatim
namespace TamedField

-- @@ L110-110 verbatim
namespace FourierEmbeddingTrack

-- @@ L111-111 verbatim
namespace EmbeddedCircleTrack


-- @@ L113-113 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L114-114 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L116-116 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L118-118 verbatim
variable (T : EmbeddedCircleTrack (V := V) h2 O)


-- @@ L120-122 verbatim
/-- Every fixed-time real lift of the smooth track is smooth. -/
theorem contDiff_lift_slice (s : ℝ) : ContDiff ℝ ∞ (T.lift s) := by
  exact T.smooth_lift.comp (contDiff_const.prodMk contDiff_id)


-- @@ L124-130 verbatim
/-- The phase derivative on every fixed-time slice is smooth. -/
theorem contDiff_deriv_lift_slice (s : ℝ) :
    ContDiff ℝ ∞ (fun u => deriv (T.lift s) u) := by
  exact
    (FourierFiniteC1Subdivision.EmbeddedCircleTrack.contDiff_phaseDeriv
      (V := V) (h2 := h2) (O := O) T).comp
        (contDiff_const.prodMk contDiff_id)


-- @@ L132-134 verbatim
/-- The literal chord from time `s` to time `t`. -/
def chordDisplacement (s t u : ℝ) : E :=
  T.lift t u - T.lift s u


-- @@ L136-138 verbatim
theorem contDiff_chordDisplacement (s t : ℝ) :
    ContDiff ℝ ∞ (T.chordDisplacement s t) := by
  exact (T.contDiff_lift_slice t).sub (T.contDiff_lift_slice s)


-- @@ L140-144 verbatim
theorem periodic_chordDisplacement (s t : ℝ) :
    Function.Periodic (T.chordDisplacement s t) 1 := by
  intro u
  simp only [chordDisplacement]
  rw [T.periodic_lift t u, T.periodic_lift s u]


-- @@ L146-146 verbatim
namespace SmoothSliceFrame


-- @@ L148-172 verbatim
/-- A smooth full frame on an embedded track slice is exactly the framed
periodic-circle input expected by the generic tube engine. -/
def toFramedPeriodicCircle {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1) : SmoothFramedPeriodicCircle n where
  lift := T.lift s
  circle := T.circle s
  smooth_lift := T.contDiff_lift_slice s
  periodic_lift := T.periodic_lift s
  circle_coe := T.circle_coe s
  isEmbedding_circle := T.isEmbedding_circle s hs
  frame := G.frame
  smooth_frame := G.smooth
  periodic_frame := G.periodic
  orthonormal_frame := G.orthonormal
  speed := fun u => ‖deriv (T.lift s) u‖
  smooth_speed := ContDiff.norm ℝ (T.contDiff_deriv_lift_slice s)
    G.deriv_ne_zero
  speed_pos := fun u => norm_pos_iff.mpr (G.deriv_ne_zero u)
  hasDerivAt_lift := fun u => by
    have hderiv : HasDerivAt (T.lift s) (deriv (T.lift s) u) u :=
      ((T.contDiff_lift_slice s).differentiable (by simp) u).hasDerivAt
    convert hderiv using 1
    rw [G.tangent_first]
    simp [unitPhaseTangent, norm_ne_zero_iff.mpr (G.deriv_ne_zero u),
      smul_smul]


-- @@ L174-182 verbatim
/-- Canonical generic-tube extension data for the chord from the framed
slice at `s` to the track slice at `t`. -/
def chordExtensionData {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (G.toFramedPeriodicCircle (T := T) hs).PeriodicDisplacementExtensionData :=
  SmoothFramedPeriodicCircle.PeriodicDisplacementExtensionData.canonical
    (G.toFramedPeriodicCircle (T := T) hs) (T.chordDisplacement s t)
    (T.contDiff_chordDisplacement s t)
    (T.periodic_chordDisplacement s t)


-- @@ L184-184 verbatim
end SmoothSliceFrame


-- @@ L186-198 verbatim
/-- The exact endpoint and relative-support contract needed to turn a
scaled generic-tube extension into an `AmbientTrackStep`.  No affine-track
hypothesis is baked into this structure: non-affine applications can supply
any displacement whose scaled endpoint is literally the desired slice. -/
structure RelativeScaledTrackStepContract
    {s t : ℝ} (F : SmoothFramedPeriodicCircle n)
    (D : F.PeriodicDisplacementExtensionData) (r : ℝ) : Prop where
  source_lift : ∀ u : ℝ, F.lift u = T.lift s u
  target_lift : ∀ u : ℝ,
    T.lift t u = F.lift u + r • D.displacement u
  field_zero_on_obstacle : ∀ x ∈
    OrbitUnknottingSupport.obstacleSet V h2 O,
    D.ambientField x = 0


-- @@ L200-220 verbatim
/-- Minimal-contract bridge from one explicit scaled tube extension to one
literal ambient track step. -/
def ambientTrackStepOfExplicitScaledExtension
    {s t : ℝ} (F : SmoothFramedPeriodicCircle n)
    (D : F.PeriodicDisplacementExtensionData)
    (r : ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K D.ambientField)
    (hsmall : ‖r‖₊ * K < 1)
    (H : T.RelativeScaledTrackStepContract (s := s) (t := t) F D r) :
    AmbientTrackStep T s t where
  move :=
    SmallAmbientDisplacement.toSmoothAmbientIsotopy
      (D.toExplicitScaledSmallAmbientDisplacement r K hLip hsmall)
  endpoint_lift u := by
    rw [← H.source_lift u]
    rw [D.toExplicitScaledSmallAmbientDisplacement_forward_lift
      r K hLip hsmall u]
    exact (H.target_lift u).symm
  fixed_obstacle :=
    D.toExplicitScaledSmallAmbientDisplacement_fixedOn
      r K hLip hsmall H.field_zero_on_obstacle


-- @@ L222-248 verbatim
/-- Direct nearby-slice specialization.  Extending the literal chord and
using scalar one carries the slice at `s` to the slice at `t` exactly; thus
the only analytic estimate left to a finite `C¹` subdivision is a Lipschitz
constant strictly below one. -/
def ambientTrackStep_chord
    {s t : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (K : ℝ≥0)
    (hLip : LipschitzWith K
      (G.chordExtensionData (T := T) hs t).ambientField)
    (hsmall : K < 1)
    (hzero : ∀ x ∈ OrbitUnknottingSupport.obstacleSet V h2 O,
      (G.chordExtensionData (T := T) hs t).ambientField x = 0) :
    AmbientTrackStep T s t := by
  apply T.ambientTrackStepOfExplicitScaledExtension
    (G.toFramedPeriodicCircle (T := T) hs)
    (G.chordExtensionData (T := T) hs t)
    1 K hLip (by simpa using hsmall)
  refine {
    source_lift := fun u => rfl
    target_lift := ?_
    field_zero_on_obstacle := hzero
  }
  intro u
  change T.lift t u = T.lift s u + 1 •
    (T.lift t u - T.lift s u)
  simp


-- @@ L250-278 verbatim
/-- Exact affine-chord specialization.  If the track obeys the displayed
affine identity based at `s`, scaling the chord toward `t` by `r` produces
the literal step `s -> s + r * (t - s)`. -/
def ambientTrackStep_affineChord
    {s t r : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (haffine : ∀ (a u : ℝ),
      T.lift (s + a * (t - s)) u =
        T.lift s u + a • T.chordDisplacement s t u)
    (K : ℝ≥0)
    (hLip : LipschitzWith K
      (G.chordExtensionData (T := T) hs t).ambientField)
    (hsmall : ‖r‖₊ * K < 1)
    (hzero : ∀ x ∈ OrbitUnknottingSupport.obstacleSet V h2 O,
      (G.chordExtensionData (T := T) hs t).ambientField x = 0) :
    AmbientTrackStep T s (s + r * (t - s)) := by
  apply T.ambientTrackStepOfExplicitScaledExtension
    (G.toFramedPeriodicCircle (T := T) hs)
    (G.chordExtensionData (T := T) hs t)
    r K hLip hsmall
  refine {
    source_lift := fun u => rfl
    target_lift := ?_
    field_zero_on_obstacle := hzero
  }
  intro u
  change T.lift (s + r * (t - s)) u =
    T.lift s u + r • T.chordDisplacement s t u
  exact haffine r u


-- @@ L280-320 verbatim
/-- Existential positive affine step, useful before a numerical Lipschitz
constant has been chosen.  The returned time increment is exactly the same
positive scalar used by the ambient displacement. -/
theorem exists_positive_ambientTrackStep_affineChord
    {s t : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (haffine : ∀ (a u : ℝ),
      T.lift (s + a * (t - s)) u =
        T.lift s u + a • T.chordDisplacement s t u)
    (hzero : ∀ x ∈ OrbitUnknottingSupport.obstacleSet V h2 O,
      (G.chordExtensionData (T := T) hs t).ambientField x = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      Nonempty (AmbientTrackStep T s (s + ε * (t - s))) := by
  let F := G.toFramedPeriodicCircle (T := T) hs
  let D := G.chordExtensionData (T := T) hs t
  obtain ⟨ε, hε, S, hfield, hforward⟩ :=
    D.exists_scaledSmallAmbientDisplacement
  refine ⟨ε, hε, ⟨{
    move := S.toSmoothAmbientIsotopy
    endpoint_lift := ?_
    fixed_obstacle := ?_
  }⟩⟩
  · intro u
    calc
      S.toSmoothAmbientIsotopy.forward 1 (T.lift s u) =
          F.lift u + ε • D.displacement u := by
        change S.toSmoothAmbientIsotopy.forward 1
            ((G.toFramedPeriodicCircle (T := T) hs).lift u) =
          (G.toFramedPeriodicCircle (T := T) hs).lift u +
            ε • T.chordDisplacement s t u
        exact hforward u
      _ = T.lift (s + ε * (t - s)) u := by
        change T.lift s u + ε • T.chordDisplacement s t u =
          T.lift (s + ε * (t - s)) u
        exact (haffine ε u).symm
  · apply SmallAmbientDisplacement.fixedOn_of_field_eq_zero
    intro x hx
    rw [hfield]
    change ε • D.ambientField x = 0
    rw [show D.ambientField x = 0 by
      simpa [D] using hzero x hx, smul_zero]


-- @@ L322-322 verbatim
end EmbeddedCircleTrack

-- @@ L323-323 verbatim
end FourierEmbeddingTrack

-- @@ L324-324 verbatim
end TamedField

-- @@ L325-325 verbatim
end Submission
