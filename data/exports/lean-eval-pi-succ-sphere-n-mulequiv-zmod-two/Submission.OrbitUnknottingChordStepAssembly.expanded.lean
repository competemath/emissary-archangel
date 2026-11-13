import Mathlib
import Submission.OrbitUnknottingParametricExtensionSmallness
import Submission.OrbitUnknottingEquisubdivisionChain


-- @@ L5-19 verbatim
/-!
# Assembly of local chord extensions into a relative orbit move

This file connects the parametric smallness theorem for framed-circle chord
extensions to the exact local ambient-step bridge and the finite
equisubdivision assembler.

For each framed source slice we choose a positive analytic radius on which
the literal, unscaled chord extension has Lipschitz constant `1 / 2`.  If
its fixed compact support core is disjoint from the relative obstacle, the
extension vanishes on the obstacle and therefore gives an
`AmbientTrackStep`.  A finite mesh whose adjacent times lie in these chosen
radii assembles automatically to an `AmbientTrackChain 0 1`, and for a
relative Fourier track directly to a `RelativeCanonicalOrbitMove`.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace TamedField

-- @@ L30-30 verbatim
namespace FourierEmbeddingTrack


-- @@ L32-32 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L33-33 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L35-35 verbatim
local notation "mesh" => AmbientTrackChain.equisubdivisionPoint


-- @@ L37-44 verbatim
/-- Every point of a positive equisubdivision with index at most its
denominator lies in the track interval. -/
theorem equisubdivisionPoint_mem_Icc (m : ℕ) (hm : 0 < m)
    (k : ℕ) (hk : k ≤ m) : mesh m k ∈ Icc (0 : ℝ) 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  constructor
  · exact div_nonneg (by positivity) hmR.le
  · exact (div_le_one hmR).2 (by exact_mod_cast hk)


-- @@ L46-47 verbatim
/-- A fixed quantitative bound used for every local chord move. -/
def localChordLipschitzBound : ℝ≥0 := 1 / 2


-- @@ L49-50 verbatim
theorem localChordLipschitzBound_pos : 0 < localChordLipschitzBound := by
  norm_num [localChordLipschitzBound]


-- @@ L52-53 verbatim
theorem localChordLipschitzBound_lt_one : localChordLipschitzBound < 1 := by
  norm_num [localChordLipschitzBound]


-- @@ L55-55 verbatim
namespace EmbeddedCircleTrack


-- @@ L57-57 verbatim
variable (T : EmbeddedCircleTrack (V := V) h2 O)


-- @@ L59-59 verbatim
namespace SmoothSliceFrame


-- @@ L61-67 verbatim
/-- A canonical positive time radius on which the unscaled chord extension
has global Lipschitz constant `1 / 2`. -/
def chordStepRadius {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1) : ℝ :=
  Classical.choose
    (G.exists_uniform_lipschitzWith_chordExtensionData (T := T) hs
      localChordLipschitzBound localChordLipschitzBound_pos)


-- @@ L69-74 verbatim
theorem chordStepRadius_pos {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < G.chordStepRadius (T := T) hs :=
  (Classical.choose_spec
    (G.exists_uniform_lipschitzWith_chordExtensionData (T := T) hs
      localChordLipschitzBound localChordLipschitzBound_pos)).1


-- @@ L76-84 verbatim
theorem lipschitz_chordExtensionData_of_lt_chordStepRadius
    {s t : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hst : |t - s| < G.chordStepRadius (T := T) hs) :
    LipschitzWith localChordLipschitzBound
      (G.chordExtensionData (T := T) hs t).ambientField :=
  (Classical.choose_spec
    (G.exists_uniform_lipschitzWith_chordExtensionData (T := T) hs
      localChordLipschitzBound localChordLipschitzBound_pos)).2 t hst


-- @@ L86-86 verbatim
end SmoothSliceFrame


-- @@ L88-88 verbatim
/-! ## One supported chord move -/


-- @@ L90-102 verbatim
/-- Complete data for one literal chord move.  The support condition is
geometric; the remaining fields are exactly the analytic output of
parametric extension smallness. -/
structure LocalChordMoveInput (s t : ℝ) where
  frame : T.SmoothSliceFrame s
  source_mem : s ∈ Icc (0 : ℝ) 1
  K : ℝ≥0
  K_lt_one : K < 1
  lipschitz : LipschitzWith K
    (frame.chordExtensionData (T := T) source_mem t).ambientField
  support_disjoint : Disjoint
    (frame.chordExtensionData (T := T) source_mem t).supportCore
    (OrbitUnknottingSupport.obstacleSet V h2 O)


-- @@ L104-104 verbatim
namespace LocalChordMoveInput


-- @@ L106-106 verbatim
variable {T : EmbeddedCircleTrack (V := V) h2 O}

-- @@ L107-107 verbatim
variable {s t : ℝ} (M : T.LocalChordMoveInput s t)


-- @@ L109-115 verbatim
/-- Disjointness of the compact support core gives the pointwise relative
vanishing contract required by the local-step bridge. -/
theorem ambientField_eq_zero_on_obstacle (x : EuclideanSpace ℝ (Fin (n + 1)))
    (hx : x ∈ OrbitUnknottingSupport.obstacleSet V h2 O) :
    (M.frame.chordExtensionData (T := T) M.source_mem t).ambientField x = 0 := by
  apply (M.frame.chordExtensionData (T := T) M.source_mem t).ambientField_eq_zero_of_not_mem_supportCore
  exact fun hcore => Set.disjoint_left.mp M.support_disjoint hcore hx


-- @@ L117-120 verbatim
/-- A supported analytic chord input gives one exact ambient track step. -/
def toAmbientTrackStep : AmbientTrackStep T s t :=
  T.ambientTrackStep_chord M.frame M.source_mem M.K M.lipschitz
    M.K_lt_one M.ambientField_eq_zero_on_obstacle


-- @@ L122-122 verbatim
end LocalChordMoveInput


-- @@ L124-147 verbatim
/-- Construct a complete local chord-move input from the canonical analytic
radius and disjointness of the parameter-independent support core. -/
def localChordMoveInputOfClose
    {s t : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hst : |t - s| < G.chordStepRadius (T := T) hs)
    (hdisj : Disjoint
      (G.parametricChordExtensionData (T := T) hs).supportCore
      (OrbitUnknottingSupport.obstacleSet V h2 O)) :
    T.LocalChordMoveInput s t where
  frame := G
  source_mem := hs
  K := localChordLipschitzBound
  K_lt_one := localChordLipschitzBound_lt_one
  lipschitz :=
    G.lipschitz_chordExtensionData_of_lt_chordStepRadius (T := T) hs hst
  support_disjoint := by
    have hsupport :
        (G.chordExtensionData (T := T) hs t).supportCore =
          (G.parametricChordExtensionData (T := T) hs).supportCore := by
      rw [← G.parametricChordExtensionData_slice (T := T) hs t]
      exact (G.parametricChordExtensionData (T := T) hs).slice_supportCore t
    rw [hsupport]
    exact hdisj


-- @@ L149-161 verbatim
/-- Local existence form: support disjointness alone gives a positive time
radius on which every target slice admits an exact ambient step. -/
theorem exists_localChordMoveInput_of_supportCore_disjoint
    {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hdisj : Disjoint
      (G.parametricChordExtensionData (T := T) hs).supportCore
      (OrbitUnknottingSupport.obstacleSet V h2 O)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      Nonempty (T.LocalChordMoveInput s t) := by
  refine ⟨G.chordStepRadius (T := T) hs, G.chordStepRadius_pos (T := T) hs, ?_⟩
  intro t hst
  exact ⟨T.localChordMoveInputOfClose G hs hst hdisj⟩


-- @@ L163-177 verbatim
/-- The same local existence statement directly at the ambient-step layer. -/
theorem exists_ambientTrackStep_of_supportCore_disjoint
    {s : ℝ} (G : T.SmoothSliceFrame s)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hdisj : Disjoint
      (G.parametricChordExtensionData (T := T) hs).supportCore
      (OrbitUnknottingSupport.obstacleSet V h2 O)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - s| < δ →
      Nonempty (AmbientTrackStep T s t) := by
  obtain ⟨δ, hδ, hinput⟩ :=
    T.exists_localChordMoveInput_of_supportCore_disjoint G hs hdisj
  refine ⟨δ, hδ, ?_⟩
  intro t hst
  obtain ⟨M⟩ := hinput t hst
  exact ⟨M.toAmbientTrackStep⟩


-- @@ L179-179 verbatim
/-! ## A certified sufficiently fine equal subdivision -/


-- @@ L181-193 verbatim
/-- The exact finite certificate that an equisubdivision is fine enough for
the analytic chord extensions and has relatively supported source tubes. -/
structure FineChordEquisubdivisionData (m : ℕ) where
  positive : 0 < m
  frame : ∀ k : ℕ, k < m → T.SmoothSliceFrame (mesh m k)
  support_disjoint : ∀ (k : ℕ) (hk : k < m), Disjoint
    ((frame k hk).parametricChordExtensionData (T := T)
      (equisubdivisionPoint_mem_Icc m positive k (Nat.le_of_lt hk))).supportCore
    (OrbitUnknottingSupport.obstacleSet V h2 O)
  fine : ∀ (k : ℕ) (hk : k < m),
    |mesh m (k + 1) - mesh m k| <
      (frame k hk).chordStepRadius (T := T)
        (equisubdivisionPoint_mem_Icc m positive k (Nat.le_of_lt hk))


-- @@ L195-195 verbatim
namespace FineChordEquisubdivisionData


-- @@ L197-197 verbatim
variable {T : EmbeddedCircleTrack (V := V) h2 O}

-- @@ L198-198 verbatim
variable {m : ℕ} (D : T.FineChordEquisubdivisionData m)


-- @@ L200-205 verbatim
/-- The certified local input on one grid interval. -/
def localChordMoveInput (k : ℕ) (hk : k < m) :
    T.LocalChordMoveInput (mesh m k) (mesh m (k + 1)) :=
  T.localChordMoveInputOfClose (D.frame k hk)
    (equisubdivisionPoint_mem_Icc m D.positive k (Nat.le_of_lt hk))
    (D.fine k hk) (D.support_disjoint k hk)


-- @@ L207-210 verbatim
/-- The exact ambient step on one grid interval. -/
def ambientTrackStep (k : ℕ) (hk : k < m) :
    AmbientTrackStep T (mesh m k) (mesh m (k + 1)) :=
  (D.localChordMoveInput k hk).toAmbientTrackStep


-- @@ L212-214 verbatim
/-- All certified chord steps assembled into one ambient chain `0 → 1`. -/
def ambientTrackChain : AmbientTrackChain T 0 1 :=
  AmbientTrackChain.equisubdivision m D.positive D.ambientTrackStep


-- @@ L216-216 verbatim
end FineChordEquisubdivisionData


-- @@ L218-218 verbatim
end EmbeddedCircleTrack

-- @@ L219-219 verbatim
end FourierEmbeddingTrack


-- @@ L221-221 verbatim
/-! ## Direct relative-track output -/


-- @@ L223-223 verbatim
namespace FourierRelativeTrack

-- @@ L224-224 verbatim
namespace RelativeEmbeddedCircleTrack


-- @@ L226-226 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L227-227 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}

-- @@ L228-228 verbatim
variable (R : RelativeEmbeddedCircleTrack (V := V) h2 O)


-- @@ L230-237 verbatim
/-- A sufficiently fine, relatively supported chord subdivision closes the
one-orbit normalization contract outright. -/
def relativeCanonicalOrbitMoveOfFineChordEquisubdivision
    {m : ℕ}
    (D : FourierEmbeddingTrack.EmbeddedCircleTrack.FineChordEquisubdivisionData
      R.track m) :
    RelativeCanonicalOrbitMove V h2 O :=
  R.relativeCanonicalOrbitMoveOfChain D.ambientTrackChain


-- @@ L239-246 verbatim
theorem nonempty_relativeCanonicalOrbitMove_of_fineChordEquisubdivision
    {m : ℕ}
    (hD : Nonempty
      (FourierEmbeddingTrack.EmbeddedCircleTrack.FineChordEquisubdivisionData
        R.track m)) :
    Nonempty (RelativeCanonicalOrbitMove V h2 O) := by
  obtain ⟨D⟩ := hD
  exact ⟨R.relativeCanonicalOrbitMoveOfFineChordEquisubdivision D⟩


-- @@ L248-248 verbatim
end RelativeEmbeddedCircleTrack

-- @@ L249-249 verbatim
end FourierRelativeTrack


-- @@ L251-251 verbatim
end TamedField

-- @@ L252-252 verbatim
end Submission
