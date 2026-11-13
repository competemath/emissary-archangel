import Mathlib
import Submission.OrbitUnknottingLocalTrackStepBridge


-- @@ L4-16 verbatim
/-!
# Equisubdivision assembly for ambient track moves

The local tube-extension argument naturally produces one ambient move on
each interval of a sufficiently fine uniform mesh.  This file performs the
dependent finite induction which assembles those moves into a chain whose
endpoints are literally `0` and `1`.

Both explicit and `Nonempty` interfaces are provided.  The latter is useful
when every local analytic construction is existential.  A final wrapper
turns the assembled chain directly into the relative canonical orbit move
consumed by the global orbit assembly.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped Topology ContDiff RealInnerProductSpace NNReal


-- @@ L25-25 verbatim
namespace Submission

-- @@ L26-26 verbatim
namespace TamedField

-- @@ L27-27 verbatim
namespace FourierEmbeddingTrack


-- @@ L29-29 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L30-30 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}

-- @@ L31-31 verbatim
variable {T : EmbeddedCircleTrack (V := V) h2 O}


-- @@ L33-33 verbatim
namespace AmbientTrackChain


-- @@ L35-37 verbatim
/-- The `k`-th point of the uniform mesh with denominator `m`. -/
def equisubdivisionPoint (m k : ℕ) : ℝ :=
  (k : ℝ) / (m : ℝ)


-- @@ L39-45 verbatim
/-- Concatenate two type-indexed ambient track chains. -/
def append {s t r : ℝ}
    (C₁ : AmbientTrackChain T s t) (C₂ : AmbientTrackChain T t r) :
    AmbientTrackChain T s r := by
  induction C₁ with
  | refl _ => exact C₂
  | cons head tail ih => exact .cons head (ih C₂)


-- @@ L47-50 verbatim
@[simp] theorem append_refl_left {s t : ℝ}
    (C : AmbientTrackChain T s t) :
    append (.refl s) C = C :=
  rfl


-- @@ L52-57 verbatim
@[simp] theorem append_cons {s t r q : ℝ}
    (head : AmbientTrackStep T s t)
    (tail : AmbientTrackChain T t r)
    (C : AmbientTrackChain T r q) :
    append (.cons head tail) C = .cons head (append tail C) :=
  rfl


-- @@ L59-74 verbatim
/-- Assemble the first `k` intervals of an equisubdivision.  Keeping the
literal mesh endpoints in this auxiliary definition makes every recursive
composition type-correct without arithmetic transports. -/
private def equisubdivisionPrefix (m : ℕ)
    (steps : ∀ k : ℕ, k < m →
      AmbientTrackStep T (equisubdivisionPoint m k)
        (equisubdivisionPoint m (k + 1))) :
    ∀ k : ℕ, k ≤ m →
      AmbientTrackChain T (equisubdivisionPoint m 0)
        (equisubdivisionPoint m k)
  | 0, _ => .refl _
  | k + 1, hk =>
      append
        (equisubdivisionPrefix m steps k
          (Nat.le_trans (Nat.le_succ k) hk))
        (.cons (steps k (Nat.lt_of_succ_le hk)) (.refl _))


-- @@ L76-86 verbatim
/-- Explicit equisubdivision assembly.  One local ambient step for every
`k < m` produces a global chain from time zero to time one. -/
def equisubdivision (m : ℕ) (hm : 0 < m)
    (steps : ∀ k : ℕ, k < m →
      AmbientTrackStep T (equisubdivisionPoint m k)
        (equisubdivisionPoint m (k + 1))) :
    AmbientTrackChain T 0 1 := by
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  simpa [equisubdivisionPoint, hmR] using
    (equisubdivisionPrefix (T := T) m steps m (le_refl m))


-- @@ L88-96 verbatim
/-- Choice interface for existentially produced local steps. -/
def equisubdivisionOfNonempty (m : ℕ) (hm : 0 < m)
    (steps : ∀ k : ℕ, k < m →
      Nonempty
        (AmbientTrackStep T (equisubdivisionPoint m k)
          (equisubdivisionPoint m (k + 1)))) :
    AmbientTrackChain T 0 1 :=
  equisubdivision (T := T) m hm
    (fun k hk => Classical.choice (steps k hk))


-- @@ L98-105 verbatim
/-- Propositional form of `equisubdivisionOfNonempty`. -/
theorem nonempty_equisubdivision (m : ℕ) (hm : 0 < m)
    (steps : ∀ k : ℕ, k < m →
      Nonempty
        (AmbientTrackStep T (equisubdivisionPoint m k)
          (equisubdivisionPoint m (k + 1)))) :
    Nonempty (AmbientTrackChain T 0 1) :=
  ⟨equisubdivisionOfNonempty (T := T) m hm steps⟩


-- @@ L107-107 verbatim
end AmbientTrackChain


-- @@ L109-109 verbatim
end FourierEmbeddingTrack


-- @@ L111-111 verbatim
namespace FourierRelativeTrack

-- @@ L112-112 verbatim
namespace RelativeEmbeddedCircleTrack


-- @@ L114-114 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}

-- @@ L115-115 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}

-- @@ L116-116 verbatim
variable (R : RelativeEmbeddedCircleTrack (V := V) h2 O)


-- @@ L118-119 verbatim
local notation "mesh" =>
  FourierEmbeddingTrack.AmbientTrackChain.equisubdivisionPoint


-- @@ L121-130 verbatim
/-- Direct explicit-mesh construction of the relative canonical orbit move. -/
def relativeCanonicalOrbitMoveOfEquisubdivision
    (m : ℕ) (hm : 0 < m)
    (steps : ∀ k : ℕ, k < m →
      FourierEmbeddingTrack.AmbientTrackStep R.track
        (mesh m k) (mesh m (k + 1))) :
    RelativeCanonicalOrbitMove V h2 O :=
  R.relativeCanonicalOrbitMoveOfChain
    (FourierEmbeddingTrack.AmbientTrackChain.equisubdivision
      (T := R.track) m hm steps)


-- @@ L132-142 verbatim
/-- Choice-valued direct construction from existential local moves. -/
def relativeCanonicalOrbitMoveOfNonemptyEquisubdivision
    (m : ℕ) (hm : 0 < m)
    (steps : ∀ k : ℕ, k < m →
      Nonempty
        (FourierEmbeddingTrack.AmbientTrackStep R.track
          (mesh m k) (mesh m (k + 1)))) :
    RelativeCanonicalOrbitMove V h2 O :=
  R.relativeCanonicalOrbitMoveOfChain
    (FourierEmbeddingTrack.AmbientTrackChain.equisubdivisionOfNonempty
      (T := R.track) m hm steps)


-- @@ L144-152 verbatim
/-- Propositional direct interface used by global relative-move assembly. -/
theorem nonempty_relativeCanonicalOrbitMove_of_equisubdivision
    (m : ℕ) (hm : 0 < m)
    (steps : ∀ k : ℕ, k < m →
      Nonempty
        (FourierEmbeddingTrack.AmbientTrackStep R.track
          (mesh m k) (mesh m (k + 1)))) :
    Nonempty (RelativeCanonicalOrbitMove V h2 O) :=
  ⟨R.relativeCanonicalOrbitMoveOfNonemptyEquisubdivision m hm steps⟩


-- @@ L154-154 verbatim
end RelativeEmbeddedCircleTrack

-- @@ L155-155 verbatim
end FourierRelativeTrack


-- @@ L157-157 verbatim
end TamedField

-- @@ L158-158 verbatim
end Submission
