import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ContDiff ENNReal


-- @@ L9-9 verbatim
namespace SymmetricPolar


-- @@ L11-11 verbatim
abbrev Position (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- @@ L12-12 verbatim
abbrev Phase (n : ℕ) := Position n × Position n


-- @@ L14-16 verbatim
def IsSymmetricConvexBody {n : ℕ} (K : Set (Position n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    ∀ x, x ∈ K ↔ -x ∈ K


-- @@ L18-19 verbatim
def polar {n : ℕ} (K : Set (Position n)) : Set (Position n) :=
  {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}


-- @@ L21-22 verbatim
def polarProduct {n : ℕ} (K : Set (Position n)) : Set (Phase n) :=
  interior K ×ˢ interior (polar K)


-- @@ L24-25 verbatim
def capacityBall (n : ℕ) (c : ℝ) : Set (Phase n) :=
  {z | Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < c}


-- @@ L27-28 verbatim
noncomputable def omega0 {n : ℕ} (v w : Phase n) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2 - inner (𝕜 := ℝ) w.1 v.2


-- @@ L30-36 verbatim
def HasSymplecticEmbedding {n : ℕ} (U V : Set (Phase n)) : Prop :=
  ∃ e : Phase n → Phase n,
    ContDiffOn ℝ ∞ e U ∧
    Topology.IsEmbedding (fun z : U => e z) ∧
    MapsTo e U V ∧
    ∀ z ∈ U, ∀ v w : Phase n,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w


-- @@ L38-39 verbatim
noncomputable def gromovWidth {n : ℕ} (U : Set (Phase n)) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {c : ℝ | 0 < c ∧ HasSymplecticEmbedding (capacityBall n c) U})


-- @@ L41-41 verbatim
end SymmetricPolar

-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end OAI
