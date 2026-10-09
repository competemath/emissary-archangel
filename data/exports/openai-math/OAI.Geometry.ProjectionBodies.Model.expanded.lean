import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set MeasureTheory

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace


-- @@ L9-9 verbatim
namespace PettyProjection


-- @@ L11-11 verbatim
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)


-- @@ L13-14 verbatim
def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty


-- @@ L16-16 verbatim
def unitBall (n : ℕ) : Set (Space n) := Metric.closedBall 0 1


-- @@ L18-18 verbatim
def kappa (n : ℕ) : ℝ := volume.real (unitBall n)


-- @@ L20-21 verbatim
def perpendicular {n : ℕ} (u : Space n) : Submodule ℝ (Space n) :=
  (Submodule.span ℝ {u})ᗮ


-- @@ L23-26 verbatim
/-- Volume in the induced Euclidean structure on the orthogonal hyperplane. -/
def shadowVolume {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  (volume : Measure (perpendicular u)).real
    ((perpendicular u).orthogonalProjectionOnto '' K)


-- @@ L28-31 verbatim
/-- The body with support function equal to the volumes of orthogonal shadows,
expressed as its defining intersection of supporting half-spaces. -/
def projectionBody {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  {x | ∀ u : Space n, ‖u‖ = 1 → ⟪u, x⟫ ≤ shadowVolume K u}


-- @@ L33-34 verbatim
def projectionRatio {n : ℕ} (K : Set (Space n)) : ℝ :=
  volume.real (projectionBody K) / volume.real K ^ (n - 1)


-- @@ L36-37 verbatim
def pettyConstant (n : ℕ) : ℝ :=
  kappa (n - 1) ^ n * kappa n ^ (2 - (n : ℤ))


-- @@ L39-41 verbatim
def IsEllipsoid {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ (a : Space n) (T : Space n ≃ₗ[ℝ] Space n),
    K = (fun x => a + T x) '' unitBall n


-- @@ L43-46 verbatim
def MainClaim : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (K : Set (Space n)), IsConvexBody K →
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K)


-- @@ L48-48 verbatim
end PettyProjection

-- @@ L49-49 verbatim
end


-- @@ L51-51 verbatim
end OAI
