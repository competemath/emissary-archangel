import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Set


-- @@ L9-9 verbatim
namespace ProjectionCounterexample


-- @@ L11-11 verbatim
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)


-- @@ L13-15 verbatim
/-- The convex hull of the origin and the `d` standard unit vectors. -/
def simplex (d : ℕ) : Set (E d) :=
  convexHull ℝ (insert 0 (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)))


-- @@ L17-19 verbatim
/-- The first ten coordinates in the standard orthogonal decomposition of R²⁰. -/
def firstBlock (x : E 20) : E 10 :=
  WithLp.toLp 2 fun i : Fin 10 => x (Fin.castAdd 10 i)


-- @@ L21-23 verbatim
/-- The last ten coordinates in the standard orthogonal decomposition of R²⁰. -/
def secondBlock (x : E 20) : E 10 :=
  WithLp.toLp 2 fun i : Fin 10 => x (Fin.natAdd 10 i)


-- @@ L25-27 verbatim
/-- The genuine Cartesian product T₁₀ × T₁₀ in Euclidean R²⁰. -/
def productBody : Set (E 20) :=
  {x | firstBlock x ∈ simplex 10 ∧ secondBlock x ∈ simplex 10}


-- @@ L29-31 verbatim
/-- Compact, convex, and full-dimensional in its specified Euclidean space. -/
def IsConvexBody {d : ℕ} (P : Set (E d)) : Prop :=
  IsCompact P ∧ Convex ℝ P ∧ (interior P).Nonempty


-- @@ L33-33 verbatim
end ProjectionCounterexample


-- @@ L35-35 verbatim
end


-- @@ L37-37 verbatim
end OAI
