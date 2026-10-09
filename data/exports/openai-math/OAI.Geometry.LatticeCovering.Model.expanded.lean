import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Convex bodies and exact coverings by a single lattice in real coordinate space. -/


-- @@ L7-7 verbatim
namespace SingleLatticeCovering


-- @@ L9-9 verbatim
open MeasureTheory

-- @@ L10-10 verbatim
open scoped Pointwise


-- @@ L12-12 verbatim
abbrev Space (n : ℕ) := Fin n → ℝ


-- @@ L14-15 verbatim
def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty


-- @@ L17-18 verbatim
def LatticeCovers {n : ℕ} (K : Set (Space n)) (L : Submodule ℤ (Space n)) : Prop :=
  K + (L : Set (Space n)) = Set.univ


-- @@ L20-20 verbatim
end SingleLatticeCovering


-- @@ L22-22 verbatim
end OAI
