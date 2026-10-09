import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-9 verbatim
/-!
The explicit twelve-point witness and the ordinary Euclidean Ramsey property.
These definitions contain no proof-specific field derivation or affine-placement assumption.
-/

-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
namespace GrahamSpherical


-- @@ L14-14 verbatim
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- @@ L15-15 verbatim
abbrev Label := Fin 3 × Fin 4


-- @@ L17-18 verbatim
/-- The factorial series starts at `1!`. -/
def parameter : ℝ := ∑' m : ℕ, 1 / (10 : ℝ) ^ ((m + 1).factorial)


-- @@ L20-20 verbatim
def u : ℝ := (1 - parameter ^ 2) / (1 + parameter ^ 2)

-- @@ L21-21 verbatim
def v : ℝ := (2 * parameter) / (1 + parameter ^ 2)


-- @@ L23-26 verbatim
def squareCoordinate (q : Fin 4) : Fin 2 → ℝ :=
  if q = 0 then ![1, 0] else
  if q = 1 then ![-1, 0] else
  if q = 2 then ![0, 1] else ![0, -1]


-- @@ L28-33 verbatim
/-- First the positively rotated square, then the negatively rotated square,
and finally the original coordinate square. -/
def coordinates (i : Label) : Fin 2 → ℝ :=
  let q := squareCoordinate i.2
  if i.1 = 0 then ![u * q 0 - v * q 1, v * q 0 + u * q 1] else
  if i.1 = 1 then ![u * q 0 + v * q 1, -v * q 0 + u * q 1] else q


-- @@ L35-35 verbatim
def vertex (i : Label) : Point 2 := WithLp.toLp 2 (coordinates i)


-- @@ L37-37 verbatim
def witness : Set (Point 2) := Set.range vertex


-- @@ L39-39 verbatim
def weight (i : Label) : ℤ := if i.1 = 2 then -2 else 1


-- @@ L41-44 verbatim
/-- Arbitrary colorings and exact distance-preserving copies; no measurability,
computability, continuity of the coloring, or extension of the copy is assumed. -/
def AvoidsCopy {d n r : ℕ} (X : Set (Point d)) (color : Point n → Fin r) : Prop :=
  ¬ ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c


-- @@ L46-49 verbatim
def EuclideanRamsey {d : ℕ} (X : Set (Point d)) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ n : ℕ, 0 < n ∧
    ∀ color : Point n → Fin r,
      ∃ f : X → Point n, Isometry f ∧ ∃ c : Fin r, ∀ x, color (f x) = c


-- @@ L51-51 verbatim
end GrahamSpherical


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
/-! Independent statement of the full authored result. -/

-- @@ L56-56 verbatim
namespace GrahamSpherical.Specification


-- @@ L58-62 verbatim
def FullAuthoredResult : Prop :=
  witness.ncard = 12 ∧
  witness ⊆ Metric.sphere (0 : Point 2) 1 ∧
  (∀ n : ℕ, 0 < n → ∃ color : Point n → Fin 50, AvoidsCopy witness color) ∧
  ¬ EuclideanRamsey witness


-- @@ L64-64 verbatim
end GrahamSpherical.Specification


-- @@ L66-66 verbatim
end OAI
