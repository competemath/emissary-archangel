import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L6-6 verbatim
open scoped ENNReal NNReal Topology


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
universe uX


-- @@ L12-12 verbatim
namespace IndependentProducts


-- @@ L14-15 verbatim
/-- The tree of finite sequences of positive integers. -/
abbrev Vertex := List ℕ+

-- @@ L16-17 verbatim
/-- Coordinates are attached only to nonroot vertices. -/
abbrev Edge := {v : Vertex // v ≠ []}

-- @@ L18-18 verbatim
abbrev Sample := Edge → ℝ


-- @@ L20-22 verbatim
/-- The product law of independent copies of the multiplier. -/
def productMeasure (μ : Measure ℝ) : Measure Sample :=
  Measure.infinitePi (fun _ : Edge => μ)


-- @@ L24-31 verbatim
/-- The nonroot prefix ending at position `j`. -/
def pathPrefix (v : Vertex) (j : Fin v.length) : Edge :=
  ⟨v.take (j.val + 1), by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_take, List.length_nil] at hl
    have := j.isLt
    omega⟩


-- @@ L33-35 verbatim
/-- Root product is the empty product 1; every other product uses the path prefixes. -/
def pathProduct (v : Vertex) (ω : Sample) : ℝ :=
  ∏ j : Fin v.length, ω (pathPrefix v j)


-- @@ L37-40 verbatim
/-- The closed real L1 span of the path products. -/
def productSpan (μ : Measure ℝ) : Submodule ℝ (Lp ℝ 1 (productMeasure μ)) :=
  (Submodule.span ℝ {f : Lp ℝ 1 (productMeasure μ) | ∃ v : Vertex,
    (f : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v}).topologicalClosure


-- @@ L42-48 verbatim
/-- Positivity, nonconstancy, mean one, and finite second moment of the multiplier law. -/
structure MultiplierHypotheses (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  positive : ∀ᵐ w ∂μ, 0 < w
  nonconstant : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)
  mean_one : ∫ w, w ∂μ = 1
  second_moment : MemLp (fun w : ℝ => w) 2 μ


-- @@ L50-50 verbatim
section Moduli


-- @@ L52-52 verbatim
variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]


-- @@ L54-56 verbatim
/-- Closed subspaces of finite codimension, with respect to the inherited topology. -/
def CofiniteSubspaces : Set (Submodule ℝ X) :=
  {F | IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)}


-- @@ L58-63 verbatim
/-- The averaged asymptotic midpoint modulus, with directions of norm at least 1. -/
def averagedMidpointModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ 1 ≤ N y ∧
        b = (N (x + t • y) + N (x - t • y)) / 2 - 1}}}


-- @@ L65-69 verbatim
/-- The usual one-sided modulus, whose directions have norm exactly 1. -/
def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}}}


-- @@ L71-73 verbatim
/-- A seminorm with these bounds is a genuine norm equivalent to the original norm. -/
def IsEquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖


-- @@ L75-75 verbatim
def IsAUC (N : Seminorm ℝ X) : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulus X N t


-- @@ L77-77 verbatim
end Moduli


-- @@ L79-81 verbatim
/-- Gaussian-tail probability, in real rather than extended-nonnegative-real notation. -/
def gaussianTail (r : ℝ) : ℝ :=
  (gaussianReal 0 1 {x : ℝ | r ≤ |x|}).toReal


-- @@ L83-85 verbatim
/-- The Gaussian excess constant at threshold twice the parameter. -/
def excessConstant (K : ℝ) : ℝ :=
  (1 / 16 : ℝ) * ∫ x : ℝ, max (|x| - 2 * K) 0 ∂gaussianReal 0 1


-- @@ L87-88 verbatim
/-- The density exp(-w) on the positive half-line. -/
def exponentialLaw : Measure ℝ := expMeasure 1


-- @@ L90-91 verbatim
/-- The law of the square of a standard real Gaussian. -/
def gaussianSquareLaw : Measure ℝ := (gaussianReal 0 1).map (fun x : ℝ => x ^ 2)


-- @@ L93-93 verbatim
end IndependentProducts


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end OAI
