import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory Filter Set

-- @@ L7-7 verbatim
open scoped ENNReal NNReal Topology


-- @@ L9-9 verbatim
universe uX u_1


-- @@ L11-11 verbatim
namespace ExactModuli


-- @@ L13-13 verbatim
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- @@ L15-17 verbatim
/-- Closed linear subspaces of finite codimension. -/
def Cofinite (F : Submodule ℝ X) : Prop :=
  IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)


-- @@ L19-21 verbatim
/-- Averaged increment for directions of norm at least one. -/
def averagedIncrement (N : Seminorm ℝ X) (x : X) (t : ℝ) (y : X) : ℝ :=
  (N (x + t • y) + N (x - t • y)) / 2 - 1


-- @@ L23-25 verbatim
def H (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, 1 ≤ N y ∧ a = averagedIncrement N x t y}}


-- @@ L27-29 verbatim
def D (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, N y = 1 ∧ a = N (x + t • y) - 1}}


-- @@ L31-32 verbatim
def averagedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = H N x t}


-- @@ L34-35 verbatim
def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = D N x t}


-- @@ L37-39 verbatim
/-- Two-sided comparison makes this seminorm a genuine norm equivalent to the original. -/
def EquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖


-- @@ L41-42 verbatim
def AUC (N : Seminorm ℝ X) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < oneSidedModulus N t


-- @@ L44-47 verbatim
/-- Every rank-one operator has the form `ell.smulRight v`. -/
def Daugavet (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (ell : X →L[ℝ] ℝ) (v : X),
    ‖ContinuousLinearMap.id ℝ X + ell.smulRight v‖ = 1 + ‖ell.smulRight v‖


-- @@ L49-49 verbatim
variable {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)


-- @@ L51-53 verbatim
/-- Convergence-in-measure distance on L1 equivalence classes. -/
def measureDistance (f g : Lp ℝ 1 μ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ μ.real {ω | a < |f ω - g ω|} < a}


-- @@ L55-58 verbatim
/-- Finite covers of the entire unit ball in convergence-in-measure distance. -/
def MeasurePrecompactBall (E : Submodule ℝ (Lp ℝ 1 μ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset (Lp ℝ 1 μ),
    ∀ y : E, ‖y‖ ≤ 1 → ∃ b ∈ s, measureDistance μ (y : Lp ℝ 1 μ) b < ε


-- @@ L60-64 verbatim
/-- Every nonempty unit-ball slice contains an almost antipodal unit vector. -/
def UnitSliceProperty (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (w : X), ‖w‖ = 1 → ∀ (ell : X →L[ℝ] ℝ) (α : ℝ),
    (∃ u : X, ‖u‖ ≤ 1 ∧ α < ell u) →
    ∀ ρ : ℝ, 0 < ρ → ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖


-- @@ L66-67 verbatim
/-- The countable product of unit intervals. -/
abbrev KWOmega := ℕ → unitInterval


-- @@ L69-69 verbatim
def kwMeasure : Measure KWOmega := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))


-- @@ L71-71 verbatim
end ExactModuli


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end OAI
