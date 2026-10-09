import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v

-- @@ L6-6 verbatim
namespace CompactBanach


-- @@ L8-11 verbatim
def DoublingAtMost {B : Type*} [MetricSpace B] (K : Set B) (bound : ℕ) : Prop :=
  ∀ x : K, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset K, centers.card ≤ bound ∧
      ∀ y : K, dist y x < r → ∃ c ∈ centers, dist y c < r / ((2 : ℕ) : ℝ)


-- @@ L13-17 verbatim
def AdmitsBiLipschitzEmbedding {B : Type*} [MetricSpace B] (K : Set B)
    (E : Type*) [MetricSpace E] : Prop :=
  ∃ f : K → E, ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ x y : K, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y


-- @@ L19-19 verbatim
end CompactBanach


-- @@ L21-21 verbatim
end OAI
