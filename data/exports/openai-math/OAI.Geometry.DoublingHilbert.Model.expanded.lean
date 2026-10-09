import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace DoublingHilbert


-- @@ L7-7 verbatim
abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2


-- @@ L9-13 verbatim
/-- Intrinsic open-ball doubling with a specified integer bound and centers in the subset. -/
def DoublingAtMost (S : Set RealL2) (bound : ℕ) : Prop :=
  ∀ x : S, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset S, centers.card ≤ bound ∧
      ∀ y : S, dist y x < r → ∃ c ∈ centers, dist y c < r / 2


-- @@ L15-20 verbatim
/-- Finite distortion includes an arbitrary positive change of scale. -/
def AdmitsBiLipschitzEmbedding (S : Set RealL2) (k : ℕ) : Prop :=
  ∃ f : S → EuclideanSpace ℝ (Fin k),
    ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
      ∀ x y : S, a * dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ D * a * dist x y


-- @@ L22-22 verbatim
end DoublingHilbert


-- @@ L24-24 verbatim
end OAI
