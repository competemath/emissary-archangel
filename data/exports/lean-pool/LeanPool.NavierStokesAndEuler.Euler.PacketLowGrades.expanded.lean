/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeDiagonal
public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualGrades


-- @@ L12-12 verbatim
/-! The low coefficients of the actual packet residual, before solving their equations. -/


-- @@ L14-14 verbatim
section


-- @@ L16-16 verbatim
/-! The graded expansion and tail estimate for the actual normalized momentum expression. -/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace EulerPacketPointJets


-- @@ L24-24 verbatim
open Finset EulerSmoothLimit EulerFiniteGrades EulerPacketResidual


-- @@ L26-30 verbatim
/-- Momentum grade, constructed using `coefficient`. -/
def momentumGrade (N : ℕ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain) (n : ℕ) : Space :=
  coefficient N (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z) n


-- @@ L32-44 verbatim
/-- The equality expands the actual derivatives of the finite velocity and pressure sums. -/
theorem momentum_fieldSum_eq (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z = 0) (hp0 : fastPressure m (jet (p 0) z) = 0) :
    momentumResidual κ FInv M m (fieldSum N κ u) (fieldSum N κ p) z =
      evaluate (2*N) κ (momentumGrade N FInv M m u p z) := by
  unfold momentumResidual
  rw [jet_fieldSum N κ u z hu, jet_fieldSum N κ p z hp]
  exact residual_eq_evaluate N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z) hu0 hp0


-- @@ L46-61 verbatim
/-- The source's finite packet has no residual grades through N once its coefficient equations hold.
-/
theorem momentum_fieldSum_tail (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N + 1, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N + 1, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z = 0) (hp0 : fastPressure m (jet (p 0) z) = 0)
    (hcancel : ∀ n ≤ N, momentumGrade (N + 1) FInv M m u p z n = 0) :
    momentumResidual κ FInv M m (fieldSum (N+1) κ u) (fieldSum (N+1) κ p) z =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n • momentumGrade (N+1) FInv M m u p z n := by
  unfold momentumResidual
  rw [jet_fieldSum (N+1) κ u z hu, jet_fieldSum (N+1) κ p z hp]
  exact packet_residual_eq_tail N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z)
    hu0 hp0 hcancel


-- @@ L63-77 verbatim
/-- A bound on the actual residual follows from the surviving coefficient norms. -/
theorem norm_momentum_fieldSum_le (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N + 1, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N + 1, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z = 0) (hp0 : fastPressure m (jet (p 0) z) = 0)
    (hcancel : ∀ n ≤ N, momentumGrade (N + 1) FInv M m u p z n = 0) :
    ‖momentumResidual κ FInv M m (fieldSum (N+1) κ u) (fieldSum (N+1) κ p) z‖ ≤
      ∑ n ∈ Ico (N+1) (2*N+3), |κ|^n * ‖momentumGrade (N+1) FInv M m u p z n‖ := by
  rw [momentum_fieldSum_tail N κ hκ FInv M m u p z hu hp hu0 hp0 hcancel]
  calc
    _ ≤ ∑ n ∈ Ico (N+1) (2*N+3), ‖κ^n • momentumGrade (N+1) FInv M m u p z n‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_smul, norm_pow, Real.norm_eq_abs]


-- @@ L79-79 verbatim
end EulerPacketPointJets


-- @@ L81-81 verbatim
end

-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
@[expose] public section


-- @@ L88-88 verbatim
noncomputable section


-- @@ L90-90 verbatim
namespace EulerPacketResidual


-- @@ L92-92 verbatim
open Finset EulerFiniteGrades


-- @@ L94-95 verbatim
variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]


-- @@ L97-107 verbatim
theorem coefficient_eq_diagonal (M n : ℕ) (hn : n + 1 ≤ M)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u : ℕ → V) (p : ℕ → Q) :
    coefficient M L G H B C u p n =
      L (u n) + G (p n) + H (p (n+1)) +
      (∑ i ∈ range (n+1), B (u i) (u (n-i))) +
      (∑ i ∈ range (n+2), C (u i) (u (n+1-i))) := by
  unfold coefficient shiftDown
  rw [truncate_of_le M n _ (by omega), truncate_of_le M n _ (by omega),
    truncate_of_le M (n+1) _ hn, truncate_of_le (2*M) (n+1) _ (by omega),
    convolution_eq_range M n (by omega), convolution_eq_range M (n+1) hn]


-- @@ L109-109 verbatim
end EulerPacketResidual


-- @@ L111-111 verbatim
namespace EulerPacketPointJets


-- @@ L113-113 verbatim
open Finset EulerSmoothLimit EulerPacketResidual


-- @@ L115-124 verbatim
/-- This is the coefficient equation used in the source recursion, with actual derivatives. -/
theorem momentumGrade_eq_diagonal (N n : ℕ) (hn : n + 1 ≤ N)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain) :
    momentumGrade N FInv M m u p z n =
      linearPart M (jet (u n) z) + slowPressure FInv (jet (p n) z) +
      fastPressure m (jet (p (n+1)) z) +
      (∑ i ∈ range (n+1), slowAdvection FInv (jet (u i) z) (jet (u (n-i)) z)) +
      (∑ i ∈ range (n+2), fastAdvection m (jet (u i) z) (jet (u (n+1-i)) z)) :=
  coefficient_eq_diagonal N n hn _ _ _ _ _ _ _


-- @@ L126-126 verbatim
end EulerPacketPointJets
