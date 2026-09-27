/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem


-- @@ L10-14 verbatim
/-!
# Morrey Balls

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory Set

-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic.Morrey



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace CKN


-- @@ L28-35 verbatim
private theorem morreyBallNorm_le_of_cell_bound
    {P τ : ℝ} {g : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hcell : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
      morreyBallCell P τ g z r ≤ K) :
    morreyBallNorm P τ g ≤ K := by
  unfold morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  exact hcell z r.1 r.2


-- @@ L37-43 verbatim
private theorem morreyBallNorm_lt_top_of_cell_bound
    {P τ : ℝ} {g : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hK : K < ⊤)
    (hcell : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
      morreyBallCell P τ g z r ≤ K) :
    morreyBallNorm P τ g < ⊤ :=
  lt_of_le_of_lt (morreyBallNorm_le_of_cell_bound hcell) hK


-- @@ L45-76 verbatim
/-- Step 2 Morrey bookkeeping.  The three cell estimates are the outputs of
the local decay estimate, the radius-shifted interpolation glue, and the
global finiteness argument.  Once those estimates are supplied, the
ball Morrey memberships follow directly, with the paper exponents
`τ₂ = 25/3` and `τ₃ = τp = 25/8`. -/
theorem step2_morrey_balls
    {Q₂ : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {Kᵤ K_Du Kₚ : ℝ≥0∞}
    (hKᵤ : Kᵤ < ⊤) (hK_Du : K_Du < ⊤) (hKₚ : Kₚ < ⊤)
    (hᵤ : ∀ i : Fin 3, ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
      morreyBallCell 3 (25 / 3 : ℝ)
        (Q₂.indicator (fun w => u w i)) z r ≤ Kᵤ)
    (hDu : ∀ i : Fin 3, ∀ j : Fin 3, ∀ z : ParabolicPoint, ∀ r : ℝ,
      0 < r → morreyBallCell 2 (25 / 8 : ℝ)
        (Q₂.indicator (fun w => Du w i j)) z r ≤ K_Du)
    (hp : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
      morreyBallCell (3 / 2 : ℝ) (25 / 8 : ℝ)
        (Q₂.indicator p) z r ≤ Kₚ) :
    morreyVecMem 3 (25 / 3 : ℝ) Q₂ u ∧
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ) Q₂ (fun z => Du z i)) ∧
      morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ) (Q₂.indicator p) < ⊤ := by
  have hu : morreyVecMem 3 (25 / 3 : ℝ) Q₂ u := by
    intro i
    exact morreyBallNorm_lt_top_of_cell_bound hKᵤ (hᵤ i)
  have hDu' : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ) Q₂ (fun z => Du z i) := by
    intro i j
    exact morreyBallNorm_lt_top_of_cell_bound hK_Du (hDu i j)
  have hp' : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      (Q₂.indicator p) < ⊤ :=
    morreyBallNorm_lt_top_of_cell_bound hKₚ hp
  exact ⟨hu, hDu', hp'⟩


-- @@ L78-78 verbatim
end CKN
