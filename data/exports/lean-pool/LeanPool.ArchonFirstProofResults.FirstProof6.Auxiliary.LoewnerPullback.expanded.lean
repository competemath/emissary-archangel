/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LaplacianBasics
import Mathlib.Algebra.Order.Star.Real


-- @@ L11-15 verbatim
/-!
# Problem 6: Large epsilon-light vertex subsets -- Loewner Pullback

Congruence pullbacks for Loewner order and epsilon-lightness from Loewner bound.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Finset Matrix BigOperators


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace Problem6


-- @@ L25-25 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V]


-- @@ L27-41 verbatim
lemma sqrt_pullback_loewner
    (L : Matrix V V ℝ)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = L)
    (M : Matrix V V ℝ) (u : ℝ)
    (hM : (u • (1 : Matrix V V ℝ) - M).PosSemidef) :
    (u • L - Lhalf * M * Lhalf).PosSemidef := by
  have h_eq : u • L - Lhalf * M * Lhalf =
      Lhalfᴴ * (u • (1 : Matrix V V ℝ) - M) * Lhalf := by
    rw [hLhalf_herm.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_mul_assoc, Matrix.mul_one,
               mul_smul_comm, Matrix.mul_assoc, ← hLhalf_sq]
  rw [h_eq]
  exact hM.conjTranspose_mul_mul_same Lhalf


-- @@ L43-62 verbatim
lemma eps_light_of_loewner_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε u : ℝ) (_hε : 0 < ε) (hu : u ≤ ε)
    (S : Finset V)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (M : Matrix V V ℝ)
    (hM_bound : (u • (1 : Matrix V V ℝ) - M).PosSemidef)
    (hM_conn : Lhalf * M * Lhalf = inducedLaplacian G S) :
    IsEpsLight G ε S := by
  unfold IsEpsLight
  have h_uL : (u • graphLaplacian G - inducedLaplacian G S).PosSemidef := by
    rw [← hM_conn]
    exact sqrt_pullback_loewner (graphLaplacian G) Lhalf hLhalf_herm hLhalf_sq M u hM_bound
  have h_split : ε • graphLaplacian G - inducedLaplacian G S =
      (u • graphLaplacian G - inducedLaplacian G S) + (ε - u) • graphLaplacian G := by
    rw [sub_smul]; abel
  rw [h_split]
  exact h_uL.add ((graphLaplacian_posSemidef G).smul (by linarith))


-- @@ L64-64 verbatim
end Problem6


-- @@ L66-66 verbatim
end
