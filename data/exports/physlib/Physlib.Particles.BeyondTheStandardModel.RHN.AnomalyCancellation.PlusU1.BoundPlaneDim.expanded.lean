/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.PlaneNonSols

-- @@ L9-15 verbatim
/-!
# Bound on plane dimension

We place an upper bound on the dimension of a plane of charges on which every point is a solution.
The upper bound is 7, proven in the theorem `plane_exists_dim_le_7`.

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace SMRHN

-- @@ L20-20 verbatim
namespace PlusU1


-- @@ L22-22 verbatim
open SMνCharges

-- @@ L23-23 verbatim
open SMνACCs

-- @@ L24-24 verbatim
open BigOperators


-- @@ L26-29 verbatim
/-- A proposition which is true if for a given `n`, a plane of charges of dimension `n` exists
in which each point is a solution. -/
def ExistsPlane (n : ℕ) : Prop := ∃ (B : Fin n → (PlusU1 3).Charges),
  LinearIndependent ℚ B ∧ ∀ (f : Fin n → ℚ), (PlusU1 3).IsSolution (∑ i, f i • B i)


-- @@ L31-49 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma exists_plane_exists_basis {n : ℕ} (hE : ExistsPlane n) :
    ∃ (B : Fin 11 ⊕ Fin n → (PlusU1 3).Charges), LinearIndependent ℚ B := by
  obtain ⟨E, hE1, hE2⟩ := hE
  obtain ⟨B, hB1, hB2⟩ := eleven_dim_plane_of_no_sols_exists
  let Y := Sum.elim B E
  refine ⟨Y, Fintype.linearIndependent_iff.mpr fun g hg ↦ ?_⟩
  rw [Fintype.sum_sum_type, add_eq_zero_iff_eq_neg] at hg
  simp only [← Finset.sum_neg_distrib, ← neg_smul] at hg
  have h2 : ∑ a₁ : Fin 11, g (Sum.inl a₁) • Y (Sum.inl a₁) = 0 := by
    apply hB2
    erw [hg]
    exact hE2 fun i => -g (Sum.inr i)
  rw [Fintype.linearIndependent_iff] at hB1 hE1
  have h3 : ∀ i, g (Sum.inl i) = 0 := hB1 (fun i => g (Sum.inl i)) h2
  rw [h2] at hg
  have h4 := hE1 (fun i => -g (Sum.inr i)) hg.symm
  simp only [neg_eq_zero] at h4
  exact fun i => i.rec h3 h4


-- @@ L51-56 verbatim
theorem plane_exists_dim_le_7 {n : ℕ} (hn : ExistsPlane n) : n ≤ 7 := by
  obtain ⟨B, hB⟩ := exists_plane_exists_basis hn
  have h1 := LinearIndependent.fintype_card_le_finrank hB
  simp only [Fintype.card_sum, Fintype.card_fin,
    show Module.finrank ℚ (PlusU1 3).Charges = 18 from Module.finrank_fin_fun ℚ] at h1
  omega


-- @@ L58-58 verbatim
end PlusU1

-- @@ L59-59 verbatim
end SMRHN
