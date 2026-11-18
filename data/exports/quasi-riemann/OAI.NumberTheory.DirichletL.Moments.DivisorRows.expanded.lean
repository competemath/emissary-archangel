import OAI.NumberTheory.DirichletL.Moments.DivisorRectangle


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentDivisorRows

-- @@ L9-9 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor

-- @@ L10-10 verbatim
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight

-- @@ L11-11 verbatim
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L15-23 verbatim
def allocatedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J


-- @@ L25-47 verbatim
theorem allocatedRectangle_eq_rows (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ((rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
          rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1)))*
          ∏ i,rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t) := by
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedRectangle
  rw [allocated_rectangle_reindex]
  rw [actual_slot_rectangle_sum η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t W₁ W₂ b₁ b₂
    _ _ _ _ hW₁ hW₂ (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1))
    (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))]


-- @@ L49-66 verbatim
theorem allocatedRectangle_norm_le (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      ‖rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
        rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))‖ *
        ∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖ := by
  rw [allocatedRectangle_eq_rows η m A z t S β D a W₁ W₂ b₁ b₂ _ _ _ _
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,norm_mul,norm_mul,allocationSign_norm,one_mul,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact row_twisted_coefficient_norm η m A z t _ (mul_ne_zero
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))


-- @@ L68-68 verbatim
end SevenEighths.CenteredMomentDivisorRows


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end OAI
