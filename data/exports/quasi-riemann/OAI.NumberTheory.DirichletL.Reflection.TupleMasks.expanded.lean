import OAI.NumberTheory.DirichletL.Reflection.SlotChoices
import OAI.NumberTheory.DirichletL.Reflection.OriginalMask


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]


-- @@ L13-30 verbatim
omit [Fintype σ] in
lemma slot_choice_fixed_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) (F : φ→Ideal Eis) :
    (∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
      (∀ j,∀ i : T,(a i).val≠F j) ∧ (∀ j,∀ i : {i // i∉T},(b i).val≠F j) := by
  constructor
  · intro h
    constructor
    · intro j i
      simpa only [slotChoiceSplit_active] using h j i.val
    · intro j i
      simpa only [slotChoiceSplit_inactive] using h j i.val
  · rintro ⟨ha,hb⟩ j i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha j ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb j ⟨i,hi⟩


-- @@ L32-40 verbatim
lemma slot_choice_mask_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val)
    (F : φ→Ideal Eis) (K : Ideal Eis) :
    (IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
    (IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j) ∧
      (IsCoprime K (∏ i : T,(a i).val) ∧ ∀ j,∀ i : T,(a i).val≠F j) := by
  rw [slot_choice_coprime_split,slot_choice_fixed_split]
  tauto


-- @@ L42-43 verbatim
def fixedTupleWeight (F : φ→Ideal Eis) (a : σ→Ideal Eis) (w : ℂ) : ℂ :=
  if ∀ j i,a i≠F j then w else 0


-- @@ L45-51 verbatim
omit [Fintype σ] [DecidableEq σ] in
lemma fixedTupleWeight_norm (F : φ→Ideal Eis) (a : σ→Ideal Eis) (w : ℂ) :
    ‖fixedTupleWeight F a w‖≤‖w‖ := by
  unfold fixedTupleWeight
  split
  · exact le_rfl
  · simp


-- @@ L53-63 verbatim
lemma split_masked_column (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val)
    (F : φ→Ideal Eis) (K : Ideal Eis) (w v : ℂ) :
    (if IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j then w*v else 0)=
    if IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j then
      (if IsCoprime K (∏ i : T,(a i).val) then fixedTupleWeight F (fun i : T => (a i).val) w*v else 0)
    else 0 := by
  simp only [slot_choice_mask_split]
  simp only [fixedTupleWeight]
  split_ifs <;> simp_all

-- @@ L64-64 verbatim
end

-- @@ L65-65 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L67-67 verbatim
end OAI
