import OAI.NumberTheory.DirichletL.Reflection.TupleMasks


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]


-- @@ L12-13 verbatim
def supportedSlotChoices (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :=
  {p : ∀ i,L i // IsCoprime K (∏ i,(p i).val) ∧ ∀ j i,(p i).val≠F j}


-- @@ L15-16 verbatim
instance supportedSlotChoices_fintype (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    Fintype (supportedSlotChoices L F K) := inferInstanceAs (Fintype {_p : ∀ i,L i // _})


-- @@ L18-34 verbatim
def supportedSlotSplit (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K ×
        supportedSlotChoices (fun i : T => L i.val) F K where
  toFun p :=
    let q := slotChoiceSplit L T p.val
    have h := (slot_choice_mask_split L T q.1 q.2 F K).mp (by simpa only [q,Prod.mk.eta,Equiv.symm_apply_apply] using p.property)
    (⟨q.2,h.1⟩,⟨q.1,h.2⟩)
  invFun q := ⟨(slotChoiceSplit L T).symm (q.2.val,q.1.val),
    (slot_choice_mask_split L T q.2.val q.1.val F K).mpr ⟨q.1.property,q.2.property⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (slotChoiceSplit L T).symm_apply_apply p.val
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.snd ((slotChoiceSplit L T).apply_symm_apply (q.2.val,q.1.val))
    · exact congrArg Prod.fst ((slotChoiceSplit L T).apply_symm_apply (q.2.val,q.1.val))


-- @@ L36-54 verbatim
theorem sum_supported_slot_choices (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (K : Ideal Eis) (H : supportedSlotChoices L F K→ℂ) :
    (∑ p : supportedSlotChoices L F K,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p.val i).val:ℂ)⁻¹)*H p)=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K,
      (∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*
        ∑ a : supportedSlotChoices (fun i : T => L i.val) F K,
          H ((supportedSlotSplit L T F K).symm (b,a)) := by
  rw [←(supportedSlotSplit L T F K).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  change (∏ i∈(Finset.univ:Finset σ)\T,
    (Ideal.absNorm (((slotChoiceSplit L T).symm (a.val,b.val)) i).val:ℂ)⁻¹)=_
  rw [slot_choice_inactive_weight,Equiv.apply_symm_apply]

-- @@ L55-55 verbatim
end

-- @@ L56-56 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L58-58 verbatim
end OAI
