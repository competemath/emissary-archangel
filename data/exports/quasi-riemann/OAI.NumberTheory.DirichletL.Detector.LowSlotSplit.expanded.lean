import OAI.NumberTheory.DirichletL.Detector.LowSelectedSum


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L10-11 verbatim
abbrev LowUnselectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : J,↥(slots i.val)

-- @@ L12-13 verbatim
abbrev LowSelectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : SelectedSlot J,↥(slots i.val)


-- @@ L15-29 verbatim
def lowSlotTupleEquiv {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :
    (∀i,↥(slots i)) ≃ LowUnselectedTuple slots J×LowSelectedTuple slots J where
  toFun p := (fun i=>p i.val,fun i=>p i.val)
  invFun p i := if hi : i∈J then p.1 ⟨i,hi⟩ else p.2 ⟨i,by simp [hi]⟩
  left_inv p := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dite_eq_left i.property]
    · funext i
      have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
      simp only [dite_eq_right hi]


-- @@ L31-33 verbatim
def lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) : Fin K→O :=
  fun i=>((lowSlotTupleEquiv slots J).symm (a,b) i).val


-- @@ L35-38 verbatim
lemma lowSlotJoin_nonzero {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : Fin K) :
    lowSlotJoin slots J a b i≠0 := hslots i _ ((lowSlotTupleEquiv slots J).symm (a,b) i).property


-- @@ L40-43 verbatim
lemma lowSlotJoin_unselected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : J) :
    lowSlotJoin slots J a b i.val=(a i).val := by
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_left i.property]


-- @@ L45-49 verbatim
lemma lowSlotJoin_selected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : SelectedSlot J) :
    lowSlotJoin slots J a b i.val=(b i).val := by
  have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_right hi]


-- @@ L51-56 verbatim
lemma lowSlotJoin_unselectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) J=∏i : J,(a i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort J]
  simp only [lowSlotJoin_unselected]


-- @@ L58-63 verbatim
lemma lowSlotJoin_selectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) (Finset.univ\J)=∏i : SelectedSlot J,(b i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort (Finset.univ\J)]
  simp only [lowSlotJoin_selected]


-- @@ L65-72 verbatim
lemma lowSlotJoin_selectedFactor {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ) :
    selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
        FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val)) := by
  unfold selectedSlotFactor
  simp only [lowSlotJoin_selected]


-- @@ L74-81 verbatim
theorem sum_lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(slots i)),F (fun i=>(p i).val))=
      ∑a : LowUnselectedTuple slots J,∑b : LowSelectedTuple slots J,F (lowSlotJoin slots J a b) := by
  calc
    _ = ∑p : LowUnselectedTuple slots J×LowSelectedTuple slots J,F (lowSlotJoin slots J p.1 p.2) :=
      (Equiv.sum_comp (lowSlotTupleEquiv slots J).symm (fun p=>F (fun i=>(p i).val))).symm
    _ = _ := Fintype.sum_prod_type _


-- @@ L83-83 verbatim
end SevenEighths.ProbePhysical

-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
