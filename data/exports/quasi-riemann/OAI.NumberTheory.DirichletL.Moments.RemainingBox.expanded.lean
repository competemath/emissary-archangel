import OAI.NumberTheory.DirichletL.Moments.CommonProfile


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentRemainingBox

-- @@ L9-9 verbatim
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L13-15 verbatim
def restoreTuple (B : Tuple ι) (v : Tuple (liveIndices B)) : Tuple ι :=
  Sum.elim (fun i => if h : i∈liveIndices B then v (Sum.inl ⟨i,h⟩) else 1)
    (fun j => v (Sum.inr j))


-- @@ L17-22 verbatim
@[simp] theorem remaining_restore (B : Tuple ι) (v : Tuple (liveIndices B)) :
    remainingTuple B (restoreTuple B v)=v := by
  funext i
  rcases i with i|j
  · simp [remainingTuple,restoreTuple]
  · rfl


-- @@ L24-33 verbatim
theorem restore_remaining (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    restoreTuple B (remainingTuple B u)=u := by
  funext i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · rfl
    · exact (hf i (by simpa [liveIndices] using hi)).symm
  · rfl


-- @@ L35-37 verbatim
def remainingSets (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O)) :
    (liveIndices B ⊕ Fin 2) → Finset (Ideal O) :=
  Sum.elim (fun i => S (Sum.inl i.val)) (fun j => S (Sum.inr j))


-- @@ L39-46 verbatim
theorem remaining_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (u : Tuple ι) (hu : u∈Fintype.piFinset S) :
    remainingTuple B u∈Fintype.piFinset (remainingSets B S) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · exact Fintype.mem_piFinset.mp hu (Sum.inl i.val)
  · exact Fintype.mem_piFinset.mp hu (Sum.inr j)


-- @@ L48-59 verbatim
theorem restore_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (v : Tuple (liveIndices B)) (hv : v∈Fintype.piFinset (remainingSets B S)) :
    restoreTuple B v∈Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · exact Fintype.mem_piFinset.mp hv (Sum.inl ⟨i,hi⟩)
    · exact hg i (by simpa [liveIndices] using hi)
  · exact Fintype.mem_piFinset.mp hv (Sum.inr j)


-- @@ L61-76 verbatim
theorem remaining_box_sum (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) := by
  apply Finset.sum_bij (fun u _ => remainingTuple B u)
  · exact fun u hu => remaining_mem B S u hu
  · intro u hu v hv he
    have hu' := restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))
    have hv' := restore_remaining B v (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hv _))
    rw [← hu',← hv',he]
  · intro v hv
    exact ⟨restoreTuple B v,restore_mem B S hg v hv,remaining_restore B v⟩
  · intro u hu
    rw [restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))]


-- @@ L78-93 verbatim
theorem remaining_box_sum_gate (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      if (∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) else 0 := by
  split_ifs with hg
  · exact remaining_box_sum B S hf hg F
  · have he : Fintype.piFinset S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      apply hg
      intro i hi
      have hui := Fintype.mem_piFinset.mp hu (Sum.inl i)
      rwa [hf i hi _ hui] at hui
    rw [he,Finset.sum_empty]


-- @@ L95-95 verbatim
end SevenEighths.CenteredMomentRemainingBox


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
end OAI
