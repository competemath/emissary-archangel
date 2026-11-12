/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Auxiliary constructions indexed by partitions -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions


-- @@ L14-17 verbatim
/-- Returns the row coordinate of a natural index relative to a list of row lengths. -/
def flatIndexRow : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, k => if k < p then 0 else 1 + flatIndexRow ps (k - p)


-- @@ L19-22 verbatim
/-- Returns the column coordinate of a natural index relative to a list of row lengths. -/
def flatIndexColumn : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, k => if k < p then k else flatIndexColumn ps (k - p)


-- @@ L24-26 verbatim
/-- Associates an auxiliary list of natural numbers with a partition. -/
noncomputable def auxiliaryPartitionNatList {n : ℕ} (la : Nat.Partition n) : List ℕ :=
  la.parts.sort (· ≥ ·)


-- @@ L28-33 verbatim
/-- A second auxiliary type indexed by a natural number and a partition of it. -/
@[source_ref "Chapter5/Definition5.12.1" (role := supporting)]
noncomputable def AuxiliaryPartitionTarget (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := (auxiliaryPartitionNatList la)
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n // Function.Bijective f }


-- @@ L35-42 verbatim
/-- An auxiliary type indexed by a natural number and a partition of it. -/
noncomputable def AuxiliaryPartitionSource (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := (auxiliaryPartitionNatList la)
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n //
    Function.Bijective f ∧
    (∀ c₁ c₂ : Cell, c₁.1.1 = c₂.1.1 → c₁.1.2 < c₂.1.2 → f c₁ < f c₂) ∧
    (∀ c₁ c₂ : Cell, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 → f c₁ < f c₂) }


-- @@ L44-48 verbatim
/-- Maps an auxiliary source object to the auxiliary target type at the same partition. -/
noncomputable def AuxiliaryPartitionSource.toAuxiliaryPartitionTarget {n : ℕ}
    {la : Nat.Partition n}
    (T : AuxiliaryPartitionSource n la) : AuxiliaryPartitionTarget n la :=
  ⟨T.1, T.2.1⟩


-- @@ L50-67 verbatim
/-- A second auxiliary subgroup of the permutations of a finite type, indexed by a partition. -/
@[source_ref "Chapter5/Definition5.12.1" (role := supporting)]
noncomputable def auxiliaryPartitionPermutationSubgroupB (n : ℕ) (la : Nat.Partition n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | ∀ k : Fin n,
    flatIndexRow (auxiliaryPartitionNatList la) (σ k).val = flatIndexRow (auxiliaryPartitionNatList la) k.val }
  one_mem' := by
    intro k
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ k
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ (τ k), hτ k]
  inv_mem' := by
    intro σ hσ k
    have h := hσ (σ⁻¹ k)
    rw [show σ (σ⁻¹ k) = k from σ.apply_symm_apply k] at h
    exact h.symm


-- @@ L69-86 verbatim
/-- An auxiliary subgroup of the permutations of a finite type, indexed by a partition. -/
@[source_ref "Chapter5/Definition5.12.1" (role := supporting)]
noncomputable def auxiliaryPartitionPermutationSubgroupA (n : ℕ) (la : Nat.Partition n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | ∀ k : Fin n,
    flatIndexColumn (auxiliaryPartitionNatList la) (σ k).val = flatIndexColumn (auxiliaryPartitionNatList la) k.val }
  one_mem' := by
    intro k
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ k
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ (τ k), hτ k]
  inv_mem' := by
    intro σ hσ k
    have h := hσ (σ⁻¹ k)
    rw [show σ (σ⁻¹ k) = k from σ.apply_symm_apply k] at h
    exact h.symm


-- @@ L88-92 verbatim
/-- A second auxiliary element of the complex group algebra of permutations, indexed by a partition. -/
noncomputable def auxiliaryPartitionGroupAlgebraElementB (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ auxiliaryPartitionPermutationSubgroupB n la) := Classical.decPred _
  ∑ g : (auxiliaryPartitionPermutationSubgroupB n la), MonoidAlgebra.of ℂ _ g.val


-- @@ L94-99 verbatim
/-- An auxiliary element of the complex group algebra of permutations of a finite type, indexed by a partition. -/
noncomputable def auxiliaryPartitionGroupAlgebraElementA (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  ∑ g : (auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : ℂ) • MonoidAlgebra.of ℂ _ g.val


-- @@ L101-104 verbatim
/-- An auxiliary element of the complex permutation group algebra, indexed by a partition. -/
noncomputable def auxiliaryPartitionGroupAlgebraElementC (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  auxiliaryPartitionGroupAlgebraElementA n la * auxiliaryPartitionGroupAlgebraElementB n la


-- @@ L106-110 verbatim
/-- Another auxiliary complex permutation group algebra element indexed by a partition. -/
@[source_ref "Chapter5/Discussion_Young_projectors" (role := supporting)]
noncomputable def auxiliaryPartitionGroupAlgebraElementF (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (Nat.card (auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹ • auxiliaryPartitionGroupAlgebraElementB n la


-- @@ L112-116 verbatim
/-- An additional auxiliary complex permutation group algebra element indexed by a partition. -/
@[source_ref "Chapter5/Discussion_Young_projectors" (role := supporting)]
noncomputable def auxiliaryPartitionGroupAlgebraElementE (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (Nat.card (auxiliaryPartitionPermutationSubgroupA n la) : ℂ)⁻¹ • auxiliaryPartitionGroupAlgebraElementA n la


-- @@ L118-122 verbatim
/-- An auxiliary complex permutation group algebra element indexed by a partition. -/
@[source_ref "Chapter5/Discussion_Young_projectors" (role := supporting)]
noncomputable def auxiliaryPartitionGroupAlgebraElementD (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  auxiliaryPartitionGroupAlgebraElementF n la * auxiliaryPartitionGroupAlgebraElementE n la


-- @@ L124-137 verbatim
/-- For an index below the sum of the row lengths, its column coordinate is below the length of its row. -/
theorem flatIndexColumn_lt_rowLength (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    flatIndexColumn parts k < parts.getD (flatIndexRow parts k) 0 := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [flatIndexRow, flatIndexColumn]
    split_ifs with hlt
    · rw [List.getD_cons_zero]; omega
    · have hk' : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      change flatIndexColumn ps (k - p) < (p :: ps).getD (1 + flatIndexRow ps (k - p)) 0
      rw [show 1 + flatIndexRow ps (k - p) = flatIndexRow ps (k - p) + 1 from by omega,
          List.getD_cons_succ]
      exact ih (k - p) hk'


-- @@ L139-156 verbatim
/-- Two indices below the sum of the row lengths are equal when both their row and column coordinates agree. -/
theorem eq_of_flatIndexRow_eq_and_column_eq (parts : List ℕ) (k₁ k₂ : ℕ)
    (hk₁ : k₁ < parts.sum) (hk₂ : k₂ < parts.sum)
    (hrow : flatIndexRow parts k₁ = flatIndexRow parts k₂)
    (hcol : flatIndexColumn parts k₁ = flatIndexColumn parts k₂) : k₁ = k₂ := by
  induction parts generalizing k₁ k₂ with
  | nil => simp [List.sum_nil] at hk₁
  | cons p ps ih =>
    simp only [flatIndexRow, flatIndexColumn] at hrow hcol
    by_cases h₁ : k₁ < p <;> by_cases h₂ : k₂ < p
    · simp [h₁, h₂] at hcol; exact hcol
    · simp only [h₁, ite_true, h₂, ite_false] at hrow; omega
    · simp only [h₁, ite_false, h₂, ite_true] at hrow; omega
    · simp only [h₁, ite_false, h₂] at hrow hcol
      have hk₁' : k₁ - p < ps.sum := by simp [List.sum_cons] at hk₁; omega
      have hk₂' : k₂ - p < ps.sum := by simp [List.sum_cons] at hk₂; omega
      have : k₁ - p = k₂ - p := ih (k₁ - p) (k₂ - p) hk₁' hk₂' (by omega) hcol
      omega


-- @@ L158-175 verbatim
/-- Every column below a specified row length is represented by an index below the sum whose row and column coordinates are the specified values. -/
theorem exists_flatIndex_of_column_lt_rowLength (parts : List ℕ) (r c : ℕ)
    (hr : c < parts.getD r 0) :
    ∃ k, k < parts.sum ∧ flatIndexRow parts k = r ∧ flatIndexColumn parts k = c := by
  induction parts generalizing r with
  | nil => simp [List.getD] at hr
  | cons p ps ih =>
    cases r with
    | zero =>
      rw [List.getD_cons_zero] at hr
      exact ⟨c, by simp [List.sum_cons]; omega,
        by simp [flatIndexRow]; omega, by simp [flatIndexColumn]; omega⟩
    | succ r =>
      rw [List.getD_cons_succ] at hr
      obtain ⟨k, hk, hrow, hcol⟩ := ih r hr
      exact ⟨p + k, by simp [List.sum_cons]; omega,
        by simp [flatIndexRow]; omega,
        by simp [flatIndexColumn]; omega⟩


-- @@ L177-179 verbatim
/-- An auxiliary operation assigning a natural number to a list of naturals and a pair of naturals. -/
def auxiliaryListPairIndex (parts : List ℕ) (rc : ℕ × ℕ) : ℕ :=
  (parts.take rc.1).sum + rc.2


-- @@ L181-186 verbatim
private theorem sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have hcoe : ((auxiliaryPartitionNatList la) : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at hcoe
  rw [hcoe, la.parts_sum]


-- @@ L188-197 verbatim
private theorem rowOfPos_lt_length (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    flatIndexRow parts k < parts.length := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [flatIndexRow, List.length_cons]
    split_ifs with h
    · omega
    · have : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      have := ih _ this; omega


-- @@ L199-204 verbatim
private theorem sum_take_le (l : List ℕ) (a b : ℕ) (h : a ≤ b) :
    (l.take a).sum ≤ (l.take b).sum := by
  calc (l.take a).sum
      = ((l.take b).take a).sum := by rw [List.take_take, Nat.min_eq_left h]
    _ ≤ ((l.take b).take a).sum + ((l.take b).drop a).sum := Nat.le_add_right _ _
    _ = (l.take b).sum := by rw [← List.sum_append, List.take_append_drop]


-- @@ L206-220 verbatim
private theorem posOfCell_rowColOfPos (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    auxiliaryListPairIndex parts (flatIndexRow parts k, flatIndexColumn parts k) = k := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    by_cases hlt : k < p
    · simp only [flatIndexRow, flatIndexColumn, hlt, if_true, auxiliaryListPairIndex, List.take_zero,
        List.sum_nil, Nat.zero_add]
    · have hk' : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      simp only [flatIndexRow, flatIndexColumn, hlt, if_false, auxiliaryListPairIndex]
      rw [show 1 + flatIndexRow ps (k - p) = flatIndexRow ps (k - p) + 1 from Nat.add_comm _ _,
          List.take_succ_cons, List.sum_cons]
      have := ih (k - p) hk'
      simp only [auxiliaryListPairIndex] at this
      omega


-- @@ L222-245 verbatim
private theorem rowColOfPos_posOfCell (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts.getD r 0) :
    flatIndexRow parts (auxiliaryListPairIndex parts (r, c)) = r ∧
    flatIndexColumn parts (auxiliaryListPairIndex parts (r, c)) = c := by
  induction parts generalizing r with
  | nil => simp at hr
  | cons p ps ih =>
    cases r with
    | zero =>
      have hcp : c < p := by rwa [List.getD_cons_zero] at hc
      refine ⟨?_, ?_⟩ <;>
        simp only [auxiliaryListPairIndex, List.take_zero, List.sum_nil, Nat.zero_add, flatIndexRow, flatIndexColumn,
          hcp, if_true]
    | succ r =>
      have hr' : r < ps.length := by simpa using hr
      have hc' : c < ps.getD r 0 := by rwa [List.getD_cons_succ] at hc
      have hpos : auxiliaryListPairIndex (p :: ps) (r + 1, c) = p + auxiliaryListPairIndex ps (r, c) := by
        simp only [auxiliaryListPairIndex, List.take_succ_cons, List.sum_cons]; ring
      rw [hpos]
      obtain ⟨ih1, ih2⟩ := ih r hr' hc'
      have hge : ¬ (p + auxiliaryListPairIndex ps (r, c) < p) := by omega
      refine ⟨?_, ?_⟩
      · simp only [flatIndexRow, hge, if_false, Nat.add_sub_cancel_left, ih1]; omega
      · simp only [flatIndexColumn, hge, if_false, Nat.add_sub_cancel_left, ih2]


-- @@ L247-258 verbatim
private theorem posOfCell_lt_sum (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts.getD r 0) :
    auxiliaryListPairIndex parts (r, c) < parts.sum := by
  have hgetD : parts.getD r 0 = parts[r] := List.getD_eq_getElem parts 0 hr
  have hsucc : (parts.take (r + 1)).sum = (parts.take r).sum + parts[r] :=
    List.sum_take_succ parts r hr
  have hle : (parts.take (r + 1)).sum ≤ (parts.take parts.length).sum :=
    sum_take_le parts (r + 1) parts.length hr
  rw [List.take_length] at hle
  simp only [auxiliaryListPairIndex]
  rw [hgetD] at hc
  omega


-- @@ L260-264 verbatim
private noncomputable def canonicalFun (n : ℕ) (la : Nat.Partition n) :
    { c : ℕ × ℕ // c.1 < (auxiliaryPartitionNatList la).length ∧ c.2 < (auxiliaryPartitionNatList la).getD c.1 0 } → Fin n :=
  fun cell => ⟨auxiliaryListPairIndex (auxiliaryPartitionNatList la) cell.1, by
    have h := posOfCell_lt_sum (auxiliaryPartitionNatList la) cell.1.1 cell.1.2 cell.2.1 cell.2.2
    rw [sortedParts_sum] at h; exact h⟩


-- @@ L266-282 verbatim
private theorem canonicalFun_bijective (n : ℕ) (la : Nat.Partition n) :
    Function.Bijective (canonicalFun n la) := by
  have hsum : (auxiliaryPartitionNatList la).sum = n := sortedParts_sum n la
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun k => ⟨(flatIndexRow (auxiliaryPartitionNatList la) k.val, flatIndexColumn (auxiliaryPartitionNatList la) k.val),
      rowOfPos_lt_length (auxiliaryPartitionNatList la) k.val (by omega),
      flatIndexColumn_lt_rowLength (auxiliaryPartitionNatList la) k.val (by omega)⟩, ?_, ?_⟩
  · intro cell
    apply Subtype.ext
    obtain ⟨⟨r, c⟩, hr, hc⟩ := cell
    simp only [canonicalFun]
    obtain ⟨e1, e2⟩ := rowColOfPos_posOfCell (auxiliaryPartitionNatList la) r c hr hc
    rw [e1, e2]
  · intro k
    apply Fin.ext
    simp only [canonicalFun]
    exact posOfCell_rowColOfPos (auxiliaryPartitionNatList la) k.val (by omega)


-- @@ L284-290 verbatim
private theorem canonicalFun_row_inc (n : ℕ) (la : Nat.Partition n)
    (c₁ c₂ : { c : ℕ × ℕ // c.1 < (auxiliaryPartitionNatList la).length ∧ c.2 < (auxiliaryPartitionNatList la).getD c.1 0 })
    (hrow : c₁.1.1 = c₂.1.1) (hcol : c₁.1.2 < c₂.1.2) :
    canonicalFun n la c₁ < canonicalFun n la c₂ := by
  simp only [canonicalFun, Fin.mk_lt_mk, auxiliaryListPairIndex]
  rw [hrow]
  omega


-- @@ L292-307 verbatim
private theorem canonicalFun_col_inc (n : ℕ) (la : Nat.Partition n)
    (c₁ c₂ : { c : ℕ × ℕ // c.1 < (auxiliaryPartitionNatList la).length ∧ c.2 < (auxiliaryPartitionNatList la).getD c.1 0 })
    (hcol : c₁.1.2 = c₂.1.2) (hrow : c₁.1.1 < c₂.1.1) :
    canonicalFun n la c₁ < canonicalFun n la c₂ := by
  simp only [canonicalFun, Fin.mk_lt_mk, auxiliaryListPairIndex]
  have hr1 : c₁.1.1 < (auxiliaryPartitionNatList la).length := c₁.2.1
  have hgetD : (auxiliaryPartitionNatList la).getD c₁.1.1 0 = (auxiliaryPartitionNatList la)[c₁.1.1] :=
    List.getD_eq_getElem (auxiliaryPartitionNatList la) 0 hr1
  have hc1 : c₁.1.2 < (auxiliaryPartitionNatList la).getD c₁.1.1 0 := c₁.2.2
  have hsucc : ((auxiliaryPartitionNatList la).take (c₁.1.1 + 1)).sum
      = ((auxiliaryPartitionNatList la).take c₁.1.1).sum + (auxiliaryPartitionNatList la)[c₁.1.1] :=
    List.sum_take_succ (auxiliaryPartitionNatList la) c₁.1.1 hr1
  have hle : ((auxiliaryPartitionNatList la).take (c₁.1.1 + 1)).sum ≤ ((auxiliaryPartitionNatList la).take c₂.1.1).sum :=
    sum_take_le (auxiliaryPartitionNatList la) (c₁.1.1 + 1) c₂.1.1 (by omega)
  rw [hgetD] at hc1
  omega


-- @@ L309-312 verbatim
/-- Selects an object of the auxiliary target type for each partition. -/
@[source_ref "Chapter5/Definition5.12.1" (role := supporting)]
noncomputable def chosenAuxiliaryPartitionTarget (n : ℕ) (la : Nat.Partition n) : AuxiliaryPartitionTarget n la :=
  ⟨canonicalFun n la, canonicalFun_bijective n la⟩


-- @@ L314-319 verbatim
/-- Selects an object of the auxiliary source type for each partition. -/
@[source_ref "Chapter5/Definition5.12.1" (role := supporting)]
noncomputable def chosenAuxiliaryPartitionSource (n : ℕ) (la : Nat.Partition n) :
    AuxiliaryPartitionSource n la :=
  ⟨canonicalFun n la, canonicalFun_bijective n la,
    canonicalFun_row_inc n la, canonicalFun_col_inc n la⟩


-- @@ L321-325 verbatim
/-- The displayed conversion sends the selected auxiliary source object to the selected auxiliary target object. -/
theorem chosenAuxiliaryPartitionObjects_compatible (n : ℕ) (la : Nat.Partition n) :
    (chosenAuxiliaryPartitionSource n la).toAuxiliaryPartitionTarget =
      chosenAuxiliaryPartitionTarget n la :=
  rfl


-- @@ L327-327 verbatim
end RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
