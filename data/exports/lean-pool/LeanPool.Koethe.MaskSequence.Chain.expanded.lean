/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import LeanPool.Koethe.MaskSequence.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L15-22 verbatim
/-!
# A coherent chain of mortal periodic masks

An arbitrary sequence of pencils can be handled under the abstract
`MaskMortality` hypothesis.  The masks are refined at every stage and the
integral sparsity bound is retained.  A pointwise choice then produces a
nonzero sequence respecting every assignment at every stage.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace KoetheCounterexample

-- @@ L29-29 verbatim
namespace MaskSequence


-- @@ L31-31 verbatim
variable {k : Type*} [Field k]


-- @@ L33-35 verbatim
/-- The word is installed at the beginning of a period, and fits in that period. -/
def Carries (M : PeriodicMask k) (w : List (Triple k)) : Prop :=
  w.length ≤ M.period ∧ ∀ i : Fin w.length, M.lookup i.val = some (w.get i)


-- @@ L37-39 verbatim
/-- A mask contains a periodically recurring mortal word for this pencil. -/
def Kills {d : ℕ} (M : PeriodicMask k) (P : Pencil k d) : Prop :=
  ∃ w : List (Triple k), Carries M w ∧ P.wordProd w = 0


-- @@ L41-43 verbatim
/-- Finite masks whose assigned density is strictly less than one quarter. -/
abbrev SparseMask (k : Type*) [Field k] :=
  {M : PeriodicMask k // 4 * M.assigned < M.period}


-- @@ L45-54 verbatim
/-- Apply mortality only to a mask with more than half its positions free,
then preserve every old assignment while installing the resulting word. -/
theorem exists_mortal_extension (hm : MaskMortality k) (M : SparseMask k)
    {d : ℕ} (P : Pencil k d) :
    ∃ N : SparseMask k, Extends N.val M.val ∧ M.val.period ∣ N.val.period ∧
      Kills N.val P := by
  obtain ⟨w, _, _, hw, hc, hz⟩ := hm d P M.val (enough_holes M.val M.property)
  refine ⟨⟨install M.val w hw, install_sparse M.val w hw M.property⟩,
    install_extends M.val w hw hc, period_dvd_install M.val w hw, w, ?_, hz⟩
  exact ⟨length_le_install_period M.val w hw, install_word M.val w hw⟩


-- @@ L56-60 verbatim
/-- Stage zero has no assignments.  Stage `j+1` additionally kills pencil `e j`. -/
def masks (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d) : ℕ → SparseMask k
  | 0 => ⟨emptyMask, by simpa only [emptyMask_assigned, mul_zero] using
      (emptyMask (k := k)).period_pos⟩
  | j + 1 => (exists_mortal_extension hm (masks hm e j) (e j).2).choose


-- @@ L62-66 verbatim
theorem masks_succ (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d) (j : ℕ) :
    Extends (masks hm e (j + 1)).val (masks hm e j).val ∧
      (masks hm e j).val.period ∣ (masks hm e (j + 1)).val.period ∧
      Kills (masks hm e (j + 1)).val (e j).2 :=
  (exists_mortal_extension hm (masks hm e j) (e j).2).choose_spec


-- @@ L68-72 verbatim
theorem masks_extends (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d)
    {i j : ℕ} (hij : i ≤ j) : Extends (masks hm e j).val (masks hm e i).val := by
  induction j, hij using Nat.le_induction with
  | base => exact Extends.refl _
  | succ j _ ih => exact (masks_succ hm e j).1.trans ih


-- @@ L74-79 verbatim
theorem masks_period_dvd (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d)
    {i j : ℕ} (hij : i ≤ j) :
    (masks hm e i).val.period ∣ (masks hm e j).val.period := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_refl _
  | succ j _ ih => exact dvd_trans ih (masks_succ hm e j).2.1


-- @@ L81-106 verbatim
/-- Any increasing chain of nonzero partial masks has a simultaneous nonzero
completion.  A site assigned at any stage retains that exact vector forever.
Sites that are never assigned can harmlessly be filled with a fixed nonzero
vector; consequently no assertion about the density of the infinite union
is required. -/
theorem exists_compatible_sequence (M : ℕ → PeriodicMask k)
    (hM : ∀ i j, i ≤ j → Extends (M j) (M i)) :
    ∃ v : ℕ → Triple k, (∀ n, v n ≠ 0) ∧ ∀ j, (M j).SeqCompatible v := by
  classical
  have hpoint : ∀ n, ∃ z : Triple k, z ≠ 0 ∧
      ∀ j t, (M j).lookup n = some t → z = t := by
    intro n
    by_cases hn : ∃ j z, (M j).lookup n = some z
    · obtain ⟨j, z, hz⟩ := hn
      refine ⟨z, lookup_nonzero (M j) hz, ?_⟩
      intro i t ht
      rcases le_total j i with hji | hij
      · exact Option.some.inj ((hM j i hji n z hz).symm.trans ht)
      · exact Option.some.inj (hz.symm.trans (hM i j hij n t ht))
    · refine ⟨fun _ => 1, ?_, ?_⟩
      · intro hz
        exact one_ne_zero (congrFun hz 0)
      · intro j t ht
        exact (hn ⟨j, t, ht⟩).elim
  choose v hvzero hv using hpoint
  exact ⟨v, hvzero, fun j n z hz => hv n j z hz⟩


-- @@ L108-114 verbatim
/-- A nonzero sequence respecting all the periodic mortal words in the chain. -/
theorem exists_sequence_for_enumeration (hm : MaskMortality k)
    (e : ℕ → Σ d : ℕ, Pencil k d) :
    ∃ v : ℕ → Triple k, (∀ n, v n ≠ 0) ∧
      ∀ j, (masks hm e j).val.SeqCompatible v :=
  exists_compatible_sequence (fun j => (masks hm e j).val)
    (fun _ _ h => masks_extends hm e h)


-- @@ L116-116 verbatim
end MaskSequence

-- @@ L117-117 verbatim
end KoetheCounterexample


-- @@ L119-119 verbatim
end
