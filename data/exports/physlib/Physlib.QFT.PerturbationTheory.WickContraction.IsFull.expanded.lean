/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Fin.Involutions
public import Physlib.QFT.PerturbationTheory.WickContraction.ExtractEquiv
public import Physlib.QFT.PerturbationTheory.WickContraction.Involutions

-- @@ L11-17 verbatim
/-!

# Full contraction

We say that a contraction is full if it has no uncontracted fields.

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open FieldSpecification

-- @@ L22-22 verbatim
variable {𝓕 : FieldSpecification}

-- @@ L23-23 verbatim
namespace WickContraction

-- @@ L24-24 verbatim
variable {n : ℕ} (c : WickContraction n)

-- @@ L25-25 verbatim
open Physlib.List

-- @@ L26-26 verbatim
open FieldStatistic

-- @@ L27-27 verbatim
open Nat


-- @@ L29-31 verbatim
/-- A contraction is full if there are no uncontracted fields, i.e. the finite set
  of uncontracted fields is empty. -/
def IsFull : Prop := c.uncontracted = ∅


-- @@ L33-34 verbatim
/-- The condition on whether or not a contraction is full is decidable. -/
instance : Decidable (IsFull c) := decEq c.uncontracted ∅


-- @@ L36-40 verbatim
lemma isFull_iff_equivInvolution_no_fixed_point :
    IsFull c ↔ ∀ (i : Fin n), (equivInvolution c).1 i ≠ i := by
  simp only [IsFull, ne_eq]
  rw [Finset.eq_empty_iff_forall_notMem]
  simp [equivInvolution, toInvolution, uncontracted]


-- @@ L42-53 verbatim
/-- The equivalence between full contractions and fixed-point free involutions. -/
def isFullInvolutionEquiv : {c : WickContraction n // IsFull c} ≃
    {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} where
  toFun c := ⟨equivInvolution c.1, by
    apply And.intro (equivInvolution c.1).2
    rw [← isFull_iff_equivInvolution_no_fixed_point]
    exact c.2⟩
  invFun f := ⟨equivInvolution.symm ⟨f.1, f.2.1⟩, by
    rw [isFull_iff_equivInvolution_no_fixed_point]
    simpa using f.2.2⟩
  left_inv c := by simp
  right_inv f := by simp


-- @@ L55-59 verbatim
/-- If `n` is even then the number of full contractions is `(n-1)!!`. -/
theorem card_of_isfull_even (he : Even n) :
    Fintype.card {c : WickContraction n // IsFull c} = (n - 1)‼ := by
  rw [Fintype.card_congr (isFullInvolutionEquiv)]
  exact Physlib.Fin.involutionNoFixed_card_even n he


-- @@ L61-66 verbatim
/-- If `n` is odd then there are no full contractions. This is because
  there will always be at least one element unpaired. -/
theorem card_of_isfull_odd (ho : Odd n) :
    Fintype.card {c : WickContraction n // IsFull c} = 0 := by
  rw [Fintype.card_congr (isFullInvolutionEquiv)]
  exact Physlib.Fin.involutionNoFixed_card_odd n ho


-- @@ L68-68 verbatim
end WickContraction
