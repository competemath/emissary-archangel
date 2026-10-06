/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import DescriptiveComplexity.Computability.FinStruct


-- @@ L11-35 verbatim
/-!
# Presenting vocabularies as data

Ways of exhibiting a `FirstOrder.Language.FinVocab`, the finite presentation
of a relational vocabulary that `FirstOrder.Language.FinStruct` encodes
structures over.

A presentation is exactly a numbering of the symbols, i.e., an equivalence

```
Fin numSyms ≃ ((n : ℕ) × L.Relations n)
```

(`FirstOrder.Language.FinVocab.symEquiv` and
`FirstOrder.Language.FinVocab.ofEquivSigma` are mutually inverse constructions),
so a presentation can be built from any such numbering: from a duplicate-free
list of all the symbols (`FirstOrder.Language.FinVocab.ofList`, the way every
vocabulary of the catalog is presented), or by combining two presentations
(`FirstOrder.Language.FinVocab.sum`).

The sum is what makes the whole development go through: the vocabularies of
the second-order machinery are sums of an instance's vocabulary with a
quantifier block's, and everything about them is encoded by the same means as
an ordinary instance.
-/


-- @@ L37-37 verbatim
namespace FirstOrder


-- @@ L39-39 verbatim
namespace Language


-- @@ L41-41 verbatim
namespace FinVocab


-- @@ L43-43 verbatim
variable {L L' : Language.{0, 0}}


-- @@ L45-51 verbatim
/-- **A presentation is a numbering of the symbols.** -/
@[simps]
def symEquiv (V : FinVocab L) : Fin V.numSyms ≃ ((n : ℕ) × L.Relations n) where
  toFun := V.symOf
  invFun p := V.index p.2
  left_inv := V.index_symOf
  right_inv p := V.symOf_index p.2


-- @@ L53-60 verbatim
/-- **A numbering of the symbols is a presentation**, the converse of
`FirstOrder.Language.FinVocab.symEquiv`. -/
def ofEquivSigma (k : ℕ) (e : Fin k ≃ ((n : ℕ) × L.Relations n)) : FinVocab L where
  numSyms := k
  symOf := e
  index R := e.symm ⟨_, R⟩
  symOf_index R := e.apply_symm_apply _
  index_symOf i := by simp


-- @@ L62-63 verbatim
@[simp] theorem numSyms_ofEquivSigma (k : ℕ) (e : Fin k ≃ ((n : ℕ) × L.Relations n)) :
    (ofEquivSigma k e).numSyms = k := rfl


-- @@ L65-66 verbatim
@[simp] theorem symOf_ofEquivSigma (k : ℕ) (e : Fin k ≃ ((n : ℕ) × L.Relations n))
    (i : Fin k) : (ofEquivSigma k e).symOf i = e i := rfl


-- @@ L68-73 verbatim
/-- **A vocabulary presented by a list of all its symbols**, without
repetitions: the way the vocabularies of the catalog, which are finite
enumerations, are presented. -/
def ofList [DecidableEq ((n : ℕ) × L.Relations n)] (l : List ((n : ℕ) × L.Relations n))
    (nd : l.Nodup) (h : ∀ p : (n : ℕ) × L.Relations n, p ∈ l) : FinVocab L :=
  ofEquivSigma l.length (List.Nodup.getEquivOfForallMemList l nd h)


-- @@ L75-96 verbatim
/-- **Presentations combine along `Language.sum`**: a symbol of the sum
vocabulary is a symbol of one side or of the other. This is what lets the
vocabularies of the second-order machinery – an instance's vocabulary summed
with a quantifier block's – be encoded like any other. -/
def sum (V : FinVocab L) (W : FinVocab L') : FinVocab (L.sum L') where
  numSyms := V.numSyms + W.numSyms
  symOf i := Fin.addCases (motive := fun _ => (n : ℕ) × (L.sum L').Relations n)
    (fun j => ⟨(V.symOf j).1, Sum.inl (V.symOf j).2⟩)
    (fun j => ⟨(W.symOf j).1, Sum.inr (W.symOf j).2⟩) i
  index R := Sum.elim (fun r => Fin.castAdd _ (V.index r)) (fun r => Fin.natAdd _ (W.index r)) R
  symOf_index R := by
    cases R with
    | inl r => simpa using congrArg (fun p : (n : ℕ) × L.Relations n => (⟨p.1, Sum.inl p.2⟩ :
        (n : ℕ) × (L.sum L').Relations n)) (V.symOf_index r)
    | inr r => simpa using congrArg (fun p : (n : ℕ) × L'.Relations n => (⟨p.1, Sum.inr p.2⟩ :
        (n : ℕ) × (L.sum L').Relations n)) (W.symOf_index r)
  index_symOf i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]
      exact congrArg (Fin.castAdd W.numSyms) (V.index_symOf j)
    · rw [Fin.addCases_right]
      exact congrArg (Fin.natAdd V.numSyms) (W.index_symOf j)


-- @@ L98-99 verbatim
@[simp] theorem numSyms_sum (V : FinVocab L) (W : FinVocab L') :
    (V.sum W).numSyms = V.numSyms + W.numSyms := rfl


-- @@ L101-106 verbatim
/-- **The numbering of a sum vocabulary**: the symbols of the left summand keep
their numbers, those of the right summand are shifted past them. This is the
only fact about `FirstOrder.Language.FinVocab.sum` anything downstream uses –
it is what fixes the layout of the table of an encoded structure. -/
theorem index_sum_inl (V : FinVocab L) (W : FinVocab L') {n : ℕ} (r : L.Relations n) :
    (V.sum W).index (Sum.inl r) = Fin.castAdd W.numSyms (V.index r) := rfl


-- @@ L108-109 verbatim
theorem index_sum_inr (V : FinVocab L) (W : FinVocab L') {n : ℕ} (r : L'.Relations n) :
    (V.sum W).index (Sum.inr r) = Fin.natAdd V.numSyms (W.index r) := rfl


-- @@ L111-113 verbatim
@[simp] theorem val_index_sum_inl (V : FinVocab L) (W : FinVocab L') {n : ℕ}
    (r : L.Relations n) : (((V.sum W).index (Sum.inl r) : Fin _) : ℕ) = (V.index r : ℕ) := by
  rw [index_sum_inl]; rfl


-- @@ L115-118 verbatim
@[simp] theorem val_index_sum_inr (V : FinVocab L) (W : FinVocab L') {n : ℕ}
    (r : L'.Relations n) :
    (((V.sum W).index (Sum.inr r) : Fin _) : ℕ) = V.numSyms + (W.index r : ℕ) := by
  rw [index_sum_inr]; rfl


-- @@ L120-120 verbatim
end FinVocab


-- @@ L122-122 verbatim
end Language


-- @@ L124-124 verbatim
end FirstOrder
