/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Bit
import LeanPool.Incompleteness.Arithmetization.Definability.Init


-- @@ L11-11 verbatim
/-! # Coding -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Arith


-- @@ L21-21 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L23-23 expanded
variable {V : Type*} [ORingStruc V] [ModelsTheory V (iSigma 1)]


-- @@ L25-28 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def finsetArithmetizeAux : List V → V
  | []      => ∅
  | x :: xs => insert x (finsetArithmetizeAux xs)


-- @@ L30-30 verbatim
@[simp] lemma finsetArithmetizeAux_nil : finsetArithmetizeAux ([] : List V) = ∅ := rfl


-- @@ L32-33 verbatim
@[simp] lemma finsetArithmetizeAux_cons (x : V) (xs) :
    finsetArithmetizeAux (x :: xs) = insert x (finsetArithmetizeAux xs) := rfl


-- @@ L35-36 verbatim
@[simp] lemma mem_finsetArithmetizeAux_iff {x : V} {s : List V} :
    x ∈ finsetArithmetizeAux s ↔ x ∈ s := by induction s <;> simp [*]


-- @@ L38-39 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.Finset.arithmetize (s : Finset V) : V := finsetArithmetizeAux s.toList


-- @@ L41-42 verbatim
@[simp] lemma mem_finsetArithmetize_iff {x : V} {s : Finset V} :
    x ∈ s.arithmetize ↔ x ∈ s := by simp [Finset.arithmetize]


-- @@ L44-45 verbatim
@[simp] lemma finset_empty_arithmetize : (∅ : Finset V).arithmetize = ∅ := by
  simp [Finset.arithmetize]


-- @@ L47-49 verbatim
@[simp] lemma finset_insert_arithmetize (a : V) (s : Finset V) :
    (insert a s).arithmetize = insert a s.arithmetize := mem_ext <| by
  intro x; simp


-- @@ L51-51 verbatim
end Arith

-- @@ L52-52 verbatim
end LO


-- @@ L54-54 verbatim
end «lp_nc_section_1»
