module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L8-8 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L10-12 verbatim
noncomputable def finsetArithmetizeAux : List V → V
  |      [] => ∅
  | x :: xs => insert x (finsetArithmetizeAux xs)


-- @@ L14-14 verbatim
@[simp] lemma finsetArithmetizeAux_nil : finsetArithmetizeAux ([] : List V) = ∅ := rfl


-- @@ L16-17 verbatim
@[simp] lemma finsetArithmetizeAux_cons (x : V) (xs) :
    finsetArithmetizeAux (x :: xs) = insert x (finsetArithmetizeAux xs) := rfl


-- @@ L19-20 verbatim
@[simp] lemma mem_finsetArithmetizeAux_iff {x : V} {s : List V} :
    x ∈ finsetArithmetizeAux s ↔ x ∈ s := by induction s <;> simp [*]


-- @@ L22-22 verbatim
noncomputable def _root_.Finset.arithmetize (s : Finset V) : V := finsetArithmetizeAux s.toList


-- @@ L24-26 verbatim
@[simp] lemma mem_finsetArithmetize_iff {x : V} {s : Finset V} :
    x ∈ s.arithmetize ↔ x ∈ s := by
  simp [Finset.arithmetize]


-- @@ L28-29 verbatim
@[simp] lemma finset_empty_arithmetize : (∅ : Finset V).arithmetize = ∅ := by
  simp [Finset.arithmetize]


-- @@ L31-33 verbatim
@[simp] lemma finset_insert_arithmetize (a : V) (s : Finset V) :
    (insert a s).arithmetize = insert a s.arithmetize := mem_ext <| by
  intro x; simp


-- @@ L35-35 verbatim
end FFL.FirstOrder.Arithmetic
