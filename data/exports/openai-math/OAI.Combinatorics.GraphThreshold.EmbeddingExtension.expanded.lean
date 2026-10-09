import Mathlib.Logic.Equiv.Fintype


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-7 verbatim
/-! Two placements of the same finite graph differ by an ambient permutation.
The statement is about arbitrary embeddings and therefore preserves isolated
vertices as well as vertices incident to edges. -/


-- @@ L9-9 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L11-21 verbatim
theorem exists_perm_comp_embedding {α β : Type*} [Finite β]
    (f g : α ↪ β) : ∃ σ : Equiv.Perm β, ∀ a, σ (f a) = g a := by
  classical
  let : Finite α := Finite.of_injective f f.injective
  let : Fintype α := Fintype.ofFinite α
  let e : Set.range f ≃ Set.range g := f.toEquivRange.symm.trans g.toEquivRange
  refine ⟨e.extendSubtype, ?_⟩
  intro a
  rw [e.extendSubtype_apply_of_mem (f a) ⟨a, rfl⟩]
  change (e (f.toEquivRange a) : β) = g a
  simp [e]


-- @@ L23-23 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L25-25 verbatim
end OAI
