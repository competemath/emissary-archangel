import OAI.RepresentationTheory.FoulkesHowe.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
universe u


-- @@ L10-10 verbatim
namespace Problem346


-- @@ L12-18 verbatim
/-- Reindexing the factors of a symmetric monomial does not change it. -/
theorem symMonomial_perm_reindex (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin n → V)
    (τ : Equiv.Perm (Fin n)) :
    symMonomial n V (fun i => v (τ i)) = symMonomial n V v := by
  apply Subtype.ext
  exact Equiv.prod_comp τ (fun i => SymmetricAlgebra.ι ℂ V (v i))


-- @@ L20-31 verbatim
/-- The canonical averaging formula is invariant under independent permutations
of the entries in each row. -/
theorem foulkesFormula_inner_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V)
    (τ : Fin b → Equiv.Perm (Fin a)) :
    foulkesFormula a b V (fun j i => v j (τ j i)) =
      foulkesFormula a b V v := by
  classical
  unfold foulkesFormula
  congr 1
  exact Fintype.sum_equiv
    (Equiv.piCongrRight (fun j => Equiv.mulLeft (τ j))) _ _ (fun σ => rfl)


-- @@ L33-47 verbatim
/-- The canonical averaging formula is invariant under permutation of rows. -/
theorem foulkesFormula_outer_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V)
    (τ : Equiv.Perm (Fin b)) :
    foulkesFormula a b V (fun j i => v (τ j) i) =
      foulkesFormula a b V v := by
  classical
  unfold foulkesFormula
  congr 1
  apply Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl (Equiv.Perm (Fin a))))
  intro σ
  congr 1
  funext i
  simpa using symMonomial_perm_reindex b V
    (fun j => v j (σ (τ.symm j) i)) τ


-- @@ L49-49 verbatim
end Problem346


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end OAI
