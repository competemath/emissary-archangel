import OAI.Combinatorics.Sensitivity.RecursiveDefinitions


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Each row clause uses exactly the stated number of distinct child blocks. -/


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical


-- @@ L10-10 verbatim
namespace Paper320


-- @@ L12-15 verbatim
def rowChildren {k r : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (i : Fin k) : Finset (Fin k × Fin r) :=
  Finset.univ.image (fun c => (i, c)) ∪
    (Finset.univ.filter (T.Adj i)).image (fun j => (j, label i j))


-- @@ L17-26 verbatim
theorem rowChildren_disjoint {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (i : Fin k) :
    Disjoint (Finset.univ.image fun c => (i, c))
      ((Finset.univ.filter (T.Adj i)).image fun j => (j, label i j)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hq
  have hji : j = i := congrArg Prod.fst he
  exact T.loopless i (hji ▸ (Finset.mem_filter.mp hj).2)


-- @@ L28-34 verbatim
theorem rowChildren_card {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (i : Fin k) :
    (rowChildren T label i).card = r + (Finset.univ.filter (T.Adj i)).card := by
  rw [rowChildren, Finset.card_union_of_disjoint (rowChildren_disjoint T label i)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp


-- @@ L36-40 verbatim
theorem regular_rowChildren_card {M r : ℕ} (T : RegularTournament M)
    (label : Fin (2 * M ^ 2 + 1) → Fin (2 * M ^ 2 + 1) → Fin r)
    (i : Fin (2 * M ^ 2 + 1)) :
    (rowChildren T.toTournament label i).card = r + M ^ 2 := by
  rw [rowChildren_card, T.outdegree]


-- @@ L42-42 verbatim
end Paper320


-- @@ L44-44 verbatim
end


-- @@ L46-46 verbatim
end OAI
