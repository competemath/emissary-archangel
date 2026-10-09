import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
/-! Finite tournaments and the target-constant labeling condition. -/


-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open scoped Classical


-- @@ L14-14 verbatim
namespace Paper320


-- @@ L16-18 verbatim
structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)


-- @@ L20-21 verbatim
structure RegularTournament (M : ℕ) extends Tournament (2 * M^2 + 1) where
  outdegree : ∀ i, (Finset.univ.filter (Adj i)).card = M^2


-- @@ L23-26 verbatim
structure GoodLabeling {k : ℕ} (T : Tournament k) (r : ℕ) where
  label : Fin k → Fin k → Fin r
  good : ∀ I : Finset (Fin k), I.card = 16 → ∀ m : Fin k → Fin r,
    ∃ i ∈ I, ∃ j ∈ I, T.Adj i j ∧ label i j ≠ m j


-- @@ L28-28 verbatim
namespace Tournament

-- @@ L29-29 verbatim
variable {k : ℕ} (T : Tournament k)


-- @@ L31-33 verbatim
theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h


-- @@ L35-36 verbatim
theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h


-- @@ L38-41 verbatim
theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)


-- @@ L43-49 verbatim
theorem internal_sink_unique {I : Finset (Fin k)} {i j : Fin k}
    (hi : i ∈ I) (hj : j ∈ I)
    (hsi : ∀ v ∈ I, ¬ T.Adj i v) (hsj : ∀ v ∈ I, ¬ T.Adj j v) : i = j := by
  by_contra h
  rcases T.adj_or_reverse h with hh | hh
  · exact hsi j hj hh
  · exact hsj i hi hh


-- @@ L51-51 verbatim
end Tournament


-- @@ L53-53 verbatim
namespace GoodLabeling

-- @@ L54-54 verbatim
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)


-- @@ L56-61 verbatim
theorem good_implies_card_lt_sixteen (I : Finset (Fin k)) (m : Fin k → Fin r)
    (h : ∀ i ∈ I, ∀ j ∈ I, T.Adj i j → A.label i j = m j) : I.card < 16 := by
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show 16 ≤ I.card by omega)
  obtain ⟨i, hi, j, hj, hij, hne⟩ := A.good J hJ m
  exact hne (h i (hJI hi) j (hJI hj) hij)


-- @@ L63-63 verbatim
end GoodLabeling

-- @@ L64-64 verbatim
end Paper320


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end OAI
