import OAI.Combinatorics.SecondNeighborhood.PruningDefinitions
import OAI.Combinatorics.SecondNeighborhood.ReductionCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SeymourSecondNeighborhood.Extremal


-- @@ L9-9 verbatim
open Pruning

-- @@ L10-10 verbatim
open scoped BigOperators


-- @@ L12-12 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V]


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-17 verbatim
def diagonal : Finset (V × V) :=
  Finset.univ.filter (fun z => z.1 = z.2)


-- @@ L19-20 verbatim
def column (P : Finset (V × V)) (j : V) : Finset V :=
  Finset.univ.filter (fun p => (p, j) ∈ P)


-- @@ L22-23 verbatim
def row (Q : Finset (V × V)) (i : V) : Finset V :=
  Finset.univ.filter (fun s => (i, s) ∈ Q)


-- @@ L25-27 verbatim
@[simp] theorem mem_diagonal {z : V × V} :
    z ∈ diagonal ↔ z.1 = z.2 := by
  simp [diagonal]


-- @@ L29-30 verbatim
@[simp] theorem diagonal_mem (v : V) : (v, v) ∈ (diagonal : Finset (V × V)) := by
  exact mem_diagonal.mpr rfl


-- @@ L32-34 verbatim
@[simp] theorem mem_column {P : Finset (V × V)} {j p : V} :
    p ∈ column P j ↔ (p, j) ∈ P := by
  simp [column]


-- @@ L36-38 verbatim
@[simp] theorem mem_row {Q : Finset (V × V)} {i s : V} :
    s ∈ row Q i ↔ (i, s) ∈ Q := by
  simp [row]


-- @@ L40-44 verbatim
@[simp] theorem column_leftImage (r : V → V → Prop) (P : Finset (V × V)) (j : V) :
    column (leftImage r P) j = image r (column P j) := by
  classical
  ext i
  simp


-- @@ L46-50 verbatim
@[simp] theorem row_rightImage (r : V → V → Prop) (Q : Finset (V × V)) (i : V) :
    row (rightImage r Q) i = image r (row Q i) := by
  classical
  ext j
  simp


-- @@ L52-57 verbatim
theorem card_eq_sum_card_column (P : Finset (V × V)) :
    P.card = ∑ j : V, (column P j).card := by
  classical
  simpa only [← Finset.card_eq_sum_ones] using
    (Finset.sum_finset_product_right P Finset.univ (column P)
      (by intro z; simp) (f := fun _ => (1 : ℕ)))


-- @@ L59-64 verbatim
theorem card_eq_sum_card_row (Q : Finset (V × V)) :
    Q.card = ∑ i : V, (row Q i).card := by
  classical
  simpa only [← Finset.card_eq_sum_ones] using
    (Finset.sum_finset_product Q Finset.univ (row Q)
      (by intro z; simp) (f := fun _ => (1 : ℕ)))


-- @@ L66-79 verbatim
theorem strict_leftImage_growth [Nonempty V]
    (r : V → V → Prop) (P : Finset (V × V)) (hgrowth : StrictSubsetGrowth r)
    (hnonempty : ∀ j, (column P j).Nonempty)
    (hproper : ∀ j, column P j ≠ Finset.univ) :
    P.card + (leftImage r (leftImage r P)).card < 2 * (leftImage r P).card := by
  classical
  have hsum :
      (∑ j : V, ((column P j).card + (column (leftImage r (leftImage r P)) j).card)) <
        ∑ j : V, 2 * (column (leftImage r P) j).card := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro j _
    simpa only [column_leftImage] using
      hgrowth (column P j) (hnonempty j) (hproper j)
  simpa only [Nat.two_mul, Finset.sum_add_distrib, ← card_eq_sum_card_column] using hsum


-- @@ L81-94 verbatim
theorem strict_rightImage_growth [Nonempty V]
    (r : V → V → Prop) (Q : Finset (V × V)) (hgrowth : StrictSubsetGrowth r)
    (hnonempty : ∀ i, (row Q i).Nonempty)
    (hproper : ∀ i, row Q i ≠ Finset.univ) :
    Q.card + (rightImage r (rightImage r Q)).card < 2 * (rightImage r Q).card := by
  classical
  have hsum :
      (∑ i : V, ((row Q i).card + (row (rightImage r (rightImage r Q)) i).card)) <
        ∑ i : V, 2 * (row (rightImage r Q) i).card := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    simpa only [row_rightImage] using
      hgrowth (row Q i) (hnonempty i) (hproper i)
  simpa only [Nat.two_mul, Finset.sum_add_distrib, ← card_eq_sum_card_row] using hsum


-- @@ L96-96 verbatim
end

-- @@ L97-97 verbatim
end SeymourSecondNeighborhood.Extremal


-- @@ L99-99 verbatim
end OAI
