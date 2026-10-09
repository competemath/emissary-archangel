import OAI.Combinatorics.Sensitivity.Tournament
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Order.Interval.Finset.Fin


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
/-! The literal regular tournament on an odd cyclic set. -/


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped Classical


-- @@ L13-13 verbatim
namespace Paper320


-- @@ L15-27 verbatim
def cyclicTournament (a : ℕ) : Tournament (2*a+1) where
  Adj i j := 0 < (j-i).val ∧ (j-i).val ≤ a
  loopless i := by simp
  edge_compl := by
    intro i j hij
    have hδ : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    have hp : 0 < (j-i).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hδ)
    have hb := (j-i).isLt
    have hn : (i-j).val = 2*a+1-(j-i).val := by
      rw [← neg_sub j i, Fin.val_neg, ite_eq_right hδ]
    change (0 < (j-i).val ∧ (j-i).val ≤ a) ↔ ¬ (0 < (i-j).val ∧ (i-j).val ≤ a)
    rw [hn]
    omega


-- @@ L29-43 verbatim
theorem cyclicTournament_outdegree (a : ℕ) (i : Fin (2*a+1)) :
    (Finset.univ.filter ((cyclicTournament a).Adj i)).card = a := by
  let z : Fin (2*a+1) := 0
  let b : Fin (2*a+1) := ⟨a, by omega⟩
  have he : (Finset.Ioc z b).card =
      (Finset.univ.filter ((cyclicTournament a).Adj i)).card :=
    Finset.card_equiv (Equiv.addLeft i) (by
      intro x
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and]
      change (0 < x.val ∧ x.val ≤ a) ↔
        (0 < ((i+x)-i).val ∧ ((i+x)-i).val ≤ a)
      rw [add_sub_cancel_left])
  rw [← he, Fin.card_Ioc]
  change a - 0 = a
  exact Nat.sub_zero a


-- @@ L45-47 verbatim
def regularCyclicTournament (M : ℕ) : RegularTournament M where
  toTournament := cyclicTournament (M^2)
  outdegree := cyclicTournament_outdegree (M^2)


-- @@ L49-49 verbatim
end Paper320


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end OAI
