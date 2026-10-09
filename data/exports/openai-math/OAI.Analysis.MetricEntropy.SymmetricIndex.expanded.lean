import Mathlib.Data.Sym.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.EquivFin


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-13 verbatim
/-!
# Symmetric indices of tuples

A tuple is sent to its literal multiset of entries. Repeated entries are retained.
Two tuples have the same index exactly when a permutation of their slots relates them.
-/


-- @@ L15-15 verbatim
namespace MetricEntropyDuality


-- @@ L17-19 verbatim
/-- The multiset of entries of a tuple, including every repetition. -/
def tupleSym {r j : ℕ} (a : Fin j → Fin r) : Sym (Fin r) j :=
  ⟨(List.ofFn a : Multiset (Fin r)), by simp⟩


-- @@ L21-23 verbatim
@[simp]
theorem coe_tupleSym {r j : ℕ} (a : Fin j → Fin r) :
    (tupleSym a : Multiset (Fin r)) = (List.ofFn a : Multiset (Fin r)) := rfl


-- @@ L25-29 verbatim
@[simp]
theorem tupleSym_cons {r j : ℕ} (a : Fin r) (args : Fin j → Fin r) :
    tupleSym (Fin.cons a args) = Sym.cons a (tupleSym args) := by
  apply Sym.ext
  simp only [coe_tupleSym, List.ofFn_cons, Sym.coe_cons, Multiset.cons_coe]


-- @@ L31-41 verbatim
/-- Every multiset of the prescribed size is represented by a tuple. -/
theorem tupleSym_surjective (r j : ℕ) : Function.Surjective (@tupleSym r j) := by
  induction j with
  | zero =>
      intro s
      exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  | succ j ih =>
      intro s
      rcases Sym.exists_eq_cons_of_succ s with ⟨a, t, rfl⟩
      obtain ⟨args, rfl⟩ := ih t
      exact ⟨Fin.cons a args, tupleSym_cons a args⟩


-- @@ L43-47 verbatim
@[simp]
theorem tupleSym_comp_perm {r j : ℕ} (a : Fin j → Fin r)
    (σ : Equiv.Perm (Fin j)) : tupleSym (a ∘ σ) = tupleSym a := by
  apply Sym.ext
  exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm a)


-- @@ L49-55 verbatim
/-- A multiset count is the number of slots carrying that basis index. -/
theorem tupleSym_count {r j : ℕ} (a : Fin j → Fin r) (x : Fin r) :
    (tupleSym a : Multiset (Fin r)).count x = Fintype.card {i // a i = x} := by
  classical
  simpa only [coe_tupleSym, Multiset.coe_count, Fintype.card_subtype,
    List.Vector.get_ofFn, List.Vector.toList_ofFn] using
    (Fin.card_filter_univ_eq_vector_get_eq_count x (List.Vector.ofFn a)).symm


-- @@ L57-72 verbatim
/-- Equality of indices is precisely permutation of tuple slots. -/
theorem tupleSym_eq_iff {r j : ℕ} (a b : Fin j → Fin r) :
    tupleSym a = tupleSym b ↔ ∃ σ : Equiv.Perm (Fin j), a ∘ σ = b := by
  classical
  constructor
  · intro h
    have hc (x : Fin r) : Fintype.card {i // b i = x} = Fintype.card {i // a i = x} := by
      simpa only [tupleSym_count] using
        congrArg (fun s : Sym (Fin r) j => (s : Multiset (Fin r)).count x) h.symm
    let es : ∀ x : Fin r, {i // b i = x} ≃ {i // a i = x} :=
      fun x => Fintype.equivOfCardEq (hc x)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨σ, rfl⟩
    exact (tupleSym_comp_perm a σ).symm


-- @@ L74-74 verbatim
end MetricEntropyDuality


-- @@ L76-76 verbatim
end OAI
