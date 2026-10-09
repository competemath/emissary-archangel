import OAI.Analysis.MetricEntropy.FormContraction
import OAI.Analysis.MetricEntropy.PartitionGraph
import Mathlib.Data.Fin.Tuple.Basic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
universe uK uι uα uV uA


-- @@ L9-17 verbatim
/-!
# Actual contraction labels obstruct short walks

One label is chosen for each edge of a hypothetical short walk. These labels
are padded to the full degree using one fixed member of the same set of
directions. Symmetry moves each edge's direction to the contracted slot, so
evaluation on this single tuple is constant along the walk. This contradicts
robust nonvanishing of the difference of its endpoints.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace MetricEntropyDuality


-- @@ L23-23 verbatim
namespace SymmetricForm


-- @@ L25-25 verbatim
variable {K : Type uK} [CommSemiring K] {r j : ℕ}


-- @@ L27-45 verbatim
/-- Equal contractions imply equal evaluations whenever the contracted vector
occurs in any slot. Repeated arguments are allowed. -/
theorem eval_eq_of_contract_eq (v : Fin r → K)
    (F G : SymmetricForm K r (j + 1))
    (hFG : contract v F = contract v G)
    (args : Fin (j + 1) → (Fin r → K)) (a : Fin (j + 1)) (ha : args a = v) :
    F.eval args = G.eval args := by
  classical
  let σ : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 a
  have hz : (args ∘ σ) 0 = v := by simp [σ, Function.comp_apply, ha]
  have hc : Fin.cons v (Fin.tail (args ∘ σ)) = args ∘ σ := by
    rw [← hz]
    exact Fin.cons_self_tail (args ∘ σ)
  calc
    F.eval args = F.eval (args ∘ σ) := (eval_comp_perm F args σ).symm
    _ = (contract v F).eval (Fin.tail (args ∘ σ)) := by rw [eval_contract, hc]
    _ = (contract v G).eval (Fin.tail (args ∘ σ)) := by rw [hFG]
    _ = G.eval (args ∘ σ) := by rw [eval_contract, hc]
    _ = G.eval args := eval_comp_perm G args σ


-- @@ L47-47 verbatim
end SymmetricForm


-- @@ L49-49 verbatim
namespace FieldGraphSeparation


-- @@ L51-51 verbatim
variable {K : Type uK} {ι : Type uι} [CommRing K] {r j : ℕ}


-- @@ L53-56 verbatim
/-- The partition labels are the actual symmetric coefficient contractions. -/
def labels (t : ι → (Fin r → K)) (i : ι)
    (F : SymmetricForm K r (j + 1)) : SymmetricForm K r j :=
  SymmetricForm.contract (t i) F


-- @@ L58-59 verbatim
private def padTuple {α : Type uα} {k h : ℕ} (a : Fin k → α) (filler : α) :
    Fin h → α := fun i => if hi : i.val < k then a ⟨i.val, hi⟩ else filler


-- @@ L61-67 verbatim
private theorem padTuple_mem {α : Type uα} {k h : ℕ} (T : Finset α)
    (a : Fin k → α) (filler : α) (ha : ∀ i, a i ∈ T) (hf : filler ∈ T)
    (i : Fin h) : padTuple a filler i ∈ T := by
  unfold padTuple
  split_ifs with hi
  · exact ha ⟨i.val, hi⟩
  · exact hf


-- @@ L69-72 verbatim
private theorem padTuple_cast {α : Type uα} {k h : ℕ} (a : Fin k → α)
    (filler : α) (hkh : k ≤ h) (i : Fin k) :
    padTuple a filler (⟨i.val, lt_of_lt_of_le i.isLt hkh⟩ : Fin h) = a i := by
  simp only [padTuple, dite_eq_left i.isLt]


-- @@ L74-88 verbatim
/-- A finite walk along which a function agrees at each consecutive pair has
equal values at its endpoints. This includes the empty walk. -/
private theorem eval_eq_of_walk_steps {V : Type uV} {A : Type uA} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (f : V → A)
    (hf : ∀ n, n < w.length → f (w.getVert n) = f (w.getVert (n + 1))) :
    f x = f y := by
  have hconst : ∀ n, n ≤ w.length → f (w.getVert n) = f x := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        exact (hf n (Nat.lt_of_succ_le hn)).symm.trans
          (ih (Nat.le_of_succ_le hn))
  simpa only [SimpleGraph.Walk.getVert_length] using (hconst w.length le_rfl).symm


-- @@ L90-118 verbatim
/-- A robustly nonzero form difference rules out every short walk in the
actual contraction partition graph. No separation certificate is assumed. -/
theorem no_short_walk (t : ι → (Fin r → K)) (T : Finset ι) (hT : T.Nonempty)
    (x y : SymmetricForm K r (j + 1))
    (hrobust : ∀ a : Fin (j + 1) → ι, (∀ l, a l ∈ T) →
      (y - x).eval (fun l => t (a l)) ≠ 0)
    (w : (PartitionGraph.graph (labels t) T).Walk x y) : j + 1 < w.length := by
  classical
  by_contra hlong
  have hlength : w.length ≤ j + 1 := Nat.le_of_not_gt hlong
  obtain ⟨filler, hfiller⟩ := hT
  have hedge : ∀ l : Fin w.length, ∃ i ∈ T,
      labels t i (w.getVert l.val) = labels t i (w.getVert (l.val + 1)) := by
    intro l
    have hadj := w.adj_getVert_succ l.isLt
    change _ ≠ _ ∧ ∃ i ∈ T, labels t i _ = labels t i _ at hadj
    exact hadj.2
  choose edge hedge_mem hedge_eq using hedge
  let a : Fin (j + 1) → ι := padTuple edge filler
  have ha : ∀ l, a l ∈ T := padTuple_mem T edge filler hedge_mem hfiller
  have heval : x.eval (fun l => t (a l)) = y.eval (fun l => t (a l)) := by
    apply eval_eq_of_walk_steps w (fun F => F.eval (fun l => t (a l)))
    intro n hn
    let l : Fin w.length := ⟨n, hn⟩
    apply SymmetricForm.eval_eq_of_contract_eq (t (edge l)) _ _ (hedge_eq l)
      (fun l => t (a l)) (⟨n, lt_of_lt_of_le hn hlength⟩ : Fin (j + 1))
    exact congrArg t (padTuple_cast edge filler hlength l)
  apply hrobust a ha
  rw [SymmetricForm.eval_sub, heval, sub_self]


-- @@ L120-127 verbatim
/-- Separation in the extended graph metric, including disconnected endpoints. -/
theorem distance_gt (t : ι → (Fin r → K)) (T : Finset ι) (hT : T.Nonempty)
    (x y : SymmetricForm K r (j + 1))
    (hrobust : ∀ a : Fin (j + 1) → ι, (∀ l, a l ∈ T) →
      (y - x).eval (fun l => t (a l)) ≠ 0) :
    ((j + 1 : ℕ) : ℕ∞) < PartitionGraph.distance (labels t) T x y := by
  exact PartitionGraph.lt_distance_of_forall_walk (labels t) T
    (no_short_walk t T hT x y hrobust)


-- @@ L129-129 verbatim
end FieldGraphSeparation

-- @@ L130-130 verbatim
end MetricEntropyDuality


-- @@ L132-132 verbatim
end


-- @@ L134-134 verbatim
end OAI
