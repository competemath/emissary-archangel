import OAI.Combinatorics.Sensitivity.LabelingConstraints
import OAI.Combinatorics.Sensitivity.FixedCoordinates
import Mathlib.Data.Fintype.EquivFin


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
/-! Exact counts of target-constant label constraints on sixteen vertices. -/


-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open scoped Classical BigOperators


-- @@ L12-12 verbatim
namespace Paper320.Tournament

-- @@ L13-13 verbatim
variable {k r n : ℕ} (T : Tournament k)


-- @@ L15-19 verbatim
def labelingEvent (v : Fin n → Fin k) (m : Fin n → Fin r) :
    Finset ((Fin k × Fin k) → Fin r) :=
  if Function.Injective v then
    Finset.univ.filter fun A => ∀ i j, T.Adj (v i) (v j) → A (v i, v j) = m j
  else ∅


-- @@ L21-24 verbatim
theorem mem_labelingEvent_iff {v : Fin n → Fin k} {m : Fin n → Fin r}
    {A : (Fin k × Fin k) → Fin r} (hv : Function.Injective v) :
    A ∈ T.labelingEvent v m ↔ ∀ i j, T.Adj (v i) (v j) → A (v i,v j) = m j := by
  simp only [labelingEvent, ite_eq_left hv, Finset.mem_filter, Finset.mem_univ, true_and]


-- @@ L26-34 verbatim
theorem labelingEvent_eq [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    T.labelingEvent v m = Finset.univ.filter fun A =>
      ∀ p ∈ T.internalEdges (Finset.univ.image v), A p = m (Function.invFun v p.2) := by
  rw [labelingEvent, ite_eq_left hv]
  apply Finset.filter_congr
  intro A _
  simpa only [Finset.mem_univ, forall_const] using
    T.labelingConstraint_iff Finset.univ v m hv A


-- @@ L36-47 verbatim
theorem card_labelingEvent [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    (T.labelingEvent v m).card = r ^ (k*k-n.choose 2) := by
  rw [T.labelingEvent_eq v m hv]
  have hc := card_fixedCoordinates (T.internalEdges (Finset.univ.image v))
    (fun p => m (Function.invFun v p.2))
  rw [T.card_internalEdges] at hc
  have hi : (Finset.univ.image v).card = n := by
    rw [Finset.card_image_of_injective _ hv]
    exact Fintype.card_fin n
  rw [hi] at hc
  simpa only [Fintype.card_fin, Fintype.card_prod] using hc


-- @@ L49-53 verbatim
theorem card_labelingEvent_le [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r) :
    (T.labelingEvent v m).card ≤ r ^ (k*k-n.choose 2) := by
  by_cases hv : Function.Injective v
  · exact (T.card_labelingEvent v m hv).le
  · simp only [labelingEvent, ite_eq_right hv, Finset.card_empty, Nat.zero_le]


-- @@ L55-57 verbatim
def badLabelings (n r : ℕ) : Finset ((Fin k × Fin k) → Fin r) :=
  Finset.univ.biUnion fun v : Fin n → Fin k =>
    Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m


-- @@ L59-63 verbatim
theorem labelingEvent_subset_bad {v : Fin n → Fin k} {m : Fin n → Fin r} :
    T.labelingEvent v m ⊆ T.badLabelings n r := by
  intro A hA
  exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨m,Finset.mem_univ _,hA⟩⟩


-- @@ L65-77 verbatim
theorem card_badLabelings_le [NeZero n] :
    (T.badLabelings n r).card ≤ k^n * r^n * r^(k*k-n.choose 2) := by
  calc
    (T.badLabelings n r).card ≤ ∑ v : Fin n → Fin k,
        (Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n → Fin k, ∑ _m : Fin n → Fin r, r^(k*k-n.choose 2) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ =>
        T.card_labelingEvent_le v m)
    _ = k^n * r^n * r^(k*k-n.choose 2) := by
      simp [Nat.mul_assoc]


-- @@ L79-79 verbatim
end Paper320.Tournament


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end OAI
