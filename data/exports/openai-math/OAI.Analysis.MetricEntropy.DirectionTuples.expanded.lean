import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Pairwise.Basic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
universe uU uE


-- @@ L10-15 verbatim
/-!
# Supports and events for direction tuples

Tuples are arbitrary functions from `Fin h`; repeated indices are allowed.
The support records distinct indices, so its cardinality can be smaller than `h`.
-/


-- @@ L17-17 verbatim
namespace MetricEntropyDuality


-- @@ L19-19 verbatim
variable {U : Type uU} {E : Type uE} {h w : ℕ}


-- @@ L21-24 verbatim
/-- The set of indices appearing in an ordered tuple, including repeated-index tuples. -/
noncomputable def tupleSupport (a : Fin h → U) : Finset U := by
  classical
  exact Finset.univ.image a


-- @@ L26-29 verbatim
@[simp] theorem mem_tupleSupport {a : Fin h → U} {x : U} :
    x ∈ tupleSupport a ↔ ∃ j, a j = x := by
  classical
  simp [tupleSupport]


-- @@ L31-34 verbatim
theorem tupleSupport_card_le (a : Fin h → U) : (tupleSupport a).card ≤ h := by
  classical
  simpa only [tupleSupport, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_image_le (s := Finset.univ) (f := a))


-- @@ L36-38 verbatim
theorem tupleSupport_nonempty (hh : 0 < h) (a : Fin h → U) :
    (tupleSupport a).Nonempty :=
  ⟨a ⟨0, hh⟩, mem_tupleSupport.mpr ⟨⟨0, hh⟩, rfl⟩⟩


-- @@ L40-47 verbatim
theorem tupleSupport_subset_iff {a : Fin h → U} {T : Finset U} :
    tupleSupport a ⊆ T ↔ ∀ j, a j ∈ T := by
  constructor
  · intro ha j
    exact ha (mem_tupleSupport.mpr ⟨j, rfl⟩)
  · intro ha x hx
    obtain ⟨j, rfl⟩ := mem_tupleSupport.mp hx
    exact ha j


-- @@ L49-51 verbatim
/-- Different tuples in the list use disjoint sets of indices. -/
def DisjointSupports (L : Fin w → Fin h → U) : Prop :=
  Pairwise fun i j => Disjoint (tupleSupport (L i)) (tupleSupport (L j))


-- @@ L53-57 verbatim
/-- Samples for which the specified tuple of sampled values satisfies `bad`. -/
noncomputable def tupleEvent [Fintype U] [Fintype E]
    (bad : (Fin h → E) → Prop) (a : Fin h → U) : Finset (U → E) := by
  classical
  exact Finset.univ.filter fun t => bad (fun j => t (a j))


-- @@ L59-63 verbatim
@[simp] theorem mem_tupleEvent [Fintype U] [Fintype E]
    {bad : (Fin h → E) → Prop} {a : Fin h → U} {t : U → E} :
    t ∈ tupleEvent bad a ↔ bad (fun j => t (a j)) := by
  classical
  simp [tupleEvent]


-- @@ L65-65 verbatim
end MetricEntropyDuality


-- @@ L67-67 verbatim
end OAI
